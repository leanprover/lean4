// Lean compiler output
// Module: Lean.Elab.Do.InferControlInfo
// Imports: public import Lean.Elab.Term meta import Lean.Parser.Do import Lean.Elab.Do.PatternVar
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
extern lean_object* l_Lean_NameSet_empty;
static lean_once_cell_t l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo_default;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instInhabitedControlInfo;
static lean_once_cell_t l_Lean_Elab_Do_ControlInfo_pure___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_ControlInfo_pure___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_pure;
lean_object* l_Lean_NameSet_append(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = ", exitsRegularly: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0_value;
lean_object* l_Lean_stringToMessageData(lean_object*);
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = ",\n    reassigns: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3;
lean_object* l_Id_instMonad___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value;
lean_object* l_Id_instMonad___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__1___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value;
lean_object* l_Id_instMonad___lam__2___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__2___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value;
lean_object* l_Id_instMonad___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__3, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value;
lean_object* l_Id_instMonad___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__4___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value;
lean_object* l_Id_instMonad___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__5___boxed, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value;
lean_object* l_Id_instMonad___lam__6(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Id_instMonad___lam__6, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__4_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__5_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*5 + 0, .m_other = 5, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__11_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__6_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__7_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__8_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__9_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__12_value),((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__10_value)}};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13_value;
lean_object* l_Lean_MessageData_ofName(lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_MessageData_ofName, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = ",\n    returnsEarly: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "false"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "true"};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18_value;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "breaks: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20;
static const lean_string_object l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = ", continues: "};
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21_value;
static lean_once_cell_t l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22;
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_foldrM___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofList(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value;
static const lean_closure_object l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__0_value)} };
static const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1 = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo = (const lean_object*)&l_Lean_Elab_Do_instToMessageDataControlInfo___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 28, .m_capacity = 28, .m_length = 27, .m_data = "builtin_doElem_control_info"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value;
lean_object* l_Lean_Name_mkStr1(lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__0_value),LEAN_SCALAR_PTR_LITERAL(29, 75, 74, 17, 172, 74, 138, 206)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "doElem_control_info"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__2_value),LEAN_SCALAR_PTR_LITERAL(252, 182, 102, 169, 76, 87, 55, 254)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doElem"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value;
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value_aux_2),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__7_value),LEAN_SCALAR_PTR_LITERAL(208, 65, 144, 138, 55, 55, 217, 220)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ControlInfoHandler"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value;
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value_aux_2),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__11_value),LEAN_SCALAR_PTR_LITERAL(18, 126, 127, 228, 104, 205, 61, 148)}};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12_value;
static const lean_string_object l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "control info inference"};
static const lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13 = (const lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13_value;
lean_object* l_Lean_Elab_mkElabAttribute___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "controlInfoElemAttribute"};
static const lean_object* l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__9_value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__10_value),LEAN_SCALAR_PTR_LITERAL(84, 203, 110, 70, 49, 253, 106, 1)}};
static const lean_ctor_object l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value_aux_2),((lean_object*)&l_Lean_Elab_Do_initFn___closed__0_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(13, 110, 218, 82, 47, 2, 10, 58)}};
static const lean_object* l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute;
static const lean_string_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 249, .m_capacity = 249, .m_length = 246, .m_data = "Registers a `ControlInfo` inference handler for the given `doElem` syntax node kind.\n\nA handler should have type `ControlInfoHandler` (i.e. `TSyntax \\`doElem → TermElabM ControlInfo`).\nFor pure handlers, use `fun stx => return ControlInfo.pure`.\n"};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0_value;
lean_object* l_Lean_addBuiltinDocString(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object*);
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(70) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(78) << 1) | 1)),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__0_value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__1_value),((lean_object*)(((size_t)(39) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(77) << 1) | 1)),((lean_object*)(((size_t)(19) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(77) << 1) | 1)),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__3_value),((lean_object*)(((size_t)(19) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__4_value),((lean_object*)(((size_t)(43) << 1) | 1))}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value;
static const lean_ctor_object l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__2_value),((lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__5_value)}};
static const lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6 = (const lean_object*)&l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6_value;
lean_object* l_Lean_addBuiltinDeclarationRanges(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object*);
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0;
static const lean_string_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "while expanding"};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__1 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__1_value;
static const lean_ctor_object l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__1_value)}};
static const lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__2 = (const lean_object*)&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__2_value;
static lean_once_cell_t l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3;
lean_object* l_Lean_MessageData_ofSyntax(lean_object*);
lean_object* l_Lean_indentD(lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "with resulting expansion"};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__0_value)}};
static const lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__1 = (const lean_object*)&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__1_value;
static lean_once_cell_t l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2;
extern lean_object* l_Lean_Elab_pp_macroStack;
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_st_ref_get(lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_getBetterRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_NameSet_insert(lean_object*, lean_object*);
size_t lean_usize_add(size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t, uint8_t, lean_object*, size_t, size_t, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* l_Lean_mkPrivateName(lean_object*, lean_object*);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_privateToUserName(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "runtime"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__0 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__0_value;
static const lean_string_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "maxRecDepth"};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__1 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__1_value;
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(2, 128, 123, 132, 117, 90, 116, 101)}};
static const lean_ctor_object l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2_value_aux_0),((lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__1_value),LEAN_SCALAR_PTR_LITERAL(88, 230, 219, 180, 63, 89, 202, 3)}};
static const lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2 = (const lean_object*)&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2_value;
extern lean_object* l_Lean_maxRecDepthErrorMessage;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4;
static lean_once_cell_t l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5;
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t l_Lean_instBEqExtraModUse_beq(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg___boxed(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_left(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0;
size_t lean_usize_sub(size_t, size_t);
static lean_once_cell_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1;
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
size_t lean_usize_shift_right(size_t, size_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg(lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___boxed(lean_object*, lean_object*, lean_object*);
uint64_t l_Lean_instHashableExtraModUse_hash(lean_object*);
size_t lean_uint64_to_usize(uint64_t);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg___boxed(lean_object*, lean_object*);
double lean_float_of_nat(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static double l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0;
static const lean_string_object l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1 = (const lean_object*)&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2;
lean_object* lean_st_ref_take(lean_object*);
lean_object* l_Lean_PersistentArray_push___redArg(lean_object*, lean_object*);
lean_object* lean_st_ref_set(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "trace"};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_value;
static const lean_ctor_object l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__0_value),LEAN_SCALAR_PTR_LITERAL(212, 145, 141, 177, 67, 149, 127, 197)}};
static const lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1 = (const lean_object*)&l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1_value;
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_instBEqExtraModUse_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instBEqExtraModUse_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__0 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__0_value;
lean_object* l_Lean_instHashableExtraModUse_hash___boxed(lean_object*);
static const lean_closure_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instHashableExtraModUse_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__1 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__1_value;
lean_object* l_Lean_PersistentHashMap_empty(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2;
lean_object* l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_object*, lean_object*);
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "extraModUses"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__7 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__7_value;
static const lean_ctor_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__7_value),LEAN_SCALAR_PTR_LITERAL(27, 95, 70, 98, 97, 66, 56, 109)}};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__8 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__8_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = " extra mod use "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__9 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__9_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " of "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__11 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__11_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "recording "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__14 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__14_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = " "};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__16 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__16_value;
static lean_once_cell_t l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "regular"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__18 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__18_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "meta"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__19 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__19_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "private"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__20 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__20_value;
static const lean_string_object l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "public"};
static const lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__21 = (const lean_object*)&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__21_value;
extern lean_object* l___private_Lean_ExtraModUses_0__Lean_extraModUses;
lean_object* l_Lean_PersistentEnvExtension_addEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isAnonymous(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Environment_header(lean_object*);
extern lean_object* l_Lean_instInhabitedEffectiveImport_default;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg___boxed(lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0;
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_usize_of_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__0 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__0_value;
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
static const lean_closure_object l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__1 = (const lean_object*)&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__1_value;
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2;
static lean_once_cell_t l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__3;
size_t lean_array_size(lean_object*);
lean_object* l_Lean_Environment_getModuleIdxFor_x3f(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
extern lean_object* l_Lean_indirectModUseExt;
uint8_t l_Lean_isMarkedMeta(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveNamespace(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ResolveName_resolveGlobalName(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 158, .m_capacity = 158, .m_length = 157, .m_data = "maximum recursion depth has been reached\nuse `set_option maxRecDepth <num>` to increase limit\nuse `set_option diagnostics true` to get diagnostic information"};
static const lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0 = (const lean_object*)&l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0_value;
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_string_dec_eq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__0_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1_value;
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__0_value),LEAN_SCALAR_PTR_LITERAL(156, 165, 255, 22, 123, 199, 70, 61)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "matchExprPat"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__2_value),LEAN_SCALAR_PTR_LITERAL(34, 152, 68, 102, 242, 224, 57, 35)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doForDecl"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__0_value),LEAN_SCALAR_PTR_LITERAL(149, 147, 251, 147, 43, 72, 7, 132)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t, size_t, lean_object*);
uint8_t l_Lean_Syntax_isNone(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0 = (const lean_object*)&l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0_value;
uint8_t l_Lean_instBEqInternalExceptionId_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Exception_isInterrupt(lean_object*);
uint8_t l_Lean_Exception_isRuntime(lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6;
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "letDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__0_value),LEAN_SCALAR_PTR_LITERAL(61, 47, 121, 206, 37, 68, 134, 111)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = "No `ControlInfo` inference handler found for `"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "` in syntax "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 49, .m_capacity = 49, .m_length = 48, .m_data = "\nRegister a handler with `@[doElem_control_info "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "]`."};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doBreak"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__10_value),LEAN_SCALAR_PTR_LITERAL(100, 48, 134, 252, 224, 171, 60, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doContinue"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__12_value),LEAN_SCALAR_PTR_LITERAL(99, 212, 187, 103, 216, 35, 231, 189)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doReturn"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__14_value),LEAN_SCALAR_PTR_LITERAL(210, 201, 30, 244, 146, 7, 54, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__16_value),LEAN_SCALAR_PTR_LITERAL(130, 168, 60, 255, 153, 218, 88, 77)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doNested"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__18_value),LEAN_SCALAR_PTR_LITERAL(220, 154, 41, 109, 103, 76, 110, 63)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doLet"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__20_value),LEAN_SCALAR_PTR_LITERAL(60, 171, 222, 145, 87, 124, 9, 205)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "doHave"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__22_value),LEAN_SCALAR_PTR_LITERAL(103, 74, 100, 51, 242, 214, 142, 115)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doLetRec"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__24_value),LEAN_SCALAR_PTR_LITERAL(82, 47, 84, 182, 64, 225, 123, 219)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetElse"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__26_value),LEAN_SCALAR_PTR_LITERAL(175, 153, 29, 134, 242, 228, 141, 99)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doIdDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__0_value),LEAN_SCALAR_PTR_LITERAL(41, 95, 84, 160, 28, 70, 78, 179)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__2_value),LEAN_SCALAR_PTR_LITERAL(205, 158, 71, 138, 110, 159, 158, 208)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 40, .m_capacity = 40, .m_length = 39, .m_data = "Not a let or reassignment declaration: "};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__8_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__11_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__11_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__11_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__10_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__11 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__11_value;
lean_object* l_Lean_Syntax_formatStx(lean_object*, lean_object*, uint8_t);
extern lean_object* l_Std_Format_defWidth;
lean_object* l_Std_Format_pretty(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getPatternVarsEx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doLetArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__28_value),LEAN_SCALAR_PTR_LITERAL(155, 105, 77, 168, 26, 188, 17, 34)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doReassign"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__30_value),LEAN_SCALAR_PTR_LITERAL(31, 163, 103, 78, 29, 183, 93, 39)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "doReassignArrow"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__32_value),LEAN_SCALAR_PTR_LITERAL(24, 63, 28, 32, 90, 193, 231, 114)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doMatch"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__34_value),LEAN_SCALAR_PTR_LITERAL(29, 50, 175, 23, 122, 111, 148, 60)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "doIf"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__36_value),LEAN_SCALAR_PTR_LITERAL(133, 56, 102, 181, 14, 156, 21, 0)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doUnless"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__38_value),LEAN_SCALAR_PTR_LITERAL(231, 120, 137, 73, 40, 67, 249, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doFor"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__40_value),LEAN_SCALAR_PTR_LITERAL(164, 12, 178, 2, 144, 97, 71, 235)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "doTry"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__42_value),LEAN_SCALAR_PTR_LITERAL(183, 105, 89, 167, 131, 32, 5, 203)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "doDbgTrace"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__44_value),LEAN_SCALAR_PTR_LITERAL(34, 125, 157, 23, 122, 81, 121, 195)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "doAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__46_value),LEAN_SCALAR_PTR_LITERAL(171, 15, 212, 125, 46, 208, 251, 33)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doDebugAssert"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__48_value),LEAN_SCALAR_PTR_LITERAL(219, 254, 62, 12, 192, 208, 196, 20)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "doMatchExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__50_value),LEAN_SCALAR_PTR_LITERAL(72, 0, 49, 218, 206, 236, 229, 165)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doLetExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__52_value),LEAN_SCALAR_PTR_LITERAL(68, 239, 85, 151, 235, 111, 29, 229)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "doLetMetaExpr"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__54_value),LEAN_SCALAR_PTR_LITERAL(231, 210, 172, 145, 91, 221, 30, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "matchExprAlts"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__56_value),LEAN_SCALAR_PTR_LITERAL(88, 158, 245, 158, 91, 207, 89, 187)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "matchExprElseAlt"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__58_value),LEAN_SCALAR_PTR_LITERAL(249, 132, 98, 23, 98, 205, 167, 22)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__60_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "doCatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__0_value),LEAN_SCALAR_PTR_LITERAL(24, 196, 191, 146, 79, 230, 20, 8)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "doCatchMatch"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__2_value),LEAN_SCALAR_PTR_LITERAL(70, 106, 10, 98, 177, 11, 181, 30)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 29, .m_capacity = 29, .m_length = 28, .m_data = "Not a catch or catch match: "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4_value;
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "matchAlts"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__6_value),LEAN_SCALAR_PTR_LITERAL(193, 186, 26, 109, 82, 172, 197, 183)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "matchAlt"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value_aux_2),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__0_value),LEAN_SCALAR_PTR_LITERAL(178, 0, 203, 112, 215, 49, 100, 229)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1_value;
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
static lean_once_cell_t l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "doFinally"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__62_value),LEAN_SCALAR_PTR_LITERAL(94, 201, 209, 4, 148, 58, 33, 223)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t, lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "generalizingParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__64_value),LEAN_SCALAR_PTR_LITERAL(147, 206, 52, 232, 193, 222, 34, 109)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "dependentParam"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__66_value),LEAN_SCALAR_PTR_LITERAL(78, 215, 202, 78, 135, 250, 138, 86)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "letIdDeclNoBinders"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__68_value),LEAN_SCALAR_PTR_LITERAL(205, 0, 127, 82, 201, 96, 42, 5)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letPatDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__70_value),LEAN_SCALAR_PTR_LITERAL(9, 25, 156, 50, 29, 105, 147, 239)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "letRecDecls"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__72_value),LEAN_SCALAR_PTR_LITERAL(103, 117, 148, 85, 88, 242, 214, 126)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73_value;
static const lean_string_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "letRecDecl"};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value;
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__4_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_0),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__5_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_1),((lean_object*)&l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__6_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value_aux_2),((lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__74_value),LEAN_SCALAR_PTR_LITERAL(202, 48, 93, 231, 206, 172, 150, 190)}};
static const lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75 = (const lean_object*)&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75_value;
static lean_once_cell_t l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76;
lean_object* l_Lean_Syntax_getOptional_x3f(lean_object*);
lean_object* l_Lean_Elab_expandMacroImpl_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_KeyedDeclsAttribute_getEntries___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_reverse___redArg(lean_object*);
lean_object* l_Lean_Elab_Do_getLetPatDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Elab_Do_getLetIdDeclVars(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object*, size_t, size_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Parser_Term_getDoElems(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33(lean_object*, lean_object*, size_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo_default(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0, &l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0_once, _init_l_Lean_Elab_Do_instInhabitedControlInfo_default___closed__0);
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Do_instInhabitedControlInfo(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_Elab_Do_instInhabitedControlInfo_default;
return x_1;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; lean_object* x_4; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_unsigned_to_nat(1u);
x_3 = 0;
x_4 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_4, 0, x_2);
lean_ctor_set(x_4, 1, x_1);
lean_ctor_set_uint8(x_4, sizeof(void*)*2, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_4, sizeof(void*)*2 + 2, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Do_ControlInfo_pure(void) {
_start:
{
lean_object* x_1; 
x_1 = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
return x_1;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_sequence(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; lean_object* x_19; uint8_t x_20; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_6 = lean_ctor_get(x_1, 0);
x_7 = lean_ctor_get(x_1, 1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_6, x_19);
if (x_20 == 0)
{
uint8_t x_21; uint8_t x_22; uint8_t x_23; uint8_t x_26; 
lean_inc(x_7);
lean_dec_ref(x_1);
x_21 = 1;
if (x_3 == 0)
{
uint8_t x_29; 
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_26 = x_29;
goto block_28;
}
else
{
x_26 = x_21;
goto block_28;
}
block_25:
{
if (x_5 == 0)
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_8 = x_23;
x_9 = x_22;
x_10 = x_24;
goto block_18;
}
else
{
x_8 = x_23;
x_9 = x_22;
x_10 = x_21;
goto block_18;
}
}
block_28:
{
if (x_4 == 0)
{
uint8_t x_27; 
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_22 = x_26;
x_23 = x_27;
goto block_25;
}
else
{
x_22 = x_26;
x_23 = x_21;
goto block_25;
}
}
}
else
{
lean_dec_ref(x_2);
return x_1;
}
block_18:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; 
x_12 = lean_ctor_get(x_2, 1);
x_13 = l_Lean_NameSet_append(x_7, x_12);
lean_ctor_set(x_2, 1, x_13);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_9);
lean_ctor_set_uint8(x_2, sizeof(void*)*2 + 1, x_8);
lean_ctor_set_uint8(x_2, sizeof(void*)*2 + 2, x_10);
return x_2;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_14 = lean_ctor_get(x_2, 0);
x_15 = lean_ctor_get(x_2, 1);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_2);
x_16 = l_Lean_NameSet_append(x_7, x_15);
x_17 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_17, 0, x_14);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_uint8(x_17, sizeof(void*)*2, x_9);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 1, x_8);
lean_ctor_set_uint8(x_17, sizeof(void*)*2 + 2, x_10);
return x_17;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_ControlInfo_alternative(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; uint8_t x_10; uint8_t x_22; uint8_t x_23; uint8_t x_26; 
x_3 = lean_ctor_get_uint8(x_1, sizeof(void*)*2);
x_4 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 1);
x_5 = lean_ctor_get_uint8(x_1, sizeof(void*)*2 + 2);
x_6 = lean_ctor_get(x_1, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_1, 1);
lean_inc(x_7);
lean_dec_ref(x_1);
if (x_3 == 0)
{
uint8_t x_29; 
x_29 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_26 = x_29;
goto block_28;
}
else
{
x_26 = x_3;
goto block_28;
}
block_21:
{
uint8_t x_11; 
x_11 = !lean_is_exclusive(x_2);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_12 = lean_ctor_get(x_2, 0);
x_13 = lean_ctor_get(x_2, 1);
x_14 = lean_nat_add(x_6, x_12);
lean_dec(x_12);
lean_dec(x_6);
x_15 = l_Lean_NameSet_append(x_7, x_13);
lean_ctor_set(x_2, 1, x_15);
lean_ctor_set(x_2, 0, x_14);
lean_ctor_set_uint8(x_2, sizeof(void*)*2, x_8);
lean_ctor_set_uint8(x_2, sizeof(void*)*2 + 1, x_9);
lean_ctor_set_uint8(x_2, sizeof(void*)*2 + 2, x_10);
return x_2;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_16 = lean_ctor_get(x_2, 0);
x_17 = lean_ctor_get(x_2, 1);
lean_inc(x_17);
lean_inc(x_16);
lean_dec(x_2);
x_18 = lean_nat_add(x_6, x_16);
lean_dec(x_16);
lean_dec(x_6);
x_19 = l_Lean_NameSet_append(x_7, x_17);
x_20 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_uint8(x_20, sizeof(void*)*2, x_8);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 1, x_9);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 2, x_10);
return x_20;
}
}
block_25:
{
if (x_5 == 0)
{
uint8_t x_24; 
x_24 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_8 = x_22;
x_9 = x_23;
x_10 = x_24;
goto block_21;
}
else
{
x_8 = x_22;
x_9 = x_23;
x_10 = x_5;
goto block_21;
}
}
block_28:
{
if (x_4 == 0)
{
uint8_t x_27; 
x_27 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_22 = x_26;
x_23 = x_27;
goto block_25;
}
else
{
x_22 = x_26;
x_23 = x_4;
goto block_25;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__0));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__15));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__19));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__21));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; uint8_t x_4; uint8_t x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_29; lean_object* x_30; lean_object* x_39; lean_object* x_40; 
x_3 = lean_ctor_get_uint8(x_2, sizeof(void*)*2);
x_4 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 1);
x_5 = lean_ctor_get_uint8(x_2, sizeof(void*)*2 + 2);
x_6 = lean_ctor_get(x_2, 0);
lean_inc(x_6);
x_7 = lean_ctor_get(x_2, 1);
lean_inc(x_7);
lean_dec_ref(x_2);
x_39 = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__20);
if (x_3 == 0)
{
lean_object* x_49; 
x_49 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
x_40 = x_49;
goto block_48;
}
else
{
lean_object* x_50; 
x_50 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
x_40 = x_50;
goto block_48;
}
block_28:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; 
x_10 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_10, 0, x_9);
x_11 = l_Lean_MessageData_ofFormat(x_10);
x_12 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_12, 0, x_8);
lean_ctor_set(x_12, 1, x_11);
x_13 = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__1);
x_14 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_14, 0, x_12);
lean_ctor_set(x_14, 1, x_13);
x_15 = l_Nat_reprFast(x_6);
x_16 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_16, 0, x_15);
x_17 = l_Lean_MessageData_ofFormat(x_16);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_14);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__3);
x_20 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_20, 0, x_18);
lean_ctor_set(x_20, 1, x_19);
x_21 = lean_box(0);
x_22 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__13));
x_23 = l_Std_DTreeMap_Internal_Impl_foldrM___redArg(x_22, x_1, x_21, x_7);
x_24 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__14));
x_25 = l_List_mapTR_loop___redArg(x_24, x_23, x_21);
x_26 = l_Lean_MessageData_ofList(x_25);
x_27 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_27, 0, x_20);
lean_ctor_set(x_27, 1, x_26);
return x_27;
}
block_38:
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_31, 0, x_30);
x_32 = l_Lean_MessageData_ofFormat(x_31);
x_33 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_33, 0, x_29);
lean_ctor_set(x_33, 1, x_32);
x_34 = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__16);
x_35 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_35, 0, x_33);
lean_ctor_set(x_35, 1, x_34);
if (x_5 == 0)
{
lean_object* x_36; 
x_36 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
x_8 = x_35;
x_9 = x_36;
goto block_28;
}
else
{
lean_object* x_37; 
x_37 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
x_8 = x_35;
x_9 = x_37;
goto block_28;
}
}
block_48:
{
lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_41 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_41, 0, x_40);
x_42 = l_Lean_MessageData_ofFormat(x_41);
x_43 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_43, 0, x_39);
lean_ctor_set(x_43, 1, x_42);
x_44 = lean_obj_once(&l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22, &l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22_once, _init_l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__22);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
if (x_4 == 0)
{
lean_object* x_46; 
x_46 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__17));
x_29 = x_45;
x_30 = x_46;
goto block_38;
}
else
{
lean_object* x_47; 
x_47 = ((lean_object*)(l_Lean_Elab_Do_instToMessageDataControlInfo___lam__1___closed__18));
x_29 = x_45;
x_30 = x_47;
goto block_38;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_3 = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__1));
x_4 = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__3));
x_5 = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__8));
x_6 = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__12));
x_7 = ((lean_object*)(l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___closed__13));
x_8 = l_Lean_Elab_mkElabAttribute___redArg(x_3, x_4, x_5, x_6, x_7, x_1);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = ((lean_object*)(l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
x_3 = l_Lean_Elab_Do_mkControlInfoElemAttributeUnsafe(x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2____boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___closed__0));
x_4 = l_Lean_addBuiltinDocString(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3() {
_start:
{
lean_object* x_2; lean_object* x_3; lean_object* x_4; 
x_2 = ((lean_object*)(l_Lean_Elab_Do_initFn___closed__1_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_));
x_3 = ((lean_object*)(l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___closed__6));
x_4 = l_Lean_addBuiltinDeclarationRanges(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_box(1);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__2));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
return x_1;
}
else
{
uint8_t x_3; 
x_3 = !lean_is_exclusive(x_2);
if (x_3 == 0)
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = !lean_is_exclusive(x_4);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_6 = lean_ctor_get(x_2, 1);
x_7 = lean_ctor_get(x_4, 0);
x_8 = lean_ctor_get(x_4, 1);
lean_dec(x_8);
x_9 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0);
lean_ctor_set_tag(x_4, 7);
lean_ctor_set(x_4, 1, x_9);
lean_ctor_set(x_4, 0, x_1);
x_10 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3);
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_10);
x_11 = l_Lean_MessageData_ofSyntax(x_7);
x_12 = l_Lean_indentD(x_11);
x_13 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_13, 0, x_2);
lean_ctor_set(x_13, 1, x_12);
x_1 = x_13;
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; 
x_15 = lean_ctor_get(x_2, 1);
x_16 = lean_ctor_get(x_4, 0);
lean_inc(x_16);
lean_dec(x_4);
x_17 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0);
x_18 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_18, 0, x_1);
lean_ctor_set(x_18, 1, x_17);
x_19 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3);
lean_ctor_set_tag(x_2, 7);
lean_ctor_set(x_2, 1, x_19);
lean_ctor_set(x_2, 0, x_18);
x_20 = l_Lean_MessageData_ofSyntax(x_16);
x_21 = l_Lean_indentD(x_20);
x_22 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_22, 0, x_2);
lean_ctor_set(x_22, 1, x_21);
x_1 = x_22;
x_2 = x_15;
goto _start;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_24 = lean_ctor_get(x_2, 0);
x_25 = lean_ctor_get(x_2, 1);
lean_inc(x_25);
lean_inc(x_24);
lean_dec(x_2);
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
if (lean_is_exclusive(x_24)) {
 lean_ctor_release(x_24, 0);
 lean_ctor_release(x_24, 1);
 x_27 = x_24;
} else {
 lean_dec_ref(x_24);
 x_27 = lean_box(0);
}
x_28 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0);
if (lean_is_scalar(x_27)) {
 x_29 = lean_alloc_ctor(7, 2, 0);
} else {
 x_29 = x_27;
 lean_ctor_set_tag(x_29, 7);
}
lean_ctor_set(x_29, 0, x_1);
lean_ctor_set(x_29, 1, x_28);
x_30 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__3);
x_31 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_31, 0, x_29);
lean_ctor_set(x_31, 1, x_30);
x_32 = l_Lean_MessageData_ofSyntax(x_26);
x_33 = l_Lean_indentD(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_31);
lean_ctor_set(x_34, 1, x_33);
x_1 = x_34;
x_2 = x_25;
goto _start;
}
}
}
}
LEAN_EXPORT uint8_t l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; lean_object* x_6; 
x_3 = lean_ctor_get(x_2, 0);
x_4 = lean_ctor_get(x_2, 1);
x_5 = lean_ctor_get(x_1, 0);
x_6 = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(x_5, x_3);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = lean_unbox(x_4);
return x_7;
}
else
{
lean_object* x_8; 
x_8 = lean_ctor_get(x_6, 0);
lean_inc(x_8);
lean_dec_ref(x_6);
if (lean_obj_tag(x_8) == 1)
{
uint8_t x_9; 
x_9 = lean_ctor_get_uint8(x_8, 0);
lean_dec_ref(x_8);
return x_9;
}
else
{
uint8_t x_10; 
lean_dec(x_8);
x_10 = lean_unbox(x_4);
return x_10;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20(x_1, x_2);
lean_dec_ref(x_2);
lean_dec_ref(x_1);
x_4 = lean_box(x_3);
return x_4;
}
}
static lean_object* _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__1));
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_5 = lean_ctor_get(x_3, 2);
x_6 = l_Lean_Elab_pp_macroStack;
x_7 = l_Lean_Option_get___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__20(x_5, x_6);
if (x_7 == 0)
{
lean_object* x_8; 
lean_dec(x_2);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_1);
return x_8;
}
else
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_9; 
x_9 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_9, 0, x_1);
return x_9;
}
else
{
lean_object* x_10; uint8_t x_11; 
x_10 = lean_ctor_get(x_2, 0);
lean_inc(x_10);
x_11 = !lean_is_exclusive(x_10);
if (x_11 == 0)
{
lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_12 = lean_ctor_get(x_10, 1);
x_13 = lean_ctor_get(x_10, 0);
lean_dec(x_13);
x_14 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0);
lean_ctor_set_tag(x_10, 7);
lean_ctor_set(x_10, 1, x_14);
lean_ctor_set(x_10, 0, x_1);
x_15 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2);
x_16 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_16, 0, x_10);
lean_ctor_set(x_16, 1, x_15);
x_17 = l_Lean_MessageData_ofSyntax(x_12);
x_18 = l_Lean_indentD(x_17);
x_19 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_19, 0, x_16);
lean_ctor_set(x_19, 1, x_18);
x_20 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21(x_19, x_2);
x_21 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_21, 0, x_20);
return x_21;
}
else
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_22 = lean_ctor_get(x_10, 1);
lean_inc(x_22);
lean_dec(x_10);
x_23 = lean_obj_once(&l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0, &l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0_once, _init_l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21___closed__0);
x_24 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_24, 0, x_1);
lean_ctor_set(x_24, 1, x_23);
x_25 = lean_obj_once(&l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2, &l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2_once, _init_l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___closed__2);
x_26 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_26, 0, x_24);
lean_ctor_set(x_26, 1, x_25);
x_27 = l_Lean_MessageData_ofSyntax(x_22);
x_28 = l_Lean_indentD(x_27);
x_29 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_29, 0, x_26);
lean_ctor_set(x_29, 1, x_28);
x_30 = l_List_foldl___at___00Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12_spec__21(x_29, x_2);
x_31 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_31, 0, x_30);
return x_31;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_7; lean_object* x_8; lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; 
x_7 = lean_st_ref_get(x_5);
x_8 = lean_ctor_get(x_7, 0);
lean_inc_ref(x_8);
lean_dec(x_7);
x_9 = lean_st_ref_get(x_3);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_2, 2);
x_12 = lean_ctor_get(x_4, 2);
lean_inc_ref(x_12);
lean_inc_ref(x_11);
x_13 = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(x_13, 0, x_8);
lean_ctor_set(x_13, 1, x_10);
lean_ctor_set(x_13, 2, x_11);
lean_ctor_set(x_13, 3, x_12);
x_14 = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(x_14, 0, x_13);
lean_ctor_set(x_14, 1, x_1);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_14);
return x_15;
}
}
LEAN_EXPORT lean_object* l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(x_1, x_2, x_3, x_4, x_5);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; uint8_t x_15; 
x_9 = lean_ctor_get(x_6, 5);
x_10 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(x_1, x_4, x_5, x_6, x_7);
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = lean_ctor_get(x_2, 1);
lean_inc(x_12);
lean_dec_ref(x_2);
lean_inc(x_12);
x_13 = l_Lean_Elab_getBetterRef(x_9, x_12);
x_14 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg(x_11, x_12, x_6);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_17, 0, x_13);
lean_ctor_set(x_17, 1, x_16);
lean_ctor_set_tag(x_14, 1);
lean_ctor_set(x_14, 0, x_17);
return x_14;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_14, 0);
lean_inc(x_18);
lean_dec(x_14);
x_19 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_19, 0, x_13);
lean_ctor_set(x_19, 1, x_18);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
return x_20;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = lean_usize_dec_eq(x_2, x_3);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; size_t x_8; size_t x_9; 
x_6 = lean_array_uget_borrowed(x_1, x_2);
lean_inc(x_6);
x_7 = l_Lean_NameSet_insert(x_4, x_6);
x_8 = 1;
x_9 = lean_usize_add(x_2, x_8);
x_2 = x_9;
x_4 = x_7;
goto _start;
}
else
{
return x_4;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; size_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_7 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(x_1, x_5, x_6, x_4);
lean_dec_ref(x_1);
return x_7;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
return x_3;
}
else
{
lean_object* x_5; lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_5 = lean_array_uget(x_3, x_2);
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = l_Lean_TSyntax_getId(x_5);
lean_dec(x_5);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(x_4, x_5, x_3);
return x_6;
}
}
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_box(0);
x_2 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_3 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg() {
_start:
{
lean_object* x_2; lean_object* x_3; 
x_2 = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___closed__0);
x_3 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_3, 0, x_2);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg___boxed(lean_object* x_1) {
_start:
{
lean_object* x_2; 
x_2 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_unsigned_to_nat(0u);
x_7 = lean_array_uset(x_3, x_2, x_6);
x_8 = lean_box(0);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_7, x_2, x_8);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(uint8_t x_1, uint8_t x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; uint8_t x_12; 
x_12 = lean_usize_dec_eq(x_4, x_5);
if (x_12 == 0)
{
lean_object* x_13; uint8_t x_14; 
x_13 = lean_ctor_get(x_6, 0);
x_14 = lean_unbox(x_13);
if (x_14 == 0)
{
uint8_t x_15; 
x_15 = !lean_is_exclusive(x_6);
if (x_15 == 0)
{
lean_object* x_16; lean_object* x_17; 
x_16 = lean_ctor_get(x_6, 0);
lean_dec(x_16);
x_17 = lean_box(x_1);
lean_ctor_set(x_6, 0, x_17);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; 
x_18 = lean_ctor_get(x_6, 1);
lean_inc(x_18);
lean_dec(x_6);
x_19 = lean_box(x_1);
x_20 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set(x_20, 1, x_18);
x_7 = x_20;
goto block_11;
}
}
else
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_6);
if (x_21 == 0)
{
lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_22 = lean_ctor_get(x_6, 1);
x_23 = lean_ctor_get(x_6, 0);
lean_dec(x_23);
x_24 = lean_array_uget_borrowed(x_3, x_4);
lean_inc(x_24);
x_25 = lean_array_push(x_22, x_24);
x_26 = lean_box(x_2);
lean_ctor_set(x_6, 1, x_25);
lean_ctor_set(x_6, 0, x_26);
x_7 = x_6;
goto block_11;
}
else
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_27 = lean_ctor_get(x_6, 1);
lean_inc(x_27);
lean_dec(x_6);
x_28 = lean_array_uget_borrowed(x_3, x_4);
lean_inc(x_28);
x_29 = lean_array_push(x_27, x_28);
x_30 = lean_box(x_2);
x_31 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_31, 0, x_30);
lean_ctor_set(x_31, 1, x_29);
x_7 = x_31;
goto block_11;
}
}
}
else
{
return x_6;
}
block_11:
{
size_t x_8; size_t x_9; 
x_8 = 1;
x_9 = lean_usize_add(x_4, x_8);
x_4 = x_9;
x_6 = x_7;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; uint8_t x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_7 = lean_unbox(x_1);
x_8 = lean_unbox(x_2);
x_9 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_10 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_11 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(x_7, x_8, x_3, x_9, x_10, x_6);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
uint8_t x_10; 
x_10 = !lean_is_exclusive(x_7);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; 
x_11 = lean_ctor_get(x_7, 5);
x_12 = l_Lean_replaceRef(x_1, x_11);
lean_dec(x_11);
lean_ctor_set(x_7, 5, x_12);
x_13 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_7);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; uint8_t x_26; lean_object* x_27; uint8_t x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; 
x_14 = lean_ctor_get(x_7, 0);
x_15 = lean_ctor_get(x_7, 1);
x_16 = lean_ctor_get(x_7, 2);
x_17 = lean_ctor_get(x_7, 3);
x_18 = lean_ctor_get(x_7, 4);
x_19 = lean_ctor_get(x_7, 5);
x_20 = lean_ctor_get(x_7, 6);
x_21 = lean_ctor_get(x_7, 7);
x_22 = lean_ctor_get(x_7, 8);
x_23 = lean_ctor_get(x_7, 9);
x_24 = lean_ctor_get(x_7, 10);
x_25 = lean_ctor_get(x_7, 11);
x_26 = lean_ctor_get_uint8(x_7, sizeof(void*)*14);
x_27 = lean_ctor_get(x_7, 12);
x_28 = lean_ctor_get_uint8(x_7, sizeof(void*)*14 + 1);
x_29 = lean_ctor_get(x_7, 13);
lean_inc(x_29);
lean_inc(x_27);
lean_inc(x_25);
lean_inc(x_24);
lean_inc(x_23);
lean_inc(x_22);
lean_inc(x_21);
lean_inc(x_20);
lean_inc(x_19);
lean_inc(x_18);
lean_inc(x_17);
lean_inc(x_16);
lean_inc(x_15);
lean_inc(x_14);
lean_dec(x_7);
x_30 = l_Lean_replaceRef(x_1, x_19);
lean_dec(x_19);
x_31 = lean_alloc_ctor(0, 14, 2);
lean_ctor_set(x_31, 0, x_14);
lean_ctor_set(x_31, 1, x_15);
lean_ctor_set(x_31, 2, x_16);
lean_ctor_set(x_31, 3, x_17);
lean_ctor_set(x_31, 4, x_18);
lean_ctor_set(x_31, 5, x_30);
lean_ctor_set(x_31, 6, x_20);
lean_ctor_set(x_31, 7, x_21);
lean_ctor_set(x_31, 8, x_22);
lean_ctor_set(x_31, 9, x_23);
lean_ctor_set(x_31, 10, x_24);
lean_ctor_set(x_31, 11, x_25);
lean_ctor_set(x_31, 12, x_27);
lean_ctor_set(x_31, 13, x_29);
lean_ctor_set_uint8(x_31, sizeof(void*)*14, x_26);
lean_ctor_set_uint8(x_31, sizeof(void*)*14 + 1, x_28);
x_32 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_31, x_8);
lean_dec_ref(x_31);
return x_32;
}
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_1);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; lean_object* x_6; lean_object* x_7; uint8_t x_8; uint8_t x_9; 
x_5 = 0;
x_6 = l_Lean_Environment_setExporting(x_1, x_5);
lean_inc(x_2);
x_7 = l_Lean_mkPrivateName(x_6, x_2);
x_8 = 1;
lean_inc_ref(x_6);
x_9 = l_Lean_Environment_contains(x_6, x_7, x_8);
if (x_9 == 0)
{
lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_10 = l_Lean_privateToUserName(x_2);
x_11 = l_Lean_Environment_contains(x_6, x_10, x_8);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_13, 0, x_12);
lean_ctor_set(x_13, 1, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
lean_dec_ref(x_6);
lean_dec(x_2);
x_14 = lean_box(x_9);
x_15 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_15, 0, x_14);
lean_ctor_set(x_15, 1, x_4);
return x_15;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = l_Lean_maxRecDepthErrorMessage;
x_2 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__3);
x_2 = l_Lean_MessageData_ofFormat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__4);
x_2 = ((lean_object*)(l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__2));
x_3 = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(x_3, 0, x_2);
lean_ctor_set(x_3, 1, x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg(lean_object* x_1) {
_start:
{
lean_object* x_3; lean_object* x_4; lean_object* x_5; 
x_3 = lean_obj_once(&l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5, &l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5_once, _init_l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___closed__5);
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_3; lean_object* x_4; 
x_3 = lean_ctor_get(x_1, 0);
lean_inc(x_3);
x_4 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_4, 0, x_3);
lean_ctor_set(x_4, 1, x_2);
return x_4;
}
else
{
lean_object* x_5; lean_object* x_6; 
x_5 = lean_ctor_get(x_1, 0);
lean_inc(x_5);
x_6 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_6, 0, x_5);
lean_ctor_set(x_6, 1, x_2);
return x_6;
}
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_1);
return x_3;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_expandMacroImpl_x3f(x_1, x_2, x_3, x_4);
if (lean_obj_tag(x_5) == 0)
{
lean_object* x_6; 
x_6 = lean_ctor_get(x_5, 0);
lean_inc(x_6);
if (lean_obj_tag(x_6) == 0)
{
uint8_t x_7; 
x_7 = !lean_is_exclusive(x_5);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_ctor_get(x_5, 0);
lean_dec(x_8);
x_9 = lean_box(0);
lean_ctor_set(x_5, 0, x_9);
return x_5;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; 
x_10 = lean_ctor_get(x_5, 1);
lean_inc(x_10);
lean_dec(x_5);
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_12, 0, x_11);
lean_ctor_set(x_12, 1, x_10);
return x_12;
}
}
else
{
uint8_t x_13; 
x_13 = !lean_is_exclusive(x_6);
if (x_13 == 0)
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_ctor_get(x_6, 0);
x_15 = lean_ctor_get(x_14, 1);
lean_inc(x_15);
lean_dec(x_14);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; uint8_t x_17; 
lean_free_object(x_6);
x_16 = lean_ctor_get(x_5, 1);
lean_inc(x_16);
lean_dec_ref(x_5);
x_17 = !lean_is_exclusive(x_15);
if (x_17 == 0)
{
lean_object* x_18; 
x_18 = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(x_15, x_16);
lean_dec_ref(x_15);
return x_18;
}
else
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_ctor_get(x_15, 0);
lean_inc(x_19);
lean_dec(x_15);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_19);
x_21 = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(x_20, x_16);
lean_dec_ref(x_20);
return x_21;
}
}
else
{
lean_object* x_22; uint8_t x_23; 
x_22 = lean_ctor_get(x_5, 1);
lean_inc(x_22);
lean_dec_ref(x_5);
x_23 = !lean_is_exclusive(x_15);
if (x_23 == 0)
{
lean_object* x_24; lean_object* x_25; 
x_24 = lean_ctor_get(x_15, 0);
lean_ctor_set(x_6, 0, x_24);
lean_ctor_set(x_15, 0, x_6);
x_25 = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(x_15, x_22);
lean_dec_ref(x_15);
return x_25;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_ctor_get(x_15, 0);
lean_inc(x_26);
lean_dec(x_15);
lean_ctor_set(x_6, 0, x_26);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_6);
x_28 = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(x_27, x_22);
lean_dec_ref(x_27);
return x_28;
}
}
}
else
{
lean_object* x_29; lean_object* x_30; 
x_29 = lean_ctor_get(x_6, 0);
lean_inc(x_29);
lean_dec(x_6);
x_30 = lean_ctor_get(x_29, 1);
lean_inc(x_30);
lean_dec(x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_31 = lean_ctor_get(x_5, 1);
lean_inc(x_31);
lean_dec_ref(x_5);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_33 = x_30;
} else {
 lean_dec_ref(x_30);
 x_33 = lean_box(0);
}
if (lean_is_scalar(x_33)) {
 x_34 = lean_alloc_ctor(0, 1, 0);
} else {
 x_34 = x_33;
}
lean_ctor_set(x_34, 0, x_32);
x_35 = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(x_34, x_31);
lean_dec_ref(x_34);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; 
x_36 = lean_ctor_get(x_5, 1);
lean_inc(x_36);
lean_dec_ref(x_5);
x_37 = lean_ctor_get(x_30, 0);
lean_inc(x_37);
if (lean_is_exclusive(x_30)) {
 lean_ctor_release(x_30, 0);
 x_38 = x_30;
} else {
 lean_dec_ref(x_30);
 x_38 = lean_box(0);
}
x_39 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_39, 0, x_37);
if (lean_is_scalar(x_38)) {
 x_40 = lean_alloc_ctor(1, 1, 0);
} else {
 x_40 = x_38;
}
lean_ctor_set(x_40, 0, x_39);
x_41 = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(x_40, x_36);
lean_dec_ref(x_40);
return x_41;
}
}
}
}
else
{
uint8_t x_42; 
x_42 = !lean_is_exclusive(x_5);
if (x_42 == 0)
{
return x_5;
}
else
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; 
x_43 = lean_ctor_get(x_5, 0);
x_44 = lean_ctor_get(x_5, 1);
lean_inc(x_44);
lean_inc(x_43);
lean_dec(x_5);
x_45 = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(x_45, 0, x_43);
lean_ctor_set(x_45, 1, x_44);
return x_45;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
return x_5;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_array_get_size(x_1);
x_5 = lean_nat_dec_lt(x_2, x_4);
if (x_5 == 0)
{
lean_dec(x_2);
return x_5;
}
else
{
lean_object* x_6; uint8_t x_7; 
x_6 = lean_array_fget_borrowed(x_1, x_2);
x_7 = l_Lean_instBEqExtraModUse_beq(x_3, x_6);
if (x_7 == 0)
{
lean_object* x_8; lean_object* x_9; 
x_8 = lean_unsigned_to_nat(1u);
x_9 = lean_nat_add(x_2, x_8);
lean_dec(x_2);
x_2 = x_9;
goto _start;
}
else
{
lean_dec(x_2);
return x_7;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg(x_1, x_2, x_3);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
x_5 = lean_box(x_4);
return x_5;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 5;
x_2 = 1;
x_3 = lean_usize_shift_left(x_2, x_1);
return x_3;
}
}
static size_t _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1(void) {
_start:
{
size_t x_1; size_t x_2; size_t x_3; 
x_1 = 1;
x_2 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__0);
x_3 = lean_usize_sub(x_2, x_1);
return x_3;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg(lean_object* x_1, size_t x_2, lean_object* x_3) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_4; lean_object* x_5; size_t x_6; size_t x_7; size_t x_8; lean_object* x_9; lean_object* x_10; 
x_4 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_4);
lean_dec_ref(x_1);
x_5 = lean_box(2);
x_6 = 5;
x_7 = lean_usize_once(&l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1, &l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1_once, _init_l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___closed__1);
x_8 = lean_usize_land(x_2, x_7);
x_9 = lean_usize_to_nat(x_8);
x_10 = lean_array_get(x_5, x_4, x_9);
lean_dec(x_9);
lean_dec_ref(x_4);
switch (lean_obj_tag(x_10)) {
case 0:
{
lean_object* x_11; uint8_t x_12; 
x_11 = lean_ctor_get(x_10, 0);
lean_inc(x_11);
lean_dec_ref(x_10);
x_12 = l_Lean_instBEqExtraModUse_beq(x_3, x_11);
lean_dec(x_11);
return x_12;
}
case 1:
{
lean_object* x_13; size_t x_14; 
x_13 = lean_ctor_get(x_10, 0);
lean_inc(x_13);
lean_dec_ref(x_10);
x_14 = lean_usize_shift_right(x_2, x_6);
x_1 = x_13;
x_2 = x_14;
goto _start;
}
default: 
{
uint8_t x_16; 
x_16 = 0;
return x_16;
}
}
}
else
{
lean_object* x_17; lean_object* x_18; uint8_t x_19; 
x_17 = lean_ctor_get(x_1, 0);
lean_inc_ref(x_17);
lean_dec_ref(x_1);
x_18 = lean_unsigned_to_nat(0u);
x_19 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg(x_17, x_18, x_3);
lean_dec_ref(x_17);
return x_19;
}
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; uint8_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg(x_1, x_4, x_3);
lean_dec_ref(x_3);
x_6 = lean_box(x_5);
return x_6;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
uint64_t x_3; size_t x_4; uint8_t x_5; 
x_3 = l_Lean_instHashableExtraModUse_hash(x_2);
x_4 = lean_uint64_to_usize(x_3);
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg(x_1, x_4, x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
uint8_t x_3; lean_object* x_4; 
x_3 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg(x_1, x_2);
lean_dec_ref(x_2);
x_4 = lean_box(x_3);
return x_4;
}
}
static double _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0(void) {
_start:
{
lean_object* x_1; double x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_float_of_nat(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_8; lean_object* x_9; uint8_t x_10; 
x_8 = lean_ctor_get(x_5, 5);
x_9 = l_Lean_addMessageContextFull___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__11(x_2, x_3, x_4, x_5, x_6);
x_10 = !lean_is_exclusive(x_9);
if (x_10 == 0)
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_11 = lean_ctor_get(x_9, 0);
x_12 = lean_st_ref_take(x_6);
x_13 = !lean_is_exclusive(x_12);
if (x_13 == 0)
{
lean_object* x_14; uint8_t x_15; 
x_14 = lean_ctor_get(x_12, 4);
x_15 = !lean_is_exclusive(x_14);
if (x_15 == 0)
{
lean_object* x_16; double x_17; uint8_t x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; 
x_16 = lean_ctor_get(x_14, 0);
x_17 = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0);
x_18 = 0;
x_19 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1));
x_20 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_20, 0, x_1);
lean_ctor_set(x_20, 1, x_19);
lean_ctor_set_float(x_20, sizeof(void*)*2, x_17);
lean_ctor_set_float(x_20, sizeof(void*)*2 + 8, x_17);
lean_ctor_set_uint8(x_20, sizeof(void*)*2 + 16, x_18);
x_21 = lean_obj_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2);
x_22 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_22, 0, x_20);
lean_ctor_set(x_22, 1, x_11);
lean_ctor_set(x_22, 2, x_21);
lean_inc(x_8);
x_23 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_23, 0, x_8);
lean_ctor_set(x_23, 1, x_22);
x_24 = l_Lean_PersistentArray_push___redArg(x_16, x_23);
lean_ctor_set(x_14, 0, x_24);
x_25 = lean_st_ref_set(x_6, x_12);
x_26 = lean_box(0);
lean_ctor_set(x_9, 0, x_26);
return x_9;
}
else
{
uint64_t x_27; lean_object* x_28; double x_29; uint8_t x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_27 = lean_ctor_get_uint64(x_14, sizeof(void*)*1);
x_28 = lean_ctor_get(x_14, 0);
lean_inc(x_28);
lean_dec(x_14);
x_29 = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0);
x_30 = 0;
x_31 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1));
x_32 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_32, 0, x_1);
lean_ctor_set(x_32, 1, x_31);
lean_ctor_set_float(x_32, sizeof(void*)*2, x_29);
lean_ctor_set_float(x_32, sizeof(void*)*2 + 8, x_29);
lean_ctor_set_uint8(x_32, sizeof(void*)*2 + 16, x_30);
x_33 = lean_obj_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2);
x_34 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_34, 0, x_32);
lean_ctor_set(x_34, 1, x_11);
lean_ctor_set(x_34, 2, x_33);
lean_inc(x_8);
x_35 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_35, 0, x_8);
lean_ctor_set(x_35, 1, x_34);
x_36 = l_Lean_PersistentArray_push___redArg(x_28, x_35);
x_37 = lean_alloc_ctor(0, 1, 8);
lean_ctor_set(x_37, 0, x_36);
lean_ctor_set_uint64(x_37, sizeof(void*)*1, x_27);
lean_ctor_set(x_12, 4, x_37);
x_38 = lean_st_ref_set(x_6, x_12);
x_39 = lean_box(0);
lean_ctor_set(x_9, 0, x_39);
return x_9;
}
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; uint64_t x_49; lean_object* x_50; lean_object* x_51; double x_52; uint8_t x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; 
x_40 = lean_ctor_get(x_12, 4);
x_41 = lean_ctor_get(x_12, 0);
x_42 = lean_ctor_get(x_12, 1);
x_43 = lean_ctor_get(x_12, 2);
x_44 = lean_ctor_get(x_12, 3);
x_45 = lean_ctor_get(x_12, 5);
x_46 = lean_ctor_get(x_12, 6);
x_47 = lean_ctor_get(x_12, 7);
x_48 = lean_ctor_get(x_12, 8);
lean_inc(x_48);
lean_inc(x_47);
lean_inc(x_46);
lean_inc(x_45);
lean_inc(x_40);
lean_inc(x_44);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_dec(x_12);
x_49 = lean_ctor_get_uint64(x_40, sizeof(void*)*1);
x_50 = lean_ctor_get(x_40, 0);
lean_inc_ref(x_50);
if (lean_is_exclusive(x_40)) {
 lean_ctor_release(x_40, 0);
 x_51 = x_40;
} else {
 lean_dec_ref(x_40);
 x_51 = lean_box(0);
}
x_52 = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0);
x_53 = 0;
x_54 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1));
x_55 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_55, 0, x_1);
lean_ctor_set(x_55, 1, x_54);
lean_ctor_set_float(x_55, sizeof(void*)*2, x_52);
lean_ctor_set_float(x_55, sizeof(void*)*2 + 8, x_52);
lean_ctor_set_uint8(x_55, sizeof(void*)*2 + 16, x_53);
x_56 = lean_obj_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2);
x_57 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_57, 0, x_55);
lean_ctor_set(x_57, 1, x_11);
lean_ctor_set(x_57, 2, x_56);
lean_inc(x_8);
x_58 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_58, 0, x_8);
lean_ctor_set(x_58, 1, x_57);
x_59 = l_Lean_PersistentArray_push___redArg(x_50, x_58);
if (lean_is_scalar(x_51)) {
 x_60 = lean_alloc_ctor(0, 1, 8);
} else {
 x_60 = x_51;
}
lean_ctor_set(x_60, 0, x_59);
lean_ctor_set_uint64(x_60, sizeof(void*)*1, x_49);
x_61 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_61, 0, x_41);
lean_ctor_set(x_61, 1, x_42);
lean_ctor_set(x_61, 2, x_43);
lean_ctor_set(x_61, 3, x_44);
lean_ctor_set(x_61, 4, x_60);
lean_ctor_set(x_61, 5, x_45);
lean_ctor_set(x_61, 6, x_46);
lean_ctor_set(x_61, 7, x_47);
lean_ctor_set(x_61, 8, x_48);
x_62 = lean_st_ref_set(x_6, x_61);
x_63 = lean_box(0);
lean_ctor_set(x_9, 0, x_63);
return x_9;
}
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_74; lean_object* x_75; uint64_t x_76; lean_object* x_77; lean_object* x_78; double x_79; uint8_t x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; 
x_64 = lean_ctor_get(x_9, 0);
lean_inc(x_64);
lean_dec(x_9);
x_65 = lean_st_ref_take(x_6);
x_66 = lean_ctor_get(x_65, 4);
lean_inc_ref(x_66);
x_67 = lean_ctor_get(x_65, 0);
lean_inc_ref(x_67);
x_68 = lean_ctor_get(x_65, 1);
lean_inc(x_68);
x_69 = lean_ctor_get(x_65, 2);
lean_inc_ref(x_69);
x_70 = lean_ctor_get(x_65, 3);
lean_inc_ref(x_70);
x_71 = lean_ctor_get(x_65, 5);
lean_inc_ref(x_71);
x_72 = lean_ctor_get(x_65, 6);
lean_inc_ref(x_72);
x_73 = lean_ctor_get(x_65, 7);
lean_inc_ref(x_73);
x_74 = lean_ctor_get(x_65, 8);
lean_inc_ref(x_74);
if (lean_is_exclusive(x_65)) {
 lean_ctor_release(x_65, 0);
 lean_ctor_release(x_65, 1);
 lean_ctor_release(x_65, 2);
 lean_ctor_release(x_65, 3);
 lean_ctor_release(x_65, 4);
 lean_ctor_release(x_65, 5);
 lean_ctor_release(x_65, 6);
 lean_ctor_release(x_65, 7);
 lean_ctor_release(x_65, 8);
 x_75 = x_65;
} else {
 lean_dec_ref(x_65);
 x_75 = lean_box(0);
}
x_76 = lean_ctor_get_uint64(x_66, sizeof(void*)*1);
x_77 = lean_ctor_get(x_66, 0);
lean_inc_ref(x_77);
if (lean_is_exclusive(x_66)) {
 lean_ctor_release(x_66, 0);
 x_78 = x_66;
} else {
 lean_dec_ref(x_66);
 x_78 = lean_box(0);
}
x_79 = lean_float_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__0);
x_80 = 0;
x_81 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1));
x_82 = lean_alloc_ctor(0, 2, 17);
lean_ctor_set(x_82, 0, x_1);
lean_ctor_set(x_82, 1, x_81);
lean_ctor_set_float(x_82, sizeof(void*)*2, x_79);
lean_ctor_set_float(x_82, sizeof(void*)*2 + 8, x_79);
lean_ctor_set_uint8(x_82, sizeof(void*)*2 + 16, x_80);
x_83 = lean_obj_once(&l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2, &l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2_once, _init_l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__2);
x_84 = lean_alloc_ctor(9, 3, 0);
lean_ctor_set(x_84, 0, x_82);
lean_ctor_set(x_84, 1, x_64);
lean_ctor_set(x_84, 2, x_83);
lean_inc(x_8);
x_85 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_85, 0, x_8);
lean_ctor_set(x_85, 1, x_84);
x_86 = l_Lean_PersistentArray_push___redArg(x_77, x_85);
if (lean_is_scalar(x_78)) {
 x_87 = lean_alloc_ctor(0, 1, 8);
} else {
 x_87 = x_78;
}
lean_ctor_set(x_87, 0, x_86);
lean_ctor_set_uint64(x_87, sizeof(void*)*1, x_76);
if (lean_is_scalar(x_75)) {
 x_88 = lean_alloc_ctor(0, 9, 0);
} else {
 x_88 = x_75;
}
lean_ctor_set(x_88, 0, x_67);
lean_ctor_set(x_88, 1, x_68);
lean_ctor_set(x_88, 2, x_69);
lean_ctor_set(x_88, 3, x_70);
lean_ctor_set(x_88, 4, x_87);
lean_ctor_set(x_88, 5, x_71);
lean_ctor_set(x_88, 6, x_72);
lean_ctor_set(x_88, 7, x_73);
lean_ctor_set(x_88, 8, x_74);
x_89 = lean_st_ref_set(x_6, x_88);
x_90 = lean_box(0);
x_91 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_91, 0, x_90);
return x_91;
}
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_4; uint8_t x_5; 
x_4 = lean_ctor_get(x_2, 2);
x_5 = lean_ctor_get_uint8(x_4, sizeof(void*)*1);
if (x_5 == 0)
{
lean_object* x_6; lean_object* x_7; 
lean_dec(x_1);
x_6 = lean_box(x_5);
x_7 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_7, 0, x_6);
return x_7;
}
else
{
lean_object* x_8; lean_object* x_9; lean_object* x_10; uint8_t x_11; lean_object* x_12; lean_object* x_13; 
x_8 = lean_ctor_get(x_2, 13);
x_9 = ((lean_object*)(l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___closed__1));
x_10 = l_Lean_Name_append(x_9, x_1);
x_11 = l___private_Lean_Util_Trace_0__Lean_checkTraceOption_go(x_8, x_4, x_10);
lean_dec(x_10);
x_12 = lean_box(x_11);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_12);
return x_13;
}
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(x_1, x_2);
lean_dec_ref(x_2);
return x_4;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__1));
x_2 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__0));
x_3 = l_Lean_PersistentHashMap_empty(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3(void) {
_start:
{
lean_object* x_1; 
x_1 = l_Lean_PersistentHashMap_mkEmptyEntriesArray(lean_box(0), lean_box(0));
return x_1;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__3);
x_2 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2, 0, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4);
x_2 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__4);
x_2 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_2, 0, x_1);
lean_ctor_set(x_2, 1, x_1);
lean_ctor_set(x_2, 2, x_1);
lean_ctor_set(x_2, 3, x_1);
lean_ctor_set(x_2, 4, x_1);
lean_ctor_set(x_2, 5, x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__9));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__11));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg___closed__1));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__14));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__16));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_74; uint8_t x_75; 
x_11 = lean_st_ref_get(x_9);
x_12 = lean_ctor_get(x_11, 0);
lean_inc_ref(x_12);
lean_dec(x_11);
x_13 = lean_ctor_get_uint8(x_12, sizeof(void*)*8);
lean_dec_ref(x_12);
x_14 = lean_st_ref_get(x_9);
x_15 = lean_ctor_get(x_14, 0);
lean_inc_ref(x_15);
lean_dec(x_14);
x_16 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__2);
lean_inc(x_1);
x_17 = lean_alloc_ctor(0, 1, 2);
lean_ctor_set(x_17, 0, x_1);
lean_ctor_set_uint8(x_17, sizeof(void*)*1, x_13);
lean_ctor_set_uint8(x_17, sizeof(void*)*1 + 1, x_2);
x_18 = l___private_Lean_ExtraModUses_0__Lean_extraModUses;
x_19 = lean_box(1);
x_20 = lean_box(0);
x_74 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_16, x_18, x_15, x_19, x_20);
x_75 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg(x_74, x_17);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_84; lean_object* x_85; uint8_t x_98; 
x_76 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__8));
x_77 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(x_76, x_8);
x_78 = lean_ctor_get(x_77, 0);
lean_inc(x_78);
lean_dec_ref(x_77);
x_98 = lean_unbox(x_78);
lean_dec(x_78);
if (x_98 == 0)
{
lean_dec(x_3);
lean_dec(x_1);
x_21 = x_7;
x_22 = x_9;
x_23 = lean_box(0);
goto block_73;
}
else
{
lean_object* x_99; lean_object* x_100; 
x_99 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__15);
if (x_13 == 0)
{
lean_object* x_108; 
x_108 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__20));
x_100 = x_108;
goto block_107;
}
else
{
lean_object* x_109; 
x_109 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__21));
x_100 = x_109;
goto block_107;
}
block_107:
{
lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; 
x_101 = l_Lean_stringToMessageData(x_100);
x_102 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_102, 0, x_99);
lean_ctor_set(x_102, 1, x_101);
x_103 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__17);
x_104 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_104, 0, x_102);
lean_ctor_set(x_104, 1, x_103);
if (x_2 == 0)
{
lean_object* x_105; 
x_105 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__18));
x_84 = x_104;
x_85 = x_105;
goto block_97;
}
else
{
lean_object* x_106; 
x_106 = ((lean_object*)(l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__19));
x_84 = x_104;
x_85 = x_106;
goto block_97;
}
}
}
block_83:
{
lean_object* x_81; lean_object* x_82; 
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_79);
lean_ctor_set(x_81, 1, x_80);
x_82 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(x_76, x_81, x_6, x_7, x_8, x_9);
if (lean_obj_tag(x_82) == 0)
{
lean_dec_ref(x_82);
x_21 = x_7;
x_22 = x_9;
x_23 = lean_box(0);
goto block_73;
}
else
{
lean_dec_ref(x_17);
return x_82;
}
}
block_97:
{
lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; uint8_t x_92; 
x_86 = l_Lean_stringToMessageData(x_85);
x_87 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_87, 0, x_84);
lean_ctor_set(x_87, 1, x_86);
x_88 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__10);
x_89 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_89, 0, x_87);
lean_ctor_set(x_89, 1, x_88);
x_90 = l_Lean_MessageData_ofName(x_1);
x_91 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_91, 0, x_89);
lean_ctor_set(x_91, 1, x_90);
x_92 = l_Lean_Name_isAnonymous(x_3);
if (x_92 == 0)
{
lean_object* x_93; lean_object* x_94; lean_object* x_95; 
x_93 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__12);
x_94 = l_Lean_MessageData_ofName(x_3);
x_95 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_95, 0, x_93);
lean_ctor_set(x_95, 1, x_94);
x_79 = x_91;
x_80 = x_95;
goto block_83;
}
else
{
lean_object* x_96; 
lean_dec(x_3);
x_96 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__13);
x_79 = x_91;
x_80 = x_96;
goto block_83;
}
}
}
else
{
lean_object* x_110; lean_object* x_111; 
lean_dec_ref(x_17);
lean_dec(x_3);
lean_dec(x_1);
x_110 = lean_box(0);
x_111 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_111, 0, x_110);
return x_111;
}
block_73:
{
lean_object* x_24; lean_object* x_25; uint8_t x_26; 
x_24 = lean_st_ref_take(x_22);
x_25 = lean_ctor_get(x_18, 0);
lean_inc_ref(x_25);
x_26 = !lean_is_exclusive(x_24);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; uint8_t x_34; 
x_27 = lean_ctor_get(x_24, 0);
x_28 = lean_ctor_get(x_24, 5);
lean_dec(x_28);
x_29 = lean_ctor_get(x_25, 2);
lean_inc(x_29);
lean_dec_ref(x_25);
x_30 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_18, x_27, x_17, x_29, x_20);
lean_dec(x_29);
x_31 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5);
lean_ctor_set(x_24, 5, x_31);
lean_ctor_set(x_24, 0, x_30);
x_32 = lean_st_ref_set(x_22, x_24);
x_33 = lean_st_ref_take(x_21);
x_34 = !lean_is_exclusive(x_33);
if (x_34 == 0)
{
lean_object* x_35; lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; 
x_35 = lean_ctor_get(x_33, 1);
lean_dec(x_35);
x_36 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6);
lean_ctor_set(x_33, 1, x_36);
x_37 = lean_st_ref_set(x_21, x_33);
x_38 = lean_box(0);
x_39 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_39, 0, x_38);
return x_39;
}
else
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; 
x_40 = lean_ctor_get(x_33, 0);
x_41 = lean_ctor_get(x_33, 2);
x_42 = lean_ctor_get(x_33, 3);
x_43 = lean_ctor_get(x_33, 4);
lean_inc(x_43);
lean_inc(x_42);
lean_inc(x_41);
lean_inc(x_40);
lean_dec(x_33);
x_44 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6);
x_45 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_45, 0, x_40);
lean_ctor_set(x_45, 1, x_44);
lean_ctor_set(x_45, 2, x_41);
lean_ctor_set(x_45, 3, x_42);
lean_ctor_set(x_45, 4, x_43);
x_46 = lean_st_ref_set(x_21, x_45);
x_47 = lean_box(0);
x_48 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_48, 0, x_47);
return x_48;
}
}
else
{
lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; lean_object* x_66; lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; 
x_49 = lean_ctor_get(x_24, 0);
x_50 = lean_ctor_get(x_24, 1);
x_51 = lean_ctor_get(x_24, 2);
x_52 = lean_ctor_get(x_24, 3);
x_53 = lean_ctor_get(x_24, 4);
x_54 = lean_ctor_get(x_24, 6);
x_55 = lean_ctor_get(x_24, 7);
x_56 = lean_ctor_get(x_24, 8);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_inc(x_49);
lean_dec(x_24);
x_57 = lean_ctor_get(x_25, 2);
lean_inc(x_57);
lean_dec_ref(x_25);
x_58 = l_Lean_PersistentEnvExtension_addEntry___redArg(x_18, x_49, x_17, x_57, x_20);
lean_dec(x_57);
x_59 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__5);
x_60 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_60, 0, x_58);
lean_ctor_set(x_60, 1, x_50);
lean_ctor_set(x_60, 2, x_51);
lean_ctor_set(x_60, 3, x_52);
lean_ctor_set(x_60, 4, x_53);
lean_ctor_set(x_60, 5, x_59);
lean_ctor_set(x_60, 6, x_54);
lean_ctor_set(x_60, 7, x_55);
lean_ctor_set(x_60, 8, x_56);
x_61 = lean_st_ref_set(x_22, x_60);
x_62 = lean_st_ref_take(x_21);
x_63 = lean_ctor_get(x_62, 0);
lean_inc_ref(x_63);
x_64 = lean_ctor_get(x_62, 2);
lean_inc(x_64);
x_65 = lean_ctor_get(x_62, 3);
lean_inc_ref(x_65);
x_66 = lean_ctor_get(x_62, 4);
lean_inc_ref(x_66);
if (lean_is_exclusive(x_62)) {
 lean_ctor_release(x_62, 0);
 lean_ctor_release(x_62, 1);
 lean_ctor_release(x_62, 2);
 lean_ctor_release(x_62, 3);
 lean_ctor_release(x_62, 4);
 x_67 = x_62;
} else {
 lean_dec_ref(x_62);
 x_67 = lean_box(0);
}
x_68 = lean_obj_once(&l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6, &l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6_once, _init_l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___closed__6);
if (lean_is_scalar(x_67)) {
 x_69 = lean_alloc_ctor(0, 5, 0);
} else {
 x_69 = x_67;
}
lean_ctor_set(x_69, 0, x_63);
lean_ctor_set(x_69, 1, x_68);
lean_ctor_set(x_69, 2, x_64);
lean_ctor_set(x_69, 3, x_65);
lean_ctor_set(x_69, 4, x_66);
x_70 = lean_st_ref_set(x_21, x_69);
x_71 = lean_box(0);
x_72 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_72, 0, x_71);
return x_72;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_11; lean_object* x_12; 
x_11 = lean_unbox(x_2);
x_12 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9(x_1, x_11, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10(lean_object* x_1, lean_object* x_2, lean_object* x_3, size_t x_4, size_t x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_14; 
x_14 = lean_usize_dec_lt(x_5, x_4);
if (x_14 == 0)
{
lean_object* x_15; 
lean_dec(x_2);
x_15 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_15, 0, x_6);
return x_15;
}
else
{
lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; uint8_t x_23; lean_object* x_24; 
x_16 = l_Lean_Environment_header(x_1);
x_17 = lean_ctor_get(x_16, 3);
lean_inc_ref(x_17);
lean_dec_ref(x_16);
x_18 = l_Lean_instInhabitedEffectiveImport_default;
x_19 = lean_array_uget_borrowed(x_3, x_5);
x_20 = lean_array_get(x_18, x_17, x_19);
lean_dec_ref(x_17);
x_21 = lean_ctor_get(x_20, 0);
lean_inc_ref(x_21);
lean_dec(x_20);
x_22 = lean_ctor_get(x_21, 0);
lean_inc(x_22);
lean_dec_ref(x_21);
x_23 = 0;
lean_inc(x_2);
x_24 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9(x_22, x_23, x_2, x_7, x_8, x_9, x_10, x_11, x_12);
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_25; size_t x_26; size_t x_27; 
lean_dec_ref(x_24);
x_25 = lean_box(0);
x_26 = 1;
x_27 = lean_usize_add(x_5, x_26);
x_5 = x_27;
x_6 = x_25;
goto _start;
}
else
{
lean_dec(x_2);
return x_24;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12, lean_object* x_13) {
_start:
{
size_t x_14; size_t x_15; lean_object* x_16; 
x_14 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_15 = lean_unbox_usize(x_5);
lean_dec(x_5);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10(x_1, x_2, x_3, x_14, x_15, x_6, x_7, x_8, x_9, x_10, x_11, x_12);
lean_dec(x_12);
lean_dec_ref(x_11);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec_ref(x_3);
lean_dec_ref(x_1);
return x_16;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_3; 
x_3 = lean_box(0);
return x_3;
}
else
{
lean_object* x_4; lean_object* x_5; lean_object* x_6; uint8_t x_7; 
x_4 = lean_ctor_get(x_2, 0);
x_5 = lean_ctor_get(x_2, 1);
x_6 = lean_ctor_get(x_2, 2);
x_7 = lean_name_eq(x_4, x_1);
if (x_7 == 0)
{
x_2 = x_6;
goto _start;
}
else
{
lean_object* x_9; 
lean_inc(x_5);
x_9 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_9, 0, x_5);
return x_9;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec(x_1);
return x_3;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0(void) {
_start:
{
lean_object* x_1; uint64_t x_2; 
x_1 = lean_unsigned_to_nat(1723u);
x_2 = lean_uint64_of_nat(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; lean_object* x_4; uint64_t x_5; 
x_3 = lean_ctor_get(x_1, 1);
x_4 = lean_array_get_size(x_3);
if (lean_obj_tag(x_2) == 0)
{
uint64_t x_20; 
x_20 = lean_uint64_once(&l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0, &l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___closed__0);
x_5 = x_20;
goto block_19;
}
else
{
uint64_t x_21; 
x_21 = lean_ctor_get_uint64(x_2, sizeof(void*)*2);
x_5 = x_21;
goto block_19;
}
block_19:
{
uint64_t x_6; uint64_t x_7; uint64_t x_8; uint64_t x_9; uint64_t x_10; uint64_t x_11; size_t x_12; size_t x_13; size_t x_14; size_t x_15; size_t x_16; lean_object* x_17; lean_object* x_18; 
x_6 = 32;
x_7 = lean_uint64_shift_right(x_5, x_6);
x_8 = lean_uint64_xor(x_5, x_7);
x_9 = 16;
x_10 = lean_uint64_shift_right(x_8, x_9);
x_11 = lean_uint64_xor(x_8, x_10);
x_12 = lean_uint64_to_usize(x_11);
x_13 = lean_usize_of_nat(x_4);
x_14 = 1;
x_15 = lean_usize_sub(x_13, x_14);
x_16 = lean_usize_land(x_12, x_15);
x_17 = lean_array_uget_borrowed(x_3, x_16);
x_18 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg(x_2, x_17);
return x_18;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg___boxed(lean_object* x_1, lean_object* x_2) {
_start:
{
lean_object* x_3; 
x_3 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg(x_1, x_2);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; lean_object* x_3; 
x_1 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__1));
x_2 = ((lean_object*)(l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__0));
x_3 = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), x_2, x_1);
return x_3;
}
}
static lean_object* _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(lean_object* x_1, uint8_t x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_25; 
x_10 = lean_st_ref_get(x_8);
x_14 = lean_ctor_get(x_10, 0);
lean_inc_ref(x_14);
lean_dec(x_10);
x_25 = l_Lean_Environment_getModuleIdxFor_x3f(x_14, x_1);
if (lean_obj_tag(x_25) == 0)
{
lean_dec_ref(x_14);
lean_dec(x_1);
goto block_13;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; uint8_t x_30; 
x_26 = lean_ctor_get(x_25, 0);
lean_inc(x_26);
lean_dec_ref(x_25);
x_27 = l_Lean_Environment_header(x_14);
x_28 = lean_ctor_get(x_27, 3);
lean_inc_ref(x_28);
lean_dec_ref(x_27);
x_29 = lean_array_get_size(x_28);
x_30 = lean_nat_dec_lt(x_26, x_29);
if (x_30 == 0)
{
lean_dec_ref(x_28);
lean_dec(x_26);
lean_dec_ref(x_14);
lean_dec(x_1);
goto block_13;
}
else
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; uint8_t x_35; 
x_31 = lean_st_ref_get(x_8);
x_32 = lean_ctor_get(x_31, 0);
lean_inc_ref(x_32);
lean_dec(x_31);
x_33 = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__2);
x_34 = lean_array_fget(x_28, x_26);
lean_dec(x_26);
lean_dec_ref(x_28);
if (x_2 == 0)
{
lean_dec_ref(x_32);
x_35 = x_2;
goto block_46;
}
else
{
uint8_t x_47; 
lean_inc(x_1);
x_47 = l_Lean_isMarkedMeta(x_32, x_1);
if (x_47 == 0)
{
x_35 = x_2;
goto block_46;
}
else
{
uint8_t x_48; 
x_48 = 0;
x_35 = x_48;
goto block_46;
}
}
block_46:
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc_ref(x_36);
lean_dec(x_34);
x_37 = lean_ctor_get(x_36, 0);
lean_inc(x_37);
lean_dec_ref(x_36);
lean_inc(x_1);
x_38 = l___private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9(x_37, x_35, x_1, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_38) == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
lean_dec_ref(x_38);
x_39 = l_Lean_indirectModUseExt;
x_40 = lean_box(1);
x_41 = lean_box(0);
lean_inc_ref(x_14);
x_42 = l_Lean_SimplePersistentEnvExtension_getState___redArg(x_33, x_39, x_14, x_40, x_41);
x_43 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg(x_42, x_1);
lean_dec(x_42);
if (lean_obj_tag(x_43) == 0)
{
lean_object* x_44; 
x_44 = lean_obj_once(&l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__3, &l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__3_once, _init_l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___closed__3);
x_15 = lean_box(0);
x_16 = x_44;
goto block_24;
}
else
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_inc(x_45);
lean_dec_ref(x_43);
x_15 = lean_box(0);
x_16 = x_45;
goto block_24;
}
}
else
{
lean_dec_ref(x_14);
lean_dec(x_1);
return x_38;
}
}
}
}
block_13:
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_box(0);
x_12 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_12, 0, x_11);
return x_12;
}
block_24:
{
lean_object* x_17; size_t x_18; size_t x_19; lean_object* x_20; 
x_17 = lean_box(0);
x_18 = lean_array_size(x_16);
x_19 = 0;
x_20 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__10(x_14, x_1, x_16, x_18, x_19, x_17, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec_ref(x_16);
lean_dec_ref(x_14);
if (lean_obj_tag(x_20) == 0)
{
uint8_t x_21; 
x_21 = !lean_is_exclusive(x_20);
if (x_21 == 0)
{
lean_object* x_22; 
x_22 = lean_ctor_get(x_20, 0);
lean_dec(x_22);
lean_ctor_set(x_20, 0, x_17);
return x_20;
}
else
{
lean_object* x_23; 
lean_dec(x_20);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_17);
return x_23;
}
}
else
{
return x_20;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_2);
x_11 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(x_1, x_10, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_11;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_10; 
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_2);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; uint8_t x_13; lean_object* x_14; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = 1;
x_14 = l_Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3(x_11, x_13, x_3, x_4, x_5, x_6, x_7, x_8);
if (lean_obj_tag(x_14) == 0)
{
lean_object* x_15; 
lean_dec_ref(x_14);
x_15 = lean_box(0);
x_1 = x_12;
x_2 = x_15;
goto _start;
}
else
{
lean_dec(x_12);
return x_14;
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; lean_object* x_8; 
x_7 = l_Lean_ResolveName_resolveNamespace(x_1, x_2, x_3, x_4);
x_8 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_8, 0, x_7);
lean_ctor_set(x_8, 1, x_6);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
lean_object* x_7; 
x_7 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_5);
return x_7;
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
x_9 = lean_box(0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; uint8_t x_16; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
x_12 = lean_ctor_get(x_1, 1);
lean_inc(x_12);
lean_dec_ref(x_1);
x_13 = lean_ctor_get(x_11, 0);
lean_inc(x_13);
x_14 = lean_ctor_get(x_11, 1);
lean_inc(x_14);
lean_dec(x_11);
lean_inc(x_13);
x_15 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(x_13, x_6);
x_16 = !lean_is_exclusive(x_15);
if (x_16 == 0)
{
lean_object* x_17; uint8_t x_18; 
x_17 = lean_ctor_get(x_15, 0);
x_18 = lean_unbox(x_17);
lean_dec(x_17);
if (x_18 == 0)
{
lean_free_object(x_15);
lean_dec(x_14);
lean_dec(x_13);
x_1 = x_12;
goto _start;
}
else
{
lean_object* x_20; lean_object* x_21; 
lean_ctor_set_tag(x_15, 3);
lean_ctor_set(x_15, 0, x_14);
x_20 = l_Lean_MessageData_ofFormat(x_15);
x_21 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(x_13, x_20, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_21) == 0)
{
lean_dec_ref(x_21);
x_1 = x_12;
goto _start;
}
else
{
lean_dec(x_12);
return x_21;
}
}
}
else
{
lean_object* x_23; uint8_t x_24; 
x_23 = lean_ctor_get(x_15, 0);
lean_inc(x_23);
lean_dec(x_15);
x_24 = lean_unbox(x_23);
lean_dec(x_23);
if (x_24 == 0)
{
lean_dec(x_14);
lean_dec(x_13);
x_1 = x_12;
goto _start;
}
else
{
lean_object* x_26; lean_object* x_27; lean_object* x_28; 
x_26 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_26, 0, x_14);
x_27 = l_Lean_MessageData_ofFormat(x_26);
x_28 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(x_13, x_27, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_28) == 0)
{
lean_dec_ref(x_28);
x_1 = x_12;
goto _start;
}
else
{
lean_dec(x_12);
return x_28;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_4, 0, x_1);
lean_ctor_set(x_4, 1, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3(x_1, x_2, x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; lean_object* x_9; 
x_8 = l_Lean_ResolveName_resolveGlobalName(x_1, x_2, x_3, x_4, x_5);
x_9 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_9, 0, x_8);
lean_ctor_set(x_9, 1, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_8; 
x_8 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; 
x_9 = lean_st_ref_get(x_7);
x_10 = lean_ctor_get(x_9, 0);
lean_inc_ref(x_10);
lean_dec(x_9);
x_11 = lean_ctor_get(x_6, 2);
x_12 = lean_ctor_get(x_6, 3);
x_13 = lean_ctor_get(x_6, 4);
x_14 = lean_ctor_get(x_6, 5);
x_15 = lean_ctor_get(x_6, 6);
x_16 = lean_ctor_get(x_6, 7);
x_17 = lean_ctor_get(x_6, 10);
x_18 = lean_ctor_get(x_6, 11);
x_19 = lean_st_ref_get(x_7);
x_20 = lean_ctor_get(x_19, 1);
lean_inc(x_20);
lean_dec(x_19);
lean_inc_ref(x_10);
x_21 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__0___boxed), 4, 1);
lean_closure_set(x_21, 0, x_10);
lean_inc_ref(x_10);
x_22 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__1___boxed), 4, 1);
lean_closure_set(x_22, 0, x_10);
lean_inc(x_16);
lean_inc(x_15);
lean_inc_ref(x_10);
x_23 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__2___boxed), 6, 3);
lean_closure_set(x_23, 0, x_10);
lean_closure_set(x_23, 1, x_15);
lean_closure_set(x_23, 2, x_16);
lean_inc(x_15);
x_24 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__3___boxed), 3, 1);
lean_closure_set(x_24, 0, x_15);
lean_inc(x_16);
lean_inc(x_15);
lean_inc_ref(x_11);
x_25 = lean_alloc_closure((void*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___lam__4___boxed), 7, 4);
lean_closure_set(x_25, 0, x_10);
lean_closure_set(x_25, 1, x_11);
lean_closure_set(x_25, 2, x_15);
lean_closure_set(x_25, 3, x_16);
x_26 = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(x_26, 0, x_21);
lean_ctor_set(x_26, 1, x_24);
lean_ctor_set(x_26, 2, x_22);
lean_ctor_set(x_26, 3, x_23);
lean_ctor_set(x_26, 4, x_25);
lean_inc(x_14);
lean_inc(x_13);
lean_inc(x_12);
lean_inc(x_18);
lean_inc(x_17);
x_27 = lean_alloc_ctor(0, 6, 0);
lean_ctor_set(x_27, 0, x_26);
lean_ctor_set(x_27, 1, x_17);
lean_ctor_set(x_27, 2, x_18);
lean_ctor_set(x_27, 3, x_12);
lean_ctor_set(x_27, 4, x_13);
lean_ctor_set(x_27, 5, x_14);
x_28 = lean_box(0);
x_29 = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(x_29, 0, x_20);
lean_ctor_set(x_29, 1, x_28);
lean_ctor_set(x_29, 2, x_28);
x_30 = lean_apply_2(x_1, x_27, x_29);
if (lean_obj_tag(x_30) == 0)
{
lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; lean_object* x_37; 
x_31 = lean_ctor_get(x_30, 1);
lean_inc(x_31);
x_32 = lean_ctor_get(x_30, 0);
lean_inc(x_32);
lean_dec_ref(x_30);
x_33 = lean_ctor_get(x_31, 0);
lean_inc(x_33);
x_34 = lean_ctor_get(x_31, 1);
lean_inc(x_34);
x_35 = lean_ctor_get(x_31, 2);
lean_inc(x_35);
lean_dec(x_31);
x_36 = lean_box(0);
x_37 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg(x_35, x_36, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_37) == 0)
{
lean_object* x_38; uint8_t x_39; 
lean_dec_ref(x_37);
x_38 = lean_st_ref_take(x_7);
x_39 = !lean_is_exclusive(x_38);
if (x_39 == 0)
{
lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; 
x_40 = lean_ctor_get(x_38, 1);
lean_dec(x_40);
lean_ctor_set(x_38, 1, x_33);
x_41 = lean_st_ref_set(x_7, x_38);
x_42 = l_List_reverse___redArg(x_34);
x_43 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(x_42, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
if (lean_obj_tag(x_43) == 0)
{
uint8_t x_44; 
x_44 = !lean_is_exclusive(x_43);
if (x_44 == 0)
{
lean_object* x_45; 
x_45 = lean_ctor_get(x_43, 0);
lean_dec(x_45);
lean_ctor_set(x_43, 0, x_32);
return x_43;
}
else
{
lean_object* x_46; 
lean_dec(x_43);
x_46 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_46, 0, x_32);
return x_46;
}
}
else
{
uint8_t x_47; 
lean_dec(x_32);
x_47 = !lean_is_exclusive(x_43);
if (x_47 == 0)
{
return x_43;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_43, 0);
lean_inc(x_48);
lean_dec(x_43);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
x_50 = lean_ctor_get(x_38, 0);
x_51 = lean_ctor_get(x_38, 2);
x_52 = lean_ctor_get(x_38, 3);
x_53 = lean_ctor_get(x_38, 4);
x_54 = lean_ctor_get(x_38, 5);
x_55 = lean_ctor_get(x_38, 6);
x_56 = lean_ctor_get(x_38, 7);
x_57 = lean_ctor_get(x_38, 8);
lean_inc(x_57);
lean_inc(x_56);
lean_inc(x_55);
lean_inc(x_54);
lean_inc(x_53);
lean_inc(x_52);
lean_inc(x_51);
lean_inc(x_50);
lean_dec(x_38);
x_58 = lean_alloc_ctor(0, 9, 0);
lean_ctor_set(x_58, 0, x_50);
lean_ctor_set(x_58, 1, x_33);
lean_ctor_set(x_58, 2, x_51);
lean_ctor_set(x_58, 3, x_52);
lean_ctor_set(x_58, 4, x_53);
lean_ctor_set(x_58, 5, x_54);
lean_ctor_set(x_58, 6, x_55);
lean_ctor_set(x_58, 7, x_56);
lean_ctor_set(x_58, 8, x_57);
x_59 = lean_st_ref_set(x_7, x_58);
x_60 = l_List_reverse___redArg(x_34);
x_61 = l_List_forM___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__5(x_60, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; lean_object* x_63; 
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_62 = x_61;
} else {
 lean_dec_ref(x_61);
 x_62 = lean_box(0);
}
if (lean_is_scalar(x_62)) {
 x_63 = lean_alloc_ctor(0, 1, 0);
} else {
 x_63 = x_62;
}
lean_ctor_set(x_63, 0, x_32);
return x_63;
}
else
{
lean_object* x_64; lean_object* x_65; lean_object* x_66; 
lean_dec(x_32);
x_64 = lean_ctor_get(x_61, 0);
lean_inc(x_64);
if (lean_is_exclusive(x_61)) {
 lean_ctor_release(x_61, 0);
 x_65 = x_61;
} else {
 lean_dec_ref(x_61);
 x_65 = lean_box(0);
}
if (lean_is_scalar(x_65)) {
 x_66 = lean_alloc_ctor(1, 1, 0);
} else {
 x_66 = x_65;
}
lean_ctor_set(x_66, 0, x_64);
return x_66;
}
}
}
else
{
uint8_t x_67; 
lean_dec(x_34);
lean_dec(x_33);
lean_dec(x_32);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_67 = !lean_is_exclusive(x_37);
if (x_67 == 0)
{
return x_37;
}
else
{
lean_object* x_68; lean_object* x_69; 
x_68 = lean_ctor_get(x_37, 0);
lean_inc(x_68);
lean_dec(x_37);
x_69 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_69, 0, x_68);
return x_69;
}
}
}
else
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_30, 0);
lean_inc(x_70);
lean_dec_ref(x_30);
if (lean_obj_tag(x_70) == 0)
{
lean_object* x_71; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_71 = lean_ctor_get(x_70, 0);
lean_inc(x_71);
x_72 = lean_ctor_get(x_70, 1);
lean_inc_ref(x_72);
lean_dec_ref(x_70);
x_73 = ((lean_object*)(l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___closed__0));
x_74 = lean_string_dec_eq(x_72, x_73);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; 
x_75 = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(x_75, 0, x_72);
x_76 = l_Lean_MessageData_ofFormat(x_75);
x_77 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(x_71, x_76, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_71);
return x_77;
}
else
{
lean_object* x_78; 
lean_dec_ref(x_72);
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_78 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg(x_71);
return x_78;
}
}
else
{
lean_object* x_79; 
lean_dec_ref(x_6);
lean_dec_ref(x_2);
x_79 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return x_79;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_3);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; uint8_t x_12; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = l_Lean_Syntax_getArg(x_6, x_10);
x_12 = l_Lean_Syntax_isOfKind(x_11, x_7);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_6);
lean_dec_ref(x_3);
x_13 = lean_box(0);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; lean_object* x_16; size_t x_17; size_t x_18; lean_object* x_19; 
x_14 = lean_unsigned_to_nat(3u);
x_15 = lean_array_uset(x_3, x_2, x_10);
x_16 = l_Lean_Syntax_getArg(x_6, x_14);
lean_dec(x_6);
x_17 = 1;
x_18 = lean_usize_add(x_2, x_17);
x_19 = lean_array_uset(x_15, x_2, x_16);
x_2 = x_18;
x_3 = x_19;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__1));
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_3);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; uint8_t x_13; 
x_10 = lean_unsigned_to_nat(1u);
x_11 = l_Lean_Syntax_getArg(x_6, x_10);
x_12 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___closed__3));
x_13 = l_Lean_Syntax_isOfKind(x_11, x_12);
if (x_13 == 0)
{
lean_object* x_14; 
lean_dec(x_6);
lean_dec_ref(x_3);
x_14 = lean_box(0);
return x_14;
}
else
{
lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; size_t x_19; size_t x_20; lean_object* x_21; 
x_15 = lean_unsigned_to_nat(3u);
x_16 = lean_unsigned_to_nat(0u);
x_17 = lean_array_uset(x_3, x_2, x_16);
x_18 = l_Lean_Syntax_getArg(x_6, x_15);
lean_dec(x_6);
x_19 = 1;
x_20 = lean_usize_add(x_2, x_19);
x_21 = lean_array_uset(x_17, x_2, x_18);
x_2 = x_20;
x_3 = x_21;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; uint8_t x_8; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___closed__1));
lean_inc(x_6);
x_8 = l_Lean_Syntax_isOfKind(x_6, x_7);
if (x_8 == 0)
{
lean_object* x_9; 
lean_dec(x_6);
lean_dec_ref(x_3);
x_9 = lean_box(0);
return x_9;
}
else
{
lean_object* x_10; lean_object* x_11; lean_object* x_18; uint8_t x_19; 
x_10 = lean_unsigned_to_nat(0u);
x_11 = lean_array_uset(x_3, x_2, x_10);
x_18 = l_Lean_Syntax_getArg(x_6, x_10);
lean_dec(x_6);
x_19 = l_Lean_Syntax_isNone(x_18);
if (x_19 == 0)
{
lean_object* x_20; uint8_t x_21; 
x_20 = lean_unsigned_to_nat(2u);
x_21 = l_Lean_Syntax_matchesNull(x_18, x_20);
if (x_21 == 0)
{
lean_object* x_22; 
lean_dec_ref(x_11);
x_22 = lean_box(0);
return x_22;
}
else
{
goto block_17;
}
}
else
{
lean_dec(x_18);
goto block_17;
}
block_17:
{
lean_object* x_12; size_t x_13; size_t x_14; lean_object* x_15; 
x_12 = lean_box(0);
x_13 = 1;
x_14 = lean_usize_add(x_2, x_13);
x_15 = lean_array_uset(x_11, x_2, x_12);
x_2 = x_14;
x_3 = x_15;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(size_t x_1, size_t x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = lean_usize_dec_lt(x_2, x_1);
if (x_4 == 0)
{
lean_object* x_5; 
x_5 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_5, 0, x_3);
return x_5;
}
else
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; size_t x_9; size_t x_10; lean_object* x_11; 
x_6 = lean_array_uget(x_3, x_2);
x_7 = lean_unsigned_to_nat(0u);
x_8 = lean_array_uset(x_3, x_2, x_7);
x_9 = 1;
x_10 = lean_usize_add(x_2, x_9);
x_11 = lean_array_uset(x_8, x_2, x_6);
x_2 = x_10;
x_3 = x_11;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
size_t x_4; size_t x_5; lean_object* x_6; 
x_4 = lean_unbox_usize(x_1);
lean_dec(x_1);
x_5 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_6 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(x_4, x_5, x_3);
return x_6;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___lam__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_6; lean_object* x_7; lean_object* x_8; 
x_6 = lean_st_ref_get(x_4);
x_7 = lean_ctor_get(x_6, 0);
lean_inc_ref(x_7);
lean_dec(x_6);
x_8 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_8, 0, x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___lam__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5) {
_start:
{
lean_object* x_6; 
x_6 = l_Lean_Elab_Do_InferControlInfo_ofElem___lam__0(x_1, x_2, x_3, x_4);
lean_dec(x_4);
lean_dec_ref(x_3);
lean_dec(x_2);
lean_dec_ref(x_1);
return x_6;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___redArg(x_2, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
lean_object* x_5; 
x_5 = l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1(x_1, x_2, x_3, x_4);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
return x_5;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_11; 
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_11 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_11, 0, x_3);
return x_11;
}
else
{
uint8_t x_12; 
lean_dec_ref(x_3);
x_12 = !lean_is_exclusive(x_2);
if (x_12 == 0)
{
lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; 
x_13 = lean_ctor_get(x_2, 0);
x_14 = lean_ctor_get(x_2, 1);
x_15 = lean_ctor_get(x_13, 1);
lean_inc(x_15);
lean_dec(x_13);
x_16 = lean_box(0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_17 = lean_apply_8(x_15, x_1, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_17) == 0)
{
uint8_t x_18; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_18 = !lean_is_exclusive(x_17);
if (x_18 == 0)
{
lean_object* x_19; lean_object* x_20; 
x_19 = lean_ctor_get(x_17, 0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_19);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_20);
lean_ctor_set(x_17, 0, x_2);
return x_17;
}
else
{
lean_object* x_21; lean_object* x_22; lean_object* x_23; 
x_21 = lean_ctor_get(x_17, 0);
lean_inc(x_21);
lean_dec(x_17);
x_22 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_22, 0, x_21);
lean_ctor_set_tag(x_2, 0);
lean_ctor_set(x_2, 1, x_16);
lean_ctor_set(x_2, 0, x_22);
x_23 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_23, 0, x_2);
return x_23;
}
}
else
{
lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; uint8_t x_28; uint8_t x_36; 
lean_free_object(x_2);
x_24 = lean_ctor_get(x_17, 0);
lean_inc(x_24);
if (lean_is_exclusive(x_17)) {
 lean_ctor_release(x_17, 0);
 x_25 = x_17;
} else {
 lean_dec_ref(x_17);
 x_25 = lean_box(0);
}
x_26 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
x_27 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_36 = l_Lean_Exception_isInterrupt(x_24);
if (x_36 == 0)
{
uint8_t x_37; 
lean_inc(x_24);
x_37 = l_Lean_Exception_isRuntime(x_24);
x_28 = x_37;
goto block_35;
}
else
{
x_28 = x_36;
goto block_35;
}
block_35:
{
if (x_28 == 0)
{
if (lean_obj_tag(x_24) == 0)
{
lean_object* x_29; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_25)) {
 x_29 = lean_alloc_ctor(1, 1, 0);
} else {
 x_29 = x_25;
}
lean_ctor_set(x_29, 0, x_24);
return x_29;
}
else
{
lean_object* x_30; uint8_t x_31; 
x_30 = lean_ctor_get(x_24, 0);
x_31 = l_Lean_instBEqInternalExceptionId_beq(x_27, x_30);
if (x_31 == 0)
{
lean_object* x_32; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_25)) {
 x_32 = lean_alloc_ctor(1, 1, 0);
} else {
 x_32 = x_25;
}
lean_ctor_set(x_32, 0, x_24);
return x_32;
}
else
{
lean_dec_ref(x_24);
lean_dec(x_25);
x_2 = x_14;
x_3 = x_26;
goto _start;
}
}
}
else
{
lean_object* x_34; 
lean_dec(x_14);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_25)) {
 x_34 = lean_alloc_ctor(1, 1, 0);
} else {
 x_34 = x_25;
}
lean_ctor_set(x_34, 0, x_24);
return x_34;
}
}
}
}
else
{
lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; 
x_38 = lean_ctor_get(x_2, 0);
x_39 = lean_ctor_get(x_2, 1);
lean_inc(x_39);
lean_inc(x_38);
lean_dec(x_2);
x_40 = lean_ctor_get(x_38, 1);
lean_inc(x_40);
lean_dec(x_38);
x_41 = lean_box(0);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_1);
x_42 = lean_apply_8(x_40, x_1, x_4, x_5, x_6, x_7, x_8, x_9, lean_box(0));
if (lean_obj_tag(x_42) == 0)
{
lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
x_43 = lean_ctor_get(x_42, 0);
lean_inc(x_43);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_44 = x_42;
} else {
 lean_dec_ref(x_42);
 x_44 = lean_box(0);
}
x_45 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_45, 0, x_43);
x_46 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_46, 0, x_45);
lean_ctor_set(x_46, 1, x_41);
if (lean_is_scalar(x_44)) {
 x_47 = lean_alloc_ctor(0, 1, 0);
} else {
 x_47 = x_44;
}
lean_ctor_set(x_47, 0, x_46);
return x_47;
}
else
{
lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; uint8_t x_52; uint8_t x_60; 
x_48 = lean_ctor_get(x_42, 0);
lean_inc(x_48);
if (lean_is_exclusive(x_42)) {
 lean_ctor_release(x_42, 0);
 x_49 = x_42;
} else {
 lean_dec_ref(x_42);
 x_49 = lean_box(0);
}
x_50 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
x_51 = l_Lean_Elab_unsupportedSyntaxExceptionId;
x_60 = l_Lean_Exception_isInterrupt(x_48);
if (x_60 == 0)
{
uint8_t x_61; 
lean_inc(x_48);
x_61 = l_Lean_Exception_isRuntime(x_48);
x_52 = x_61;
goto block_59;
}
else
{
x_52 = x_60;
goto block_59;
}
block_59:
{
if (x_52 == 0)
{
if (lean_obj_tag(x_48) == 0)
{
lean_object* x_53; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_49)) {
 x_53 = lean_alloc_ctor(1, 1, 0);
} else {
 x_53 = x_49;
}
lean_ctor_set(x_53, 0, x_48);
return x_53;
}
else
{
lean_object* x_54; uint8_t x_55; 
x_54 = lean_ctor_get(x_48, 0);
x_55 = l_Lean_instBEqInternalExceptionId_beq(x_51, x_54);
if (x_55 == 0)
{
lean_object* x_56; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_49)) {
 x_56 = lean_alloc_ctor(1, 1, 0);
} else {
 x_56 = x_49;
}
lean_ctor_set(x_56, 0, x_48);
return x_56;
}
else
{
lean_dec_ref(x_48);
lean_dec(x_49);
x_2 = x_39;
x_3 = x_50;
goto _start;
}
}
}
else
{
lean_object* x_58; 
lean_dec(x_39);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_1);
if (lean_is_scalar(x_49)) {
 x_58 = lean_alloc_ctor(1, 1, 0);
} else {
 x_58 = x_49;
}
lean_ctor_set(x_58, 0, x_48);
return x_58;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; uint8_t x_13; uint8_t x_14; lean_object* x_15; uint8_t x_16; lean_object* x_17; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_50; lean_object* x_51; lean_object* x_52; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_65; 
if (lean_obj_tag(x_2) == 0)
{
lean_object* x_71; 
x_71 = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
x_58 = x_71;
x_59 = x_5;
x_60 = x_6;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = lean_box(0);
goto block_70;
}
else
{
lean_object* x_72; lean_object* x_73; 
x_72 = lean_ctor_get(x_2, 0);
lean_inc(x_72);
lean_dec_ref(x_2);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_73 = l_Lean_Elab_Do_InferControlInfo_ofElem(x_72, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_73) == 0)
{
lean_object* x_74; 
x_74 = lean_ctor_get(x_73, 0);
lean_inc(x_74);
lean_dec_ref(x_73);
x_58 = x_74;
x_59 = x_5;
x_60 = x_6;
x_61 = x_7;
x_62 = x_8;
x_63 = x_9;
x_64 = x_10;
x_65 = lean_box(0);
goto block_70;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec(x_3);
lean_dec_ref(x_1);
return x_73;
}
}
block_20:
{
lean_object* x_18; lean_object* x_19; 
x_18 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_18, 0, x_12);
lean_ctor_set(x_18, 1, x_17);
lean_ctor_set_uint8(x_18, sizeof(void*)*2, x_14);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 1, x_13);
lean_ctor_set_uint8(x_18, sizeof(void*)*2 + 2, x_16);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_18);
return x_19;
}
block_43:
{
lean_object* x_25; lean_object* x_26; uint8_t x_27; uint8_t x_28; uint8_t x_29; lean_object* x_30; lean_object* x_31; size_t x_32; size_t x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; uint8_t x_37; 
x_25 = l_Lean_Elab_Do_ControlInfo_alternative(x_23, x_22);
x_26 = l_Lean_Elab_Do_ControlInfo_sequence(x_21, x_25);
x_27 = lean_ctor_get_uint8(x_26, sizeof(void*)*2);
x_28 = lean_ctor_get_uint8(x_26, sizeof(void*)*2 + 1);
x_29 = lean_ctor_get_uint8(x_26, sizeof(void*)*2 + 2);
x_30 = lean_ctor_get(x_26, 0);
lean_inc(x_30);
x_31 = lean_ctor_get(x_26, 1);
lean_inc(x_31);
lean_dec_ref(x_26);
x_32 = lean_array_size(x_1);
x_33 = 0;
x_34 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__20(x_32, x_33, x_1);
x_35 = lean_unsigned_to_nat(0u);
x_36 = lean_array_get_size(x_34);
x_37 = lean_nat_dec_lt(x_35, x_36);
if (x_37 == 0)
{
lean_dec_ref(x_34);
x_12 = x_30;
x_13 = x_28;
x_14 = x_27;
x_15 = lean_box(0);
x_16 = x_29;
x_17 = x_31;
goto block_20;
}
else
{
uint8_t x_38; 
x_38 = lean_nat_dec_le(x_36, x_36);
if (x_38 == 0)
{
if (x_37 == 0)
{
lean_dec_ref(x_34);
x_12 = x_30;
x_13 = x_28;
x_14 = x_27;
x_15 = lean_box(0);
x_16 = x_29;
x_17 = x_31;
goto block_20;
}
else
{
size_t x_39; lean_object* x_40; 
x_39 = lean_usize_of_nat(x_36);
x_40 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(x_34, x_33, x_39, x_31);
lean_dec_ref(x_34);
x_12 = x_30;
x_13 = x_28;
x_14 = x_27;
x_15 = lean_box(0);
x_16 = x_29;
x_17 = x_40;
goto block_20;
}
}
else
{
size_t x_41; lean_object* x_42; 
x_41 = lean_usize_of_nat(x_36);
x_42 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofLetOrReassign_spec__21(x_34, x_33, x_41, x_31);
lean_dec_ref(x_34);
x_12 = x_30;
x_13 = x_28;
x_14 = x_27;
x_15 = lean_box(0);
x_16 = x_29;
x_17 = x_42;
goto block_20;
}
}
}
block_57:
{
if (lean_obj_tag(x_4) == 0)
{
lean_object* x_53; 
lean_dec(x_51);
lean_dec_ref(x_50);
lean_dec(x_49);
lean_dec_ref(x_48);
lean_dec(x_47);
lean_dec_ref(x_46);
x_53 = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
x_21 = x_44;
x_22 = x_45;
x_23 = x_53;
x_24 = lean_box(0);
goto block_43;
}
else
{
lean_object* x_54; lean_object* x_55; 
x_54 = lean_ctor_get(x_4, 0);
lean_inc(x_54);
lean_dec_ref(x_4);
x_55 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_54, x_46, x_47, x_48, x_49, x_50, x_51);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
lean_dec_ref(x_55);
x_21 = x_44;
x_22 = x_45;
x_23 = x_56;
x_24 = lean_box(0);
goto block_43;
}
else
{
lean_dec_ref(x_45);
lean_dec_ref(x_44);
lean_dec_ref(x_1);
return x_55;
}
}
}
block_70:
{
if (lean_obj_tag(x_3) == 0)
{
lean_object* x_66; 
x_66 = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
x_44 = x_58;
x_45 = x_66;
x_46 = x_59;
x_47 = x_60;
x_48 = x_61;
x_49 = x_62;
x_50 = x_63;
x_51 = x_64;
x_52 = lean_box(0);
goto block_57;
}
else
{
lean_object* x_67; lean_object* x_68; 
x_67 = lean_ctor_get(x_3, 0);
lean_inc(x_67);
lean_dec_ref(x_3);
lean_inc(x_64);
lean_inc_ref(x_63);
lean_inc(x_62);
lean_inc_ref(x_61);
lean_inc(x_60);
lean_inc_ref(x_59);
x_68 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_67, x_59, x_60, x_61, x_62, x_63, x_64);
if (lean_obj_tag(x_68) == 0)
{
lean_object* x_69; 
x_69 = lean_ctor_get(x_68, 0);
lean_inc(x_69);
lean_dec_ref(x_68);
x_44 = x_58;
x_45 = x_69;
x_46 = x_59;
x_47 = x_60;
x_48 = x_61;
x_49 = x_62;
x_50 = x_63;
x_51 = x_64;
x_52 = lean_box(0);
goto block_57;
}
else
{
lean_dec(x_64);
lean_dec_ref(x_63);
lean_dec(x_62);
lean_dec_ref(x_61);
lean_dec(x_60);
lean_dec_ref(x_59);
lean_dec_ref(x_58);
lean_dec(x_4);
lean_dec_ref(x_1);
return x_68;
}
}
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__2));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__6));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__8));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(1u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(uint8_t x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_18; lean_object* x_23; uint8_t x_24; 
x_23 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(x_2);
x_24 = l_Lean_Syntax_isOfKind(x_2, x_23);
if (x_24 == 0)
{
lean_object* x_25; uint8_t x_26; 
x_25 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(x_2);
x_26 = l_Lean_Syntax_isOfKind(x_2, x_25);
if (x_26 == 0)
{
lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; lean_object* x_35; 
x_27 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
x_28 = lean_box(0);
x_29 = l_Lean_Syntax_formatStx(x_2, x_28, x_26);
x_30 = l_Std_Format_defWidth;
x_31 = lean_unsigned_to_nat(0u);
x_32 = l_Std_Format_pretty(x_29, x_30, x_31, x_31);
x_33 = l_Lean_stringToMessageData(x_32);
x_34 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_34, 0, x_27);
lean_ctor_set(x_34, 1, x_33);
x_35 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_34, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_35;
}
else
{
lean_object* x_36; lean_object* x_37; lean_object* x_38; lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_49; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; lean_object* x_62; lean_object* x_63; lean_object* x_64; lean_object* x_72; lean_object* x_73; uint8_t x_74; 
x_36 = lean_unsigned_to_nat(0u);
x_37 = l_Lean_Syntax_getArg(x_2, x_36);
x_38 = lean_unsigned_to_nat(2u);
x_39 = l_Lean_Syntax_getArg(x_2, x_38);
x_72 = lean_unsigned_to_nat(3u);
x_73 = l_Lean_Syntax_getArg(x_2, x_72);
x_74 = l_Lean_Syntax_isNone(x_73);
if (x_74 == 0)
{
uint8_t x_75; 
lean_inc(x_73);
x_75 = l_Lean_Syntax_matchesNull(x_73, x_72);
if (x_75 == 0)
{
lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; 
lean_dec(x_73);
lean_dec(x_39);
lean_dec(x_37);
x_76 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
x_77 = lean_box(0);
x_78 = l_Lean_Syntax_formatStx(x_2, x_77, x_75);
x_79 = l_Std_Format_defWidth;
x_80 = l_Std_Format_pretty(x_78, x_79, x_36, x_36);
x_81 = l_Lean_stringToMessageData(x_80);
x_82 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_82, 0, x_76);
lean_ctor_set(x_82, 1, x_81);
x_83 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_82, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_83;
}
else
{
lean_object* x_84; lean_object* x_85; lean_object* x_86; lean_object* x_87; lean_object* x_88; lean_object* x_89; lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_97; uint8_t x_98; 
x_84 = lean_unsigned_to_nat(1u);
x_85 = l_Lean_Syntax_getArg(x_73, x_84);
x_97 = l_Lean_Syntax_getArg(x_73, x_38);
lean_dec(x_73);
x_98 = l_Lean_Syntax_isNone(x_97);
if (x_98 == 0)
{
uint8_t x_99; 
lean_inc(x_97);
x_99 = l_Lean_Syntax_matchesNull(x_97, x_84);
if (x_99 == 0)
{
lean_object* x_100; lean_object* x_101; lean_object* x_102; lean_object* x_103; lean_object* x_104; lean_object* x_105; lean_object* x_106; lean_object* x_107; 
lean_dec(x_97);
lean_dec(x_85);
lean_dec(x_39);
lean_dec(x_37);
x_100 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
x_101 = lean_box(0);
x_102 = l_Lean_Syntax_formatStx(x_2, x_101, x_99);
x_103 = l_Std_Format_defWidth;
x_104 = l_Std_Format_pretty(x_102, x_103, x_36, x_36);
x_105 = l_Lean_stringToMessageData(x_104);
x_106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_106, 0, x_100);
lean_ctor_set(x_106, 1, x_105);
x_107 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_106, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_107;
}
else
{
lean_object* x_108; lean_object* x_109; 
lean_dec(x_2);
x_108 = l_Lean_Syntax_getArg(x_97, x_36);
lean_dec(x_97);
x_109 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_109, 0, x_108);
x_86 = x_109;
x_87 = x_3;
x_88 = x_4;
x_89 = x_5;
x_90 = x_6;
x_91 = x_7;
x_92 = x_8;
x_93 = lean_box(0);
goto block_96;
}
}
else
{
lean_object* x_110; 
lean_dec(x_97);
lean_dec(x_2);
x_110 = lean_box(0);
x_86 = x_110;
x_87 = x_3;
x_88 = x_4;
x_89 = x_5;
x_90 = x_6;
x_91 = x_7;
x_92 = x_8;
x_93 = lean_box(0);
goto block_96;
}
block_96:
{
lean_object* x_94; lean_object* x_95; 
x_94 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_94, 0, x_85);
x_95 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_95, 0, x_86);
x_56 = x_94;
x_57 = x_95;
x_58 = x_87;
x_59 = x_88;
x_60 = x_89;
x_61 = x_90;
x_62 = x_91;
x_63 = x_92;
x_64 = lean_box(0);
goto block_71;
}
}
}
else
{
lean_object* x_111; 
lean_dec(x_73);
lean_dec(x_2);
x_111 = lean_box(0);
x_56 = x_111;
x_57 = x_111;
x_58 = x_3;
x_59 = x_4;
x_60 = x_5;
x_61 = x_6;
x_62 = x_7;
x_63 = x_8;
x_64 = lean_box(0);
goto block_71;
}
block_55:
{
lean_object* x_50; 
x_50 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_50, 0, x_39);
if (lean_obj_tag(x_40) == 0)
{
lean_object* x_51; lean_object* x_52; 
x_51 = lean_box(0);
x_52 = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(x_42, x_50, x_41, x_51, x_43, x_44, x_45, x_46, x_47, x_48);
return x_52;
}
else
{
lean_object* x_53; lean_object* x_54; 
x_53 = lean_ctor_get(x_40, 0);
lean_inc(x_53);
lean_dec_ref(x_40);
x_54 = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(x_42, x_50, x_41, x_53, x_43, x_44, x_45, x_46, x_47, x_48);
return x_54;
}
}
block_71:
{
if (x_1 == 0)
{
lean_object* x_65; 
lean_dec(x_37);
x_65 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6);
x_40 = x_57;
x_41 = x_56;
x_42 = x_65;
x_43 = x_58;
x_44 = x_59;
x_45 = x_60;
x_46 = x_61;
x_47 = x_62;
x_48 = x_63;
x_49 = lean_box(0);
goto block_55;
}
else
{
lean_object* x_66; 
lean_inc(x_63);
lean_inc_ref(x_62);
lean_inc(x_61);
lean_inc_ref(x_60);
lean_inc(x_59);
lean_inc_ref(x_58);
x_66 = l_Lean_Elab_Do_getPatternVarsEx(x_37, x_58, x_59, x_60, x_61, x_62, x_63);
if (lean_obj_tag(x_66) == 0)
{
lean_object* x_67; 
x_67 = lean_ctor_get(x_66, 0);
lean_inc(x_67);
lean_dec_ref(x_66);
x_40 = x_57;
x_41 = x_56;
x_42 = x_67;
x_43 = x_58;
x_44 = x_59;
x_45 = x_60;
x_46 = x_61;
x_47 = x_62;
x_48 = x_63;
x_49 = lean_box(0);
goto block_55;
}
else
{
uint8_t x_68; 
lean_dec(x_63);
lean_dec_ref(x_62);
lean_dec(x_61);
lean_dec_ref(x_60);
lean_dec(x_59);
lean_dec_ref(x_58);
lean_dec(x_57);
lean_dec(x_56);
lean_dec(x_39);
x_68 = !lean_is_exclusive(x_66);
if (x_68 == 0)
{
return x_66;
}
else
{
lean_object* x_69; lean_object* x_70; 
x_69 = lean_ctor_get(x_66, 0);
lean_inc(x_69);
lean_dec(x_66);
x_70 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_70, 0, x_69);
return x_70;
}
}
}
}
}
}
else
{
lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; lean_object* x_119; lean_object* x_120; lean_object* x_127; uint8_t x_128; 
x_112 = lean_unsigned_to_nat(0u);
x_113 = l_Lean_Syntax_getArg(x_2, x_112);
x_127 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__9));
lean_inc(x_113);
x_128 = l_Lean_Syntax_isOfKind(x_113, x_127);
if (x_128 == 0)
{
lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
lean_dec(x_113);
x_129 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
x_130 = lean_box(0);
x_131 = l_Lean_Syntax_formatStx(x_2, x_130, x_128);
x_132 = l_Std_Format_defWidth;
x_133 = l_Std_Format_pretty(x_131, x_132, x_112, x_112);
x_134 = l_Lean_stringToMessageData(x_133);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_129);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_135, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; uint8_t x_139; 
x_137 = lean_unsigned_to_nat(1u);
x_138 = l_Lean_Syntax_getArg(x_2, x_137);
x_139 = l_Lean_Syntax_isNone(x_138);
if (x_139 == 0)
{
uint8_t x_140; 
lean_inc(x_138);
x_140 = l_Lean_Syntax_matchesNull(x_138, x_137);
if (x_140 == 0)
{
lean_object* x_141; lean_object* x_142; lean_object* x_143; lean_object* x_144; lean_object* x_145; lean_object* x_146; lean_object* x_147; lean_object* x_148; 
lean_dec(x_138);
lean_dec(x_113);
x_141 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
x_142 = lean_box(0);
x_143 = l_Lean_Syntax_formatStx(x_2, x_142, x_140);
x_144 = l_Std_Format_defWidth;
x_145 = l_Std_Format_pretty(x_143, x_144, x_112, x_112);
x_146 = l_Lean_stringToMessageData(x_145);
x_147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_147, 0, x_141);
lean_ctor_set(x_147, 1, x_146);
x_148 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_147, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_148;
}
else
{
lean_object* x_149; lean_object* x_150; uint8_t x_151; 
x_149 = l_Lean_Syntax_getArg(x_138, x_112);
lean_dec(x_138);
x_150 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__11));
x_151 = l_Lean_Syntax_isOfKind(x_149, x_150);
if (x_151 == 0)
{
lean_object* x_152; lean_object* x_153; lean_object* x_154; lean_object* x_155; lean_object* x_156; lean_object* x_157; lean_object* x_158; lean_object* x_159; 
lean_dec(x_113);
x_152 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__5);
x_153 = lean_box(0);
x_154 = l_Lean_Syntax_formatStx(x_2, x_153, x_151);
x_155 = l_Std_Format_defWidth;
x_156 = l_Std_Format_pretty(x_154, x_155, x_112, x_112);
x_157 = l_Lean_stringToMessageData(x_156);
x_158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_158, 0, x_152);
lean_ctor_set(x_158, 1, x_157);
x_159 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_158, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_159;
}
else
{
x_114 = x_3;
x_115 = x_4;
x_116 = x_5;
x_117 = x_6;
x_118 = x_7;
x_119 = x_8;
x_120 = lean_box(0);
goto block_126;
}
}
}
else
{
lean_dec(x_138);
x_114 = x_3;
x_115 = x_4;
x_116 = x_5;
x_117 = x_6;
x_118 = x_7;
x_119 = x_8;
x_120 = lean_box(0);
goto block_126;
}
}
block_126:
{
lean_object* x_121; lean_object* x_122; 
x_121 = lean_unsigned_to_nat(3u);
x_122 = l_Lean_Syntax_getArg(x_2, x_121);
lean_dec(x_2);
if (x_1 == 0)
{
lean_object* x_123; 
lean_dec(x_113);
x_123 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6);
x_10 = x_122;
x_11 = x_117;
x_12 = x_114;
x_13 = x_118;
x_14 = lean_box(0);
x_15 = x_119;
x_16 = x_115;
x_17 = x_116;
x_18 = x_123;
goto block_22;
}
else
{
lean_object* x_124; lean_object* x_125; 
x_124 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__7);
x_125 = lean_array_push(x_124, x_113);
x_10 = x_122;
x_11 = x_117;
x_12 = x_114;
x_13 = x_118;
x_14 = lean_box(0);
x_15 = x_119;
x_16 = x_115;
x_17 = x_116;
x_18 = x_125;
goto block_22;
}
}
}
block_22:
{
lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_19 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_19, 0, x_10);
x_20 = lean_box(0);
x_21 = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(x_18, x_19, x_20, x_20, x_12, x_16, x_17, x_11, x_13, x_15);
return x_21;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
lean_object* x_14; lean_object* x_15; 
x_14 = lean_array_uget_borrowed(x_1, x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_14);
x_15 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_14, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_15) == 0)
{
lean_object* x_16; lean_object* x_17; size_t x_18; size_t x_19; 
x_16 = lean_ctor_get(x_15, 0);
lean_inc(x_16);
lean_dec_ref(x_15);
x_17 = l_Lean_Elab_Do_ControlInfo_alternative(x_16, x_4);
x_18 = 1;
x_19 = lean_usize_add(x_3, x_18);
x_3 = x_19;
x_4 = x_17;
goto _start;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_15;
}
}
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__4));
x_2 = l_Lean_stringToMessageData(x_1);
return x_2;
}
}
static lean_object* _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2(void) {
_start:
{
lean_object* x_1; lean_object* x_2; 
x_1 = lean_unsigned_to_nat(0u);
x_2 = lean_mk_empty_array_with_capacity(x_1);
return x_2;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_4, x_3);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
x_22 = lean_array_uget_borrowed(x_2, x_4);
lean_inc(x_22);
x_23 = l_Lean_Syntax_isOfKind(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_24);
x_13 = x_5;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_unsigned_to_nat(3u);
x_43 = l_Lean_Syntax_getArg(x_22, x_28);
x_44 = l_Lean_Syntax_getArgs(x_43);
lean_dec(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2);
x_47 = lean_array_get_size(x_44);
x_48 = lean_nat_dec_lt(x_45, x_47);
if (x_48 == 0)
{
lean_dec_ref(x_44);
x_30 = x_46;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_box(x_23);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
x_51 = lean_nat_dec_le(x_47, x_47);
if (x_51 == 0)
{
if (x_48 == 0)
{
lean_dec_ref(x_50);
lean_dec_ref(x_44);
x_30 = x_46;
goto block_42;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_47);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(x_23, x_1, x_44, x_52, x_53, x_50);
lean_dec_ref(x_44);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_30 = x_55;
goto block_42;
}
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_47);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(x_23, x_1, x_44, x_56, x_57, x_50);
lean_dec_ref(x_44);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec_ref(x_58);
x_30 = x_59;
goto block_42;
}
}
block_42:
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_array_size(x_30);
x_32 = 0;
x_33 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(x_31, x_32, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(x_34) == 0)
{
lean_dec_ref(x_34);
x_13 = x_5;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_33);
x_38 = l_Lean_Syntax_getArg(x_22, x_29);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_39 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_38, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Elab_Do_ControlInfo_alternative(x_5, x_40);
x_13 = x_41;
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_39;
}
}
}
}
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_4 = x_16;
x_5 = x_13;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; lean_object* x_13; uint8_t x_18; 
x_18 = lean_usize_dec_lt(x_3, x_2);
if (x_18 == 0)
{
lean_object* x_19; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_19 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_19, 0, x_4);
return x_19;
}
else
{
lean_object* x_20; lean_object* x_21; lean_object* x_22; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_35; uint8_t x_36; 
x_20 = lean_unsigned_to_nat(0u);
x_21 = lean_array_uget_borrowed(x_1, x_3);
x_35 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__1));
lean_inc(x_21);
x_36 = l_Lean_Syntax_isOfKind(x_21, x_35);
if (x_36 == 0)
{
lean_object* x_37; uint8_t x_38; 
x_37 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__3));
lean_inc(x_21);
x_38 = l_Lean_Syntax_isOfKind(x_21, x_37);
if (x_38 == 0)
{
lean_object* x_39; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; 
x_39 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
x_40 = lean_box(0);
lean_inc(x_21);
x_41 = l_Lean_Syntax_formatStx(x_21, x_40, x_38);
x_42 = l_Std_Format_defWidth;
x_43 = l_Std_Format_pretty(x_41, x_42, x_20, x_20);
x_44 = l_Lean_stringToMessageData(x_43);
x_45 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_45, 0, x_39);
lean_ctor_set(x_45, 1, x_44);
lean_inc_ref(x_5);
x_46 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_45, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_46) == 0)
{
lean_dec_ref(x_46);
x_12 = x_4;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_47; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_47 = !lean_is_exclusive(x_46);
if (x_47 == 0)
{
return x_46;
}
else
{
lean_object* x_48; lean_object* x_49; 
x_48 = lean_ctor_get(x_46, 0);
lean_inc(x_48);
lean_dec(x_46);
x_49 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_49, 0, x_48);
return x_49;
}
}
}
else
{
lean_object* x_50; lean_object* x_51; lean_object* x_52; uint8_t x_53; 
x_50 = lean_unsigned_to_nat(1u);
x_51 = l_Lean_Syntax_getArg(x_21, x_50);
x_52 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(x_51);
x_53 = l_Lean_Syntax_isOfKind(x_51, x_52);
if (x_53 == 0)
{
lean_object* x_54; lean_object* x_55; lean_object* x_56; lean_object* x_57; lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_51);
x_54 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
x_55 = lean_box(0);
lean_inc(x_21);
x_56 = l_Lean_Syntax_formatStx(x_21, x_55, x_53);
x_57 = l_Std_Format_defWidth;
x_58 = l_Std_Format_pretty(x_56, x_57, x_20, x_20);
x_59 = l_Lean_stringToMessageData(x_58);
x_60 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_60, 0, x_54);
lean_ctor_set(x_60, 1, x_59);
lean_inc_ref(x_5);
x_61 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_60, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_61) == 0)
{
lean_dec_ref(x_61);
x_12 = x_4;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_62; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_62 = !lean_is_exclusive(x_61);
if (x_62 == 0)
{
return x_61;
}
else
{
lean_object* x_63; lean_object* x_64; 
x_63 = lean_ctor_get(x_61, 0);
lean_inc(x_63);
lean_dec(x_61);
x_64 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_64, 0, x_63);
return x_64;
}
}
}
else
{
lean_object* x_65; lean_object* x_66; size_t x_67; size_t x_68; lean_object* x_69; 
x_65 = l_Lean_Syntax_getArg(x_51, x_20);
lean_dec(x_51);
x_66 = l_Lean_Syntax_getArgs(x_65);
lean_dec(x_65);
x_67 = lean_array_size(x_66);
x_68 = 0;
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_69 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(x_36, x_66, x_67, x_68, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_66);
if (lean_obj_tag(x_69) == 0)
{
lean_object* x_70; 
x_70 = lean_ctor_get(x_69, 0);
lean_inc(x_70);
lean_dec_ref(x_69);
x_12 = x_70;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_69;
}
}
}
}
else
{
lean_object* x_71; lean_object* x_72; uint8_t x_73; 
x_71 = lean_unsigned_to_nat(2u);
x_72 = l_Lean_Syntax_getArg(x_21, x_71);
x_73 = l_Lean_Syntax_isNone(x_72);
if (x_73 == 0)
{
uint8_t x_74; 
x_74 = l_Lean_Syntax_matchesNull(x_72, x_71);
if (x_74 == 0)
{
lean_object* x_75; lean_object* x_76; lean_object* x_77; lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; 
x_75 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__5);
x_76 = lean_box(0);
lean_inc(x_21);
x_77 = l_Lean_Syntax_formatStx(x_21, x_76, x_74);
x_78 = l_Std_Format_defWidth;
x_79 = l_Std_Format_pretty(x_77, x_78, x_20, x_20);
x_80 = l_Lean_stringToMessageData(x_79);
x_81 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_81, 0, x_75);
lean_ctor_set(x_81, 1, x_80);
lean_inc_ref(x_5);
x_82 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_81, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_82) == 0)
{
lean_dec_ref(x_82);
x_12 = x_4;
x_13 = lean_box(0);
goto block_17;
}
else
{
uint8_t x_83; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
x_83 = !lean_is_exclusive(x_82);
if (x_83 == 0)
{
return x_82;
}
else
{
lean_object* x_84; lean_object* x_85; 
x_84 = lean_ctor_get(x_82, 0);
lean_inc(x_84);
lean_dec(x_82);
x_85 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_85, 0, x_84);
return x_85;
}
}
}
else
{
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = lean_box(0);
goto block_34;
}
}
else
{
lean_dec(x_72);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
x_22 = x_5;
x_23 = x_6;
x_24 = x_7;
x_25 = x_8;
x_26 = x_9;
x_27 = x_10;
x_28 = lean_box(0);
goto block_34;
}
}
block_34:
{
lean_object* x_29; lean_object* x_30; lean_object* x_31; 
x_29 = lean_unsigned_to_nat(4u);
x_30 = l_Lean_Syntax_getArg(x_21, x_29);
x_31 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_30, x_22, x_23, x_24, x_25, x_26, x_27);
if (lean_obj_tag(x_31) == 0)
{
lean_object* x_32; lean_object* x_33; 
x_32 = lean_ctor_get(x_31, 0);
lean_inc(x_32);
lean_dec_ref(x_31);
x_33 = l_Lean_Elab_Do_ControlInfo_alternative(x_32, x_4);
x_12 = x_33;
x_13 = lean_box(0);
goto block_17;
}
else
{
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec_ref(x_4);
return x_31;
}
}
}
block_17:
{
size_t x_14; size_t x_15; 
x_14 = 1;
x_15 = lean_usize_add(x_3, x_14);
x_3 = x_15;
x_4 = x_12;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
if (lean_obj_tag(x_1) == 0)
{
lean_object* x_9; lean_object* x_10; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_9 = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
x_10 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_10, 0, x_9);
return x_10;
}
else
{
lean_object* x_11; lean_object* x_12; 
x_11 = lean_ctor_get(x_1, 0);
lean_inc(x_11);
lean_dec_ref(x_1);
x_12 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_11, x_2, x_3, x_4, x_5, x_6, x_7);
return x_12;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(uint8_t x_1, lean_object* x_2, size_t x_3, size_t x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; lean_object* x_14; uint8_t x_19; 
x_19 = lean_usize_dec_lt(x_4, x_3);
if (x_19 == 0)
{
lean_object* x_20; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
x_20 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_20, 0, x_5);
return x_20;
}
else
{
lean_object* x_21; lean_object* x_22; uint8_t x_23; 
x_21 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__1));
x_22 = lean_array_uget_borrowed(x_2, x_4);
lean_inc(x_22);
x_23 = l_Lean_Syntax_isOfKind(x_22, x_21);
if (x_23 == 0)
{
lean_object* x_24; 
x_24 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(x_24) == 0)
{
lean_dec_ref(x_24);
x_13 = x_5;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_25; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_25 = !lean_is_exclusive(x_24);
if (x_25 == 0)
{
return x_24;
}
else
{
lean_object* x_26; lean_object* x_27; 
x_26 = lean_ctor_get(x_24, 0);
lean_inc(x_26);
lean_dec(x_24);
x_27 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_27, 0, x_26);
return x_27;
}
}
}
else
{
lean_object* x_28; lean_object* x_29; lean_object* x_30; lean_object* x_43; lean_object* x_44; lean_object* x_45; lean_object* x_46; lean_object* x_47; uint8_t x_48; 
x_28 = lean_unsigned_to_nat(1u);
x_29 = lean_unsigned_to_nat(3u);
x_43 = l_Lean_Syntax_getArg(x_22, x_28);
x_44 = l_Lean_Syntax_getArgs(x_43);
lean_dec(x_43);
x_45 = lean_unsigned_to_nat(0u);
x_46 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2);
x_47 = lean_array_get_size(x_44);
x_48 = lean_nat_dec_lt(x_45, x_47);
if (x_48 == 0)
{
lean_dec_ref(x_44);
x_30 = x_46;
goto block_42;
}
else
{
lean_object* x_49; lean_object* x_50; uint8_t x_51; 
x_49 = lean_box(x_23);
x_50 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_50, 0, x_49);
lean_ctor_set(x_50, 1, x_46);
x_51 = lean_nat_dec_le(x_47, x_47);
if (x_51 == 0)
{
if (x_48 == 0)
{
lean_dec_ref(x_50);
lean_dec_ref(x_44);
x_30 = x_46;
goto block_42;
}
else
{
size_t x_52; size_t x_53; lean_object* x_54; lean_object* x_55; 
x_52 = 0;
x_53 = lean_usize_of_nat(x_47);
x_54 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(x_23, x_1, x_44, x_52, x_53, x_50);
lean_dec_ref(x_44);
x_55 = lean_ctor_get(x_54, 1);
lean_inc(x_55);
lean_dec_ref(x_54);
x_30 = x_55;
goto block_42;
}
}
else
{
size_t x_56; size_t x_57; lean_object* x_58; lean_object* x_59; 
x_56 = 0;
x_57 = lean_usize_of_nat(x_47);
x_58 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(x_23, x_1, x_44, x_56, x_57, x_50);
lean_dec_ref(x_44);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec_ref(x_58);
x_30 = x_59;
goto block_42;
}
}
block_42:
{
size_t x_31; size_t x_32; lean_object* x_33; 
x_31 = lean_array_size(x_30);
x_32 = 0;
x_33 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__8(x_31, x_32, x_30);
if (lean_obj_tag(x_33) == 0)
{
lean_object* x_34; 
x_34 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
if (lean_obj_tag(x_34) == 0)
{
lean_dec_ref(x_34);
x_13 = x_5;
x_14 = lean_box(0);
goto block_18;
}
else
{
uint8_t x_35; 
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
x_35 = !lean_is_exclusive(x_34);
if (x_35 == 0)
{
return x_34;
}
else
{
lean_object* x_36; lean_object* x_37; 
x_36 = lean_ctor_get(x_34, 0);
lean_inc(x_36);
lean_dec(x_34);
x_37 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_37, 0, x_36);
return x_37;
}
}
}
else
{
lean_object* x_38; lean_object* x_39; 
lean_dec_ref(x_33);
x_38 = l_Lean_Syntax_getArg(x_22, x_29);
lean_inc(x_11);
lean_inc_ref(x_10);
lean_inc(x_9);
lean_inc_ref(x_8);
lean_inc(x_7);
lean_inc_ref(x_6);
x_39 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_38, x_6, x_7, x_8, x_9, x_10, x_11);
if (lean_obj_tag(x_39) == 0)
{
lean_object* x_40; lean_object* x_41; 
x_40 = lean_ctor_get(x_39, 0);
lean_inc(x_40);
lean_dec_ref(x_39);
x_41 = l_Lean_Elab_Do_ControlInfo_alternative(x_5, x_40);
x_13 = x_41;
x_14 = lean_box(0);
goto block_18;
}
else
{
lean_dec(x_11);
lean_dec_ref(x_10);
lean_dec(x_9);
lean_dec_ref(x_8);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec_ref(x_5);
return x_39;
}
}
}
}
}
block_18:
{
size_t x_15; size_t x_16; 
x_15 = 1;
x_16 = lean_usize_add(x_4, x_15);
x_4 = x_16;
x_5 = x_13;
goto _start;
}
}
}
static lean_object* _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76(void) {
_start:
{
lean_object* x_1; lean_object* x_2; uint8_t x_3; uint8_t x_4; lean_object* x_5; 
x_1 = l_Lean_NameSet_empty;
x_2 = lean_unsigned_to_nat(0u);
x_3 = 0;
x_4 = 1;
x_5 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_5, 0, x_2);
lean_ctor_set(x_5, 1, x_1);
lean_ctor_set_uint8(x_5, sizeof(void*)*2, x_4);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 1, x_3);
lean_ctor_set_uint8(x_5, sizeof(void*)*2 + 2, x_3);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; lean_object* x_11; lean_object* x_12; lean_object* x_13; lean_object* x_14; lean_object* x_15; lean_object* x_16; lean_object* x_17; lean_object* x_23; lean_object* x_24; lean_object* x_25; lean_object* x_26; lean_object* x_27; lean_object* x_28; lean_object* x_29; lean_object* x_40; lean_object* x_41; lean_object* x_42; lean_object* x_46; lean_object* x_47; lean_object* x_48; lean_object* x_52; lean_object* x_53; lean_object* x_54; lean_object* x_55; 
x_52 = lean_st_ref_get(x_7);
x_53 = lean_ctor_get(x_52, 0);
lean_inc_ref(x_53);
lean_dec(x_52);
lean_inc(x_1);
x_54 = lean_alloc_closure((void*)(l_Lean_Elab_expandMacroImpl_x3f___boxed), 4, 2);
lean_closure_set(x_54, 0, x_53);
lean_closure_set(x_54, 1, x_1);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_55 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(x_54, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_55) == 0)
{
lean_object* x_56; lean_object* x_57; 
x_56 = lean_ctor_get(x_55, 0);
lean_inc(x_56);
if (lean_is_exclusive(x_55)) {
 lean_ctor_release(x_55, 0);
 x_57 = x_55;
} else {
 lean_dec_ref(x_55);
 x_57 = lean_box(0);
}
if (lean_obj_tag(x_56) == 1)
{
lean_object* x_58; lean_object* x_59; lean_object* x_60; lean_object* x_61; 
lean_dec(x_57);
lean_dec(x_1);
x_58 = lean_ctor_get(x_56, 0);
lean_inc(x_58);
lean_dec_ref(x_56);
x_59 = lean_ctor_get(x_58, 1);
lean_inc(x_59);
lean_dec(x_58);
x_60 = lean_alloc_closure((void*)(l_liftExcept___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__1___boxed), 4, 2);
lean_closure_set(x_60, 0, lean_box(0));
lean_closure_set(x_60, 1, x_59);
lean_inc_ref(x_6);
lean_inc_ref(x_2);
x_61 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(x_60, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_61) == 0)
{
lean_object* x_62; 
x_62 = lean_ctor_get(x_61, 0);
lean_inc(x_62);
lean_dec_ref(x_61);
x_1 = x_62;
goto _start;
}
else
{
uint8_t x_64; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_64 = !lean_is_exclusive(x_61);
if (x_64 == 0)
{
return x_61;
}
else
{
lean_object* x_65; lean_object* x_66; 
x_65 = lean_ctor_get(x_61, 0);
lean_inc(x_65);
lean_dec(x_61);
x_66 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_66, 0, x_65);
return x_66;
}
}
}
else
{
lean_object* x_67; lean_object* x_68; lean_object* x_69; lean_object* x_70; lean_object* x_71; lean_object* x_72; lean_object* x_73; lean_object* x_145; uint8_t x_146; uint8_t x_147; 
lean_dec(x_56);
x_145 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__11));
lean_inc(x_1);
x_146 = l_Lean_Syntax_isOfKind(x_1, x_145);
x_147 = 1;
if (x_146 == 0)
{
lean_object* x_148; uint8_t x_149; 
x_148 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__13));
lean_inc(x_1);
x_149 = l_Lean_Syntax_isOfKind(x_1, x_148);
if (x_149 == 0)
{
lean_object* x_150; uint8_t x_151; 
x_150 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__15));
lean_inc(x_1);
x_151 = l_Lean_Syntax_isOfKind(x_1, x_150);
if (x_151 == 0)
{
lean_object* x_152; uint8_t x_153; 
x_152 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__17));
lean_inc(x_1);
x_153 = l_Lean_Syntax_isOfKind(x_1, x_152);
if (x_153 == 0)
{
lean_object* x_154; uint8_t x_155; 
x_154 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__19));
lean_inc(x_1);
x_155 = l_Lean_Syntax_isOfKind(x_1, x_154);
if (x_155 == 0)
{
lean_object* x_156; uint8_t x_157; 
x_156 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__21));
lean_inc(x_1);
x_157 = l_Lean_Syntax_isOfKind(x_1, x_156);
if (x_157 == 0)
{
lean_object* x_158; uint8_t x_159; 
lean_dec(x_57);
x_158 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__23));
lean_inc(x_1);
x_159 = l_Lean_Syntax_isOfKind(x_1, x_158);
if (x_159 == 0)
{
lean_object* x_160; uint8_t x_161; 
x_160 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__25));
lean_inc(x_1);
x_161 = l_Lean_Syntax_isOfKind(x_1, x_160);
if (x_161 == 0)
{
lean_object* x_162; uint8_t x_163; lean_object* x_164; lean_object* x_165; lean_object* x_166; lean_object* x_167; lean_object* x_168; lean_object* x_169; lean_object* x_170; 
x_162 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__27));
lean_inc(x_1);
x_163 = l_Lean_Syntax_isOfKind(x_1, x_162);
if (x_163 == 0)
{
lean_object* x_175; uint8_t x_176; 
x_175 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__29));
lean_inc(x_1);
x_176 = l_Lean_Syntax_isOfKind(x_1, x_175);
if (x_176 == 0)
{
lean_object* x_177; uint8_t x_178; 
x_177 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__31));
lean_inc(x_1);
x_178 = l_Lean_Syntax_isOfKind(x_1, x_177);
if (x_178 == 0)
{
lean_object* x_179; uint8_t x_180; 
x_179 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__33));
lean_inc(x_1);
x_180 = l_Lean_Syntax_isOfKind(x_1, x_179);
if (x_180 == 0)
{
lean_object* x_181; uint8_t x_182; 
x_181 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__35));
lean_inc(x_1);
x_182 = l_Lean_Syntax_isOfKind(x_1, x_181);
if (x_182 == 0)
{
lean_object* x_183; uint8_t x_184; 
x_183 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__37));
lean_inc(x_1);
x_184 = l_Lean_Syntax_isOfKind(x_1, x_183);
if (x_184 == 0)
{
lean_object* x_185; uint8_t x_186; 
x_185 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__39));
lean_inc(x_1);
x_186 = l_Lean_Syntax_isOfKind(x_1, x_185);
if (x_186 == 0)
{
lean_object* x_187; uint8_t x_188; 
x_187 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__41));
lean_inc(x_1);
x_188 = l_Lean_Syntax_isOfKind(x_1, x_187);
if (x_188 == 0)
{
lean_object* x_189; uint8_t x_190; 
x_189 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__43));
lean_inc(x_1);
x_190 = l_Lean_Syntax_isOfKind(x_1, x_189);
if (x_190 == 0)
{
lean_object* x_191; uint8_t x_192; 
x_191 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__45));
lean_inc(x_1);
x_192 = l_Lean_Syntax_isOfKind(x_1, x_191);
if (x_192 == 0)
{
lean_object* x_193; uint8_t x_194; 
x_193 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__47));
lean_inc(x_1);
x_194 = l_Lean_Syntax_isOfKind(x_1, x_193);
if (x_194 == 0)
{
lean_object* x_195; uint8_t x_196; 
x_195 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__49));
lean_inc(x_1);
x_196 = l_Lean_Syntax_isOfKind(x_1, x_195);
if (x_196 == 0)
{
lean_object* x_197; uint8_t x_198; 
x_197 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__51));
lean_inc(x_1);
x_198 = l_Lean_Syntax_isOfKind(x_1, x_197);
if (x_198 == 0)
{
lean_object* x_199; uint8_t x_200; 
x_199 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__53));
lean_inc(x_1);
x_200 = l_Lean_Syntax_isOfKind(x_1, x_199);
if (x_200 == 0)
{
lean_object* x_201; uint8_t x_202; 
x_201 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__55));
lean_inc(x_1);
x_202 = l_Lean_Syntax_isOfKind(x_1, x_201);
if (x_202 == 0)
{
lean_object* x_203; lean_object* x_204; lean_object* x_205; lean_object* x_206; lean_object* x_207; lean_object* x_208; lean_object* x_209; 
x_203 = lean_st_ref_get(x_7);
x_204 = lean_ctor_get(x_203, 0);
lean_inc_ref(x_204);
lean_dec(x_203);
x_205 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_206 = l_Lean_Syntax_getKind(x_1);
x_207 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_205, x_204, x_206);
x_208 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_209 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_207, x_208, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_209) == 0)
{
uint8_t x_210; 
x_210 = !lean_is_exclusive(x_209);
if (x_210 == 0)
{
lean_object* x_211; uint8_t x_212; 
x_211 = lean_ctor_get(x_209, 0);
x_212 = !lean_is_exclusive(x_211);
if (x_212 == 0)
{
lean_object* x_213; lean_object* x_214; 
x_213 = lean_ctor_get(x_211, 0);
x_214 = lean_ctor_get(x_211, 1);
lean_dec(x_214);
if (lean_obj_tag(x_213) == 0)
{
lean_object* x_215; lean_object* x_216; lean_object* x_217; lean_object* x_218; lean_object* x_219; lean_object* x_220; lean_object* x_221; lean_object* x_222; lean_object* x_223; lean_object* x_224; lean_object* x_225; lean_object* x_226; lean_object* x_227; 
lean_free_object(x_209);
x_215 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_216 = l_Lean_MessageData_ofName(x_206);
lean_inc_ref(x_216);
lean_ctor_set_tag(x_211, 7);
lean_ctor_set(x_211, 1, x_216);
lean_ctor_set(x_211, 0, x_215);
x_217 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_218 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_218, 0, x_211);
lean_ctor_set(x_218, 1, x_217);
x_219 = l_Lean_MessageData_ofSyntax(x_1);
x_220 = l_Lean_indentD(x_219);
x_221 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_221, 0, x_218);
lean_ctor_set(x_221, 1, x_220);
x_222 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_223 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_223, 0, x_221);
lean_ctor_set(x_223, 1, x_222);
x_224 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_224, 0, x_223);
lean_ctor_set(x_224, 1, x_216);
x_225 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_226, 0, x_224);
lean_ctor_set(x_226, 1, x_225);
x_227 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_226, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_227;
}
else
{
lean_object* x_228; 
lean_free_object(x_211);
lean_dec(x_206);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_228 = lean_ctor_get(x_213, 0);
lean_inc(x_228);
lean_dec_ref(x_213);
lean_ctor_set(x_209, 0, x_228);
return x_209;
}
}
else
{
lean_object* x_229; 
x_229 = lean_ctor_get(x_211, 0);
lean_inc(x_229);
lean_dec(x_211);
if (lean_obj_tag(x_229) == 0)
{
lean_object* x_230; lean_object* x_231; lean_object* x_232; lean_object* x_233; lean_object* x_234; lean_object* x_235; lean_object* x_236; lean_object* x_237; lean_object* x_238; lean_object* x_239; lean_object* x_240; lean_object* x_241; lean_object* x_242; lean_object* x_243; 
lean_free_object(x_209);
x_230 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_231 = l_Lean_MessageData_ofName(x_206);
lean_inc_ref(x_231);
x_232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_232, 0, x_230);
lean_ctor_set(x_232, 1, x_231);
x_233 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_234, 0, x_232);
lean_ctor_set(x_234, 1, x_233);
x_235 = l_Lean_MessageData_ofSyntax(x_1);
x_236 = l_Lean_indentD(x_235);
x_237 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_237, 0, x_234);
lean_ctor_set(x_237, 1, x_236);
x_238 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_239, 0, x_237);
lean_ctor_set(x_239, 1, x_238);
x_240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_240, 0, x_239);
lean_ctor_set(x_240, 1, x_231);
x_241 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_242, 0, x_240);
lean_ctor_set(x_242, 1, x_241);
x_243 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_242, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_243;
}
else
{
lean_object* x_244; 
lean_dec(x_206);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_244 = lean_ctor_get(x_229, 0);
lean_inc(x_244);
lean_dec_ref(x_229);
lean_ctor_set(x_209, 0, x_244);
return x_209;
}
}
}
else
{
lean_object* x_245; lean_object* x_246; lean_object* x_247; 
x_245 = lean_ctor_get(x_209, 0);
lean_inc(x_245);
lean_dec(x_209);
x_246 = lean_ctor_get(x_245, 0);
lean_inc(x_246);
if (lean_is_exclusive(x_245)) {
 lean_ctor_release(x_245, 0);
 lean_ctor_release(x_245, 1);
 x_247 = x_245;
} else {
 lean_dec_ref(x_245);
 x_247 = lean_box(0);
}
if (lean_obj_tag(x_246) == 0)
{
lean_object* x_248; lean_object* x_249; lean_object* x_250; lean_object* x_251; lean_object* x_252; lean_object* x_253; lean_object* x_254; lean_object* x_255; lean_object* x_256; lean_object* x_257; lean_object* x_258; lean_object* x_259; lean_object* x_260; lean_object* x_261; 
x_248 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_249 = l_Lean_MessageData_ofName(x_206);
lean_inc_ref(x_249);
if (lean_is_scalar(x_247)) {
 x_250 = lean_alloc_ctor(7, 2, 0);
} else {
 x_250 = x_247;
 lean_ctor_set_tag(x_250, 7);
}
lean_ctor_set(x_250, 0, x_248);
lean_ctor_set(x_250, 1, x_249);
x_251 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_252 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_252, 0, x_250);
lean_ctor_set(x_252, 1, x_251);
x_253 = l_Lean_MessageData_ofSyntax(x_1);
x_254 = l_Lean_indentD(x_253);
x_255 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_255, 0, x_252);
lean_ctor_set(x_255, 1, x_254);
x_256 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_257 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_257, 0, x_255);
lean_ctor_set(x_257, 1, x_256);
x_258 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_258, 0, x_257);
lean_ctor_set(x_258, 1, x_249);
x_259 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_260 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_260, 0, x_258);
lean_ctor_set(x_260, 1, x_259);
x_261 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_260, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_261;
}
else
{
lean_object* x_262; lean_object* x_263; 
lean_dec(x_247);
lean_dec(x_206);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_262 = lean_ctor_get(x_246, 0);
lean_inc(x_262);
lean_dec_ref(x_246);
x_263 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_263, 0, x_262);
return x_263;
}
}
}
else
{
uint8_t x_264; 
lean_dec(x_206);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_264 = !lean_is_exclusive(x_209);
if (x_264 == 0)
{
return x_209;
}
else
{
lean_object* x_265; lean_object* x_266; 
x_265 = lean_ctor_get(x_209, 0);
lean_inc(x_265);
lean_dec(x_209);
x_266 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_266, 0, x_265);
return x_266;
}
}
}
else
{
lean_object* x_267; lean_object* x_268; lean_object* x_269; lean_object* x_270; lean_object* x_280; lean_object* x_281; lean_object* x_282; 
x_267 = lean_unsigned_to_nat(1u);
x_268 = lean_unsigned_to_nat(5u);
x_269 = l_Lean_Syntax_getArg(x_1, x_268);
x_280 = lean_unsigned_to_nat(6u);
x_281 = l_Lean_Syntax_getArg(x_1, x_280);
lean_dec(x_1);
x_282 = l_Lean_Syntax_getOptional_x3f(x_281);
lean_dec(x_281);
if (lean_obj_tag(x_282) == 0)
{
lean_object* x_283; 
x_283 = lean_box(0);
x_270 = x_283;
goto block_279;
}
else
{
uint8_t x_284; 
x_284 = !lean_is_exclusive(x_282);
if (x_284 == 0)
{
x_270 = x_282;
goto block_279;
}
else
{
lean_object* x_285; lean_object* x_286; 
x_285 = lean_ctor_get(x_282, 0);
lean_inc(x_285);
lean_dec(x_282);
x_286 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_286, 0, x_285);
x_270 = x_286;
goto block_279;
}
}
block_279:
{
lean_object* x_271; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_271 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_269, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_271) == 0)
{
if (lean_obj_tag(x_270) == 0)
{
lean_object* x_272; lean_object* x_273; lean_object* x_274; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_272 = lean_ctor_get(x_271, 0);
lean_inc(x_272);
lean_dec_ref(x_271);
x_273 = l_Lean_NameSet_empty;
x_274 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_274, 0, x_267);
lean_ctor_set(x_274, 1, x_273);
lean_ctor_set_uint8(x_274, sizeof(void*)*2, x_200);
lean_ctor_set_uint8(x_274, sizeof(void*)*2 + 1, x_200);
lean_ctor_set_uint8(x_274, sizeof(void*)*2 + 2, x_200);
x_46 = x_272;
x_47 = x_274;
x_48 = lean_box(0);
goto block_51;
}
else
{
lean_object* x_275; lean_object* x_276; lean_object* x_277; 
x_275 = lean_ctor_get(x_271, 0);
lean_inc(x_275);
lean_dec_ref(x_271);
x_276 = lean_ctor_get(x_270, 0);
lean_inc(x_276);
lean_dec_ref(x_270);
x_277 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_276, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_277) == 0)
{
lean_object* x_278; 
x_278 = lean_ctor_get(x_277, 0);
lean_inc(x_278);
lean_dec_ref(x_277);
x_46 = x_275;
x_47 = x_278;
x_48 = lean_box(0);
goto block_51;
}
else
{
lean_dec(x_275);
return x_277;
}
}
}
else
{
lean_dec(x_270);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_271;
}
}
}
}
else
{
lean_object* x_287; lean_object* x_288; lean_object* x_289; lean_object* x_290; lean_object* x_300; lean_object* x_301; lean_object* x_302; 
x_287 = lean_unsigned_to_nat(1u);
x_288 = lean_unsigned_to_nat(5u);
x_289 = l_Lean_Syntax_getArg(x_1, x_288);
x_300 = lean_unsigned_to_nat(6u);
x_301 = l_Lean_Syntax_getArg(x_1, x_300);
lean_dec(x_1);
x_302 = l_Lean_Syntax_getOptional_x3f(x_301);
lean_dec(x_301);
if (lean_obj_tag(x_302) == 0)
{
lean_object* x_303; 
x_303 = lean_box(0);
x_290 = x_303;
goto block_299;
}
else
{
uint8_t x_304; 
x_304 = !lean_is_exclusive(x_302);
if (x_304 == 0)
{
x_290 = x_302;
goto block_299;
}
else
{
lean_object* x_305; lean_object* x_306; 
x_305 = lean_ctor_get(x_302, 0);
lean_inc(x_305);
lean_dec(x_302);
x_306 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_306, 0, x_305);
x_290 = x_306;
goto block_299;
}
}
block_299:
{
lean_object* x_291; 
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_291 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_289, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_291) == 0)
{
if (lean_obj_tag(x_290) == 0)
{
lean_object* x_292; lean_object* x_293; lean_object* x_294; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_292 = lean_ctor_get(x_291, 0);
lean_inc(x_292);
lean_dec_ref(x_291);
x_293 = l_Lean_NameSet_empty;
x_294 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_294, 0, x_287);
lean_ctor_set(x_294, 1, x_293);
lean_ctor_set_uint8(x_294, sizeof(void*)*2, x_198);
lean_ctor_set_uint8(x_294, sizeof(void*)*2 + 1, x_198);
lean_ctor_set_uint8(x_294, sizeof(void*)*2 + 2, x_198);
x_40 = x_292;
x_41 = x_294;
x_42 = lean_box(0);
goto block_45;
}
else
{
lean_object* x_295; lean_object* x_296; lean_object* x_297; 
x_295 = lean_ctor_get(x_291, 0);
lean_inc(x_295);
lean_dec_ref(x_291);
x_296 = lean_ctor_get(x_290, 0);
lean_inc(x_296);
lean_dec_ref(x_290);
x_297 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_296, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_297) == 0)
{
lean_object* x_298; 
x_298 = lean_ctor_get(x_297, 0);
lean_inc(x_298);
lean_dec_ref(x_297);
x_40 = x_295;
x_41 = x_298;
x_42 = lean_box(0);
goto block_45;
}
else
{
lean_dec(x_295);
return x_297;
}
}
}
else
{
lean_dec(x_290);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_291;
}
}
}
}
else
{
lean_object* x_307; lean_object* x_308; lean_object* x_309; lean_object* x_310; lean_object* x_311; lean_object* x_312; lean_object* x_313; lean_object* x_314; lean_object* x_315; lean_object* x_595; uint8_t x_596; 
x_307 = lean_unsigned_to_nat(0u);
x_308 = lean_unsigned_to_nat(1u);
x_595 = l_Lean_Syntax_getArg(x_1, x_308);
x_596 = l_Lean_Syntax_isNone(x_595);
if (x_596 == 0)
{
lean_object* x_597; uint8_t x_598; 
x_597 = lean_unsigned_to_nat(5u);
x_598 = l_Lean_Syntax_matchesNull(x_595, x_597);
if (x_598 == 0)
{
lean_object* x_599; lean_object* x_600; lean_object* x_601; lean_object* x_602; lean_object* x_603; lean_object* x_604; lean_object* x_605; 
x_599 = lean_st_ref_get(x_7);
x_600 = lean_ctor_get(x_599, 0);
lean_inc_ref(x_600);
lean_dec(x_599);
x_601 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_602 = l_Lean_Syntax_getKind(x_1);
x_603 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_601, x_600, x_602);
x_604 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_605 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_603, x_604, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_605) == 0)
{
uint8_t x_606; 
x_606 = !lean_is_exclusive(x_605);
if (x_606 == 0)
{
lean_object* x_607; uint8_t x_608; 
x_607 = lean_ctor_get(x_605, 0);
x_608 = !lean_is_exclusive(x_607);
if (x_608 == 0)
{
lean_object* x_609; lean_object* x_610; 
x_609 = lean_ctor_get(x_607, 0);
x_610 = lean_ctor_get(x_607, 1);
lean_dec(x_610);
if (lean_obj_tag(x_609) == 0)
{
lean_object* x_611; lean_object* x_612; lean_object* x_613; lean_object* x_614; lean_object* x_615; lean_object* x_616; lean_object* x_617; lean_object* x_618; lean_object* x_619; lean_object* x_620; lean_object* x_621; lean_object* x_622; lean_object* x_623; 
lean_free_object(x_605);
x_611 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_612 = l_Lean_MessageData_ofName(x_602);
lean_inc_ref(x_612);
lean_ctor_set_tag(x_607, 7);
lean_ctor_set(x_607, 1, x_612);
lean_ctor_set(x_607, 0, x_611);
x_613 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_614 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_614, 0, x_607);
lean_ctor_set(x_614, 1, x_613);
x_615 = l_Lean_MessageData_ofSyntax(x_1);
x_616 = l_Lean_indentD(x_615);
x_617 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_617, 0, x_614);
lean_ctor_set(x_617, 1, x_616);
x_618 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_619 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_619, 0, x_617);
lean_ctor_set(x_619, 1, x_618);
x_620 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_620, 0, x_619);
lean_ctor_set(x_620, 1, x_612);
x_621 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_622 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_622, 0, x_620);
lean_ctor_set(x_622, 1, x_621);
x_623 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_622, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_623;
}
else
{
lean_object* x_624; 
lean_free_object(x_607);
lean_dec(x_602);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_624 = lean_ctor_get(x_609, 0);
lean_inc(x_624);
lean_dec_ref(x_609);
lean_ctor_set(x_605, 0, x_624);
return x_605;
}
}
else
{
lean_object* x_625; 
x_625 = lean_ctor_get(x_607, 0);
lean_inc(x_625);
lean_dec(x_607);
if (lean_obj_tag(x_625) == 0)
{
lean_object* x_626; lean_object* x_627; lean_object* x_628; lean_object* x_629; lean_object* x_630; lean_object* x_631; lean_object* x_632; lean_object* x_633; lean_object* x_634; lean_object* x_635; lean_object* x_636; lean_object* x_637; lean_object* x_638; lean_object* x_639; 
lean_free_object(x_605);
x_626 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_627 = l_Lean_MessageData_ofName(x_602);
lean_inc_ref(x_627);
x_628 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_628, 0, x_626);
lean_ctor_set(x_628, 1, x_627);
x_629 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_630 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_630, 0, x_628);
lean_ctor_set(x_630, 1, x_629);
x_631 = l_Lean_MessageData_ofSyntax(x_1);
x_632 = l_Lean_indentD(x_631);
x_633 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_633, 0, x_630);
lean_ctor_set(x_633, 1, x_632);
x_634 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_635 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_635, 0, x_633);
lean_ctor_set(x_635, 1, x_634);
x_636 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_636, 0, x_635);
lean_ctor_set(x_636, 1, x_627);
x_637 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_638 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_638, 0, x_636);
lean_ctor_set(x_638, 1, x_637);
x_639 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_638, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_639;
}
else
{
lean_object* x_640; 
lean_dec(x_602);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_640 = lean_ctor_get(x_625, 0);
lean_inc(x_640);
lean_dec_ref(x_625);
lean_ctor_set(x_605, 0, x_640);
return x_605;
}
}
}
else
{
lean_object* x_641; lean_object* x_642; lean_object* x_643; 
x_641 = lean_ctor_get(x_605, 0);
lean_inc(x_641);
lean_dec(x_605);
x_642 = lean_ctor_get(x_641, 0);
lean_inc(x_642);
if (lean_is_exclusive(x_641)) {
 lean_ctor_release(x_641, 0);
 lean_ctor_release(x_641, 1);
 x_643 = x_641;
} else {
 lean_dec_ref(x_641);
 x_643 = lean_box(0);
}
if (lean_obj_tag(x_642) == 0)
{
lean_object* x_644; lean_object* x_645; lean_object* x_646; lean_object* x_647; lean_object* x_648; lean_object* x_649; lean_object* x_650; lean_object* x_651; lean_object* x_652; lean_object* x_653; lean_object* x_654; lean_object* x_655; lean_object* x_656; lean_object* x_657; 
x_644 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_645 = l_Lean_MessageData_ofName(x_602);
lean_inc_ref(x_645);
if (lean_is_scalar(x_643)) {
 x_646 = lean_alloc_ctor(7, 2, 0);
} else {
 x_646 = x_643;
 lean_ctor_set_tag(x_646, 7);
}
lean_ctor_set(x_646, 0, x_644);
lean_ctor_set(x_646, 1, x_645);
x_647 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_648 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_648, 0, x_646);
lean_ctor_set(x_648, 1, x_647);
x_649 = l_Lean_MessageData_ofSyntax(x_1);
x_650 = l_Lean_indentD(x_649);
x_651 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_651, 0, x_648);
lean_ctor_set(x_651, 1, x_650);
x_652 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_653 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_653, 0, x_651);
lean_ctor_set(x_653, 1, x_652);
x_654 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_654, 0, x_653);
lean_ctor_set(x_654, 1, x_645);
x_655 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_656 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_656, 0, x_654);
lean_ctor_set(x_656, 1, x_655);
x_657 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_656, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_657;
}
else
{
lean_object* x_658; lean_object* x_659; 
lean_dec(x_643);
lean_dec(x_602);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_658 = lean_ctor_get(x_642, 0);
lean_inc(x_658);
lean_dec_ref(x_642);
x_659 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_659, 0, x_658);
return x_659;
}
}
}
else
{
uint8_t x_660; 
lean_dec(x_602);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_660 = !lean_is_exclusive(x_605);
if (x_660 == 0)
{
return x_605;
}
else
{
lean_object* x_661; lean_object* x_662; 
x_661 = lean_ctor_get(x_605, 0);
lean_inc(x_661);
lean_dec(x_605);
x_662 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_662, 0, x_661);
return x_662;
}
}
}
else
{
x_309 = x_2;
x_310 = x_3;
x_311 = x_4;
x_312 = x_5;
x_313 = x_6;
x_314 = x_7;
x_315 = lean_box(0);
goto block_594;
}
}
else
{
lean_dec(x_595);
x_309 = x_2;
x_310 = x_3;
x_311 = x_4;
x_312 = x_5;
x_313 = x_6;
x_314 = x_7;
x_315 = lean_box(0);
goto block_594;
}
block_594:
{
lean_object* x_316; lean_object* x_317; lean_object* x_318; uint8_t x_319; 
x_316 = lean_unsigned_to_nat(4u);
x_317 = l_Lean_Syntax_getArg(x_1, x_316);
x_318 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__57));
lean_inc(x_317);
x_319 = l_Lean_Syntax_isOfKind(x_317, x_318);
if (x_319 == 0)
{
lean_object* x_320; lean_object* x_321; lean_object* x_322; lean_object* x_323; lean_object* x_324; lean_object* x_325; lean_object* x_326; 
lean_dec(x_317);
x_320 = lean_st_ref_get(x_314);
x_321 = lean_ctor_get(x_320, 0);
lean_inc_ref(x_321);
lean_dec(x_320);
x_322 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_323 = l_Lean_Syntax_getKind(x_1);
x_324 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_322, x_321, x_323);
x_325 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc(x_312);
lean_inc_ref(x_311);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_1);
x_326 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_324, x_325, x_309, x_310, x_311, x_312, x_313, x_314);
if (lean_obj_tag(x_326) == 0)
{
uint8_t x_327; 
x_327 = !lean_is_exclusive(x_326);
if (x_327 == 0)
{
lean_object* x_328; uint8_t x_329; 
x_328 = lean_ctor_get(x_326, 0);
x_329 = !lean_is_exclusive(x_328);
if (x_329 == 0)
{
lean_object* x_330; lean_object* x_331; 
x_330 = lean_ctor_get(x_328, 0);
x_331 = lean_ctor_get(x_328, 1);
lean_dec(x_331);
if (lean_obj_tag(x_330) == 0)
{
lean_object* x_332; lean_object* x_333; lean_object* x_334; lean_object* x_335; lean_object* x_336; lean_object* x_337; lean_object* x_338; lean_object* x_339; lean_object* x_340; lean_object* x_341; lean_object* x_342; lean_object* x_343; lean_object* x_344; 
lean_free_object(x_326);
x_332 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_333 = l_Lean_MessageData_ofName(x_323);
lean_inc_ref(x_333);
lean_ctor_set_tag(x_328, 7);
lean_ctor_set(x_328, 1, x_333);
lean_ctor_set(x_328, 0, x_332);
x_334 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_335 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_335, 0, x_328);
lean_ctor_set(x_335, 1, x_334);
x_336 = l_Lean_MessageData_ofSyntax(x_1);
x_337 = l_Lean_indentD(x_336);
x_338 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_338, 0, x_335);
lean_ctor_set(x_338, 1, x_337);
x_339 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_340 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_340, 0, x_338);
lean_ctor_set(x_340, 1, x_339);
x_341 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_341, 0, x_340);
lean_ctor_set(x_341, 1, x_333);
x_342 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_343 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_343, 0, x_341);
lean_ctor_set(x_343, 1, x_342);
x_344 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_343, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_344;
}
else
{
lean_object* x_345; 
lean_free_object(x_328);
lean_dec(x_323);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_345 = lean_ctor_get(x_330, 0);
lean_inc(x_345);
lean_dec_ref(x_330);
lean_ctor_set(x_326, 0, x_345);
return x_326;
}
}
else
{
lean_object* x_346; 
x_346 = lean_ctor_get(x_328, 0);
lean_inc(x_346);
lean_dec(x_328);
if (lean_obj_tag(x_346) == 0)
{
lean_object* x_347; lean_object* x_348; lean_object* x_349; lean_object* x_350; lean_object* x_351; lean_object* x_352; lean_object* x_353; lean_object* x_354; lean_object* x_355; lean_object* x_356; lean_object* x_357; lean_object* x_358; lean_object* x_359; lean_object* x_360; 
lean_free_object(x_326);
x_347 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_348 = l_Lean_MessageData_ofName(x_323);
lean_inc_ref(x_348);
x_349 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_349, 0, x_347);
lean_ctor_set(x_349, 1, x_348);
x_350 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_351 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_351, 0, x_349);
lean_ctor_set(x_351, 1, x_350);
x_352 = l_Lean_MessageData_ofSyntax(x_1);
x_353 = l_Lean_indentD(x_352);
x_354 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_354, 0, x_351);
lean_ctor_set(x_354, 1, x_353);
x_355 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_356 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_356, 0, x_354);
lean_ctor_set(x_356, 1, x_355);
x_357 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_357, 0, x_356);
lean_ctor_set(x_357, 1, x_348);
x_358 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_359 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_359, 0, x_357);
lean_ctor_set(x_359, 1, x_358);
x_360 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_359, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_360;
}
else
{
lean_object* x_361; 
lean_dec(x_323);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_361 = lean_ctor_get(x_346, 0);
lean_inc(x_361);
lean_dec_ref(x_346);
lean_ctor_set(x_326, 0, x_361);
return x_326;
}
}
}
else
{
lean_object* x_362; lean_object* x_363; lean_object* x_364; 
x_362 = lean_ctor_get(x_326, 0);
lean_inc(x_362);
lean_dec(x_326);
x_363 = lean_ctor_get(x_362, 0);
lean_inc(x_363);
if (lean_is_exclusive(x_362)) {
 lean_ctor_release(x_362, 0);
 lean_ctor_release(x_362, 1);
 x_364 = x_362;
} else {
 lean_dec_ref(x_362);
 x_364 = lean_box(0);
}
if (lean_obj_tag(x_363) == 0)
{
lean_object* x_365; lean_object* x_366; lean_object* x_367; lean_object* x_368; lean_object* x_369; lean_object* x_370; lean_object* x_371; lean_object* x_372; lean_object* x_373; lean_object* x_374; lean_object* x_375; lean_object* x_376; lean_object* x_377; lean_object* x_378; 
x_365 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_366 = l_Lean_MessageData_ofName(x_323);
lean_inc_ref(x_366);
if (lean_is_scalar(x_364)) {
 x_367 = lean_alloc_ctor(7, 2, 0);
} else {
 x_367 = x_364;
 lean_ctor_set_tag(x_367, 7);
}
lean_ctor_set(x_367, 0, x_365);
lean_ctor_set(x_367, 1, x_366);
x_368 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_369 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_369, 0, x_367);
lean_ctor_set(x_369, 1, x_368);
x_370 = l_Lean_MessageData_ofSyntax(x_1);
x_371 = l_Lean_indentD(x_370);
x_372 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_372, 0, x_369);
lean_ctor_set(x_372, 1, x_371);
x_373 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_374 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_374, 0, x_372);
lean_ctor_set(x_374, 1, x_373);
x_375 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_375, 0, x_374);
lean_ctor_set(x_375, 1, x_366);
x_376 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_377 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_377, 0, x_375);
lean_ctor_set(x_377, 1, x_376);
x_378 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_377, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_378;
}
else
{
lean_object* x_379; lean_object* x_380; 
lean_dec(x_364);
lean_dec(x_323);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_379 = lean_ctor_get(x_363, 0);
lean_inc(x_379);
lean_dec_ref(x_363);
x_380 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_380, 0, x_379);
return x_380;
}
}
}
else
{
uint8_t x_381; 
lean_dec(x_323);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_381 = !lean_is_exclusive(x_326);
if (x_381 == 0)
{
return x_326;
}
else
{
lean_object* x_382; lean_object* x_383; 
x_382 = lean_ctor_get(x_326, 0);
lean_inc(x_382);
lean_dec(x_326);
x_383 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_383, 0, x_382);
return x_383;
}
}
}
else
{
lean_object* x_384; lean_object* x_385; size_t x_386; size_t x_387; lean_object* x_388; 
x_384 = l_Lean_Syntax_getArg(x_317, x_307);
x_385 = l_Lean_Syntax_getArgs(x_384);
lean_dec(x_384);
x_386 = lean_array_size(x_385);
x_387 = 0;
x_388 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__4(x_386, x_387, x_385);
if (lean_obj_tag(x_388) == 0)
{
lean_object* x_389; lean_object* x_390; lean_object* x_391; lean_object* x_392; lean_object* x_393; lean_object* x_394; lean_object* x_395; 
lean_dec(x_317);
x_389 = lean_st_ref_get(x_314);
x_390 = lean_ctor_get(x_389, 0);
lean_inc_ref(x_390);
lean_dec(x_389);
x_391 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_392 = l_Lean_Syntax_getKind(x_1);
x_393 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_391, x_390, x_392);
x_394 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc(x_312);
lean_inc_ref(x_311);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_1);
x_395 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_393, x_394, x_309, x_310, x_311, x_312, x_313, x_314);
if (lean_obj_tag(x_395) == 0)
{
uint8_t x_396; 
x_396 = !lean_is_exclusive(x_395);
if (x_396 == 0)
{
lean_object* x_397; uint8_t x_398; 
x_397 = lean_ctor_get(x_395, 0);
x_398 = !lean_is_exclusive(x_397);
if (x_398 == 0)
{
lean_object* x_399; lean_object* x_400; 
x_399 = lean_ctor_get(x_397, 0);
x_400 = lean_ctor_get(x_397, 1);
lean_dec(x_400);
if (lean_obj_tag(x_399) == 0)
{
lean_object* x_401; lean_object* x_402; lean_object* x_403; lean_object* x_404; lean_object* x_405; lean_object* x_406; lean_object* x_407; lean_object* x_408; lean_object* x_409; lean_object* x_410; lean_object* x_411; lean_object* x_412; lean_object* x_413; 
lean_free_object(x_395);
x_401 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_402 = l_Lean_MessageData_ofName(x_392);
lean_inc_ref(x_402);
lean_ctor_set_tag(x_397, 7);
lean_ctor_set(x_397, 1, x_402);
lean_ctor_set(x_397, 0, x_401);
x_403 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_404 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_404, 0, x_397);
lean_ctor_set(x_404, 1, x_403);
x_405 = l_Lean_MessageData_ofSyntax(x_1);
x_406 = l_Lean_indentD(x_405);
x_407 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_407, 0, x_404);
lean_ctor_set(x_407, 1, x_406);
x_408 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_409 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_409, 0, x_407);
lean_ctor_set(x_409, 1, x_408);
x_410 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_410, 0, x_409);
lean_ctor_set(x_410, 1, x_402);
x_411 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_412 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_412, 0, x_410);
lean_ctor_set(x_412, 1, x_411);
x_413 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_412, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_413;
}
else
{
lean_object* x_414; 
lean_free_object(x_397);
lean_dec(x_392);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_414 = lean_ctor_get(x_399, 0);
lean_inc(x_414);
lean_dec_ref(x_399);
lean_ctor_set(x_395, 0, x_414);
return x_395;
}
}
else
{
lean_object* x_415; 
x_415 = lean_ctor_get(x_397, 0);
lean_inc(x_415);
lean_dec(x_397);
if (lean_obj_tag(x_415) == 0)
{
lean_object* x_416; lean_object* x_417; lean_object* x_418; lean_object* x_419; lean_object* x_420; lean_object* x_421; lean_object* x_422; lean_object* x_423; lean_object* x_424; lean_object* x_425; lean_object* x_426; lean_object* x_427; lean_object* x_428; lean_object* x_429; 
lean_free_object(x_395);
x_416 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_417 = l_Lean_MessageData_ofName(x_392);
lean_inc_ref(x_417);
x_418 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_418, 0, x_416);
lean_ctor_set(x_418, 1, x_417);
x_419 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_420 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_420, 0, x_418);
lean_ctor_set(x_420, 1, x_419);
x_421 = l_Lean_MessageData_ofSyntax(x_1);
x_422 = l_Lean_indentD(x_421);
x_423 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_423, 0, x_420);
lean_ctor_set(x_423, 1, x_422);
x_424 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_425 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_425, 0, x_423);
lean_ctor_set(x_425, 1, x_424);
x_426 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_426, 0, x_425);
lean_ctor_set(x_426, 1, x_417);
x_427 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_428 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_428, 0, x_426);
lean_ctor_set(x_428, 1, x_427);
x_429 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_428, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_429;
}
else
{
lean_object* x_430; 
lean_dec(x_392);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_430 = lean_ctor_get(x_415, 0);
lean_inc(x_430);
lean_dec_ref(x_415);
lean_ctor_set(x_395, 0, x_430);
return x_395;
}
}
}
else
{
lean_object* x_431; lean_object* x_432; lean_object* x_433; 
x_431 = lean_ctor_get(x_395, 0);
lean_inc(x_431);
lean_dec(x_395);
x_432 = lean_ctor_get(x_431, 0);
lean_inc(x_432);
if (lean_is_exclusive(x_431)) {
 lean_ctor_release(x_431, 0);
 lean_ctor_release(x_431, 1);
 x_433 = x_431;
} else {
 lean_dec_ref(x_431);
 x_433 = lean_box(0);
}
if (lean_obj_tag(x_432) == 0)
{
lean_object* x_434; lean_object* x_435; lean_object* x_436; lean_object* x_437; lean_object* x_438; lean_object* x_439; lean_object* x_440; lean_object* x_441; lean_object* x_442; lean_object* x_443; lean_object* x_444; lean_object* x_445; lean_object* x_446; lean_object* x_447; 
x_434 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_435 = l_Lean_MessageData_ofName(x_392);
lean_inc_ref(x_435);
if (lean_is_scalar(x_433)) {
 x_436 = lean_alloc_ctor(7, 2, 0);
} else {
 x_436 = x_433;
 lean_ctor_set_tag(x_436, 7);
}
lean_ctor_set(x_436, 0, x_434);
lean_ctor_set(x_436, 1, x_435);
x_437 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_438 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_438, 0, x_436);
lean_ctor_set(x_438, 1, x_437);
x_439 = l_Lean_MessageData_ofSyntax(x_1);
x_440 = l_Lean_indentD(x_439);
x_441 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_441, 0, x_438);
lean_ctor_set(x_441, 1, x_440);
x_442 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_443 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_443, 0, x_441);
lean_ctor_set(x_443, 1, x_442);
x_444 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_444, 0, x_443);
lean_ctor_set(x_444, 1, x_435);
x_445 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_446 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_446, 0, x_444);
lean_ctor_set(x_446, 1, x_445);
x_447 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_446, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_447;
}
else
{
lean_object* x_448; lean_object* x_449; 
lean_dec(x_433);
lean_dec(x_392);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_448 = lean_ctor_get(x_432, 0);
lean_inc(x_448);
lean_dec_ref(x_432);
x_449 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_449, 0, x_448);
return x_449;
}
}
}
else
{
uint8_t x_450; 
lean_dec(x_392);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_450 = !lean_is_exclusive(x_395);
if (x_450 == 0)
{
return x_395;
}
else
{
lean_object* x_451; lean_object* x_452; 
x_451 = lean_ctor_get(x_395, 0);
lean_inc(x_451);
lean_dec(x_395);
x_452 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_452, 0, x_451);
return x_452;
}
}
}
else
{
lean_object* x_453; lean_object* x_454; lean_object* x_455; uint8_t x_456; 
x_453 = lean_ctor_get(x_388, 0);
lean_inc(x_453);
lean_dec_ref(x_388);
x_454 = l_Lean_Syntax_getArg(x_317, x_308);
lean_dec(x_317);
x_455 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__59));
lean_inc(x_454);
x_456 = l_Lean_Syntax_isOfKind(x_454, x_455);
if (x_456 == 0)
{
lean_object* x_457; lean_object* x_458; lean_object* x_459; lean_object* x_460; lean_object* x_461; lean_object* x_462; lean_object* x_463; 
lean_dec(x_454);
lean_dec(x_453);
x_457 = lean_st_ref_get(x_314);
x_458 = lean_ctor_get(x_457, 0);
lean_inc_ref(x_458);
lean_dec(x_457);
x_459 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_460 = l_Lean_Syntax_getKind(x_1);
x_461 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_459, x_458, x_460);
x_462 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc(x_312);
lean_inc_ref(x_311);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_1);
x_463 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_461, x_462, x_309, x_310, x_311, x_312, x_313, x_314);
if (lean_obj_tag(x_463) == 0)
{
uint8_t x_464; 
x_464 = !lean_is_exclusive(x_463);
if (x_464 == 0)
{
lean_object* x_465; uint8_t x_466; 
x_465 = lean_ctor_get(x_463, 0);
x_466 = !lean_is_exclusive(x_465);
if (x_466 == 0)
{
lean_object* x_467; lean_object* x_468; 
x_467 = lean_ctor_get(x_465, 0);
x_468 = lean_ctor_get(x_465, 1);
lean_dec(x_468);
if (lean_obj_tag(x_467) == 0)
{
lean_object* x_469; lean_object* x_470; lean_object* x_471; lean_object* x_472; lean_object* x_473; lean_object* x_474; lean_object* x_475; lean_object* x_476; lean_object* x_477; lean_object* x_478; lean_object* x_479; lean_object* x_480; lean_object* x_481; 
lean_free_object(x_463);
x_469 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_470 = l_Lean_MessageData_ofName(x_460);
lean_inc_ref(x_470);
lean_ctor_set_tag(x_465, 7);
lean_ctor_set(x_465, 1, x_470);
lean_ctor_set(x_465, 0, x_469);
x_471 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_472 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_472, 0, x_465);
lean_ctor_set(x_472, 1, x_471);
x_473 = l_Lean_MessageData_ofSyntax(x_1);
x_474 = l_Lean_indentD(x_473);
x_475 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_475, 0, x_472);
lean_ctor_set(x_475, 1, x_474);
x_476 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_477 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_477, 0, x_475);
lean_ctor_set(x_477, 1, x_476);
x_478 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_478, 0, x_477);
lean_ctor_set(x_478, 1, x_470);
x_479 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_480 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_480, 0, x_478);
lean_ctor_set(x_480, 1, x_479);
x_481 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_480, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_481;
}
else
{
lean_object* x_482; 
lean_free_object(x_465);
lean_dec(x_460);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_482 = lean_ctor_get(x_467, 0);
lean_inc(x_482);
lean_dec_ref(x_467);
lean_ctor_set(x_463, 0, x_482);
return x_463;
}
}
else
{
lean_object* x_483; 
x_483 = lean_ctor_get(x_465, 0);
lean_inc(x_483);
lean_dec(x_465);
if (lean_obj_tag(x_483) == 0)
{
lean_object* x_484; lean_object* x_485; lean_object* x_486; lean_object* x_487; lean_object* x_488; lean_object* x_489; lean_object* x_490; lean_object* x_491; lean_object* x_492; lean_object* x_493; lean_object* x_494; lean_object* x_495; lean_object* x_496; lean_object* x_497; 
lean_free_object(x_463);
x_484 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_485 = l_Lean_MessageData_ofName(x_460);
lean_inc_ref(x_485);
x_486 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_486, 0, x_484);
lean_ctor_set(x_486, 1, x_485);
x_487 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_488 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_488, 0, x_486);
lean_ctor_set(x_488, 1, x_487);
x_489 = l_Lean_MessageData_ofSyntax(x_1);
x_490 = l_Lean_indentD(x_489);
x_491 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_491, 0, x_488);
lean_ctor_set(x_491, 1, x_490);
x_492 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_493 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_493, 0, x_491);
lean_ctor_set(x_493, 1, x_492);
x_494 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_494, 0, x_493);
lean_ctor_set(x_494, 1, x_485);
x_495 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_496 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_496, 0, x_494);
lean_ctor_set(x_496, 1, x_495);
x_497 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_496, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_497;
}
else
{
lean_object* x_498; 
lean_dec(x_460);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_498 = lean_ctor_get(x_483, 0);
lean_inc(x_498);
lean_dec_ref(x_483);
lean_ctor_set(x_463, 0, x_498);
return x_463;
}
}
}
else
{
lean_object* x_499; lean_object* x_500; lean_object* x_501; 
x_499 = lean_ctor_get(x_463, 0);
lean_inc(x_499);
lean_dec(x_463);
x_500 = lean_ctor_get(x_499, 0);
lean_inc(x_500);
if (lean_is_exclusive(x_499)) {
 lean_ctor_release(x_499, 0);
 lean_ctor_release(x_499, 1);
 x_501 = x_499;
} else {
 lean_dec_ref(x_499);
 x_501 = lean_box(0);
}
if (lean_obj_tag(x_500) == 0)
{
lean_object* x_502; lean_object* x_503; lean_object* x_504; lean_object* x_505; lean_object* x_506; lean_object* x_507; lean_object* x_508; lean_object* x_509; lean_object* x_510; lean_object* x_511; lean_object* x_512; lean_object* x_513; lean_object* x_514; lean_object* x_515; 
x_502 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_503 = l_Lean_MessageData_ofName(x_460);
lean_inc_ref(x_503);
if (lean_is_scalar(x_501)) {
 x_504 = lean_alloc_ctor(7, 2, 0);
} else {
 x_504 = x_501;
 lean_ctor_set_tag(x_504, 7);
}
lean_ctor_set(x_504, 0, x_502);
lean_ctor_set(x_504, 1, x_503);
x_505 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_506 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_506, 0, x_504);
lean_ctor_set(x_506, 1, x_505);
x_507 = l_Lean_MessageData_ofSyntax(x_1);
x_508 = l_Lean_indentD(x_507);
x_509 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_509, 0, x_506);
lean_ctor_set(x_509, 1, x_508);
x_510 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_511 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_511, 0, x_509);
lean_ctor_set(x_511, 1, x_510);
x_512 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_512, 0, x_511);
lean_ctor_set(x_512, 1, x_503);
x_513 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_514 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_514, 0, x_512);
lean_ctor_set(x_514, 1, x_513);
x_515 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_514, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_515;
}
else
{
lean_object* x_516; lean_object* x_517; 
lean_dec(x_501);
lean_dec(x_460);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_516 = lean_ctor_get(x_500, 0);
lean_inc(x_516);
lean_dec_ref(x_500);
x_517 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_517, 0, x_516);
return x_517;
}
}
}
else
{
uint8_t x_518; 
lean_dec(x_460);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_518 = !lean_is_exclusive(x_463);
if (x_518 == 0)
{
return x_463;
}
else
{
lean_object* x_519; lean_object* x_520; 
x_519 = lean_ctor_get(x_463, 0);
lean_inc(x_519);
lean_dec(x_463);
x_520 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_520, 0, x_519);
return x_520;
}
}
}
else
{
lean_object* x_521; lean_object* x_522; uint8_t x_523; 
x_521 = l_Lean_Syntax_getArg(x_454, x_308);
x_522 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__61));
x_523 = l_Lean_Syntax_isOfKind(x_521, x_522);
if (x_523 == 0)
{
lean_object* x_524; lean_object* x_525; lean_object* x_526; lean_object* x_527; lean_object* x_528; lean_object* x_529; lean_object* x_530; 
lean_dec(x_454);
lean_dec(x_453);
x_524 = lean_st_ref_get(x_314);
x_525 = lean_ctor_get(x_524, 0);
lean_inc_ref(x_525);
lean_dec(x_524);
x_526 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_527 = l_Lean_Syntax_getKind(x_1);
x_528 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_526, x_525, x_527);
x_529 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc(x_312);
lean_inc_ref(x_311);
lean_inc(x_310);
lean_inc_ref(x_309);
lean_inc(x_1);
x_530 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_528, x_529, x_309, x_310, x_311, x_312, x_313, x_314);
if (lean_obj_tag(x_530) == 0)
{
uint8_t x_531; 
x_531 = !lean_is_exclusive(x_530);
if (x_531 == 0)
{
lean_object* x_532; uint8_t x_533; 
x_532 = lean_ctor_get(x_530, 0);
x_533 = !lean_is_exclusive(x_532);
if (x_533 == 0)
{
lean_object* x_534; lean_object* x_535; 
x_534 = lean_ctor_get(x_532, 0);
x_535 = lean_ctor_get(x_532, 1);
lean_dec(x_535);
if (lean_obj_tag(x_534) == 0)
{
lean_object* x_536; lean_object* x_537; lean_object* x_538; lean_object* x_539; lean_object* x_540; lean_object* x_541; lean_object* x_542; lean_object* x_543; lean_object* x_544; lean_object* x_545; lean_object* x_546; lean_object* x_547; lean_object* x_548; 
lean_free_object(x_530);
x_536 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_537 = l_Lean_MessageData_ofName(x_527);
lean_inc_ref(x_537);
lean_ctor_set_tag(x_532, 7);
lean_ctor_set(x_532, 1, x_537);
lean_ctor_set(x_532, 0, x_536);
x_538 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_539 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_539, 0, x_532);
lean_ctor_set(x_539, 1, x_538);
x_540 = l_Lean_MessageData_ofSyntax(x_1);
x_541 = l_Lean_indentD(x_540);
x_542 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_542, 0, x_539);
lean_ctor_set(x_542, 1, x_541);
x_543 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_544 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_544, 0, x_542);
lean_ctor_set(x_544, 1, x_543);
x_545 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_545, 0, x_544);
lean_ctor_set(x_545, 1, x_537);
x_546 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_547 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_547, 0, x_545);
lean_ctor_set(x_547, 1, x_546);
x_548 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_547, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_548;
}
else
{
lean_object* x_549; 
lean_free_object(x_532);
lean_dec(x_527);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_549 = lean_ctor_get(x_534, 0);
lean_inc(x_549);
lean_dec_ref(x_534);
lean_ctor_set(x_530, 0, x_549);
return x_530;
}
}
else
{
lean_object* x_550; 
x_550 = lean_ctor_get(x_532, 0);
lean_inc(x_550);
lean_dec(x_532);
if (lean_obj_tag(x_550) == 0)
{
lean_object* x_551; lean_object* x_552; lean_object* x_553; lean_object* x_554; lean_object* x_555; lean_object* x_556; lean_object* x_557; lean_object* x_558; lean_object* x_559; lean_object* x_560; lean_object* x_561; lean_object* x_562; lean_object* x_563; lean_object* x_564; 
lean_free_object(x_530);
x_551 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_552 = l_Lean_MessageData_ofName(x_527);
lean_inc_ref(x_552);
x_553 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_553, 0, x_551);
lean_ctor_set(x_553, 1, x_552);
x_554 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_555 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_555, 0, x_553);
lean_ctor_set(x_555, 1, x_554);
x_556 = l_Lean_MessageData_ofSyntax(x_1);
x_557 = l_Lean_indentD(x_556);
x_558 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_558, 0, x_555);
lean_ctor_set(x_558, 1, x_557);
x_559 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_560 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_560, 0, x_558);
lean_ctor_set(x_560, 1, x_559);
x_561 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_561, 0, x_560);
lean_ctor_set(x_561, 1, x_552);
x_562 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_563 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_563, 0, x_561);
lean_ctor_set(x_563, 1, x_562);
x_564 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_563, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_564;
}
else
{
lean_object* x_565; 
lean_dec(x_527);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_565 = lean_ctor_get(x_550, 0);
lean_inc(x_565);
lean_dec_ref(x_550);
lean_ctor_set(x_530, 0, x_565);
return x_530;
}
}
}
else
{
lean_object* x_566; lean_object* x_567; lean_object* x_568; 
x_566 = lean_ctor_get(x_530, 0);
lean_inc(x_566);
lean_dec(x_530);
x_567 = lean_ctor_get(x_566, 0);
lean_inc(x_567);
if (lean_is_exclusive(x_566)) {
 lean_ctor_release(x_566, 0);
 lean_ctor_release(x_566, 1);
 x_568 = x_566;
} else {
 lean_dec_ref(x_566);
 x_568 = lean_box(0);
}
if (lean_obj_tag(x_567) == 0)
{
lean_object* x_569; lean_object* x_570; lean_object* x_571; lean_object* x_572; lean_object* x_573; lean_object* x_574; lean_object* x_575; lean_object* x_576; lean_object* x_577; lean_object* x_578; lean_object* x_579; lean_object* x_580; lean_object* x_581; lean_object* x_582; 
x_569 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_570 = l_Lean_MessageData_ofName(x_527);
lean_inc_ref(x_570);
if (lean_is_scalar(x_568)) {
 x_571 = lean_alloc_ctor(7, 2, 0);
} else {
 x_571 = x_568;
 lean_ctor_set_tag(x_571, 7);
}
lean_ctor_set(x_571, 0, x_569);
lean_ctor_set(x_571, 1, x_570);
x_572 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_573 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_573, 0, x_571);
lean_ctor_set(x_573, 1, x_572);
x_574 = l_Lean_MessageData_ofSyntax(x_1);
x_575 = l_Lean_indentD(x_574);
x_576 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_576, 0, x_573);
lean_ctor_set(x_576, 1, x_575);
x_577 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_578 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_578, 0, x_576);
lean_ctor_set(x_578, 1, x_577);
x_579 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_579, 0, x_578);
lean_ctor_set(x_579, 1, x_570);
x_580 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_581 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_581, 0, x_579);
lean_ctor_set(x_581, 1, x_580);
x_582 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_581, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
return x_582;
}
else
{
lean_object* x_583; lean_object* x_584; 
lean_dec(x_568);
lean_dec(x_527);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_583 = lean_ctor_get(x_567, 0);
lean_inc(x_583);
lean_dec_ref(x_567);
x_584 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_584, 0, x_583);
return x_584;
}
}
}
else
{
uint8_t x_585; 
lean_dec(x_527);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
lean_dec(x_1);
x_585 = !lean_is_exclusive(x_530);
if (x_585 == 0)
{
return x_530;
}
else
{
lean_object* x_586; lean_object* x_587; 
x_586 = lean_ctor_get(x_530, 0);
lean_inc(x_586);
lean_dec(x_530);
x_587 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_587, 0, x_586);
return x_587;
}
}
}
else
{
lean_object* x_588; lean_object* x_589; lean_object* x_590; 
lean_dec(x_1);
x_588 = lean_unsigned_to_nat(3u);
x_589 = l_Lean_Syntax_getArg(x_454, x_588);
lean_dec(x_454);
lean_inc(x_314);
lean_inc_ref(x_313);
lean_inc(x_312);
lean_inc_ref(x_311);
lean_inc(x_310);
lean_inc_ref(x_309);
x_590 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_589, x_309, x_310, x_311, x_312, x_313, x_314);
if (lean_obj_tag(x_590) == 0)
{
lean_object* x_591; size_t x_592; lean_object* x_593; 
x_591 = lean_ctor_get(x_590, 0);
lean_inc(x_591);
lean_dec_ref(x_590);
x_592 = lean_array_size(x_453);
x_593 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(x_453, x_592, x_387, x_591, x_309, x_310, x_311, x_312, x_313, x_314);
lean_dec(x_453);
return x_593;
}
else
{
lean_dec(x_453);
lean_dec(x_314);
lean_dec_ref(x_313);
lean_dec(x_312);
lean_dec_ref(x_311);
lean_dec(x_310);
lean_dec_ref(x_309);
return x_590;
}
}
}
}
}
}
}
}
else
{
lean_object* x_663; lean_object* x_664; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_663 = l_Lean_Elab_Do_ControlInfo_pure;
x_664 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_664, 0, x_663);
return x_664;
}
}
else
{
lean_object* x_665; lean_object* x_666; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_665 = l_Lean_Elab_Do_ControlInfo_pure;
x_666 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_666, 0, x_665);
return x_666;
}
}
else
{
lean_object* x_667; lean_object* x_668; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_667 = l_Lean_Elab_Do_ControlInfo_pure;
x_668 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_668, 0, x_667);
return x_668;
}
}
else
{
lean_object* x_669; lean_object* x_670; lean_object* x_671; size_t x_672; size_t x_673; lean_object* x_674; 
x_669 = lean_unsigned_to_nat(2u);
x_670 = l_Lean_Syntax_getArg(x_1, x_669);
x_671 = l_Lean_Syntax_getArgs(x_670);
lean_dec(x_670);
x_672 = lean_array_size(x_671);
x_673 = 0;
x_674 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__6(x_672, x_673, x_671);
if (lean_obj_tag(x_674) == 0)
{
lean_object* x_675; lean_object* x_676; lean_object* x_677; lean_object* x_678; lean_object* x_679; lean_object* x_680; lean_object* x_681; 
x_675 = lean_st_ref_get(x_7);
x_676 = lean_ctor_get(x_675, 0);
lean_inc_ref(x_676);
lean_dec(x_675);
x_677 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_678 = l_Lean_Syntax_getKind(x_1);
x_679 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_677, x_676, x_678);
x_680 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_681 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_679, x_680, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_681) == 0)
{
uint8_t x_682; 
x_682 = !lean_is_exclusive(x_681);
if (x_682 == 0)
{
lean_object* x_683; uint8_t x_684; 
x_683 = lean_ctor_get(x_681, 0);
x_684 = !lean_is_exclusive(x_683);
if (x_684 == 0)
{
lean_object* x_685; lean_object* x_686; 
x_685 = lean_ctor_get(x_683, 0);
x_686 = lean_ctor_get(x_683, 1);
lean_dec(x_686);
if (lean_obj_tag(x_685) == 0)
{
lean_object* x_687; lean_object* x_688; lean_object* x_689; lean_object* x_690; lean_object* x_691; lean_object* x_692; lean_object* x_693; lean_object* x_694; lean_object* x_695; lean_object* x_696; lean_object* x_697; lean_object* x_698; lean_object* x_699; 
lean_free_object(x_681);
x_687 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_688 = l_Lean_MessageData_ofName(x_678);
lean_inc_ref(x_688);
lean_ctor_set_tag(x_683, 7);
lean_ctor_set(x_683, 1, x_688);
lean_ctor_set(x_683, 0, x_687);
x_689 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_690 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_690, 0, x_683);
lean_ctor_set(x_690, 1, x_689);
x_691 = l_Lean_MessageData_ofSyntax(x_1);
x_692 = l_Lean_indentD(x_691);
x_693 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_693, 0, x_690);
lean_ctor_set(x_693, 1, x_692);
x_694 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_695 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_695, 0, x_693);
lean_ctor_set(x_695, 1, x_694);
x_696 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_696, 0, x_695);
lean_ctor_set(x_696, 1, x_688);
x_697 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_698 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_698, 0, x_696);
lean_ctor_set(x_698, 1, x_697);
x_699 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_698, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_699;
}
else
{
lean_object* x_700; 
lean_free_object(x_683);
lean_dec(x_678);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_700 = lean_ctor_get(x_685, 0);
lean_inc(x_700);
lean_dec_ref(x_685);
lean_ctor_set(x_681, 0, x_700);
return x_681;
}
}
else
{
lean_object* x_701; 
x_701 = lean_ctor_get(x_683, 0);
lean_inc(x_701);
lean_dec(x_683);
if (lean_obj_tag(x_701) == 0)
{
lean_object* x_702; lean_object* x_703; lean_object* x_704; lean_object* x_705; lean_object* x_706; lean_object* x_707; lean_object* x_708; lean_object* x_709; lean_object* x_710; lean_object* x_711; lean_object* x_712; lean_object* x_713; lean_object* x_714; lean_object* x_715; 
lean_free_object(x_681);
x_702 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_703 = l_Lean_MessageData_ofName(x_678);
lean_inc_ref(x_703);
x_704 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_704, 0, x_702);
lean_ctor_set(x_704, 1, x_703);
x_705 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_706 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_706, 0, x_704);
lean_ctor_set(x_706, 1, x_705);
x_707 = l_Lean_MessageData_ofSyntax(x_1);
x_708 = l_Lean_indentD(x_707);
x_709 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_709, 0, x_706);
lean_ctor_set(x_709, 1, x_708);
x_710 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_711 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_711, 0, x_709);
lean_ctor_set(x_711, 1, x_710);
x_712 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_712, 0, x_711);
lean_ctor_set(x_712, 1, x_703);
x_713 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_714 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_714, 0, x_712);
lean_ctor_set(x_714, 1, x_713);
x_715 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_714, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_715;
}
else
{
lean_object* x_716; 
lean_dec(x_678);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_716 = lean_ctor_get(x_701, 0);
lean_inc(x_716);
lean_dec_ref(x_701);
lean_ctor_set(x_681, 0, x_716);
return x_681;
}
}
}
else
{
lean_object* x_717; lean_object* x_718; lean_object* x_719; 
x_717 = lean_ctor_get(x_681, 0);
lean_inc(x_717);
lean_dec(x_681);
x_718 = lean_ctor_get(x_717, 0);
lean_inc(x_718);
if (lean_is_exclusive(x_717)) {
 lean_ctor_release(x_717, 0);
 lean_ctor_release(x_717, 1);
 x_719 = x_717;
} else {
 lean_dec_ref(x_717);
 x_719 = lean_box(0);
}
if (lean_obj_tag(x_718) == 0)
{
lean_object* x_720; lean_object* x_721; lean_object* x_722; lean_object* x_723; lean_object* x_724; lean_object* x_725; lean_object* x_726; lean_object* x_727; lean_object* x_728; lean_object* x_729; lean_object* x_730; lean_object* x_731; lean_object* x_732; lean_object* x_733; 
x_720 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_721 = l_Lean_MessageData_ofName(x_678);
lean_inc_ref(x_721);
if (lean_is_scalar(x_719)) {
 x_722 = lean_alloc_ctor(7, 2, 0);
} else {
 x_722 = x_719;
 lean_ctor_set_tag(x_722, 7);
}
lean_ctor_set(x_722, 0, x_720);
lean_ctor_set(x_722, 1, x_721);
x_723 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_724 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_724, 0, x_722);
lean_ctor_set(x_724, 1, x_723);
x_725 = l_Lean_MessageData_ofSyntax(x_1);
x_726 = l_Lean_indentD(x_725);
x_727 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_727, 0, x_724);
lean_ctor_set(x_727, 1, x_726);
x_728 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_729 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_729, 0, x_727);
lean_ctor_set(x_729, 1, x_728);
x_730 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_730, 0, x_729);
lean_ctor_set(x_730, 1, x_721);
x_731 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_732 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_732, 0, x_730);
lean_ctor_set(x_732, 1, x_731);
x_733 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_732, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_733;
}
else
{
lean_object* x_734; lean_object* x_735; 
lean_dec(x_719);
lean_dec(x_678);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_734 = lean_ctor_get(x_718, 0);
lean_inc(x_734);
lean_dec_ref(x_718);
x_735 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_735, 0, x_734);
return x_735;
}
}
}
else
{
uint8_t x_736; 
lean_dec(x_678);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_736 = !lean_is_exclusive(x_681);
if (x_736 == 0)
{
return x_681;
}
else
{
lean_object* x_737; lean_object* x_738; 
x_737 = lean_ctor_get(x_681, 0);
lean_inc(x_737);
lean_dec(x_681);
x_738 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_738, 0, x_737);
return x_738;
}
}
}
else
{
uint8_t x_739; 
x_739 = !lean_is_exclusive(x_674);
if (x_739 == 0)
{
lean_object* x_740; lean_object* x_741; lean_object* x_742; lean_object* x_743; lean_object* x_744; lean_object* x_745; lean_object* x_746; lean_object* x_747; lean_object* x_748; lean_object* x_749; lean_object* x_750; lean_object* x_764; lean_object* x_765; uint8_t x_766; 
x_740 = lean_ctor_get(x_674, 0);
x_741 = lean_unsigned_to_nat(1u);
x_742 = l_Lean_Syntax_getArg(x_1, x_741);
x_764 = lean_unsigned_to_nat(3u);
x_765 = l_Lean_Syntax_getArg(x_1, x_764);
x_766 = l_Lean_Syntax_isNone(x_765);
if (x_766 == 0)
{
uint8_t x_767; 
lean_inc(x_765);
x_767 = l_Lean_Syntax_matchesNull(x_765, x_741);
if (x_767 == 0)
{
lean_object* x_768; lean_object* x_769; lean_object* x_770; lean_object* x_771; lean_object* x_772; lean_object* x_773; lean_object* x_774; 
lean_dec(x_765);
lean_dec(x_742);
lean_free_object(x_674);
lean_dec(x_740);
x_768 = lean_st_ref_get(x_7);
x_769 = lean_ctor_get(x_768, 0);
lean_inc_ref(x_769);
lean_dec(x_768);
x_770 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_771 = l_Lean_Syntax_getKind(x_1);
x_772 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_770, x_769, x_771);
x_773 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_774 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_772, x_773, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_774) == 0)
{
uint8_t x_775; 
x_775 = !lean_is_exclusive(x_774);
if (x_775 == 0)
{
lean_object* x_776; uint8_t x_777; 
x_776 = lean_ctor_get(x_774, 0);
x_777 = !lean_is_exclusive(x_776);
if (x_777 == 0)
{
lean_object* x_778; lean_object* x_779; 
x_778 = lean_ctor_get(x_776, 0);
x_779 = lean_ctor_get(x_776, 1);
lean_dec(x_779);
if (lean_obj_tag(x_778) == 0)
{
lean_object* x_780; lean_object* x_781; lean_object* x_782; lean_object* x_783; lean_object* x_784; lean_object* x_785; lean_object* x_786; lean_object* x_787; lean_object* x_788; lean_object* x_789; lean_object* x_790; lean_object* x_791; lean_object* x_792; 
lean_free_object(x_774);
x_780 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_781 = l_Lean_MessageData_ofName(x_771);
lean_inc_ref(x_781);
lean_ctor_set_tag(x_776, 7);
lean_ctor_set(x_776, 1, x_781);
lean_ctor_set(x_776, 0, x_780);
x_782 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_783 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_783, 0, x_776);
lean_ctor_set(x_783, 1, x_782);
x_784 = l_Lean_MessageData_ofSyntax(x_1);
x_785 = l_Lean_indentD(x_784);
x_786 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_786, 0, x_783);
lean_ctor_set(x_786, 1, x_785);
x_787 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_788 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_788, 0, x_786);
lean_ctor_set(x_788, 1, x_787);
x_789 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_789, 0, x_788);
lean_ctor_set(x_789, 1, x_781);
x_790 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_791 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_791, 0, x_789);
lean_ctor_set(x_791, 1, x_790);
x_792 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_791, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_792;
}
else
{
lean_object* x_793; 
lean_free_object(x_776);
lean_dec(x_771);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_793 = lean_ctor_get(x_778, 0);
lean_inc(x_793);
lean_dec_ref(x_778);
lean_ctor_set(x_774, 0, x_793);
return x_774;
}
}
else
{
lean_object* x_794; 
x_794 = lean_ctor_get(x_776, 0);
lean_inc(x_794);
lean_dec(x_776);
if (lean_obj_tag(x_794) == 0)
{
lean_object* x_795; lean_object* x_796; lean_object* x_797; lean_object* x_798; lean_object* x_799; lean_object* x_800; lean_object* x_801; lean_object* x_802; lean_object* x_803; lean_object* x_804; lean_object* x_805; lean_object* x_806; lean_object* x_807; lean_object* x_808; 
lean_free_object(x_774);
x_795 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_796 = l_Lean_MessageData_ofName(x_771);
lean_inc_ref(x_796);
x_797 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_797, 0, x_795);
lean_ctor_set(x_797, 1, x_796);
x_798 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_799 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_799, 0, x_797);
lean_ctor_set(x_799, 1, x_798);
x_800 = l_Lean_MessageData_ofSyntax(x_1);
x_801 = l_Lean_indentD(x_800);
x_802 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_802, 0, x_799);
lean_ctor_set(x_802, 1, x_801);
x_803 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_804 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_804, 0, x_802);
lean_ctor_set(x_804, 1, x_803);
x_805 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_805, 0, x_804);
lean_ctor_set(x_805, 1, x_796);
x_806 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_807 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_807, 0, x_805);
lean_ctor_set(x_807, 1, x_806);
x_808 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_807, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_808;
}
else
{
lean_object* x_809; 
lean_dec(x_771);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_809 = lean_ctor_get(x_794, 0);
lean_inc(x_809);
lean_dec_ref(x_794);
lean_ctor_set(x_774, 0, x_809);
return x_774;
}
}
}
else
{
lean_object* x_810; lean_object* x_811; lean_object* x_812; 
x_810 = lean_ctor_get(x_774, 0);
lean_inc(x_810);
lean_dec(x_774);
x_811 = lean_ctor_get(x_810, 0);
lean_inc(x_811);
if (lean_is_exclusive(x_810)) {
 lean_ctor_release(x_810, 0);
 lean_ctor_release(x_810, 1);
 x_812 = x_810;
} else {
 lean_dec_ref(x_810);
 x_812 = lean_box(0);
}
if (lean_obj_tag(x_811) == 0)
{
lean_object* x_813; lean_object* x_814; lean_object* x_815; lean_object* x_816; lean_object* x_817; lean_object* x_818; lean_object* x_819; lean_object* x_820; lean_object* x_821; lean_object* x_822; lean_object* x_823; lean_object* x_824; lean_object* x_825; lean_object* x_826; 
x_813 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_814 = l_Lean_MessageData_ofName(x_771);
lean_inc_ref(x_814);
if (lean_is_scalar(x_812)) {
 x_815 = lean_alloc_ctor(7, 2, 0);
} else {
 x_815 = x_812;
 lean_ctor_set_tag(x_815, 7);
}
lean_ctor_set(x_815, 0, x_813);
lean_ctor_set(x_815, 1, x_814);
x_816 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_817 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_817, 0, x_815);
lean_ctor_set(x_817, 1, x_816);
x_818 = l_Lean_MessageData_ofSyntax(x_1);
x_819 = l_Lean_indentD(x_818);
x_820 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_820, 0, x_817);
lean_ctor_set(x_820, 1, x_819);
x_821 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_822 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_822, 0, x_820);
lean_ctor_set(x_822, 1, x_821);
x_823 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_823, 0, x_822);
lean_ctor_set(x_823, 1, x_814);
x_824 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_825 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_825, 0, x_823);
lean_ctor_set(x_825, 1, x_824);
x_826 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_825, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_826;
}
else
{
lean_object* x_827; lean_object* x_828; 
lean_dec(x_812);
lean_dec(x_771);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_827 = lean_ctor_get(x_811, 0);
lean_inc(x_827);
lean_dec_ref(x_811);
x_828 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_828, 0, x_827);
return x_828;
}
}
}
else
{
uint8_t x_829; 
lean_dec(x_771);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_829 = !lean_is_exclusive(x_774);
if (x_829 == 0)
{
return x_774;
}
else
{
lean_object* x_830; lean_object* x_831; 
x_830 = lean_ctor_get(x_774, 0);
lean_inc(x_830);
lean_dec(x_774);
x_831 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_831, 0, x_830);
return x_831;
}
}
}
else
{
lean_object* x_832; lean_object* x_833; lean_object* x_834; uint8_t x_835; 
x_832 = lean_unsigned_to_nat(0u);
x_833 = l_Lean_Syntax_getArg(x_765, x_832);
lean_dec(x_765);
x_834 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63));
lean_inc(x_833);
x_835 = l_Lean_Syntax_isOfKind(x_833, x_834);
if (x_835 == 0)
{
lean_object* x_836; lean_object* x_837; lean_object* x_838; lean_object* x_839; lean_object* x_840; lean_object* x_841; lean_object* x_842; 
lean_dec(x_833);
lean_dec(x_742);
lean_free_object(x_674);
lean_dec(x_740);
x_836 = lean_st_ref_get(x_7);
x_837 = lean_ctor_get(x_836, 0);
lean_inc_ref(x_837);
lean_dec(x_836);
x_838 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_839 = l_Lean_Syntax_getKind(x_1);
x_840 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_838, x_837, x_839);
x_841 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_842 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_840, x_841, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_842) == 0)
{
uint8_t x_843; 
x_843 = !lean_is_exclusive(x_842);
if (x_843 == 0)
{
lean_object* x_844; uint8_t x_845; 
x_844 = lean_ctor_get(x_842, 0);
x_845 = !lean_is_exclusive(x_844);
if (x_845 == 0)
{
lean_object* x_846; lean_object* x_847; 
x_846 = lean_ctor_get(x_844, 0);
x_847 = lean_ctor_get(x_844, 1);
lean_dec(x_847);
if (lean_obj_tag(x_846) == 0)
{
lean_object* x_848; lean_object* x_849; lean_object* x_850; lean_object* x_851; lean_object* x_852; lean_object* x_853; lean_object* x_854; lean_object* x_855; lean_object* x_856; lean_object* x_857; lean_object* x_858; lean_object* x_859; lean_object* x_860; 
lean_free_object(x_842);
x_848 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_849 = l_Lean_MessageData_ofName(x_839);
lean_inc_ref(x_849);
lean_ctor_set_tag(x_844, 7);
lean_ctor_set(x_844, 1, x_849);
lean_ctor_set(x_844, 0, x_848);
x_850 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_851 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_851, 0, x_844);
lean_ctor_set(x_851, 1, x_850);
x_852 = l_Lean_MessageData_ofSyntax(x_1);
x_853 = l_Lean_indentD(x_852);
x_854 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_854, 0, x_851);
lean_ctor_set(x_854, 1, x_853);
x_855 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_856 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_856, 0, x_854);
lean_ctor_set(x_856, 1, x_855);
x_857 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_857, 0, x_856);
lean_ctor_set(x_857, 1, x_849);
x_858 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_859 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_859, 0, x_857);
lean_ctor_set(x_859, 1, x_858);
x_860 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_859, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_860;
}
else
{
lean_object* x_861; 
lean_free_object(x_844);
lean_dec(x_839);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_861 = lean_ctor_get(x_846, 0);
lean_inc(x_861);
lean_dec_ref(x_846);
lean_ctor_set(x_842, 0, x_861);
return x_842;
}
}
else
{
lean_object* x_862; 
x_862 = lean_ctor_get(x_844, 0);
lean_inc(x_862);
lean_dec(x_844);
if (lean_obj_tag(x_862) == 0)
{
lean_object* x_863; lean_object* x_864; lean_object* x_865; lean_object* x_866; lean_object* x_867; lean_object* x_868; lean_object* x_869; lean_object* x_870; lean_object* x_871; lean_object* x_872; lean_object* x_873; lean_object* x_874; lean_object* x_875; lean_object* x_876; 
lean_free_object(x_842);
x_863 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_864 = l_Lean_MessageData_ofName(x_839);
lean_inc_ref(x_864);
x_865 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_865, 0, x_863);
lean_ctor_set(x_865, 1, x_864);
x_866 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_867 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_867, 0, x_865);
lean_ctor_set(x_867, 1, x_866);
x_868 = l_Lean_MessageData_ofSyntax(x_1);
x_869 = l_Lean_indentD(x_868);
x_870 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_870, 0, x_867);
lean_ctor_set(x_870, 1, x_869);
x_871 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_872 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_872, 0, x_870);
lean_ctor_set(x_872, 1, x_871);
x_873 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_873, 0, x_872);
lean_ctor_set(x_873, 1, x_864);
x_874 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_875 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_875, 0, x_873);
lean_ctor_set(x_875, 1, x_874);
x_876 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_875, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_876;
}
else
{
lean_object* x_877; 
lean_dec(x_839);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_877 = lean_ctor_get(x_862, 0);
lean_inc(x_877);
lean_dec_ref(x_862);
lean_ctor_set(x_842, 0, x_877);
return x_842;
}
}
}
else
{
lean_object* x_878; lean_object* x_879; lean_object* x_880; 
x_878 = lean_ctor_get(x_842, 0);
lean_inc(x_878);
lean_dec(x_842);
x_879 = lean_ctor_get(x_878, 0);
lean_inc(x_879);
if (lean_is_exclusive(x_878)) {
 lean_ctor_release(x_878, 0);
 lean_ctor_release(x_878, 1);
 x_880 = x_878;
} else {
 lean_dec_ref(x_878);
 x_880 = lean_box(0);
}
if (lean_obj_tag(x_879) == 0)
{
lean_object* x_881; lean_object* x_882; lean_object* x_883; lean_object* x_884; lean_object* x_885; lean_object* x_886; lean_object* x_887; lean_object* x_888; lean_object* x_889; lean_object* x_890; lean_object* x_891; lean_object* x_892; lean_object* x_893; lean_object* x_894; 
x_881 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_882 = l_Lean_MessageData_ofName(x_839);
lean_inc_ref(x_882);
if (lean_is_scalar(x_880)) {
 x_883 = lean_alloc_ctor(7, 2, 0);
} else {
 x_883 = x_880;
 lean_ctor_set_tag(x_883, 7);
}
lean_ctor_set(x_883, 0, x_881);
lean_ctor_set(x_883, 1, x_882);
x_884 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_885 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_885, 0, x_883);
lean_ctor_set(x_885, 1, x_884);
x_886 = l_Lean_MessageData_ofSyntax(x_1);
x_887 = l_Lean_indentD(x_886);
x_888 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_888, 0, x_885);
lean_ctor_set(x_888, 1, x_887);
x_889 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_890 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_890, 0, x_888);
lean_ctor_set(x_890, 1, x_889);
x_891 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_891, 0, x_890);
lean_ctor_set(x_891, 1, x_882);
x_892 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_893 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_893, 0, x_891);
lean_ctor_set(x_893, 1, x_892);
x_894 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_893, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_894;
}
else
{
lean_object* x_895; lean_object* x_896; 
lean_dec(x_880);
lean_dec(x_839);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_895 = lean_ctor_get(x_879, 0);
lean_inc(x_895);
lean_dec_ref(x_879);
x_896 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_896, 0, x_895);
return x_896;
}
}
}
else
{
uint8_t x_897; 
lean_dec(x_839);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_897 = !lean_is_exclusive(x_842);
if (x_897 == 0)
{
return x_842;
}
else
{
lean_object* x_898; lean_object* x_899; 
x_898 = lean_ctor_get(x_842, 0);
lean_inc(x_898);
lean_dec(x_842);
x_899 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_899, 0, x_898);
return x_899;
}
}
}
else
{
lean_object* x_900; 
lean_dec(x_1);
x_900 = l_Lean_Syntax_getArg(x_833, x_741);
lean_dec(x_833);
lean_ctor_set(x_674, 0, x_900);
x_743 = x_674;
x_744 = x_2;
x_745 = x_3;
x_746 = x_4;
x_747 = x_5;
x_748 = x_6;
x_749 = x_7;
x_750 = lean_box(0);
goto block_763;
}
}
}
else
{
lean_object* x_901; 
lean_dec(x_765);
lean_free_object(x_674);
lean_dec(x_1);
x_901 = lean_box(0);
x_743 = x_901;
x_744 = x_2;
x_745 = x_3;
x_746 = x_4;
x_747 = x_5;
x_748 = x_6;
x_749 = x_7;
x_750 = lean_box(0);
goto block_763;
}
block_763:
{
lean_object* x_751; 
lean_inc(x_749);
lean_inc_ref(x_748);
lean_inc(x_747);
lean_inc_ref(x_746);
lean_inc(x_745);
lean_inc_ref(x_744);
x_751 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_742, x_744, x_745, x_746, x_747, x_748, x_749);
if (lean_obj_tag(x_751) == 0)
{
lean_object* x_752; size_t x_753; lean_object* x_754; 
x_752 = lean_ctor_get(x_751, 0);
lean_inc(x_752);
lean_dec_ref(x_751);
x_753 = lean_array_size(x_740);
lean_inc(x_749);
lean_inc_ref(x_748);
lean_inc(x_747);
lean_inc_ref(x_746);
lean_inc(x_745);
lean_inc_ref(x_744);
x_754 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(x_740, x_753, x_673, x_752, x_744, x_745, x_746, x_747, x_748, x_749);
lean_dec(x_740);
if (lean_obj_tag(x_754) == 0)
{
lean_object* x_755; lean_object* x_756; 
x_755 = lean_ctor_get(x_754, 0);
lean_inc(x_755);
lean_dec_ref(x_754);
x_756 = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(x_743, x_744, x_745, x_746, x_747, x_748, x_749);
if (lean_obj_tag(x_756) == 0)
{
uint8_t x_757; 
x_757 = !lean_is_exclusive(x_756);
if (x_757 == 0)
{
lean_object* x_758; lean_object* x_759; 
x_758 = lean_ctor_get(x_756, 0);
x_759 = l_Lean_Elab_Do_ControlInfo_sequence(x_755, x_758);
lean_ctor_set(x_756, 0, x_759);
return x_756;
}
else
{
lean_object* x_760; lean_object* x_761; lean_object* x_762; 
x_760 = lean_ctor_get(x_756, 0);
lean_inc(x_760);
lean_dec(x_756);
x_761 = l_Lean_Elab_Do_ControlInfo_sequence(x_755, x_760);
x_762 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_762, 0, x_761);
return x_762;
}
}
else
{
lean_dec(x_755);
return x_756;
}
}
else
{
lean_dec(x_749);
lean_dec_ref(x_748);
lean_dec(x_747);
lean_dec_ref(x_746);
lean_dec(x_745);
lean_dec_ref(x_744);
lean_dec(x_743);
return x_754;
}
}
else
{
lean_dec(x_749);
lean_dec_ref(x_748);
lean_dec(x_747);
lean_dec_ref(x_746);
lean_dec(x_745);
lean_dec_ref(x_744);
lean_dec(x_743);
lean_dec(x_740);
return x_751;
}
}
}
else
{
lean_object* x_902; lean_object* x_903; lean_object* x_904; lean_object* x_905; lean_object* x_906; lean_object* x_907; lean_object* x_908; lean_object* x_909; lean_object* x_910; lean_object* x_911; lean_object* x_912; lean_object* x_924; lean_object* x_925; uint8_t x_926; 
x_902 = lean_ctor_get(x_674, 0);
lean_inc(x_902);
lean_dec(x_674);
x_903 = lean_unsigned_to_nat(1u);
x_904 = l_Lean_Syntax_getArg(x_1, x_903);
x_924 = lean_unsigned_to_nat(3u);
x_925 = l_Lean_Syntax_getArg(x_1, x_924);
x_926 = l_Lean_Syntax_isNone(x_925);
if (x_926 == 0)
{
uint8_t x_927; 
lean_inc(x_925);
x_927 = l_Lean_Syntax_matchesNull(x_925, x_903);
if (x_927 == 0)
{
lean_object* x_928; lean_object* x_929; lean_object* x_930; lean_object* x_931; lean_object* x_932; lean_object* x_933; lean_object* x_934; 
lean_dec(x_925);
lean_dec(x_904);
lean_dec(x_902);
x_928 = lean_st_ref_get(x_7);
x_929 = lean_ctor_get(x_928, 0);
lean_inc_ref(x_929);
lean_dec(x_928);
x_930 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_931 = l_Lean_Syntax_getKind(x_1);
x_932 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_930, x_929, x_931);
x_933 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_934 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_932, x_933, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_934) == 0)
{
lean_object* x_935; lean_object* x_936; lean_object* x_937; lean_object* x_938; 
x_935 = lean_ctor_get(x_934, 0);
lean_inc(x_935);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 x_936 = x_934;
} else {
 lean_dec_ref(x_934);
 x_936 = lean_box(0);
}
x_937 = lean_ctor_get(x_935, 0);
lean_inc(x_937);
if (lean_is_exclusive(x_935)) {
 lean_ctor_release(x_935, 0);
 lean_ctor_release(x_935, 1);
 x_938 = x_935;
} else {
 lean_dec_ref(x_935);
 x_938 = lean_box(0);
}
if (lean_obj_tag(x_937) == 0)
{
lean_object* x_939; lean_object* x_940; lean_object* x_941; lean_object* x_942; lean_object* x_943; lean_object* x_944; lean_object* x_945; lean_object* x_946; lean_object* x_947; lean_object* x_948; lean_object* x_949; lean_object* x_950; lean_object* x_951; lean_object* x_952; 
lean_dec(x_936);
x_939 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_940 = l_Lean_MessageData_ofName(x_931);
lean_inc_ref(x_940);
if (lean_is_scalar(x_938)) {
 x_941 = lean_alloc_ctor(7, 2, 0);
} else {
 x_941 = x_938;
 lean_ctor_set_tag(x_941, 7);
}
lean_ctor_set(x_941, 0, x_939);
lean_ctor_set(x_941, 1, x_940);
x_942 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_943 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_943, 0, x_941);
lean_ctor_set(x_943, 1, x_942);
x_944 = l_Lean_MessageData_ofSyntax(x_1);
x_945 = l_Lean_indentD(x_944);
x_946 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_946, 0, x_943);
lean_ctor_set(x_946, 1, x_945);
x_947 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_948 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_948, 0, x_946);
lean_ctor_set(x_948, 1, x_947);
x_949 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_949, 0, x_948);
lean_ctor_set(x_949, 1, x_940);
x_950 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_951 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_951, 0, x_949);
lean_ctor_set(x_951, 1, x_950);
x_952 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_951, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_952;
}
else
{
lean_object* x_953; lean_object* x_954; 
lean_dec(x_938);
lean_dec(x_931);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_953 = lean_ctor_get(x_937, 0);
lean_inc(x_953);
lean_dec_ref(x_937);
if (lean_is_scalar(x_936)) {
 x_954 = lean_alloc_ctor(0, 1, 0);
} else {
 x_954 = x_936;
}
lean_ctor_set(x_954, 0, x_953);
return x_954;
}
}
else
{
lean_object* x_955; lean_object* x_956; lean_object* x_957; 
lean_dec(x_931);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_955 = lean_ctor_get(x_934, 0);
lean_inc(x_955);
if (lean_is_exclusive(x_934)) {
 lean_ctor_release(x_934, 0);
 x_956 = x_934;
} else {
 lean_dec_ref(x_934);
 x_956 = lean_box(0);
}
if (lean_is_scalar(x_956)) {
 x_957 = lean_alloc_ctor(1, 1, 0);
} else {
 x_957 = x_956;
}
lean_ctor_set(x_957, 0, x_955);
return x_957;
}
}
else
{
lean_object* x_958; lean_object* x_959; lean_object* x_960; uint8_t x_961; 
x_958 = lean_unsigned_to_nat(0u);
x_959 = l_Lean_Syntax_getArg(x_925, x_958);
lean_dec(x_925);
x_960 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__63));
lean_inc(x_959);
x_961 = l_Lean_Syntax_isOfKind(x_959, x_960);
if (x_961 == 0)
{
lean_object* x_962; lean_object* x_963; lean_object* x_964; lean_object* x_965; lean_object* x_966; lean_object* x_967; lean_object* x_968; 
lean_dec(x_959);
lean_dec(x_904);
lean_dec(x_902);
x_962 = lean_st_ref_get(x_7);
x_963 = lean_ctor_get(x_962, 0);
lean_inc_ref(x_963);
lean_dec(x_962);
x_964 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_965 = l_Lean_Syntax_getKind(x_1);
x_966 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_964, x_963, x_965);
x_967 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_968 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_966, x_967, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_968) == 0)
{
lean_object* x_969; lean_object* x_970; lean_object* x_971; lean_object* x_972; 
x_969 = lean_ctor_get(x_968, 0);
lean_inc(x_969);
if (lean_is_exclusive(x_968)) {
 lean_ctor_release(x_968, 0);
 x_970 = x_968;
} else {
 lean_dec_ref(x_968);
 x_970 = lean_box(0);
}
x_971 = lean_ctor_get(x_969, 0);
lean_inc(x_971);
if (lean_is_exclusive(x_969)) {
 lean_ctor_release(x_969, 0);
 lean_ctor_release(x_969, 1);
 x_972 = x_969;
} else {
 lean_dec_ref(x_969);
 x_972 = lean_box(0);
}
if (lean_obj_tag(x_971) == 0)
{
lean_object* x_973; lean_object* x_974; lean_object* x_975; lean_object* x_976; lean_object* x_977; lean_object* x_978; lean_object* x_979; lean_object* x_980; lean_object* x_981; lean_object* x_982; lean_object* x_983; lean_object* x_984; lean_object* x_985; lean_object* x_986; 
lean_dec(x_970);
x_973 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_974 = l_Lean_MessageData_ofName(x_965);
lean_inc_ref(x_974);
if (lean_is_scalar(x_972)) {
 x_975 = lean_alloc_ctor(7, 2, 0);
} else {
 x_975 = x_972;
 lean_ctor_set_tag(x_975, 7);
}
lean_ctor_set(x_975, 0, x_973);
lean_ctor_set(x_975, 1, x_974);
x_976 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_977 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_977, 0, x_975);
lean_ctor_set(x_977, 1, x_976);
x_978 = l_Lean_MessageData_ofSyntax(x_1);
x_979 = l_Lean_indentD(x_978);
x_980 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_980, 0, x_977);
lean_ctor_set(x_980, 1, x_979);
x_981 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_982 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_982, 0, x_980);
lean_ctor_set(x_982, 1, x_981);
x_983 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_983, 0, x_982);
lean_ctor_set(x_983, 1, x_974);
x_984 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_985 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_985, 0, x_983);
lean_ctor_set(x_985, 1, x_984);
x_986 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_985, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_986;
}
else
{
lean_object* x_987; lean_object* x_988; 
lean_dec(x_972);
lean_dec(x_965);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_987 = lean_ctor_get(x_971, 0);
lean_inc(x_987);
lean_dec_ref(x_971);
if (lean_is_scalar(x_970)) {
 x_988 = lean_alloc_ctor(0, 1, 0);
} else {
 x_988 = x_970;
}
lean_ctor_set(x_988, 0, x_987);
return x_988;
}
}
else
{
lean_object* x_989; lean_object* x_990; lean_object* x_991; 
lean_dec(x_965);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_989 = lean_ctor_get(x_968, 0);
lean_inc(x_989);
if (lean_is_exclusive(x_968)) {
 lean_ctor_release(x_968, 0);
 x_990 = x_968;
} else {
 lean_dec_ref(x_968);
 x_990 = lean_box(0);
}
if (lean_is_scalar(x_990)) {
 x_991 = lean_alloc_ctor(1, 1, 0);
} else {
 x_991 = x_990;
}
lean_ctor_set(x_991, 0, x_989);
return x_991;
}
}
else
{
lean_object* x_992; lean_object* x_993; 
lean_dec(x_1);
x_992 = l_Lean_Syntax_getArg(x_959, x_903);
lean_dec(x_959);
x_993 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_993, 0, x_992);
x_905 = x_993;
x_906 = x_2;
x_907 = x_3;
x_908 = x_4;
x_909 = x_5;
x_910 = x_6;
x_911 = x_7;
x_912 = lean_box(0);
goto block_923;
}
}
}
else
{
lean_object* x_994; 
lean_dec(x_925);
lean_dec(x_1);
x_994 = lean_box(0);
x_905 = x_994;
x_906 = x_2;
x_907 = x_3;
x_908 = x_4;
x_909 = x_5;
x_910 = x_6;
x_911 = x_7;
x_912 = lean_box(0);
goto block_923;
}
block_923:
{
lean_object* x_913; 
lean_inc(x_911);
lean_inc_ref(x_910);
lean_inc(x_909);
lean_inc_ref(x_908);
lean_inc(x_907);
lean_inc_ref(x_906);
x_913 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_904, x_906, x_907, x_908, x_909, x_910, x_911);
if (lean_obj_tag(x_913) == 0)
{
lean_object* x_914; size_t x_915; lean_object* x_916; 
x_914 = lean_ctor_get(x_913, 0);
lean_inc(x_914);
lean_dec_ref(x_913);
x_915 = lean_array_size(x_902);
lean_inc(x_911);
lean_inc_ref(x_910);
lean_inc(x_909);
lean_inc_ref(x_908);
lean_inc(x_907);
lean_inc_ref(x_906);
x_916 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(x_902, x_915, x_673, x_914, x_906, x_907, x_908, x_909, x_910, x_911);
lean_dec(x_902);
if (lean_obj_tag(x_916) == 0)
{
lean_object* x_917; lean_object* x_918; 
x_917 = lean_ctor_get(x_916, 0);
lean_inc(x_917);
lean_dec_ref(x_916);
x_918 = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(x_905, x_906, x_907, x_908, x_909, x_910, x_911);
if (lean_obj_tag(x_918) == 0)
{
lean_object* x_919; lean_object* x_920; lean_object* x_921; lean_object* x_922; 
x_919 = lean_ctor_get(x_918, 0);
lean_inc(x_919);
if (lean_is_exclusive(x_918)) {
 lean_ctor_release(x_918, 0);
 x_920 = x_918;
} else {
 lean_dec_ref(x_918);
 x_920 = lean_box(0);
}
x_921 = l_Lean_Elab_Do_ControlInfo_sequence(x_917, x_919);
if (lean_is_scalar(x_920)) {
 x_922 = lean_alloc_ctor(0, 1, 0);
} else {
 x_922 = x_920;
}
lean_ctor_set(x_922, 0, x_921);
return x_922;
}
else
{
lean_dec(x_917);
return x_918;
}
}
else
{
lean_dec(x_911);
lean_dec_ref(x_910);
lean_dec(x_909);
lean_dec_ref(x_908);
lean_dec(x_907);
lean_dec_ref(x_906);
lean_dec(x_905);
return x_916;
}
}
else
{
lean_dec(x_911);
lean_dec_ref(x_910);
lean_dec(x_909);
lean_dec_ref(x_908);
lean_dec(x_907);
lean_dec_ref(x_906);
lean_dec(x_905);
lean_dec(x_902);
return x_913;
}
}
}
}
}
}
else
{
lean_object* x_995; lean_object* x_996; lean_object* x_1081; lean_object* x_1082; lean_object* x_1083; lean_object* x_1084; lean_object* x_1085; uint8_t x_1086; 
x_995 = lean_unsigned_to_nat(1u);
x_1081 = l_Lean_Syntax_getArg(x_1, x_995);
x_1082 = l_Lean_Syntax_getArgs(x_1081);
lean_dec(x_1081);
x_1083 = lean_unsigned_to_nat(0u);
x_1084 = lean_obj_once(&l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2, &l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2_once, _init_l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___closed__2);
x_1085 = lean_array_get_size(x_1082);
x_1086 = lean_nat_dec_lt(x_1083, x_1085);
if (x_1086 == 0)
{
lean_dec_ref(x_1082);
x_996 = x_1084;
goto block_1080;
}
else
{
lean_object* x_1087; lean_object* x_1088; uint8_t x_1089; 
x_1087 = lean_box(x_188);
x_1088 = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(x_1088, 0, x_1087);
lean_ctor_set(x_1088, 1, x_1084);
x_1089 = lean_nat_dec_le(x_1085, x_1085);
if (x_1089 == 0)
{
if (x_1086 == 0)
{
lean_dec_ref(x_1088);
lean_dec_ref(x_1082);
x_996 = x_1084;
goto block_1080;
}
else
{
size_t x_1090; size_t x_1091; lean_object* x_1092; lean_object* x_1093; 
x_1090 = 0;
x_1091 = lean_usize_of_nat(x_1085);
x_1092 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(x_188, x_186, x_1082, x_1090, x_1091, x_1088);
lean_dec_ref(x_1082);
x_1093 = lean_ctor_get(x_1092, 1);
lean_inc(x_1093);
lean_dec_ref(x_1092);
x_996 = x_1093;
goto block_1080;
}
}
else
{
size_t x_1094; size_t x_1095; lean_object* x_1096; lean_object* x_1097; 
x_1094 = 0;
x_1095 = lean_usize_of_nat(x_1085);
x_1096 = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__9(x_188, x_186, x_1082, x_1094, x_1095, x_1088);
lean_dec_ref(x_1082);
x_1097 = lean_ctor_get(x_1096, 1);
lean_inc(x_1097);
lean_dec_ref(x_1096);
x_996 = x_1097;
goto block_1080;
}
}
block_1080:
{
size_t x_997; size_t x_998; lean_object* x_999; 
x_997 = lean_array_size(x_996);
x_998 = 0;
x_999 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__12(x_997, x_998, x_996);
if (lean_obj_tag(x_999) == 0)
{
lean_object* x_1000; lean_object* x_1001; lean_object* x_1002; lean_object* x_1003; lean_object* x_1004; lean_object* x_1005; lean_object* x_1006; 
x_1000 = lean_st_ref_get(x_7);
x_1001 = lean_ctor_get(x_1000, 0);
lean_inc_ref(x_1001);
lean_dec(x_1000);
x_1002 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1003 = l_Lean_Syntax_getKind(x_1);
x_1004 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1002, x_1001, x_1003);
x_1005 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_1006 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1004, x_1005, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1006) == 0)
{
uint8_t x_1007; 
x_1007 = !lean_is_exclusive(x_1006);
if (x_1007 == 0)
{
lean_object* x_1008; uint8_t x_1009; 
x_1008 = lean_ctor_get(x_1006, 0);
x_1009 = !lean_is_exclusive(x_1008);
if (x_1009 == 0)
{
lean_object* x_1010; lean_object* x_1011; 
x_1010 = lean_ctor_get(x_1008, 0);
x_1011 = lean_ctor_get(x_1008, 1);
lean_dec(x_1011);
if (lean_obj_tag(x_1010) == 0)
{
lean_object* x_1012; lean_object* x_1013; lean_object* x_1014; lean_object* x_1015; lean_object* x_1016; lean_object* x_1017; lean_object* x_1018; lean_object* x_1019; lean_object* x_1020; lean_object* x_1021; lean_object* x_1022; lean_object* x_1023; lean_object* x_1024; 
lean_free_object(x_1006);
x_1012 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1013 = l_Lean_MessageData_ofName(x_1003);
lean_inc_ref(x_1013);
lean_ctor_set_tag(x_1008, 7);
lean_ctor_set(x_1008, 1, x_1013);
lean_ctor_set(x_1008, 0, x_1012);
x_1014 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1015 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1015, 0, x_1008);
lean_ctor_set(x_1015, 1, x_1014);
x_1016 = l_Lean_MessageData_ofSyntax(x_1);
x_1017 = l_Lean_indentD(x_1016);
x_1018 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1018, 0, x_1015);
lean_ctor_set(x_1018, 1, x_1017);
x_1019 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1020 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1020, 0, x_1018);
lean_ctor_set(x_1020, 1, x_1019);
x_1021 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1021, 0, x_1020);
lean_ctor_set(x_1021, 1, x_1013);
x_1022 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1023 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1023, 0, x_1021);
lean_ctor_set(x_1023, 1, x_1022);
x_1024 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1023, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1024;
}
else
{
lean_object* x_1025; 
lean_free_object(x_1008);
lean_dec(x_1003);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1025 = lean_ctor_get(x_1010, 0);
lean_inc(x_1025);
lean_dec_ref(x_1010);
lean_ctor_set(x_1006, 0, x_1025);
return x_1006;
}
}
else
{
lean_object* x_1026; 
x_1026 = lean_ctor_get(x_1008, 0);
lean_inc(x_1026);
lean_dec(x_1008);
if (lean_obj_tag(x_1026) == 0)
{
lean_object* x_1027; lean_object* x_1028; lean_object* x_1029; lean_object* x_1030; lean_object* x_1031; lean_object* x_1032; lean_object* x_1033; lean_object* x_1034; lean_object* x_1035; lean_object* x_1036; lean_object* x_1037; lean_object* x_1038; lean_object* x_1039; lean_object* x_1040; 
lean_free_object(x_1006);
x_1027 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1028 = l_Lean_MessageData_ofName(x_1003);
lean_inc_ref(x_1028);
x_1029 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1029, 0, x_1027);
lean_ctor_set(x_1029, 1, x_1028);
x_1030 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1031 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1031, 0, x_1029);
lean_ctor_set(x_1031, 1, x_1030);
x_1032 = l_Lean_MessageData_ofSyntax(x_1);
x_1033 = l_Lean_indentD(x_1032);
x_1034 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1034, 0, x_1031);
lean_ctor_set(x_1034, 1, x_1033);
x_1035 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1036 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1036, 0, x_1034);
lean_ctor_set(x_1036, 1, x_1035);
x_1037 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1037, 0, x_1036);
lean_ctor_set(x_1037, 1, x_1028);
x_1038 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1039 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1039, 0, x_1037);
lean_ctor_set(x_1039, 1, x_1038);
x_1040 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1039, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1040;
}
else
{
lean_object* x_1041; 
lean_dec(x_1003);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1041 = lean_ctor_get(x_1026, 0);
lean_inc(x_1041);
lean_dec_ref(x_1026);
lean_ctor_set(x_1006, 0, x_1041);
return x_1006;
}
}
}
else
{
lean_object* x_1042; lean_object* x_1043; lean_object* x_1044; 
x_1042 = lean_ctor_get(x_1006, 0);
lean_inc(x_1042);
lean_dec(x_1006);
x_1043 = lean_ctor_get(x_1042, 0);
lean_inc(x_1043);
if (lean_is_exclusive(x_1042)) {
 lean_ctor_release(x_1042, 0);
 lean_ctor_release(x_1042, 1);
 x_1044 = x_1042;
} else {
 lean_dec_ref(x_1042);
 x_1044 = lean_box(0);
}
if (lean_obj_tag(x_1043) == 0)
{
lean_object* x_1045; lean_object* x_1046; lean_object* x_1047; lean_object* x_1048; lean_object* x_1049; lean_object* x_1050; lean_object* x_1051; lean_object* x_1052; lean_object* x_1053; lean_object* x_1054; lean_object* x_1055; lean_object* x_1056; lean_object* x_1057; lean_object* x_1058; 
x_1045 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1046 = l_Lean_MessageData_ofName(x_1003);
lean_inc_ref(x_1046);
if (lean_is_scalar(x_1044)) {
 x_1047 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1047 = x_1044;
 lean_ctor_set_tag(x_1047, 7);
}
lean_ctor_set(x_1047, 0, x_1045);
lean_ctor_set(x_1047, 1, x_1046);
x_1048 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1049 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1049, 0, x_1047);
lean_ctor_set(x_1049, 1, x_1048);
x_1050 = l_Lean_MessageData_ofSyntax(x_1);
x_1051 = l_Lean_indentD(x_1050);
x_1052 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1052, 0, x_1049);
lean_ctor_set(x_1052, 1, x_1051);
x_1053 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1054 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1054, 0, x_1052);
lean_ctor_set(x_1054, 1, x_1053);
x_1055 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1055, 0, x_1054);
lean_ctor_set(x_1055, 1, x_1046);
x_1056 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1057 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1057, 0, x_1055);
lean_ctor_set(x_1057, 1, x_1056);
x_1058 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1057, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1058;
}
else
{
lean_object* x_1059; lean_object* x_1060; 
lean_dec(x_1044);
lean_dec(x_1003);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1059 = lean_ctor_get(x_1043, 0);
lean_inc(x_1059);
lean_dec_ref(x_1043);
x_1060 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1060, 0, x_1059);
return x_1060;
}
}
}
else
{
uint8_t x_1061; 
lean_dec(x_1003);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1061 = !lean_is_exclusive(x_1006);
if (x_1061 == 0)
{
return x_1006;
}
else
{
lean_object* x_1062; lean_object* x_1063; 
x_1062 = lean_ctor_get(x_1006, 0);
lean_inc(x_1062);
lean_dec(x_1006);
x_1063 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1063, 0, x_1062);
return x_1063;
}
}
}
else
{
lean_object* x_1064; lean_object* x_1065; lean_object* x_1066; 
lean_dec_ref(x_999);
x_1064 = lean_unsigned_to_nat(3u);
x_1065 = l_Lean_Syntax_getArg(x_1, x_1064);
lean_dec(x_1);
x_1066 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_1065, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1066) == 0)
{
uint8_t x_1067; 
x_1067 = !lean_is_exclusive(x_1066);
if (x_1067 == 0)
{
lean_object* x_1068; uint8_t x_1069; 
x_1068 = lean_ctor_get(x_1066, 0);
x_1069 = !lean_is_exclusive(x_1068);
if (x_1069 == 0)
{
lean_object* x_1070; 
x_1070 = lean_ctor_get(x_1068, 0);
lean_dec(x_1070);
lean_ctor_set(x_1068, 0, x_995);
lean_ctor_set_uint8(x_1068, sizeof(void*)*2, x_186);
lean_ctor_set_uint8(x_1068, sizeof(void*)*2 + 1, x_186);
return x_1066;
}
else
{
uint8_t x_1071; lean_object* x_1072; lean_object* x_1073; 
x_1071 = lean_ctor_get_uint8(x_1068, sizeof(void*)*2 + 2);
x_1072 = lean_ctor_get(x_1068, 1);
lean_inc(x_1072);
lean_dec(x_1068);
x_1073 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_1073, 0, x_995);
lean_ctor_set(x_1073, 1, x_1072);
lean_ctor_set_uint8(x_1073, sizeof(void*)*2, x_186);
lean_ctor_set_uint8(x_1073, sizeof(void*)*2 + 1, x_186);
lean_ctor_set_uint8(x_1073, sizeof(void*)*2 + 2, x_1071);
lean_ctor_set(x_1066, 0, x_1073);
return x_1066;
}
}
else
{
lean_object* x_1074; uint8_t x_1075; lean_object* x_1076; lean_object* x_1077; lean_object* x_1078; lean_object* x_1079; 
x_1074 = lean_ctor_get(x_1066, 0);
lean_inc(x_1074);
lean_dec(x_1066);
x_1075 = lean_ctor_get_uint8(x_1074, sizeof(void*)*2 + 2);
x_1076 = lean_ctor_get(x_1074, 1);
lean_inc(x_1076);
if (lean_is_exclusive(x_1074)) {
 lean_ctor_release(x_1074, 0);
 lean_ctor_release(x_1074, 1);
 x_1077 = x_1074;
} else {
 lean_dec_ref(x_1074);
 x_1077 = lean_box(0);
}
if (lean_is_scalar(x_1077)) {
 x_1078 = lean_alloc_ctor(0, 2, 3);
} else {
 x_1078 = x_1077;
}
lean_ctor_set(x_1078, 0, x_995);
lean_ctor_set(x_1078, 1, x_1076);
lean_ctor_set_uint8(x_1078, sizeof(void*)*2, x_186);
lean_ctor_set_uint8(x_1078, sizeof(void*)*2 + 1, x_186);
lean_ctor_set_uint8(x_1078, sizeof(void*)*2 + 2, x_1075);
x_1079 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1079, 0, x_1078);
return x_1079;
}
}
else
{
return x_1066;
}
}
}
}
}
else
{
lean_object* x_1098; lean_object* x_1099; lean_object* x_1100; lean_object* x_1101; lean_object* x_1102; lean_object* x_1103; 
x_1098 = lean_unsigned_to_nat(1u);
x_1099 = lean_unsigned_to_nat(3u);
x_1100 = l_Lean_Syntax_getArg(x_1, x_1099);
lean_dec(x_1);
x_1101 = l_Lean_NameSet_empty;
x_1102 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_1102, 0, x_1098);
lean_ctor_set(x_1102, 1, x_1101);
lean_ctor_set_uint8(x_1102, sizeof(void*)*2, x_184);
lean_ctor_set_uint8(x_1102, sizeof(void*)*2 + 1, x_184);
lean_ctor_set_uint8(x_1102, sizeof(void*)*2 + 2, x_184);
x_1103 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_1100, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1103) == 0)
{
uint8_t x_1104; 
x_1104 = !lean_is_exclusive(x_1103);
if (x_1104 == 0)
{
lean_object* x_1105; lean_object* x_1106; 
x_1105 = lean_ctor_get(x_1103, 0);
x_1106 = l_Lean_Elab_Do_ControlInfo_alternative(x_1102, x_1105);
lean_ctor_set(x_1103, 0, x_1106);
return x_1103;
}
else
{
lean_object* x_1107; lean_object* x_1108; lean_object* x_1109; 
x_1107 = lean_ctor_get(x_1103, 0);
lean_inc(x_1107);
lean_dec(x_1103);
x_1108 = l_Lean_Elab_Do_ControlInfo_alternative(x_1102, x_1107);
x_1109 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1109, 0, x_1108);
return x_1109;
}
}
else
{
lean_dec_ref(x_1102);
return x_1103;
}
}
}
else
{
lean_object* x_1110; lean_object* x_1111; lean_object* x_1112; size_t x_1113; size_t x_1114; lean_object* x_1115; 
x_1110 = lean_unsigned_to_nat(4u);
x_1111 = l_Lean_Syntax_getArg(x_1, x_1110);
x_1112 = l_Lean_Syntax_getArgs(x_1111);
lean_dec(x_1111);
x_1113 = lean_array_size(x_1112);
x_1114 = 0;
x_1115 = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13(x_1113, x_1114, x_1112);
if (lean_obj_tag(x_1115) == 0)
{
lean_object* x_1116; lean_object* x_1117; lean_object* x_1118; lean_object* x_1119; lean_object* x_1120; lean_object* x_1121; lean_object* x_1122; 
x_1116 = lean_st_ref_get(x_7);
x_1117 = lean_ctor_get(x_1116, 0);
lean_inc_ref(x_1117);
lean_dec(x_1116);
x_1118 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1119 = l_Lean_Syntax_getKind(x_1);
x_1120 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1118, x_1117, x_1119);
x_1121 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_1122 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1120, x_1121, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1122) == 0)
{
uint8_t x_1123; 
x_1123 = !lean_is_exclusive(x_1122);
if (x_1123 == 0)
{
lean_object* x_1124; uint8_t x_1125; 
x_1124 = lean_ctor_get(x_1122, 0);
x_1125 = !lean_is_exclusive(x_1124);
if (x_1125 == 0)
{
lean_object* x_1126; lean_object* x_1127; 
x_1126 = lean_ctor_get(x_1124, 0);
x_1127 = lean_ctor_get(x_1124, 1);
lean_dec(x_1127);
if (lean_obj_tag(x_1126) == 0)
{
lean_object* x_1128; lean_object* x_1129; lean_object* x_1130; lean_object* x_1131; lean_object* x_1132; lean_object* x_1133; lean_object* x_1134; lean_object* x_1135; lean_object* x_1136; lean_object* x_1137; lean_object* x_1138; lean_object* x_1139; lean_object* x_1140; 
lean_free_object(x_1122);
x_1128 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1129 = l_Lean_MessageData_ofName(x_1119);
lean_inc_ref(x_1129);
lean_ctor_set_tag(x_1124, 7);
lean_ctor_set(x_1124, 1, x_1129);
lean_ctor_set(x_1124, 0, x_1128);
x_1130 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1131 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1131, 0, x_1124);
lean_ctor_set(x_1131, 1, x_1130);
x_1132 = l_Lean_MessageData_ofSyntax(x_1);
x_1133 = l_Lean_indentD(x_1132);
x_1134 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1134, 0, x_1131);
lean_ctor_set(x_1134, 1, x_1133);
x_1135 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1136 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1136, 0, x_1134);
lean_ctor_set(x_1136, 1, x_1135);
x_1137 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1137, 0, x_1136);
lean_ctor_set(x_1137, 1, x_1129);
x_1138 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1139 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1139, 0, x_1137);
lean_ctor_set(x_1139, 1, x_1138);
x_1140 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1139, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1140;
}
else
{
lean_object* x_1141; 
lean_free_object(x_1124);
lean_dec(x_1119);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1141 = lean_ctor_get(x_1126, 0);
lean_inc(x_1141);
lean_dec_ref(x_1126);
lean_ctor_set(x_1122, 0, x_1141);
return x_1122;
}
}
else
{
lean_object* x_1142; 
x_1142 = lean_ctor_get(x_1124, 0);
lean_inc(x_1142);
lean_dec(x_1124);
if (lean_obj_tag(x_1142) == 0)
{
lean_object* x_1143; lean_object* x_1144; lean_object* x_1145; lean_object* x_1146; lean_object* x_1147; lean_object* x_1148; lean_object* x_1149; lean_object* x_1150; lean_object* x_1151; lean_object* x_1152; lean_object* x_1153; lean_object* x_1154; lean_object* x_1155; lean_object* x_1156; 
lean_free_object(x_1122);
x_1143 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1144 = l_Lean_MessageData_ofName(x_1119);
lean_inc_ref(x_1144);
x_1145 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1145, 0, x_1143);
lean_ctor_set(x_1145, 1, x_1144);
x_1146 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1147 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1147, 0, x_1145);
lean_ctor_set(x_1147, 1, x_1146);
x_1148 = l_Lean_MessageData_ofSyntax(x_1);
x_1149 = l_Lean_indentD(x_1148);
x_1150 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1150, 0, x_1147);
lean_ctor_set(x_1150, 1, x_1149);
x_1151 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1152 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1152, 0, x_1150);
lean_ctor_set(x_1152, 1, x_1151);
x_1153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1153, 0, x_1152);
lean_ctor_set(x_1153, 1, x_1144);
x_1154 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1155 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1155, 0, x_1153);
lean_ctor_set(x_1155, 1, x_1154);
x_1156 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1155, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1156;
}
else
{
lean_object* x_1157; 
lean_dec(x_1119);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1157 = lean_ctor_get(x_1142, 0);
lean_inc(x_1157);
lean_dec_ref(x_1142);
lean_ctor_set(x_1122, 0, x_1157);
return x_1122;
}
}
}
else
{
lean_object* x_1158; lean_object* x_1159; lean_object* x_1160; 
x_1158 = lean_ctor_get(x_1122, 0);
lean_inc(x_1158);
lean_dec(x_1122);
x_1159 = lean_ctor_get(x_1158, 0);
lean_inc(x_1159);
if (lean_is_exclusive(x_1158)) {
 lean_ctor_release(x_1158, 0);
 lean_ctor_release(x_1158, 1);
 x_1160 = x_1158;
} else {
 lean_dec_ref(x_1158);
 x_1160 = lean_box(0);
}
if (lean_obj_tag(x_1159) == 0)
{
lean_object* x_1161; lean_object* x_1162; lean_object* x_1163; lean_object* x_1164; lean_object* x_1165; lean_object* x_1166; lean_object* x_1167; lean_object* x_1168; lean_object* x_1169; lean_object* x_1170; lean_object* x_1171; lean_object* x_1172; lean_object* x_1173; lean_object* x_1174; 
x_1161 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1162 = l_Lean_MessageData_ofName(x_1119);
lean_inc_ref(x_1162);
if (lean_is_scalar(x_1160)) {
 x_1163 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1163 = x_1160;
 lean_ctor_set_tag(x_1163, 7);
}
lean_ctor_set(x_1163, 0, x_1161);
lean_ctor_set(x_1163, 1, x_1162);
x_1164 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1165 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1165, 0, x_1163);
lean_ctor_set(x_1165, 1, x_1164);
x_1166 = l_Lean_MessageData_ofSyntax(x_1);
x_1167 = l_Lean_indentD(x_1166);
x_1168 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1168, 0, x_1165);
lean_ctor_set(x_1168, 1, x_1167);
x_1169 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1170 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1170, 0, x_1168);
lean_ctor_set(x_1170, 1, x_1169);
x_1171 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1171, 0, x_1170);
lean_ctor_set(x_1171, 1, x_1162);
x_1172 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1173 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1173, 0, x_1171);
lean_ctor_set(x_1173, 1, x_1172);
x_1174 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1173, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1174;
}
else
{
lean_object* x_1175; lean_object* x_1176; 
lean_dec(x_1160);
lean_dec(x_1119);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1175 = lean_ctor_get(x_1159, 0);
lean_inc(x_1175);
lean_dec_ref(x_1159);
x_1176 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1176, 0, x_1175);
return x_1176;
}
}
}
else
{
uint8_t x_1177; 
lean_dec(x_1119);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1177 = !lean_is_exclusive(x_1122);
if (x_1177 == 0)
{
return x_1122;
}
else
{
lean_object* x_1178; lean_object* x_1179; 
x_1178 = lean_ctor_get(x_1122, 0);
lean_inc(x_1178);
lean_dec(x_1122);
x_1179 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1179, 0, x_1178);
return x_1179;
}
}
}
else
{
uint8_t x_1180; 
x_1180 = !lean_is_exclusive(x_1115);
if (x_1180 == 0)
{
lean_object* x_1181; lean_object* x_1182; lean_object* x_1183; lean_object* x_1184; lean_object* x_1185; lean_object* x_1186; lean_object* x_1187; lean_object* x_1188; lean_object* x_1189; lean_object* x_1190; lean_object* x_1191; lean_object* x_1206; lean_object* x_1207; uint8_t x_1208; 
x_1181 = lean_ctor_get(x_1115, 0);
x_1182 = lean_unsigned_to_nat(3u);
x_1183 = l_Lean_Syntax_getArg(x_1, x_1182);
x_1206 = lean_unsigned_to_nat(5u);
x_1207 = l_Lean_Syntax_getArg(x_1, x_1206);
x_1208 = l_Lean_Syntax_isNone(x_1207);
if (x_1208 == 0)
{
lean_object* x_1209; uint8_t x_1210; 
x_1209 = lean_unsigned_to_nat(2u);
lean_inc(x_1207);
x_1210 = l_Lean_Syntax_matchesNull(x_1207, x_1209);
if (x_1210 == 0)
{
lean_object* x_1211; lean_object* x_1212; lean_object* x_1213; lean_object* x_1214; lean_object* x_1215; lean_object* x_1216; lean_object* x_1217; 
lean_dec(x_1207);
lean_dec(x_1183);
lean_free_object(x_1115);
lean_dec(x_1181);
x_1211 = lean_st_ref_get(x_7);
x_1212 = lean_ctor_get(x_1211, 0);
lean_inc_ref(x_1212);
lean_dec(x_1211);
x_1213 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1214 = l_Lean_Syntax_getKind(x_1);
x_1215 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1213, x_1212, x_1214);
x_1216 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_1217 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1215, x_1216, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1217) == 0)
{
uint8_t x_1218; 
x_1218 = !lean_is_exclusive(x_1217);
if (x_1218 == 0)
{
lean_object* x_1219; uint8_t x_1220; 
x_1219 = lean_ctor_get(x_1217, 0);
x_1220 = !lean_is_exclusive(x_1219);
if (x_1220 == 0)
{
lean_object* x_1221; lean_object* x_1222; 
x_1221 = lean_ctor_get(x_1219, 0);
x_1222 = lean_ctor_get(x_1219, 1);
lean_dec(x_1222);
if (lean_obj_tag(x_1221) == 0)
{
lean_object* x_1223; lean_object* x_1224; lean_object* x_1225; lean_object* x_1226; lean_object* x_1227; lean_object* x_1228; lean_object* x_1229; lean_object* x_1230; lean_object* x_1231; lean_object* x_1232; lean_object* x_1233; lean_object* x_1234; lean_object* x_1235; 
lean_free_object(x_1217);
x_1223 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1224 = l_Lean_MessageData_ofName(x_1214);
lean_inc_ref(x_1224);
lean_ctor_set_tag(x_1219, 7);
lean_ctor_set(x_1219, 1, x_1224);
lean_ctor_set(x_1219, 0, x_1223);
x_1225 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1226, 0, x_1219);
lean_ctor_set(x_1226, 1, x_1225);
x_1227 = l_Lean_MessageData_ofSyntax(x_1);
x_1228 = l_Lean_indentD(x_1227);
x_1229 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1229, 0, x_1226);
lean_ctor_set(x_1229, 1, x_1228);
x_1230 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1231 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1231, 0, x_1229);
lean_ctor_set(x_1231, 1, x_1230);
x_1232 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1232, 0, x_1231);
lean_ctor_set(x_1232, 1, x_1224);
x_1233 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1234, 0, x_1232);
lean_ctor_set(x_1234, 1, x_1233);
x_1235 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1234, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1235;
}
else
{
lean_object* x_1236; 
lean_free_object(x_1219);
lean_dec(x_1214);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1236 = lean_ctor_get(x_1221, 0);
lean_inc(x_1236);
lean_dec_ref(x_1221);
lean_ctor_set(x_1217, 0, x_1236);
return x_1217;
}
}
else
{
lean_object* x_1237; 
x_1237 = lean_ctor_get(x_1219, 0);
lean_inc(x_1237);
lean_dec(x_1219);
if (lean_obj_tag(x_1237) == 0)
{
lean_object* x_1238; lean_object* x_1239; lean_object* x_1240; lean_object* x_1241; lean_object* x_1242; lean_object* x_1243; lean_object* x_1244; lean_object* x_1245; lean_object* x_1246; lean_object* x_1247; lean_object* x_1248; lean_object* x_1249; lean_object* x_1250; lean_object* x_1251; 
lean_free_object(x_1217);
x_1238 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1239 = l_Lean_MessageData_ofName(x_1214);
lean_inc_ref(x_1239);
x_1240 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1240, 0, x_1238);
lean_ctor_set(x_1240, 1, x_1239);
x_1241 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1242, 0, x_1240);
lean_ctor_set(x_1242, 1, x_1241);
x_1243 = l_Lean_MessageData_ofSyntax(x_1);
x_1244 = l_Lean_indentD(x_1243);
x_1245 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1245, 0, x_1242);
lean_ctor_set(x_1245, 1, x_1244);
x_1246 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1247 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1247, 0, x_1245);
lean_ctor_set(x_1247, 1, x_1246);
x_1248 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1248, 0, x_1247);
lean_ctor_set(x_1248, 1, x_1239);
x_1249 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1250 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1250, 0, x_1248);
lean_ctor_set(x_1250, 1, x_1249);
x_1251 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1250, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1251;
}
else
{
lean_object* x_1252; 
lean_dec(x_1214);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1252 = lean_ctor_get(x_1237, 0);
lean_inc(x_1252);
lean_dec_ref(x_1237);
lean_ctor_set(x_1217, 0, x_1252);
return x_1217;
}
}
}
else
{
lean_object* x_1253; lean_object* x_1254; lean_object* x_1255; 
x_1253 = lean_ctor_get(x_1217, 0);
lean_inc(x_1253);
lean_dec(x_1217);
x_1254 = lean_ctor_get(x_1253, 0);
lean_inc(x_1254);
if (lean_is_exclusive(x_1253)) {
 lean_ctor_release(x_1253, 0);
 lean_ctor_release(x_1253, 1);
 x_1255 = x_1253;
} else {
 lean_dec_ref(x_1253);
 x_1255 = lean_box(0);
}
if (lean_obj_tag(x_1254) == 0)
{
lean_object* x_1256; lean_object* x_1257; lean_object* x_1258; lean_object* x_1259; lean_object* x_1260; lean_object* x_1261; lean_object* x_1262; lean_object* x_1263; lean_object* x_1264; lean_object* x_1265; lean_object* x_1266; lean_object* x_1267; lean_object* x_1268; lean_object* x_1269; 
x_1256 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1257 = l_Lean_MessageData_ofName(x_1214);
lean_inc_ref(x_1257);
if (lean_is_scalar(x_1255)) {
 x_1258 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1258 = x_1255;
 lean_ctor_set_tag(x_1258, 7);
}
lean_ctor_set(x_1258, 0, x_1256);
lean_ctor_set(x_1258, 1, x_1257);
x_1259 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1260 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1260, 0, x_1258);
lean_ctor_set(x_1260, 1, x_1259);
x_1261 = l_Lean_MessageData_ofSyntax(x_1);
x_1262 = l_Lean_indentD(x_1261);
x_1263 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1263, 0, x_1260);
lean_ctor_set(x_1263, 1, x_1262);
x_1264 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1265 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1265, 0, x_1263);
lean_ctor_set(x_1265, 1, x_1264);
x_1266 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1266, 0, x_1265);
lean_ctor_set(x_1266, 1, x_1257);
x_1267 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1268 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1268, 0, x_1266);
lean_ctor_set(x_1268, 1, x_1267);
x_1269 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1268, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1269;
}
else
{
lean_object* x_1270; lean_object* x_1271; 
lean_dec(x_1255);
lean_dec(x_1214);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1270 = lean_ctor_get(x_1254, 0);
lean_inc(x_1270);
lean_dec_ref(x_1254);
x_1271 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1271, 0, x_1270);
return x_1271;
}
}
}
else
{
uint8_t x_1272; 
lean_dec(x_1214);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1272 = !lean_is_exclusive(x_1217);
if (x_1272 == 0)
{
return x_1217;
}
else
{
lean_object* x_1273; lean_object* x_1274; 
x_1273 = lean_ctor_get(x_1217, 0);
lean_inc(x_1273);
lean_dec(x_1217);
x_1274 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1274, 0, x_1273);
return x_1274;
}
}
}
else
{
lean_object* x_1275; lean_object* x_1276; 
lean_dec(x_1);
x_1275 = lean_unsigned_to_nat(1u);
x_1276 = l_Lean_Syntax_getArg(x_1207, x_1275);
lean_dec(x_1207);
lean_ctor_set(x_1115, 0, x_1276);
x_1184 = x_1115;
x_1185 = x_2;
x_1186 = x_3;
x_1187 = x_4;
x_1188 = x_5;
x_1189 = x_6;
x_1190 = x_7;
x_1191 = lean_box(0);
goto block_1205;
}
}
else
{
lean_object* x_1277; 
lean_dec(x_1207);
lean_free_object(x_1115);
lean_dec(x_1);
x_1277 = lean_box(0);
x_1184 = x_1277;
x_1185 = x_2;
x_1186 = x_3;
x_1187 = x_4;
x_1188 = x_5;
x_1189 = x_6;
x_1190 = x_7;
x_1191 = lean_box(0);
goto block_1205;
}
block_1205:
{
lean_object* x_1192; 
lean_inc(x_1190);
lean_inc_ref(x_1189);
lean_inc(x_1188);
lean_inc_ref(x_1187);
lean_inc(x_1186);
lean_inc_ref(x_1185);
x_1192 = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(x_1184, x_1185, x_1186, x_1187, x_1188, x_1189, x_1190);
if (lean_obj_tag(x_1192) == 0)
{
lean_object* x_1193; lean_object* x_1194; size_t x_1195; lean_object* x_1196; 
x_1193 = lean_ctor_get(x_1192, 0);
lean_inc(x_1193);
lean_dec_ref(x_1192);
x_1194 = l_Array_reverse___redArg(x_1181);
x_1195 = lean_array_size(x_1194);
lean_inc(x_1190);
lean_inc_ref(x_1189);
lean_inc(x_1188);
lean_inc_ref(x_1187);
lean_inc(x_1186);
lean_inc_ref(x_1185);
x_1196 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(x_1194, x_1195, x_1114, x_1193, x_1185, x_1186, x_1187, x_1188, x_1189, x_1190);
lean_dec_ref(x_1194);
if (lean_obj_tag(x_1196) == 0)
{
lean_object* x_1197; lean_object* x_1198; 
x_1197 = lean_ctor_get(x_1196, 0);
lean_inc(x_1197);
lean_dec_ref(x_1196);
x_1198 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_1183, x_1185, x_1186, x_1187, x_1188, x_1189, x_1190);
if (lean_obj_tag(x_1198) == 0)
{
uint8_t x_1199; 
x_1199 = !lean_is_exclusive(x_1198);
if (x_1199 == 0)
{
lean_object* x_1200; lean_object* x_1201; 
x_1200 = lean_ctor_get(x_1198, 0);
x_1201 = l_Lean_Elab_Do_ControlInfo_alternative(x_1200, x_1197);
lean_ctor_set(x_1198, 0, x_1201);
return x_1198;
}
else
{
lean_object* x_1202; lean_object* x_1203; lean_object* x_1204; 
x_1202 = lean_ctor_get(x_1198, 0);
lean_inc(x_1202);
lean_dec(x_1198);
x_1203 = l_Lean_Elab_Do_ControlInfo_alternative(x_1202, x_1197);
x_1204 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1204, 0, x_1203);
return x_1204;
}
}
else
{
lean_dec(x_1197);
return x_1198;
}
}
else
{
lean_dec(x_1190);
lean_dec_ref(x_1189);
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1183);
return x_1196;
}
}
else
{
lean_dec(x_1190);
lean_dec_ref(x_1189);
lean_dec(x_1188);
lean_dec_ref(x_1187);
lean_dec(x_1186);
lean_dec_ref(x_1185);
lean_dec(x_1183);
lean_dec(x_1181);
return x_1192;
}
}
}
else
{
lean_object* x_1278; lean_object* x_1279; lean_object* x_1280; lean_object* x_1281; lean_object* x_1282; lean_object* x_1283; lean_object* x_1284; lean_object* x_1285; lean_object* x_1286; lean_object* x_1287; lean_object* x_1288; lean_object* x_1301; lean_object* x_1302; uint8_t x_1303; 
x_1278 = lean_ctor_get(x_1115, 0);
lean_inc(x_1278);
lean_dec(x_1115);
x_1279 = lean_unsigned_to_nat(3u);
x_1280 = l_Lean_Syntax_getArg(x_1, x_1279);
x_1301 = lean_unsigned_to_nat(5u);
x_1302 = l_Lean_Syntax_getArg(x_1, x_1301);
x_1303 = l_Lean_Syntax_isNone(x_1302);
if (x_1303 == 0)
{
lean_object* x_1304; uint8_t x_1305; 
x_1304 = lean_unsigned_to_nat(2u);
lean_inc(x_1302);
x_1305 = l_Lean_Syntax_matchesNull(x_1302, x_1304);
if (x_1305 == 0)
{
lean_object* x_1306; lean_object* x_1307; lean_object* x_1308; lean_object* x_1309; lean_object* x_1310; lean_object* x_1311; lean_object* x_1312; 
lean_dec(x_1302);
lean_dec(x_1280);
lean_dec(x_1278);
x_1306 = lean_st_ref_get(x_7);
x_1307 = lean_ctor_get(x_1306, 0);
lean_inc_ref(x_1307);
lean_dec(x_1306);
x_1308 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1309 = l_Lean_Syntax_getKind(x_1);
x_1310 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1308, x_1307, x_1309);
x_1311 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_1312 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1310, x_1311, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1312) == 0)
{
lean_object* x_1313; lean_object* x_1314; lean_object* x_1315; lean_object* x_1316; 
x_1313 = lean_ctor_get(x_1312, 0);
lean_inc(x_1313);
if (lean_is_exclusive(x_1312)) {
 lean_ctor_release(x_1312, 0);
 x_1314 = x_1312;
} else {
 lean_dec_ref(x_1312);
 x_1314 = lean_box(0);
}
x_1315 = lean_ctor_get(x_1313, 0);
lean_inc(x_1315);
if (lean_is_exclusive(x_1313)) {
 lean_ctor_release(x_1313, 0);
 lean_ctor_release(x_1313, 1);
 x_1316 = x_1313;
} else {
 lean_dec_ref(x_1313);
 x_1316 = lean_box(0);
}
if (lean_obj_tag(x_1315) == 0)
{
lean_object* x_1317; lean_object* x_1318; lean_object* x_1319; lean_object* x_1320; lean_object* x_1321; lean_object* x_1322; lean_object* x_1323; lean_object* x_1324; lean_object* x_1325; lean_object* x_1326; lean_object* x_1327; lean_object* x_1328; lean_object* x_1329; lean_object* x_1330; 
lean_dec(x_1314);
x_1317 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1318 = l_Lean_MessageData_ofName(x_1309);
lean_inc_ref(x_1318);
if (lean_is_scalar(x_1316)) {
 x_1319 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1319 = x_1316;
 lean_ctor_set_tag(x_1319, 7);
}
lean_ctor_set(x_1319, 0, x_1317);
lean_ctor_set(x_1319, 1, x_1318);
x_1320 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1321 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1321, 0, x_1319);
lean_ctor_set(x_1321, 1, x_1320);
x_1322 = l_Lean_MessageData_ofSyntax(x_1);
x_1323 = l_Lean_indentD(x_1322);
x_1324 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1324, 0, x_1321);
lean_ctor_set(x_1324, 1, x_1323);
x_1325 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1326 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1326, 0, x_1324);
lean_ctor_set(x_1326, 1, x_1325);
x_1327 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1327, 0, x_1326);
lean_ctor_set(x_1327, 1, x_1318);
x_1328 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1329 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1329, 0, x_1327);
lean_ctor_set(x_1329, 1, x_1328);
x_1330 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1329, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1330;
}
else
{
lean_object* x_1331; lean_object* x_1332; 
lean_dec(x_1316);
lean_dec(x_1309);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1331 = lean_ctor_get(x_1315, 0);
lean_inc(x_1331);
lean_dec_ref(x_1315);
if (lean_is_scalar(x_1314)) {
 x_1332 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1332 = x_1314;
}
lean_ctor_set(x_1332, 0, x_1331);
return x_1332;
}
}
else
{
lean_object* x_1333; lean_object* x_1334; lean_object* x_1335; 
lean_dec(x_1309);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1333 = lean_ctor_get(x_1312, 0);
lean_inc(x_1333);
if (lean_is_exclusive(x_1312)) {
 lean_ctor_release(x_1312, 0);
 x_1334 = x_1312;
} else {
 lean_dec_ref(x_1312);
 x_1334 = lean_box(0);
}
if (lean_is_scalar(x_1334)) {
 x_1335 = lean_alloc_ctor(1, 1, 0);
} else {
 x_1335 = x_1334;
}
lean_ctor_set(x_1335, 0, x_1333);
return x_1335;
}
}
else
{
lean_object* x_1336; lean_object* x_1337; lean_object* x_1338; 
lean_dec(x_1);
x_1336 = lean_unsigned_to_nat(1u);
x_1337 = l_Lean_Syntax_getArg(x_1302, x_1336);
lean_dec(x_1302);
x_1338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1338, 0, x_1337);
x_1281 = x_1338;
x_1282 = x_2;
x_1283 = x_3;
x_1284 = x_4;
x_1285 = x_5;
x_1286 = x_6;
x_1287 = x_7;
x_1288 = lean_box(0);
goto block_1300;
}
}
else
{
lean_object* x_1339; 
lean_dec(x_1302);
lean_dec(x_1);
x_1339 = lean_box(0);
x_1281 = x_1339;
x_1282 = x_2;
x_1283 = x_3;
x_1284 = x_4;
x_1285 = x_5;
x_1286 = x_6;
x_1287 = x_7;
x_1288 = lean_box(0);
goto block_1300;
}
block_1300:
{
lean_object* x_1289; 
lean_inc(x_1287);
lean_inc_ref(x_1286);
lean_inc(x_1285);
lean_inc_ref(x_1284);
lean_inc(x_1283);
lean_inc_ref(x_1282);
x_1289 = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(x_1281, x_1282, x_1283, x_1284, x_1285, x_1286, x_1287);
if (lean_obj_tag(x_1289) == 0)
{
lean_object* x_1290; lean_object* x_1291; size_t x_1292; lean_object* x_1293; 
x_1290 = lean_ctor_get(x_1289, 0);
lean_inc(x_1290);
lean_dec_ref(x_1289);
x_1291 = l_Array_reverse___redArg(x_1278);
x_1292 = lean_array_size(x_1291);
lean_inc(x_1287);
lean_inc_ref(x_1286);
lean_inc(x_1285);
lean_inc_ref(x_1284);
lean_inc(x_1283);
lean_inc_ref(x_1282);
x_1293 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(x_1291, x_1292, x_1114, x_1290, x_1282, x_1283, x_1284, x_1285, x_1286, x_1287);
lean_dec_ref(x_1291);
if (lean_obj_tag(x_1293) == 0)
{
lean_object* x_1294; lean_object* x_1295; 
x_1294 = lean_ctor_get(x_1293, 0);
lean_inc(x_1294);
lean_dec_ref(x_1293);
x_1295 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_1280, x_1282, x_1283, x_1284, x_1285, x_1286, x_1287);
if (lean_obj_tag(x_1295) == 0)
{
lean_object* x_1296; lean_object* x_1297; lean_object* x_1298; lean_object* x_1299; 
x_1296 = lean_ctor_get(x_1295, 0);
lean_inc(x_1296);
if (lean_is_exclusive(x_1295)) {
 lean_ctor_release(x_1295, 0);
 x_1297 = x_1295;
} else {
 lean_dec_ref(x_1295);
 x_1297 = lean_box(0);
}
x_1298 = l_Lean_Elab_Do_ControlInfo_alternative(x_1296, x_1294);
if (lean_is_scalar(x_1297)) {
 x_1299 = lean_alloc_ctor(0, 1, 0);
} else {
 x_1299 = x_1297;
}
lean_ctor_set(x_1299, 0, x_1298);
return x_1299;
}
else
{
lean_dec(x_1294);
return x_1295;
}
}
else
{
lean_dec(x_1287);
lean_dec_ref(x_1286);
lean_dec(x_1285);
lean_dec_ref(x_1284);
lean_dec(x_1283);
lean_dec_ref(x_1282);
lean_dec(x_1280);
return x_1293;
}
}
else
{
lean_dec(x_1287);
lean_dec_ref(x_1286);
lean_dec(x_1285);
lean_dec_ref(x_1284);
lean_dec(x_1283);
lean_dec_ref(x_1282);
lean_dec(x_1280);
lean_dec(x_1278);
return x_1289;
}
}
}
}
}
}
else
{
lean_object* x_1340; lean_object* x_1341; lean_object* x_1342; lean_object* x_1343; lean_object* x_1344; lean_object* x_1345; lean_object* x_1346; lean_object* x_1347; lean_object* x_1348; lean_object* x_1425; lean_object* x_1426; lean_object* x_1427; lean_object* x_1428; lean_object* x_1429; lean_object* x_1430; lean_object* x_1431; lean_object* x_1568; uint8_t x_1569; 
x_1340 = lean_unsigned_to_nat(0u);
x_1341 = lean_unsigned_to_nat(1u);
x_1568 = l_Lean_Syntax_getArg(x_1, x_1341);
x_1569 = l_Lean_Syntax_isNone(x_1568);
if (x_1569 == 0)
{
uint8_t x_1570; 
lean_inc(x_1568);
x_1570 = l_Lean_Syntax_matchesNull(x_1568, x_1341);
if (x_1570 == 0)
{
lean_object* x_1571; lean_object* x_1572; lean_object* x_1573; lean_object* x_1574; lean_object* x_1575; lean_object* x_1576; lean_object* x_1577; 
lean_dec(x_1568);
x_1571 = lean_st_ref_get(x_7);
x_1572 = lean_ctor_get(x_1571, 0);
lean_inc_ref(x_1572);
lean_dec(x_1571);
x_1573 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1574 = l_Lean_Syntax_getKind(x_1);
x_1575 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1573, x_1572, x_1574);
x_1576 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_1577 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1575, x_1576, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1577) == 0)
{
uint8_t x_1578; 
x_1578 = !lean_is_exclusive(x_1577);
if (x_1578 == 0)
{
lean_object* x_1579; uint8_t x_1580; 
x_1579 = lean_ctor_get(x_1577, 0);
x_1580 = !lean_is_exclusive(x_1579);
if (x_1580 == 0)
{
lean_object* x_1581; lean_object* x_1582; 
x_1581 = lean_ctor_get(x_1579, 0);
x_1582 = lean_ctor_get(x_1579, 1);
lean_dec(x_1582);
if (lean_obj_tag(x_1581) == 0)
{
lean_object* x_1583; lean_object* x_1584; lean_object* x_1585; lean_object* x_1586; lean_object* x_1587; lean_object* x_1588; lean_object* x_1589; lean_object* x_1590; lean_object* x_1591; lean_object* x_1592; lean_object* x_1593; lean_object* x_1594; lean_object* x_1595; 
lean_free_object(x_1577);
x_1583 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1584 = l_Lean_MessageData_ofName(x_1574);
lean_inc_ref(x_1584);
lean_ctor_set_tag(x_1579, 7);
lean_ctor_set(x_1579, 1, x_1584);
lean_ctor_set(x_1579, 0, x_1583);
x_1585 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1586 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1586, 0, x_1579);
lean_ctor_set(x_1586, 1, x_1585);
x_1587 = l_Lean_MessageData_ofSyntax(x_1);
x_1588 = l_Lean_indentD(x_1587);
x_1589 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1589, 0, x_1586);
lean_ctor_set(x_1589, 1, x_1588);
x_1590 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1591 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1591, 0, x_1589);
lean_ctor_set(x_1591, 1, x_1590);
x_1592 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1592, 0, x_1591);
lean_ctor_set(x_1592, 1, x_1584);
x_1593 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1594 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1594, 0, x_1592);
lean_ctor_set(x_1594, 1, x_1593);
x_1595 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1594, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1595;
}
else
{
lean_object* x_1596; 
lean_free_object(x_1579);
lean_dec(x_1574);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1596 = lean_ctor_get(x_1581, 0);
lean_inc(x_1596);
lean_dec_ref(x_1581);
lean_ctor_set(x_1577, 0, x_1596);
return x_1577;
}
}
else
{
lean_object* x_1597; 
x_1597 = lean_ctor_get(x_1579, 0);
lean_inc(x_1597);
lean_dec(x_1579);
if (lean_obj_tag(x_1597) == 0)
{
lean_object* x_1598; lean_object* x_1599; lean_object* x_1600; lean_object* x_1601; lean_object* x_1602; lean_object* x_1603; lean_object* x_1604; lean_object* x_1605; lean_object* x_1606; lean_object* x_1607; lean_object* x_1608; lean_object* x_1609; lean_object* x_1610; lean_object* x_1611; 
lean_free_object(x_1577);
x_1598 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1599 = l_Lean_MessageData_ofName(x_1574);
lean_inc_ref(x_1599);
x_1600 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1600, 0, x_1598);
lean_ctor_set(x_1600, 1, x_1599);
x_1601 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1602 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1602, 0, x_1600);
lean_ctor_set(x_1602, 1, x_1601);
x_1603 = l_Lean_MessageData_ofSyntax(x_1);
x_1604 = l_Lean_indentD(x_1603);
x_1605 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1605, 0, x_1602);
lean_ctor_set(x_1605, 1, x_1604);
x_1606 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1607 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1607, 0, x_1605);
lean_ctor_set(x_1607, 1, x_1606);
x_1608 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1608, 0, x_1607);
lean_ctor_set(x_1608, 1, x_1599);
x_1609 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1610 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1610, 0, x_1608);
lean_ctor_set(x_1610, 1, x_1609);
x_1611 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1610, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1611;
}
else
{
lean_object* x_1612; 
lean_dec(x_1574);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1612 = lean_ctor_get(x_1597, 0);
lean_inc(x_1612);
lean_dec_ref(x_1597);
lean_ctor_set(x_1577, 0, x_1612);
return x_1577;
}
}
}
else
{
lean_object* x_1613; lean_object* x_1614; lean_object* x_1615; 
x_1613 = lean_ctor_get(x_1577, 0);
lean_inc(x_1613);
lean_dec(x_1577);
x_1614 = lean_ctor_get(x_1613, 0);
lean_inc(x_1614);
if (lean_is_exclusive(x_1613)) {
 lean_ctor_release(x_1613, 0);
 lean_ctor_release(x_1613, 1);
 x_1615 = x_1613;
} else {
 lean_dec_ref(x_1613);
 x_1615 = lean_box(0);
}
if (lean_obj_tag(x_1614) == 0)
{
lean_object* x_1616; lean_object* x_1617; lean_object* x_1618; lean_object* x_1619; lean_object* x_1620; lean_object* x_1621; lean_object* x_1622; lean_object* x_1623; lean_object* x_1624; lean_object* x_1625; lean_object* x_1626; lean_object* x_1627; lean_object* x_1628; lean_object* x_1629; 
x_1616 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1617 = l_Lean_MessageData_ofName(x_1574);
lean_inc_ref(x_1617);
if (lean_is_scalar(x_1615)) {
 x_1618 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1618 = x_1615;
 lean_ctor_set_tag(x_1618, 7);
}
lean_ctor_set(x_1618, 0, x_1616);
lean_ctor_set(x_1618, 1, x_1617);
x_1619 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1620 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1620, 0, x_1618);
lean_ctor_set(x_1620, 1, x_1619);
x_1621 = l_Lean_MessageData_ofSyntax(x_1);
x_1622 = l_Lean_indentD(x_1621);
x_1623 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1623, 0, x_1620);
lean_ctor_set(x_1623, 1, x_1622);
x_1624 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1625 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1625, 0, x_1623);
lean_ctor_set(x_1625, 1, x_1624);
x_1626 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1626, 0, x_1625);
lean_ctor_set(x_1626, 1, x_1617);
x_1627 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1628 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1628, 0, x_1626);
lean_ctor_set(x_1628, 1, x_1627);
x_1629 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1628, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1629;
}
else
{
lean_object* x_1630; lean_object* x_1631; 
lean_dec(x_1615);
lean_dec(x_1574);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1630 = lean_ctor_get(x_1614, 0);
lean_inc(x_1630);
lean_dec_ref(x_1614);
x_1631 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1631, 0, x_1630);
return x_1631;
}
}
}
else
{
uint8_t x_1632; 
lean_dec(x_1574);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1632 = !lean_is_exclusive(x_1577);
if (x_1632 == 0)
{
return x_1577;
}
else
{
lean_object* x_1633; lean_object* x_1634; 
x_1633 = lean_ctor_get(x_1577, 0);
lean_inc(x_1633);
lean_dec(x_1577);
x_1634 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1634, 0, x_1633);
return x_1634;
}
}
}
else
{
lean_object* x_1635; lean_object* x_1636; uint8_t x_1637; 
x_1635 = l_Lean_Syntax_getArg(x_1568, x_1340);
lean_dec(x_1568);
x_1636 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__67));
x_1637 = l_Lean_Syntax_isOfKind(x_1635, x_1636);
if (x_1637 == 0)
{
lean_object* x_1638; lean_object* x_1639; lean_object* x_1640; lean_object* x_1641; lean_object* x_1642; lean_object* x_1643; lean_object* x_1644; 
x_1638 = lean_st_ref_get(x_7);
x_1639 = lean_ctor_get(x_1638, 0);
lean_inc_ref(x_1639);
lean_dec(x_1638);
x_1640 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1641 = l_Lean_Syntax_getKind(x_1);
x_1642 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1640, x_1639, x_1641);
x_1643 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_1644 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1642, x_1643, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1644) == 0)
{
uint8_t x_1645; 
x_1645 = !lean_is_exclusive(x_1644);
if (x_1645 == 0)
{
lean_object* x_1646; uint8_t x_1647; 
x_1646 = lean_ctor_get(x_1644, 0);
x_1647 = !lean_is_exclusive(x_1646);
if (x_1647 == 0)
{
lean_object* x_1648; lean_object* x_1649; 
x_1648 = lean_ctor_get(x_1646, 0);
x_1649 = lean_ctor_get(x_1646, 1);
lean_dec(x_1649);
if (lean_obj_tag(x_1648) == 0)
{
lean_object* x_1650; lean_object* x_1651; lean_object* x_1652; lean_object* x_1653; lean_object* x_1654; lean_object* x_1655; lean_object* x_1656; lean_object* x_1657; lean_object* x_1658; lean_object* x_1659; lean_object* x_1660; lean_object* x_1661; lean_object* x_1662; 
lean_free_object(x_1644);
x_1650 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1651 = l_Lean_MessageData_ofName(x_1641);
lean_inc_ref(x_1651);
lean_ctor_set_tag(x_1646, 7);
lean_ctor_set(x_1646, 1, x_1651);
lean_ctor_set(x_1646, 0, x_1650);
x_1652 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1653 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1653, 0, x_1646);
lean_ctor_set(x_1653, 1, x_1652);
x_1654 = l_Lean_MessageData_ofSyntax(x_1);
x_1655 = l_Lean_indentD(x_1654);
x_1656 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1656, 0, x_1653);
lean_ctor_set(x_1656, 1, x_1655);
x_1657 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1658 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1658, 0, x_1656);
lean_ctor_set(x_1658, 1, x_1657);
x_1659 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1659, 0, x_1658);
lean_ctor_set(x_1659, 1, x_1651);
x_1660 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1661 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1661, 0, x_1659);
lean_ctor_set(x_1661, 1, x_1660);
x_1662 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1661, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1662;
}
else
{
lean_object* x_1663; 
lean_free_object(x_1646);
lean_dec(x_1641);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1663 = lean_ctor_get(x_1648, 0);
lean_inc(x_1663);
lean_dec_ref(x_1648);
lean_ctor_set(x_1644, 0, x_1663);
return x_1644;
}
}
else
{
lean_object* x_1664; 
x_1664 = lean_ctor_get(x_1646, 0);
lean_inc(x_1664);
lean_dec(x_1646);
if (lean_obj_tag(x_1664) == 0)
{
lean_object* x_1665; lean_object* x_1666; lean_object* x_1667; lean_object* x_1668; lean_object* x_1669; lean_object* x_1670; lean_object* x_1671; lean_object* x_1672; lean_object* x_1673; lean_object* x_1674; lean_object* x_1675; lean_object* x_1676; lean_object* x_1677; lean_object* x_1678; 
lean_free_object(x_1644);
x_1665 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1666 = l_Lean_MessageData_ofName(x_1641);
lean_inc_ref(x_1666);
x_1667 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1667, 0, x_1665);
lean_ctor_set(x_1667, 1, x_1666);
x_1668 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1669 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1669, 0, x_1667);
lean_ctor_set(x_1669, 1, x_1668);
x_1670 = l_Lean_MessageData_ofSyntax(x_1);
x_1671 = l_Lean_indentD(x_1670);
x_1672 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1672, 0, x_1669);
lean_ctor_set(x_1672, 1, x_1671);
x_1673 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1674 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1674, 0, x_1672);
lean_ctor_set(x_1674, 1, x_1673);
x_1675 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1675, 0, x_1674);
lean_ctor_set(x_1675, 1, x_1666);
x_1676 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1677 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1677, 0, x_1675);
lean_ctor_set(x_1677, 1, x_1676);
x_1678 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1677, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1678;
}
else
{
lean_object* x_1679; 
lean_dec(x_1641);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1679 = lean_ctor_get(x_1664, 0);
lean_inc(x_1679);
lean_dec_ref(x_1664);
lean_ctor_set(x_1644, 0, x_1679);
return x_1644;
}
}
}
else
{
lean_object* x_1680; lean_object* x_1681; lean_object* x_1682; 
x_1680 = lean_ctor_get(x_1644, 0);
lean_inc(x_1680);
lean_dec(x_1644);
x_1681 = lean_ctor_get(x_1680, 0);
lean_inc(x_1681);
if (lean_is_exclusive(x_1680)) {
 lean_ctor_release(x_1680, 0);
 lean_ctor_release(x_1680, 1);
 x_1682 = x_1680;
} else {
 lean_dec_ref(x_1680);
 x_1682 = lean_box(0);
}
if (lean_obj_tag(x_1681) == 0)
{
lean_object* x_1683; lean_object* x_1684; lean_object* x_1685; lean_object* x_1686; lean_object* x_1687; lean_object* x_1688; lean_object* x_1689; lean_object* x_1690; lean_object* x_1691; lean_object* x_1692; lean_object* x_1693; lean_object* x_1694; lean_object* x_1695; lean_object* x_1696; 
x_1683 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1684 = l_Lean_MessageData_ofName(x_1641);
lean_inc_ref(x_1684);
if (lean_is_scalar(x_1682)) {
 x_1685 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1685 = x_1682;
 lean_ctor_set_tag(x_1685, 7);
}
lean_ctor_set(x_1685, 0, x_1683);
lean_ctor_set(x_1685, 1, x_1684);
x_1686 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1687 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1687, 0, x_1685);
lean_ctor_set(x_1687, 1, x_1686);
x_1688 = l_Lean_MessageData_ofSyntax(x_1);
x_1689 = l_Lean_indentD(x_1688);
x_1690 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1690, 0, x_1687);
lean_ctor_set(x_1690, 1, x_1689);
x_1691 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1692 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1692, 0, x_1690);
lean_ctor_set(x_1692, 1, x_1691);
x_1693 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1693, 0, x_1692);
lean_ctor_set(x_1693, 1, x_1684);
x_1694 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1695 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1695, 0, x_1693);
lean_ctor_set(x_1695, 1, x_1694);
x_1696 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1695, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1696;
}
else
{
lean_object* x_1697; lean_object* x_1698; 
lean_dec(x_1682);
lean_dec(x_1641);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1697 = lean_ctor_get(x_1681, 0);
lean_inc(x_1697);
lean_dec_ref(x_1681);
x_1698 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1698, 0, x_1697);
return x_1698;
}
}
}
else
{
uint8_t x_1699; 
lean_dec(x_1641);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1699 = !lean_is_exclusive(x_1644);
if (x_1699 == 0)
{
return x_1644;
}
else
{
lean_object* x_1700; lean_object* x_1701; 
x_1700 = lean_ctor_get(x_1644, 0);
lean_inc(x_1700);
lean_dec(x_1644);
x_1701 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1701, 0, x_1700);
return x_1701;
}
}
}
else
{
x_1425 = x_2;
x_1426 = x_3;
x_1427 = x_4;
x_1428 = x_5;
x_1429 = x_6;
x_1430 = x_7;
x_1431 = lean_box(0);
goto block_1567;
}
}
}
else
{
lean_dec(x_1568);
x_1425 = x_2;
x_1426 = x_3;
x_1427 = x_4;
x_1428 = x_5;
x_1429 = x_6;
x_1430 = x_7;
x_1431 = lean_box(0);
goto block_1567;
}
block_1424:
{
lean_object* x_1349; lean_object* x_1350; lean_object* x_1351; uint8_t x_1352; 
x_1349 = lean_unsigned_to_nat(6u);
x_1350 = l_Lean_Syntax_getArg(x_1, x_1349);
x_1351 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___closed__7));
lean_inc(x_1350);
x_1352 = l_Lean_Syntax_isOfKind(x_1350, x_1351);
if (x_1352 == 0)
{
lean_object* x_1353; lean_object* x_1354; lean_object* x_1355; lean_object* x_1356; lean_object* x_1357; lean_object* x_1358; lean_object* x_1359; 
lean_dec(x_1350);
x_1353 = lean_st_ref_get(x_1347);
x_1354 = lean_ctor_get(x_1353, 0);
lean_inc_ref(x_1354);
lean_dec(x_1353);
x_1355 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1356 = l_Lean_Syntax_getKind(x_1);
x_1357 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1355, x_1354, x_1356);
x_1358 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_1347);
lean_inc_ref(x_1346);
lean_inc(x_1345);
lean_inc_ref(x_1344);
lean_inc(x_1343);
lean_inc_ref(x_1342);
lean_inc(x_1);
x_1359 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1357, x_1358, x_1342, x_1343, x_1344, x_1345, x_1346, x_1347);
if (lean_obj_tag(x_1359) == 0)
{
uint8_t x_1360; 
x_1360 = !lean_is_exclusive(x_1359);
if (x_1360 == 0)
{
lean_object* x_1361; uint8_t x_1362; 
x_1361 = lean_ctor_get(x_1359, 0);
x_1362 = !lean_is_exclusive(x_1361);
if (x_1362 == 0)
{
lean_object* x_1363; lean_object* x_1364; 
x_1363 = lean_ctor_get(x_1361, 0);
x_1364 = lean_ctor_get(x_1361, 1);
lean_dec(x_1364);
if (lean_obj_tag(x_1363) == 0)
{
lean_object* x_1365; lean_object* x_1366; lean_object* x_1367; lean_object* x_1368; lean_object* x_1369; lean_object* x_1370; lean_object* x_1371; lean_object* x_1372; lean_object* x_1373; lean_object* x_1374; lean_object* x_1375; lean_object* x_1376; lean_object* x_1377; 
lean_free_object(x_1359);
x_1365 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1366 = l_Lean_MessageData_ofName(x_1356);
lean_inc_ref(x_1366);
lean_ctor_set_tag(x_1361, 7);
lean_ctor_set(x_1361, 1, x_1366);
lean_ctor_set(x_1361, 0, x_1365);
x_1367 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1368 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1368, 0, x_1361);
lean_ctor_set(x_1368, 1, x_1367);
x_1369 = l_Lean_MessageData_ofSyntax(x_1);
x_1370 = l_Lean_indentD(x_1369);
x_1371 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1371, 0, x_1368);
lean_ctor_set(x_1371, 1, x_1370);
x_1372 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1373 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1373, 0, x_1371);
lean_ctor_set(x_1373, 1, x_1372);
x_1374 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1374, 0, x_1373);
lean_ctor_set(x_1374, 1, x_1366);
x_1375 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1376 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1376, 0, x_1374);
lean_ctor_set(x_1376, 1, x_1375);
x_1377 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1376, x_1342, x_1343, x_1344, x_1345, x_1346, x_1347);
lean_dec(x_1347);
lean_dec_ref(x_1346);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
return x_1377;
}
else
{
lean_object* x_1378; 
lean_free_object(x_1361);
lean_dec(x_1356);
lean_dec(x_1347);
lean_dec_ref(x_1346);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1);
x_1378 = lean_ctor_get(x_1363, 0);
lean_inc(x_1378);
lean_dec_ref(x_1363);
lean_ctor_set(x_1359, 0, x_1378);
return x_1359;
}
}
else
{
lean_object* x_1379; 
x_1379 = lean_ctor_get(x_1361, 0);
lean_inc(x_1379);
lean_dec(x_1361);
if (lean_obj_tag(x_1379) == 0)
{
lean_object* x_1380; lean_object* x_1381; lean_object* x_1382; lean_object* x_1383; lean_object* x_1384; lean_object* x_1385; lean_object* x_1386; lean_object* x_1387; lean_object* x_1388; lean_object* x_1389; lean_object* x_1390; lean_object* x_1391; lean_object* x_1392; lean_object* x_1393; 
lean_free_object(x_1359);
x_1380 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1381 = l_Lean_MessageData_ofName(x_1356);
lean_inc_ref(x_1381);
x_1382 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1382, 0, x_1380);
lean_ctor_set(x_1382, 1, x_1381);
x_1383 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1384 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1384, 0, x_1382);
lean_ctor_set(x_1384, 1, x_1383);
x_1385 = l_Lean_MessageData_ofSyntax(x_1);
x_1386 = l_Lean_indentD(x_1385);
x_1387 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1387, 0, x_1384);
lean_ctor_set(x_1387, 1, x_1386);
x_1388 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1389 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1389, 0, x_1387);
lean_ctor_set(x_1389, 1, x_1388);
x_1390 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1390, 0, x_1389);
lean_ctor_set(x_1390, 1, x_1381);
x_1391 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1392 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1392, 0, x_1390);
lean_ctor_set(x_1392, 1, x_1391);
x_1393 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1392, x_1342, x_1343, x_1344, x_1345, x_1346, x_1347);
lean_dec(x_1347);
lean_dec_ref(x_1346);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
return x_1393;
}
else
{
lean_object* x_1394; 
lean_dec(x_1356);
lean_dec(x_1347);
lean_dec_ref(x_1346);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1);
x_1394 = lean_ctor_get(x_1379, 0);
lean_inc(x_1394);
lean_dec_ref(x_1379);
lean_ctor_set(x_1359, 0, x_1394);
return x_1359;
}
}
}
else
{
lean_object* x_1395; lean_object* x_1396; lean_object* x_1397; 
x_1395 = lean_ctor_get(x_1359, 0);
lean_inc(x_1395);
lean_dec(x_1359);
x_1396 = lean_ctor_get(x_1395, 0);
lean_inc(x_1396);
if (lean_is_exclusive(x_1395)) {
 lean_ctor_release(x_1395, 0);
 lean_ctor_release(x_1395, 1);
 x_1397 = x_1395;
} else {
 lean_dec_ref(x_1395);
 x_1397 = lean_box(0);
}
if (lean_obj_tag(x_1396) == 0)
{
lean_object* x_1398; lean_object* x_1399; lean_object* x_1400; lean_object* x_1401; lean_object* x_1402; lean_object* x_1403; lean_object* x_1404; lean_object* x_1405; lean_object* x_1406; lean_object* x_1407; lean_object* x_1408; lean_object* x_1409; lean_object* x_1410; lean_object* x_1411; 
x_1398 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1399 = l_Lean_MessageData_ofName(x_1356);
lean_inc_ref(x_1399);
if (lean_is_scalar(x_1397)) {
 x_1400 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1400 = x_1397;
 lean_ctor_set_tag(x_1400, 7);
}
lean_ctor_set(x_1400, 0, x_1398);
lean_ctor_set(x_1400, 1, x_1399);
x_1401 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1402 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1402, 0, x_1400);
lean_ctor_set(x_1402, 1, x_1401);
x_1403 = l_Lean_MessageData_ofSyntax(x_1);
x_1404 = l_Lean_indentD(x_1403);
x_1405 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1405, 0, x_1402);
lean_ctor_set(x_1405, 1, x_1404);
x_1406 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1407 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1407, 0, x_1405);
lean_ctor_set(x_1407, 1, x_1406);
x_1408 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1408, 0, x_1407);
lean_ctor_set(x_1408, 1, x_1399);
x_1409 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1410 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1410, 0, x_1408);
lean_ctor_set(x_1410, 1, x_1409);
x_1411 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1410, x_1342, x_1343, x_1344, x_1345, x_1346, x_1347);
lean_dec(x_1347);
lean_dec_ref(x_1346);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
return x_1411;
}
else
{
lean_object* x_1412; lean_object* x_1413; 
lean_dec(x_1397);
lean_dec(x_1356);
lean_dec(x_1347);
lean_dec_ref(x_1346);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1);
x_1412 = lean_ctor_get(x_1396, 0);
lean_inc(x_1412);
lean_dec_ref(x_1396);
x_1413 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1413, 0, x_1412);
return x_1413;
}
}
}
else
{
uint8_t x_1414; 
lean_dec(x_1356);
lean_dec(x_1347);
lean_dec_ref(x_1346);
lean_dec(x_1345);
lean_dec_ref(x_1344);
lean_dec(x_1343);
lean_dec_ref(x_1342);
lean_dec(x_1);
x_1414 = !lean_is_exclusive(x_1359);
if (x_1414 == 0)
{
return x_1359;
}
else
{
lean_object* x_1415; lean_object* x_1416; 
x_1415 = lean_ctor_get(x_1359, 0);
lean_inc(x_1415);
lean_dec(x_1359);
x_1416 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1416, 0, x_1415);
return x_1416;
}
}
}
else
{
lean_object* x_1417; lean_object* x_1418; lean_object* x_1419; lean_object* x_1420; size_t x_1421; size_t x_1422; lean_object* x_1423; 
lean_dec(x_1);
x_1417 = l_Lean_Syntax_getArg(x_1350, x_1340);
lean_dec(x_1350);
x_1418 = l_Lean_Syntax_getArgs(x_1417);
lean_dec(x_1417);
x_1419 = l_Lean_NameSet_empty;
x_1420 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_1420, 0, x_1341);
lean_ctor_set(x_1420, 1, x_1419);
lean_ctor_set_uint8(x_1420, sizeof(void*)*2, x_180);
lean_ctor_set_uint8(x_1420, sizeof(void*)*2 + 1, x_180);
lean_ctor_set_uint8(x_1420, sizeof(void*)*2 + 2, x_180);
x_1421 = lean_array_size(x_1418);
x_1422 = 0;
x_1423 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(x_180, x_1418, x_1421, x_1422, x_1420, x_1342, x_1343, x_1344, x_1345, x_1346, x_1347);
lean_dec_ref(x_1418);
return x_1423;
}
}
block_1567:
{
lean_object* x_1432; lean_object* x_1433; uint8_t x_1434; 
x_1432 = lean_unsigned_to_nat(2u);
x_1433 = l_Lean_Syntax_getArg(x_1, x_1432);
x_1434 = l_Lean_Syntax_isNone(x_1433);
if (x_1434 == 0)
{
uint8_t x_1435; 
lean_inc(x_1433);
x_1435 = l_Lean_Syntax_matchesNull(x_1433, x_1341);
if (x_1435 == 0)
{
lean_object* x_1436; lean_object* x_1437; lean_object* x_1438; lean_object* x_1439; lean_object* x_1440; lean_object* x_1441; lean_object* x_1442; 
lean_dec(x_1433);
x_1436 = lean_st_ref_get(x_1430);
x_1437 = lean_ctor_get(x_1436, 0);
lean_inc_ref(x_1437);
lean_dec(x_1436);
x_1438 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1439 = l_Lean_Syntax_getKind(x_1);
x_1440 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1438, x_1437, x_1439);
x_1441 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_1430);
lean_inc_ref(x_1429);
lean_inc(x_1428);
lean_inc_ref(x_1427);
lean_inc(x_1426);
lean_inc_ref(x_1425);
lean_inc(x_1);
x_1442 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1440, x_1441, x_1425, x_1426, x_1427, x_1428, x_1429, x_1430);
if (lean_obj_tag(x_1442) == 0)
{
uint8_t x_1443; 
x_1443 = !lean_is_exclusive(x_1442);
if (x_1443 == 0)
{
lean_object* x_1444; uint8_t x_1445; 
x_1444 = lean_ctor_get(x_1442, 0);
x_1445 = !lean_is_exclusive(x_1444);
if (x_1445 == 0)
{
lean_object* x_1446; lean_object* x_1447; 
x_1446 = lean_ctor_get(x_1444, 0);
x_1447 = lean_ctor_get(x_1444, 1);
lean_dec(x_1447);
if (lean_obj_tag(x_1446) == 0)
{
lean_object* x_1448; lean_object* x_1449; lean_object* x_1450; lean_object* x_1451; lean_object* x_1452; lean_object* x_1453; lean_object* x_1454; lean_object* x_1455; lean_object* x_1456; lean_object* x_1457; lean_object* x_1458; lean_object* x_1459; lean_object* x_1460; 
lean_free_object(x_1442);
x_1448 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1449 = l_Lean_MessageData_ofName(x_1439);
lean_inc_ref(x_1449);
lean_ctor_set_tag(x_1444, 7);
lean_ctor_set(x_1444, 1, x_1449);
lean_ctor_set(x_1444, 0, x_1448);
x_1450 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1451 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1451, 0, x_1444);
lean_ctor_set(x_1451, 1, x_1450);
x_1452 = l_Lean_MessageData_ofSyntax(x_1);
x_1453 = l_Lean_indentD(x_1452);
x_1454 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1454, 0, x_1451);
lean_ctor_set(x_1454, 1, x_1453);
x_1455 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1456 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1456, 0, x_1454);
lean_ctor_set(x_1456, 1, x_1455);
x_1457 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1457, 0, x_1456);
lean_ctor_set(x_1457, 1, x_1449);
x_1458 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1459 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1459, 0, x_1457);
lean_ctor_set(x_1459, 1, x_1458);
x_1460 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1459, x_1425, x_1426, x_1427, x_1428, x_1429, x_1430);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
return x_1460;
}
else
{
lean_object* x_1461; 
lean_free_object(x_1444);
lean_dec(x_1439);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
lean_dec_ref(x_1425);
lean_dec(x_1);
x_1461 = lean_ctor_get(x_1446, 0);
lean_inc(x_1461);
lean_dec_ref(x_1446);
lean_ctor_set(x_1442, 0, x_1461);
return x_1442;
}
}
else
{
lean_object* x_1462; 
x_1462 = lean_ctor_get(x_1444, 0);
lean_inc(x_1462);
lean_dec(x_1444);
if (lean_obj_tag(x_1462) == 0)
{
lean_object* x_1463; lean_object* x_1464; lean_object* x_1465; lean_object* x_1466; lean_object* x_1467; lean_object* x_1468; lean_object* x_1469; lean_object* x_1470; lean_object* x_1471; lean_object* x_1472; lean_object* x_1473; lean_object* x_1474; lean_object* x_1475; lean_object* x_1476; 
lean_free_object(x_1442);
x_1463 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1464 = l_Lean_MessageData_ofName(x_1439);
lean_inc_ref(x_1464);
x_1465 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1465, 0, x_1463);
lean_ctor_set(x_1465, 1, x_1464);
x_1466 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1467 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1467, 0, x_1465);
lean_ctor_set(x_1467, 1, x_1466);
x_1468 = l_Lean_MessageData_ofSyntax(x_1);
x_1469 = l_Lean_indentD(x_1468);
x_1470 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1470, 0, x_1467);
lean_ctor_set(x_1470, 1, x_1469);
x_1471 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1472 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1472, 0, x_1470);
lean_ctor_set(x_1472, 1, x_1471);
x_1473 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1473, 0, x_1472);
lean_ctor_set(x_1473, 1, x_1464);
x_1474 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1475 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1475, 0, x_1473);
lean_ctor_set(x_1475, 1, x_1474);
x_1476 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1475, x_1425, x_1426, x_1427, x_1428, x_1429, x_1430);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
return x_1476;
}
else
{
lean_object* x_1477; 
lean_dec(x_1439);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
lean_dec_ref(x_1425);
lean_dec(x_1);
x_1477 = lean_ctor_get(x_1462, 0);
lean_inc(x_1477);
lean_dec_ref(x_1462);
lean_ctor_set(x_1442, 0, x_1477);
return x_1442;
}
}
}
else
{
lean_object* x_1478; lean_object* x_1479; lean_object* x_1480; 
x_1478 = lean_ctor_get(x_1442, 0);
lean_inc(x_1478);
lean_dec(x_1442);
x_1479 = lean_ctor_get(x_1478, 0);
lean_inc(x_1479);
if (lean_is_exclusive(x_1478)) {
 lean_ctor_release(x_1478, 0);
 lean_ctor_release(x_1478, 1);
 x_1480 = x_1478;
} else {
 lean_dec_ref(x_1478);
 x_1480 = lean_box(0);
}
if (lean_obj_tag(x_1479) == 0)
{
lean_object* x_1481; lean_object* x_1482; lean_object* x_1483; lean_object* x_1484; lean_object* x_1485; lean_object* x_1486; lean_object* x_1487; lean_object* x_1488; lean_object* x_1489; lean_object* x_1490; lean_object* x_1491; lean_object* x_1492; lean_object* x_1493; lean_object* x_1494; 
x_1481 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1482 = l_Lean_MessageData_ofName(x_1439);
lean_inc_ref(x_1482);
if (lean_is_scalar(x_1480)) {
 x_1483 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1483 = x_1480;
 lean_ctor_set_tag(x_1483, 7);
}
lean_ctor_set(x_1483, 0, x_1481);
lean_ctor_set(x_1483, 1, x_1482);
x_1484 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1485 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1485, 0, x_1483);
lean_ctor_set(x_1485, 1, x_1484);
x_1486 = l_Lean_MessageData_ofSyntax(x_1);
x_1487 = l_Lean_indentD(x_1486);
x_1488 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1488, 0, x_1485);
lean_ctor_set(x_1488, 1, x_1487);
x_1489 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1490 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1490, 0, x_1488);
lean_ctor_set(x_1490, 1, x_1489);
x_1491 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1491, 0, x_1490);
lean_ctor_set(x_1491, 1, x_1482);
x_1492 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1493 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1493, 0, x_1491);
lean_ctor_set(x_1493, 1, x_1492);
x_1494 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1493, x_1425, x_1426, x_1427, x_1428, x_1429, x_1430);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
return x_1494;
}
else
{
lean_object* x_1495; lean_object* x_1496; 
lean_dec(x_1480);
lean_dec(x_1439);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
lean_dec_ref(x_1425);
lean_dec(x_1);
x_1495 = lean_ctor_get(x_1479, 0);
lean_inc(x_1495);
lean_dec_ref(x_1479);
x_1496 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1496, 0, x_1495);
return x_1496;
}
}
}
else
{
uint8_t x_1497; 
lean_dec(x_1439);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
lean_dec_ref(x_1425);
lean_dec(x_1);
x_1497 = !lean_is_exclusive(x_1442);
if (x_1497 == 0)
{
return x_1442;
}
else
{
lean_object* x_1498; lean_object* x_1499; 
x_1498 = lean_ctor_get(x_1442, 0);
lean_inc(x_1498);
lean_dec(x_1442);
x_1499 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1499, 0, x_1498);
return x_1499;
}
}
}
else
{
lean_object* x_1500; lean_object* x_1501; uint8_t x_1502; 
x_1500 = l_Lean_Syntax_getArg(x_1433, x_1340);
lean_dec(x_1433);
x_1501 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__65));
x_1502 = l_Lean_Syntax_isOfKind(x_1500, x_1501);
if (x_1502 == 0)
{
lean_object* x_1503; lean_object* x_1504; lean_object* x_1505; lean_object* x_1506; lean_object* x_1507; lean_object* x_1508; lean_object* x_1509; 
x_1503 = lean_st_ref_get(x_1430);
x_1504 = lean_ctor_get(x_1503, 0);
lean_inc_ref(x_1504);
lean_dec(x_1503);
x_1505 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1506 = l_Lean_Syntax_getKind(x_1);
x_1507 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1505, x_1504, x_1506);
x_1508 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_1430);
lean_inc_ref(x_1429);
lean_inc(x_1428);
lean_inc_ref(x_1427);
lean_inc(x_1426);
lean_inc_ref(x_1425);
lean_inc(x_1);
x_1509 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1507, x_1508, x_1425, x_1426, x_1427, x_1428, x_1429, x_1430);
if (lean_obj_tag(x_1509) == 0)
{
uint8_t x_1510; 
x_1510 = !lean_is_exclusive(x_1509);
if (x_1510 == 0)
{
lean_object* x_1511; uint8_t x_1512; 
x_1511 = lean_ctor_get(x_1509, 0);
x_1512 = !lean_is_exclusive(x_1511);
if (x_1512 == 0)
{
lean_object* x_1513; lean_object* x_1514; 
x_1513 = lean_ctor_get(x_1511, 0);
x_1514 = lean_ctor_get(x_1511, 1);
lean_dec(x_1514);
if (lean_obj_tag(x_1513) == 0)
{
lean_object* x_1515; lean_object* x_1516; lean_object* x_1517; lean_object* x_1518; lean_object* x_1519; lean_object* x_1520; lean_object* x_1521; lean_object* x_1522; lean_object* x_1523; lean_object* x_1524; lean_object* x_1525; lean_object* x_1526; lean_object* x_1527; 
lean_free_object(x_1509);
x_1515 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1516 = l_Lean_MessageData_ofName(x_1506);
lean_inc_ref(x_1516);
lean_ctor_set_tag(x_1511, 7);
lean_ctor_set(x_1511, 1, x_1516);
lean_ctor_set(x_1511, 0, x_1515);
x_1517 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1518 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1518, 0, x_1511);
lean_ctor_set(x_1518, 1, x_1517);
x_1519 = l_Lean_MessageData_ofSyntax(x_1);
x_1520 = l_Lean_indentD(x_1519);
x_1521 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1521, 0, x_1518);
lean_ctor_set(x_1521, 1, x_1520);
x_1522 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1523 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1523, 0, x_1521);
lean_ctor_set(x_1523, 1, x_1522);
x_1524 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1524, 0, x_1523);
lean_ctor_set(x_1524, 1, x_1516);
x_1525 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1526 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1526, 0, x_1524);
lean_ctor_set(x_1526, 1, x_1525);
x_1527 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1526, x_1425, x_1426, x_1427, x_1428, x_1429, x_1430);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
return x_1527;
}
else
{
lean_object* x_1528; 
lean_free_object(x_1511);
lean_dec(x_1506);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
lean_dec_ref(x_1425);
lean_dec(x_1);
x_1528 = lean_ctor_get(x_1513, 0);
lean_inc(x_1528);
lean_dec_ref(x_1513);
lean_ctor_set(x_1509, 0, x_1528);
return x_1509;
}
}
else
{
lean_object* x_1529; 
x_1529 = lean_ctor_get(x_1511, 0);
lean_inc(x_1529);
lean_dec(x_1511);
if (lean_obj_tag(x_1529) == 0)
{
lean_object* x_1530; lean_object* x_1531; lean_object* x_1532; lean_object* x_1533; lean_object* x_1534; lean_object* x_1535; lean_object* x_1536; lean_object* x_1537; lean_object* x_1538; lean_object* x_1539; lean_object* x_1540; lean_object* x_1541; lean_object* x_1542; lean_object* x_1543; 
lean_free_object(x_1509);
x_1530 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1531 = l_Lean_MessageData_ofName(x_1506);
lean_inc_ref(x_1531);
x_1532 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1532, 0, x_1530);
lean_ctor_set(x_1532, 1, x_1531);
x_1533 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1534 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1534, 0, x_1532);
lean_ctor_set(x_1534, 1, x_1533);
x_1535 = l_Lean_MessageData_ofSyntax(x_1);
x_1536 = l_Lean_indentD(x_1535);
x_1537 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1537, 0, x_1534);
lean_ctor_set(x_1537, 1, x_1536);
x_1538 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1539 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1539, 0, x_1537);
lean_ctor_set(x_1539, 1, x_1538);
x_1540 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1540, 0, x_1539);
lean_ctor_set(x_1540, 1, x_1531);
x_1541 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1542 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1542, 0, x_1540);
lean_ctor_set(x_1542, 1, x_1541);
x_1543 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1542, x_1425, x_1426, x_1427, x_1428, x_1429, x_1430);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
return x_1543;
}
else
{
lean_object* x_1544; 
lean_dec(x_1506);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
lean_dec_ref(x_1425);
lean_dec(x_1);
x_1544 = lean_ctor_get(x_1529, 0);
lean_inc(x_1544);
lean_dec_ref(x_1529);
lean_ctor_set(x_1509, 0, x_1544);
return x_1509;
}
}
}
else
{
lean_object* x_1545; lean_object* x_1546; lean_object* x_1547; 
x_1545 = lean_ctor_get(x_1509, 0);
lean_inc(x_1545);
lean_dec(x_1509);
x_1546 = lean_ctor_get(x_1545, 0);
lean_inc(x_1546);
if (lean_is_exclusive(x_1545)) {
 lean_ctor_release(x_1545, 0);
 lean_ctor_release(x_1545, 1);
 x_1547 = x_1545;
} else {
 lean_dec_ref(x_1545);
 x_1547 = lean_box(0);
}
if (lean_obj_tag(x_1546) == 0)
{
lean_object* x_1548; lean_object* x_1549; lean_object* x_1550; lean_object* x_1551; lean_object* x_1552; lean_object* x_1553; lean_object* x_1554; lean_object* x_1555; lean_object* x_1556; lean_object* x_1557; lean_object* x_1558; lean_object* x_1559; lean_object* x_1560; lean_object* x_1561; 
x_1548 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1549 = l_Lean_MessageData_ofName(x_1506);
lean_inc_ref(x_1549);
if (lean_is_scalar(x_1547)) {
 x_1550 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1550 = x_1547;
 lean_ctor_set_tag(x_1550, 7);
}
lean_ctor_set(x_1550, 0, x_1548);
lean_ctor_set(x_1550, 1, x_1549);
x_1551 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1552 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1552, 0, x_1550);
lean_ctor_set(x_1552, 1, x_1551);
x_1553 = l_Lean_MessageData_ofSyntax(x_1);
x_1554 = l_Lean_indentD(x_1553);
x_1555 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1555, 0, x_1552);
lean_ctor_set(x_1555, 1, x_1554);
x_1556 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1557 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1557, 0, x_1555);
lean_ctor_set(x_1557, 1, x_1556);
x_1558 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1558, 0, x_1557);
lean_ctor_set(x_1558, 1, x_1549);
x_1559 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1560 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1560, 0, x_1558);
lean_ctor_set(x_1560, 1, x_1559);
x_1561 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1560, x_1425, x_1426, x_1427, x_1428, x_1429, x_1430);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
return x_1561;
}
else
{
lean_object* x_1562; lean_object* x_1563; 
lean_dec(x_1547);
lean_dec(x_1506);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
lean_dec_ref(x_1425);
lean_dec(x_1);
x_1562 = lean_ctor_get(x_1546, 0);
lean_inc(x_1562);
lean_dec_ref(x_1546);
x_1563 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1563, 0, x_1562);
return x_1563;
}
}
}
else
{
uint8_t x_1564; 
lean_dec(x_1506);
lean_dec(x_1430);
lean_dec_ref(x_1429);
lean_dec(x_1428);
lean_dec_ref(x_1427);
lean_dec(x_1426);
lean_dec_ref(x_1425);
lean_dec(x_1);
x_1564 = !lean_is_exclusive(x_1509);
if (x_1564 == 0)
{
return x_1509;
}
else
{
lean_object* x_1565; lean_object* x_1566; 
x_1565 = lean_ctor_get(x_1509, 0);
lean_inc(x_1565);
lean_dec(x_1509);
x_1566 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1566, 0, x_1565);
return x_1566;
}
}
}
else
{
x_1342 = x_1425;
x_1343 = x_1426;
x_1344 = x_1427;
x_1345 = x_1428;
x_1346 = x_1429;
x_1347 = x_1430;
x_1348 = lean_box(0);
goto block_1424;
}
}
}
else
{
lean_dec(x_1433);
x_1342 = x_1425;
x_1343 = x_1426;
x_1344 = x_1427;
x_1345 = x_1428;
x_1346 = x_1429;
x_1347 = x_1430;
x_1348 = lean_box(0);
goto block_1424;
}
}
}
}
else
{
lean_object* x_1702; lean_object* x_1703; lean_object* x_1704; uint8_t x_1705; 
x_1702 = lean_unsigned_to_nat(0u);
x_1703 = l_Lean_Syntax_getArg(x_1, x_1702);
x_1704 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__1));
lean_inc(x_1703);
x_1705 = l_Lean_Syntax_isOfKind(x_1703, x_1704);
if (x_1705 == 0)
{
lean_object* x_1706; uint8_t x_1707; 
x_1706 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__3));
lean_inc(x_1703);
x_1707 = l_Lean_Syntax_isOfKind(x_1703, x_1706);
if (x_1707 == 0)
{
lean_object* x_1708; 
lean_dec(x_1703);
x_1708 = l_Lean_Elab_Do_InferControlInfo_ofElem___lam__0(x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1708) == 0)
{
lean_object* x_1709; lean_object* x_1710; lean_object* x_1711; lean_object* x_1712; lean_object* x_1713; lean_object* x_1714; 
x_1709 = lean_ctor_get(x_1708, 0);
lean_inc(x_1709);
lean_dec_ref(x_1708);
x_1710 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1711 = l_Lean_Syntax_getKind(x_1);
x_1712 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1710, x_1709, x_1711);
x_1713 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_1714 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1712, x_1713, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1714) == 0)
{
uint8_t x_1715; 
x_1715 = !lean_is_exclusive(x_1714);
if (x_1715 == 0)
{
lean_object* x_1716; uint8_t x_1717; 
x_1716 = lean_ctor_get(x_1714, 0);
x_1717 = !lean_is_exclusive(x_1716);
if (x_1717 == 0)
{
lean_object* x_1718; lean_object* x_1719; 
x_1718 = lean_ctor_get(x_1716, 0);
x_1719 = lean_ctor_get(x_1716, 1);
lean_dec(x_1719);
if (lean_obj_tag(x_1718) == 0)
{
lean_object* x_1720; lean_object* x_1721; lean_object* x_1722; lean_object* x_1723; lean_object* x_1724; lean_object* x_1725; lean_object* x_1726; lean_object* x_1727; lean_object* x_1728; lean_object* x_1729; lean_object* x_1730; lean_object* x_1731; lean_object* x_1732; 
lean_free_object(x_1714);
x_1720 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1721 = l_Lean_MessageData_ofName(x_1711);
lean_inc_ref(x_1721);
lean_ctor_set_tag(x_1716, 7);
lean_ctor_set(x_1716, 1, x_1721);
lean_ctor_set(x_1716, 0, x_1720);
x_1722 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1723 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1723, 0, x_1716);
lean_ctor_set(x_1723, 1, x_1722);
x_1724 = l_Lean_MessageData_ofSyntax(x_1);
x_1725 = l_Lean_indentD(x_1724);
x_1726 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1726, 0, x_1723);
lean_ctor_set(x_1726, 1, x_1725);
x_1727 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1728 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1728, 0, x_1726);
lean_ctor_set(x_1728, 1, x_1727);
x_1729 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1729, 0, x_1728);
lean_ctor_set(x_1729, 1, x_1721);
x_1730 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1731 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1731, 0, x_1729);
lean_ctor_set(x_1731, 1, x_1730);
x_1732 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1731, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1732;
}
else
{
lean_object* x_1733; 
lean_free_object(x_1716);
lean_dec(x_1711);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1733 = lean_ctor_get(x_1718, 0);
lean_inc(x_1733);
lean_dec_ref(x_1718);
lean_ctor_set(x_1714, 0, x_1733);
return x_1714;
}
}
else
{
lean_object* x_1734; 
x_1734 = lean_ctor_get(x_1716, 0);
lean_inc(x_1734);
lean_dec(x_1716);
if (lean_obj_tag(x_1734) == 0)
{
lean_object* x_1735; lean_object* x_1736; lean_object* x_1737; lean_object* x_1738; lean_object* x_1739; lean_object* x_1740; lean_object* x_1741; lean_object* x_1742; lean_object* x_1743; lean_object* x_1744; lean_object* x_1745; lean_object* x_1746; lean_object* x_1747; lean_object* x_1748; 
lean_free_object(x_1714);
x_1735 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1736 = l_Lean_MessageData_ofName(x_1711);
lean_inc_ref(x_1736);
x_1737 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1737, 0, x_1735);
lean_ctor_set(x_1737, 1, x_1736);
x_1738 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1739 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1739, 0, x_1737);
lean_ctor_set(x_1739, 1, x_1738);
x_1740 = l_Lean_MessageData_ofSyntax(x_1);
x_1741 = l_Lean_indentD(x_1740);
x_1742 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1742, 0, x_1739);
lean_ctor_set(x_1742, 1, x_1741);
x_1743 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1744 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1744, 0, x_1742);
lean_ctor_set(x_1744, 1, x_1743);
x_1745 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1745, 0, x_1744);
lean_ctor_set(x_1745, 1, x_1736);
x_1746 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1747 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1747, 0, x_1745);
lean_ctor_set(x_1747, 1, x_1746);
x_1748 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1747, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1748;
}
else
{
lean_object* x_1749; 
lean_dec(x_1711);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1749 = lean_ctor_get(x_1734, 0);
lean_inc(x_1749);
lean_dec_ref(x_1734);
lean_ctor_set(x_1714, 0, x_1749);
return x_1714;
}
}
}
else
{
lean_object* x_1750; lean_object* x_1751; lean_object* x_1752; 
x_1750 = lean_ctor_get(x_1714, 0);
lean_inc(x_1750);
lean_dec(x_1714);
x_1751 = lean_ctor_get(x_1750, 0);
lean_inc(x_1751);
if (lean_is_exclusive(x_1750)) {
 lean_ctor_release(x_1750, 0);
 lean_ctor_release(x_1750, 1);
 x_1752 = x_1750;
} else {
 lean_dec_ref(x_1750);
 x_1752 = lean_box(0);
}
if (lean_obj_tag(x_1751) == 0)
{
lean_object* x_1753; lean_object* x_1754; lean_object* x_1755; lean_object* x_1756; lean_object* x_1757; lean_object* x_1758; lean_object* x_1759; lean_object* x_1760; lean_object* x_1761; lean_object* x_1762; lean_object* x_1763; lean_object* x_1764; lean_object* x_1765; lean_object* x_1766; 
x_1753 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1754 = l_Lean_MessageData_ofName(x_1711);
lean_inc_ref(x_1754);
if (lean_is_scalar(x_1752)) {
 x_1755 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1755 = x_1752;
 lean_ctor_set_tag(x_1755, 7);
}
lean_ctor_set(x_1755, 0, x_1753);
lean_ctor_set(x_1755, 1, x_1754);
x_1756 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1757 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1757, 0, x_1755);
lean_ctor_set(x_1757, 1, x_1756);
x_1758 = l_Lean_MessageData_ofSyntax(x_1);
x_1759 = l_Lean_indentD(x_1758);
x_1760 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1760, 0, x_1757);
lean_ctor_set(x_1760, 1, x_1759);
x_1761 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1762 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1762, 0, x_1760);
lean_ctor_set(x_1762, 1, x_1761);
x_1763 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1763, 0, x_1762);
lean_ctor_set(x_1763, 1, x_1754);
x_1764 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1765 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1765, 0, x_1763);
lean_ctor_set(x_1765, 1, x_1764);
x_1766 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1765, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1766;
}
else
{
lean_object* x_1767; lean_object* x_1768; 
lean_dec(x_1752);
lean_dec(x_1711);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1767 = lean_ctor_get(x_1751, 0);
lean_inc(x_1767);
lean_dec_ref(x_1751);
x_1768 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1768, 0, x_1767);
return x_1768;
}
}
}
else
{
uint8_t x_1769; 
lean_dec(x_1711);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1769 = !lean_is_exclusive(x_1714);
if (x_1769 == 0)
{
return x_1714;
}
else
{
lean_object* x_1770; lean_object* x_1771; 
x_1770 = lean_ctor_get(x_1714, 0);
lean_inc(x_1770);
lean_dec(x_1714);
x_1771 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1771, 0, x_1770);
return x_1771;
}
}
}
else
{
uint8_t x_1772; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1772 = !lean_is_exclusive(x_1708);
if (x_1772 == 0)
{
return x_1708;
}
else
{
lean_object* x_1773; lean_object* x_1774; 
x_1773 = lean_ctor_get(x_1708, 0);
lean_inc(x_1773);
lean_dec(x_1708);
x_1774 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1774, 0, x_1773);
return x_1774;
}
}
}
else
{
lean_object* x_1775; 
lean_dec(x_1);
x_1775 = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(x_147, x_1703, x_2, x_3, x_4, x_5, x_6, x_7);
return x_1775;
}
}
else
{
lean_object* x_1776; 
lean_dec(x_1);
x_1776 = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(x_147, x_1703, x_2, x_3, x_4, x_5, x_6, x_7);
return x_1776;
}
}
}
else
{
lean_object* x_1777; lean_object* x_1778; lean_object* x_1779; uint8_t x_1780; 
x_1777 = lean_unsigned_to_nat(0u);
x_1778 = l_Lean_Syntax_getArg(x_1, x_1777);
x_1779 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__69));
lean_inc(x_1778);
x_1780 = l_Lean_Syntax_isOfKind(x_1778, x_1779);
if (x_1780 == 0)
{
lean_object* x_1781; uint8_t x_1782; 
x_1781 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__71));
lean_inc(x_1778);
x_1782 = l_Lean_Syntax_isOfKind(x_1778, x_1781);
if (x_1782 == 0)
{
lean_object* x_1783; 
lean_dec(x_1778);
x_1783 = l_Lean_Elab_Do_InferControlInfo_ofElem___lam__0(x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1783) == 0)
{
lean_object* x_1784; lean_object* x_1785; lean_object* x_1786; lean_object* x_1787; lean_object* x_1788; lean_object* x_1789; 
x_1784 = lean_ctor_get(x_1783, 0);
lean_inc(x_1784);
lean_dec_ref(x_1783);
x_1785 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1786 = l_Lean_Syntax_getKind(x_1);
x_1787 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1785, x_1784, x_1786);
x_1788 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_1789 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1787, x_1788, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1789) == 0)
{
uint8_t x_1790; 
x_1790 = !lean_is_exclusive(x_1789);
if (x_1790 == 0)
{
lean_object* x_1791; uint8_t x_1792; 
x_1791 = lean_ctor_get(x_1789, 0);
x_1792 = !lean_is_exclusive(x_1791);
if (x_1792 == 0)
{
lean_object* x_1793; lean_object* x_1794; 
x_1793 = lean_ctor_get(x_1791, 0);
x_1794 = lean_ctor_get(x_1791, 1);
lean_dec(x_1794);
if (lean_obj_tag(x_1793) == 0)
{
lean_object* x_1795; lean_object* x_1796; lean_object* x_1797; lean_object* x_1798; lean_object* x_1799; lean_object* x_1800; lean_object* x_1801; lean_object* x_1802; lean_object* x_1803; lean_object* x_1804; lean_object* x_1805; lean_object* x_1806; lean_object* x_1807; 
lean_free_object(x_1789);
x_1795 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1796 = l_Lean_MessageData_ofName(x_1786);
lean_inc_ref(x_1796);
lean_ctor_set_tag(x_1791, 7);
lean_ctor_set(x_1791, 1, x_1796);
lean_ctor_set(x_1791, 0, x_1795);
x_1797 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1798 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1798, 0, x_1791);
lean_ctor_set(x_1798, 1, x_1797);
x_1799 = l_Lean_MessageData_ofSyntax(x_1);
x_1800 = l_Lean_indentD(x_1799);
x_1801 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1801, 0, x_1798);
lean_ctor_set(x_1801, 1, x_1800);
x_1802 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1803 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1803, 0, x_1801);
lean_ctor_set(x_1803, 1, x_1802);
x_1804 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1804, 0, x_1803);
lean_ctor_set(x_1804, 1, x_1796);
x_1805 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1806 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1806, 0, x_1804);
lean_ctor_set(x_1806, 1, x_1805);
x_1807 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1806, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1807;
}
else
{
lean_object* x_1808; 
lean_free_object(x_1791);
lean_dec(x_1786);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1808 = lean_ctor_get(x_1793, 0);
lean_inc(x_1808);
lean_dec_ref(x_1793);
lean_ctor_set(x_1789, 0, x_1808);
return x_1789;
}
}
else
{
lean_object* x_1809; 
x_1809 = lean_ctor_get(x_1791, 0);
lean_inc(x_1809);
lean_dec(x_1791);
if (lean_obj_tag(x_1809) == 0)
{
lean_object* x_1810; lean_object* x_1811; lean_object* x_1812; lean_object* x_1813; lean_object* x_1814; lean_object* x_1815; lean_object* x_1816; lean_object* x_1817; lean_object* x_1818; lean_object* x_1819; lean_object* x_1820; lean_object* x_1821; lean_object* x_1822; lean_object* x_1823; 
lean_free_object(x_1789);
x_1810 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1811 = l_Lean_MessageData_ofName(x_1786);
lean_inc_ref(x_1811);
x_1812 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1812, 0, x_1810);
lean_ctor_set(x_1812, 1, x_1811);
x_1813 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1814 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1814, 0, x_1812);
lean_ctor_set(x_1814, 1, x_1813);
x_1815 = l_Lean_MessageData_ofSyntax(x_1);
x_1816 = l_Lean_indentD(x_1815);
x_1817 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1817, 0, x_1814);
lean_ctor_set(x_1817, 1, x_1816);
x_1818 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1819 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1819, 0, x_1817);
lean_ctor_set(x_1819, 1, x_1818);
x_1820 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1820, 0, x_1819);
lean_ctor_set(x_1820, 1, x_1811);
x_1821 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1822 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1822, 0, x_1820);
lean_ctor_set(x_1822, 1, x_1821);
x_1823 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1822, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1823;
}
else
{
lean_object* x_1824; 
lean_dec(x_1786);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1824 = lean_ctor_get(x_1809, 0);
lean_inc(x_1824);
lean_dec_ref(x_1809);
lean_ctor_set(x_1789, 0, x_1824);
return x_1789;
}
}
}
else
{
lean_object* x_1825; lean_object* x_1826; lean_object* x_1827; 
x_1825 = lean_ctor_get(x_1789, 0);
lean_inc(x_1825);
lean_dec(x_1789);
x_1826 = lean_ctor_get(x_1825, 0);
lean_inc(x_1826);
if (lean_is_exclusive(x_1825)) {
 lean_ctor_release(x_1825, 0);
 lean_ctor_release(x_1825, 1);
 x_1827 = x_1825;
} else {
 lean_dec_ref(x_1825);
 x_1827 = lean_box(0);
}
if (lean_obj_tag(x_1826) == 0)
{
lean_object* x_1828; lean_object* x_1829; lean_object* x_1830; lean_object* x_1831; lean_object* x_1832; lean_object* x_1833; lean_object* x_1834; lean_object* x_1835; lean_object* x_1836; lean_object* x_1837; lean_object* x_1838; lean_object* x_1839; lean_object* x_1840; lean_object* x_1841; 
x_1828 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1829 = l_Lean_MessageData_ofName(x_1786);
lean_inc_ref(x_1829);
if (lean_is_scalar(x_1827)) {
 x_1830 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1830 = x_1827;
 lean_ctor_set_tag(x_1830, 7);
}
lean_ctor_set(x_1830, 0, x_1828);
lean_ctor_set(x_1830, 1, x_1829);
x_1831 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1832 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1832, 0, x_1830);
lean_ctor_set(x_1832, 1, x_1831);
x_1833 = l_Lean_MessageData_ofSyntax(x_1);
x_1834 = l_Lean_indentD(x_1833);
x_1835 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1835, 0, x_1832);
lean_ctor_set(x_1835, 1, x_1834);
x_1836 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1837 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1837, 0, x_1835);
lean_ctor_set(x_1837, 1, x_1836);
x_1838 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1838, 0, x_1837);
lean_ctor_set(x_1838, 1, x_1829);
x_1839 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1840 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1840, 0, x_1838);
lean_ctor_set(x_1840, 1, x_1839);
x_1841 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1840, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1841;
}
else
{
lean_object* x_1842; lean_object* x_1843; 
lean_dec(x_1827);
lean_dec(x_1786);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1842 = lean_ctor_get(x_1826, 0);
lean_inc(x_1842);
lean_dec_ref(x_1826);
x_1843 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1843, 0, x_1842);
return x_1843;
}
}
}
else
{
uint8_t x_1844; 
lean_dec(x_1786);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1844 = !lean_is_exclusive(x_1789);
if (x_1844 == 0)
{
return x_1789;
}
else
{
lean_object* x_1845; lean_object* x_1846; 
x_1845 = lean_ctor_get(x_1789, 0);
lean_inc(x_1845);
lean_dec(x_1789);
x_1846 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1846, 0, x_1845);
return x_1846;
}
}
}
else
{
uint8_t x_1847; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1847 = !lean_is_exclusive(x_1783);
if (x_1847 == 0)
{
return x_1783;
}
else
{
lean_object* x_1848; lean_object* x_1849; 
x_1848 = lean_ctor_get(x_1783, 0);
lean_inc(x_1848);
lean_dec(x_1783);
x_1849 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1849, 0, x_1848);
return x_1849;
}
}
}
else
{
lean_object* x_1850; 
lean_dec(x_1);
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
x_1850 = l_Lean_Elab_Do_getLetPatDeclVars(x_1778, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1778);
if (lean_obj_tag(x_1850) == 0)
{
lean_object* x_1851; lean_object* x_1852; lean_object* x_1853; 
x_1851 = lean_ctor_get(x_1850, 0);
lean_inc(x_1851);
lean_dec_ref(x_1850);
x_1852 = lean_box(0);
x_1853 = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(x_1851, x_1852, x_1852, x_1852, x_2, x_3, x_4, x_5, x_6, x_7);
return x_1853;
}
else
{
uint8_t x_1854; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1854 = !lean_is_exclusive(x_1850);
if (x_1854 == 0)
{
return x_1850;
}
else
{
lean_object* x_1855; lean_object* x_1856; 
x_1855 = lean_ctor_get(x_1850, 0);
lean_inc(x_1855);
lean_dec(x_1850);
x_1856 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1856, 0, x_1855);
return x_1856;
}
}
}
}
else
{
lean_object* x_1857; 
lean_dec(x_1);
lean_inc_ref(x_2);
x_1857 = l_Lean_Elab_Do_getLetIdDeclVars(x_1778, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_1778);
if (lean_obj_tag(x_1857) == 0)
{
lean_object* x_1858; lean_object* x_1859; lean_object* x_1860; 
x_1858 = lean_ctor_get(x_1857, 0);
lean_inc(x_1858);
lean_dec_ref(x_1857);
x_1859 = lean_box(0);
x_1860 = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(x_1858, x_1859, x_1859, x_1859, x_2, x_3, x_4, x_5, x_6, x_7);
return x_1860;
}
else
{
uint8_t x_1861; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
x_1861 = !lean_is_exclusive(x_1857);
if (x_1861 == 0)
{
return x_1857;
}
else
{
lean_object* x_1862; lean_object* x_1863; 
x_1862 = lean_ctor_get(x_1857, 0);
lean_inc(x_1862);
lean_dec(x_1857);
x_1863 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1863, 0, x_1862);
return x_1863;
}
}
}
}
}
else
{
lean_object* x_1864; lean_object* x_1865; uint8_t x_1866; 
x_1864 = lean_unsigned_to_nat(1u);
x_1865 = l_Lean_Syntax_getArg(x_1, x_1864);
x_1866 = l_Lean_Syntax_isNone(x_1865);
if (x_1866 == 0)
{
uint8_t x_1867; 
x_1867 = l_Lean_Syntax_matchesNull(x_1865, x_1864);
if (x_1867 == 0)
{
lean_object* x_1868; lean_object* x_1869; lean_object* x_1870; lean_object* x_1871; lean_object* x_1872; lean_object* x_1873; lean_object* x_1874; 
x_1868 = lean_st_ref_get(x_7);
x_1869 = lean_ctor_get(x_1868, 0);
lean_inc_ref(x_1869);
lean_dec(x_1868);
x_1870 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1871 = l_Lean_Syntax_getKind(x_1);
x_1872 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1870, x_1869, x_1871);
x_1873 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_1874 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1872, x_1873, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1874) == 0)
{
uint8_t x_1875; 
x_1875 = !lean_is_exclusive(x_1874);
if (x_1875 == 0)
{
lean_object* x_1876; uint8_t x_1877; 
x_1876 = lean_ctor_get(x_1874, 0);
x_1877 = !lean_is_exclusive(x_1876);
if (x_1877 == 0)
{
lean_object* x_1878; lean_object* x_1879; 
x_1878 = lean_ctor_get(x_1876, 0);
x_1879 = lean_ctor_get(x_1876, 1);
lean_dec(x_1879);
if (lean_obj_tag(x_1878) == 0)
{
lean_object* x_1880; lean_object* x_1881; lean_object* x_1882; lean_object* x_1883; lean_object* x_1884; lean_object* x_1885; lean_object* x_1886; lean_object* x_1887; lean_object* x_1888; lean_object* x_1889; lean_object* x_1890; lean_object* x_1891; lean_object* x_1892; 
lean_free_object(x_1874);
x_1880 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1881 = l_Lean_MessageData_ofName(x_1871);
lean_inc_ref(x_1881);
lean_ctor_set_tag(x_1876, 7);
lean_ctor_set(x_1876, 1, x_1881);
lean_ctor_set(x_1876, 0, x_1880);
x_1882 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1883 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1883, 0, x_1876);
lean_ctor_set(x_1883, 1, x_1882);
x_1884 = l_Lean_MessageData_ofSyntax(x_1);
x_1885 = l_Lean_indentD(x_1884);
x_1886 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1886, 0, x_1883);
lean_ctor_set(x_1886, 1, x_1885);
x_1887 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1888 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1888, 0, x_1886);
lean_ctor_set(x_1888, 1, x_1887);
x_1889 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1889, 0, x_1888);
lean_ctor_set(x_1889, 1, x_1881);
x_1890 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1891 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1891, 0, x_1889);
lean_ctor_set(x_1891, 1, x_1890);
x_1892 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1891, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1892;
}
else
{
lean_object* x_1893; 
lean_free_object(x_1876);
lean_dec(x_1871);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1893 = lean_ctor_get(x_1878, 0);
lean_inc(x_1893);
lean_dec_ref(x_1878);
lean_ctor_set(x_1874, 0, x_1893);
return x_1874;
}
}
else
{
lean_object* x_1894; 
x_1894 = lean_ctor_get(x_1876, 0);
lean_inc(x_1894);
lean_dec(x_1876);
if (lean_obj_tag(x_1894) == 0)
{
lean_object* x_1895; lean_object* x_1896; lean_object* x_1897; lean_object* x_1898; lean_object* x_1899; lean_object* x_1900; lean_object* x_1901; lean_object* x_1902; lean_object* x_1903; lean_object* x_1904; lean_object* x_1905; lean_object* x_1906; lean_object* x_1907; lean_object* x_1908; 
lean_free_object(x_1874);
x_1895 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1896 = l_Lean_MessageData_ofName(x_1871);
lean_inc_ref(x_1896);
x_1897 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1897, 0, x_1895);
lean_ctor_set(x_1897, 1, x_1896);
x_1898 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1899 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1899, 0, x_1897);
lean_ctor_set(x_1899, 1, x_1898);
x_1900 = l_Lean_MessageData_ofSyntax(x_1);
x_1901 = l_Lean_indentD(x_1900);
x_1902 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1902, 0, x_1899);
lean_ctor_set(x_1902, 1, x_1901);
x_1903 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1904 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1904, 0, x_1902);
lean_ctor_set(x_1904, 1, x_1903);
x_1905 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1905, 0, x_1904);
lean_ctor_set(x_1905, 1, x_1896);
x_1906 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1907 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1907, 0, x_1905);
lean_ctor_set(x_1907, 1, x_1906);
x_1908 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1907, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1908;
}
else
{
lean_object* x_1909; 
lean_dec(x_1871);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1909 = lean_ctor_get(x_1894, 0);
lean_inc(x_1909);
lean_dec_ref(x_1894);
lean_ctor_set(x_1874, 0, x_1909);
return x_1874;
}
}
}
else
{
lean_object* x_1910; lean_object* x_1911; lean_object* x_1912; 
x_1910 = lean_ctor_get(x_1874, 0);
lean_inc(x_1910);
lean_dec(x_1874);
x_1911 = lean_ctor_get(x_1910, 0);
lean_inc(x_1911);
if (lean_is_exclusive(x_1910)) {
 lean_ctor_release(x_1910, 0);
 lean_ctor_release(x_1910, 1);
 x_1912 = x_1910;
} else {
 lean_dec_ref(x_1910);
 x_1912 = lean_box(0);
}
if (lean_obj_tag(x_1911) == 0)
{
lean_object* x_1913; lean_object* x_1914; lean_object* x_1915; lean_object* x_1916; lean_object* x_1917; lean_object* x_1918; lean_object* x_1919; lean_object* x_1920; lean_object* x_1921; lean_object* x_1922; lean_object* x_1923; lean_object* x_1924; lean_object* x_1925; lean_object* x_1926; 
x_1913 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1914 = l_Lean_MessageData_ofName(x_1871);
lean_inc_ref(x_1914);
if (lean_is_scalar(x_1912)) {
 x_1915 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1915 = x_1912;
 lean_ctor_set_tag(x_1915, 7);
}
lean_ctor_set(x_1915, 0, x_1913);
lean_ctor_set(x_1915, 1, x_1914);
x_1916 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1917 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1917, 0, x_1915);
lean_ctor_set(x_1917, 1, x_1916);
x_1918 = l_Lean_MessageData_ofSyntax(x_1);
x_1919 = l_Lean_indentD(x_1918);
x_1920 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1920, 0, x_1917);
lean_ctor_set(x_1920, 1, x_1919);
x_1921 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1922 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1922, 0, x_1920);
lean_ctor_set(x_1922, 1, x_1921);
x_1923 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1923, 0, x_1922);
lean_ctor_set(x_1923, 1, x_1914);
x_1924 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1925 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1925, 0, x_1923);
lean_ctor_set(x_1925, 1, x_1924);
x_1926 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1925, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1926;
}
else
{
lean_object* x_1927; lean_object* x_1928; 
lean_dec(x_1912);
lean_dec(x_1871);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1927 = lean_ctor_get(x_1911, 0);
lean_inc(x_1927);
lean_dec_ref(x_1911);
x_1928 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1928, 0, x_1927);
return x_1928;
}
}
}
else
{
uint8_t x_1929; 
lean_dec(x_1871);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1929 = !lean_is_exclusive(x_1874);
if (x_1929 == 0)
{
return x_1874;
}
else
{
lean_object* x_1930; lean_object* x_1931; 
x_1930 = lean_ctor_get(x_1874, 0);
lean_inc(x_1930);
lean_dec(x_1874);
x_1931 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1931, 0, x_1930);
return x_1931;
}
}
}
else
{
x_164 = x_2;
x_165 = x_3;
x_166 = x_4;
x_167 = x_5;
x_168 = x_6;
x_169 = x_7;
x_170 = lean_box(0);
goto block_174;
}
}
else
{
lean_dec(x_1865);
x_164 = x_2;
x_165 = x_3;
x_166 = x_4;
x_167 = x_5;
x_168 = x_6;
x_169 = x_7;
x_170 = lean_box(0);
goto block_174;
}
}
}
else
{
lean_object* x_1932; lean_object* x_1933; uint8_t x_1934; 
x_1932 = lean_unsigned_to_nat(1u);
x_1933 = l_Lean_Syntax_getArg(x_1, x_1932);
x_1934 = l_Lean_Syntax_isNone(x_1933);
if (x_1934 == 0)
{
uint8_t x_1935; 
x_1935 = l_Lean_Syntax_matchesNull(x_1933, x_1932);
if (x_1935 == 0)
{
lean_object* x_1936; lean_object* x_1937; lean_object* x_1938; lean_object* x_1939; lean_object* x_1940; lean_object* x_1941; lean_object* x_1942; 
x_1936 = lean_st_ref_get(x_7);
x_1937 = lean_ctor_get(x_1936, 0);
lean_inc_ref(x_1937);
lean_dec(x_1936);
x_1938 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_1939 = l_Lean_Syntax_getKind(x_1);
x_1940 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_1938, x_1937, x_1939);
x_1941 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_1942 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_1940, x_1941, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_1942) == 0)
{
uint8_t x_1943; 
x_1943 = !lean_is_exclusive(x_1942);
if (x_1943 == 0)
{
lean_object* x_1944; uint8_t x_1945; 
x_1944 = lean_ctor_get(x_1942, 0);
x_1945 = !lean_is_exclusive(x_1944);
if (x_1945 == 0)
{
lean_object* x_1946; lean_object* x_1947; 
x_1946 = lean_ctor_get(x_1944, 0);
x_1947 = lean_ctor_get(x_1944, 1);
lean_dec(x_1947);
if (lean_obj_tag(x_1946) == 0)
{
lean_object* x_1948; lean_object* x_1949; lean_object* x_1950; lean_object* x_1951; lean_object* x_1952; lean_object* x_1953; lean_object* x_1954; lean_object* x_1955; lean_object* x_1956; lean_object* x_1957; lean_object* x_1958; lean_object* x_1959; lean_object* x_1960; 
lean_free_object(x_1942);
x_1948 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1949 = l_Lean_MessageData_ofName(x_1939);
lean_inc_ref(x_1949);
lean_ctor_set_tag(x_1944, 7);
lean_ctor_set(x_1944, 1, x_1949);
lean_ctor_set(x_1944, 0, x_1948);
x_1950 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1951 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1951, 0, x_1944);
lean_ctor_set(x_1951, 1, x_1950);
x_1952 = l_Lean_MessageData_ofSyntax(x_1);
x_1953 = l_Lean_indentD(x_1952);
x_1954 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1954, 0, x_1951);
lean_ctor_set(x_1954, 1, x_1953);
x_1955 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1956 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1956, 0, x_1954);
lean_ctor_set(x_1956, 1, x_1955);
x_1957 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1957, 0, x_1956);
lean_ctor_set(x_1957, 1, x_1949);
x_1958 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1959 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1959, 0, x_1957);
lean_ctor_set(x_1959, 1, x_1958);
x_1960 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1959, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1960;
}
else
{
lean_object* x_1961; 
lean_free_object(x_1944);
lean_dec(x_1939);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1961 = lean_ctor_get(x_1946, 0);
lean_inc(x_1961);
lean_dec_ref(x_1946);
lean_ctor_set(x_1942, 0, x_1961);
return x_1942;
}
}
else
{
lean_object* x_1962; 
x_1962 = lean_ctor_get(x_1944, 0);
lean_inc(x_1962);
lean_dec(x_1944);
if (lean_obj_tag(x_1962) == 0)
{
lean_object* x_1963; lean_object* x_1964; lean_object* x_1965; lean_object* x_1966; lean_object* x_1967; lean_object* x_1968; lean_object* x_1969; lean_object* x_1970; lean_object* x_1971; lean_object* x_1972; lean_object* x_1973; lean_object* x_1974; lean_object* x_1975; lean_object* x_1976; 
lean_free_object(x_1942);
x_1963 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1964 = l_Lean_MessageData_ofName(x_1939);
lean_inc_ref(x_1964);
x_1965 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1965, 0, x_1963);
lean_ctor_set(x_1965, 1, x_1964);
x_1966 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1967 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1967, 0, x_1965);
lean_ctor_set(x_1967, 1, x_1966);
x_1968 = l_Lean_MessageData_ofSyntax(x_1);
x_1969 = l_Lean_indentD(x_1968);
x_1970 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1970, 0, x_1967);
lean_ctor_set(x_1970, 1, x_1969);
x_1971 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1972 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1972, 0, x_1970);
lean_ctor_set(x_1972, 1, x_1971);
x_1973 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1973, 0, x_1972);
lean_ctor_set(x_1973, 1, x_1964);
x_1974 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1975 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1975, 0, x_1973);
lean_ctor_set(x_1975, 1, x_1974);
x_1976 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1975, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1976;
}
else
{
lean_object* x_1977; 
lean_dec(x_1939);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1977 = lean_ctor_get(x_1962, 0);
lean_inc(x_1977);
lean_dec_ref(x_1962);
lean_ctor_set(x_1942, 0, x_1977);
return x_1942;
}
}
}
else
{
lean_object* x_1978; lean_object* x_1979; lean_object* x_1980; 
x_1978 = lean_ctor_get(x_1942, 0);
lean_inc(x_1978);
lean_dec(x_1942);
x_1979 = lean_ctor_get(x_1978, 0);
lean_inc(x_1979);
if (lean_is_exclusive(x_1978)) {
 lean_ctor_release(x_1978, 0);
 lean_ctor_release(x_1978, 1);
 x_1980 = x_1978;
} else {
 lean_dec_ref(x_1978);
 x_1980 = lean_box(0);
}
if (lean_obj_tag(x_1979) == 0)
{
lean_object* x_1981; lean_object* x_1982; lean_object* x_1983; lean_object* x_1984; lean_object* x_1985; lean_object* x_1986; lean_object* x_1987; lean_object* x_1988; lean_object* x_1989; lean_object* x_1990; lean_object* x_1991; lean_object* x_1992; lean_object* x_1993; lean_object* x_1994; 
x_1981 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_1982 = l_Lean_MessageData_ofName(x_1939);
lean_inc_ref(x_1982);
if (lean_is_scalar(x_1980)) {
 x_1983 = lean_alloc_ctor(7, 2, 0);
} else {
 x_1983 = x_1980;
 lean_ctor_set_tag(x_1983, 7);
}
lean_ctor_set(x_1983, 0, x_1981);
lean_ctor_set(x_1983, 1, x_1982);
x_1984 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_1985 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1985, 0, x_1983);
lean_ctor_set(x_1985, 1, x_1984);
x_1986 = l_Lean_MessageData_ofSyntax(x_1);
x_1987 = l_Lean_indentD(x_1986);
x_1988 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1988, 0, x_1985);
lean_ctor_set(x_1988, 1, x_1987);
x_1989 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_1990 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1990, 0, x_1988);
lean_ctor_set(x_1990, 1, x_1989);
x_1991 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1991, 0, x_1990);
lean_ctor_set(x_1991, 1, x_1982);
x_1992 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_1993 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_1993, 0, x_1991);
lean_ctor_set(x_1993, 1, x_1992);
x_1994 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_1993, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_1994;
}
else
{
lean_object* x_1995; lean_object* x_1996; 
lean_dec(x_1980);
lean_dec(x_1939);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1995 = lean_ctor_get(x_1979, 0);
lean_inc(x_1995);
lean_dec_ref(x_1979);
x_1996 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_1996, 0, x_1995);
return x_1996;
}
}
}
else
{
uint8_t x_1997; 
lean_dec(x_1939);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_1997 = !lean_is_exclusive(x_1942);
if (x_1997 == 0)
{
return x_1942;
}
else
{
lean_object* x_1998; lean_object* x_1999; 
x_1998 = lean_ctor_get(x_1942, 0);
lean_inc(x_1998);
lean_dec(x_1942);
x_1999 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_1999, 0, x_1998);
return x_1999;
}
}
}
else
{
x_23 = x_2;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = lean_box(0);
goto block_39;
}
}
else
{
lean_dec(x_1933);
x_23 = x_2;
x_24 = x_3;
x_25 = x_4;
x_26 = x_5;
x_27 = x_6;
x_28 = x_7;
x_29 = lean_box(0);
goto block_39;
}
}
block_174:
{
lean_object* x_171; lean_object* x_172; lean_object* x_173; 
x_171 = lean_unsigned_to_nat(2u);
x_172 = l_Lean_Syntax_getArg(x_1, x_171);
lean_dec(x_1);
x_173 = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(x_163, x_172, x_164, x_165, x_166, x_167, x_168, x_169);
return x_173;
}
}
else
{
lean_object* x_2000; lean_object* x_2001; lean_object* x_2002; uint8_t x_2003; 
x_2000 = lean_unsigned_to_nat(0u);
x_2001 = l_Lean_Syntax_getArg(x_1, x_2000);
x_2002 = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__13___closed__1));
x_2003 = l_Lean_Syntax_isOfKind(x_2001, x_2002);
if (x_2003 == 0)
{
lean_object* x_2004; lean_object* x_2005; lean_object* x_2006; lean_object* x_2007; lean_object* x_2008; lean_object* x_2009; lean_object* x_2010; 
x_2004 = lean_st_ref_get(x_7);
x_2005 = lean_ctor_get(x_2004, 0);
lean_inc_ref(x_2005);
lean_dec(x_2004);
x_2006 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_2007 = l_Lean_Syntax_getKind(x_1);
x_2008 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_2006, x_2005, x_2007);
x_2009 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_2010 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_2008, x_2009, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_2010) == 0)
{
uint8_t x_2011; 
x_2011 = !lean_is_exclusive(x_2010);
if (x_2011 == 0)
{
lean_object* x_2012; uint8_t x_2013; 
x_2012 = lean_ctor_get(x_2010, 0);
x_2013 = !lean_is_exclusive(x_2012);
if (x_2013 == 0)
{
lean_object* x_2014; lean_object* x_2015; 
x_2014 = lean_ctor_get(x_2012, 0);
x_2015 = lean_ctor_get(x_2012, 1);
lean_dec(x_2015);
if (lean_obj_tag(x_2014) == 0)
{
lean_object* x_2016; lean_object* x_2017; lean_object* x_2018; lean_object* x_2019; lean_object* x_2020; lean_object* x_2021; lean_object* x_2022; lean_object* x_2023; lean_object* x_2024; lean_object* x_2025; lean_object* x_2026; lean_object* x_2027; lean_object* x_2028; 
lean_free_object(x_2010);
x_2016 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2017 = l_Lean_MessageData_ofName(x_2007);
lean_inc_ref(x_2017);
lean_ctor_set_tag(x_2012, 7);
lean_ctor_set(x_2012, 1, x_2017);
lean_ctor_set(x_2012, 0, x_2016);
x_2018 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2019 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2019, 0, x_2012);
lean_ctor_set(x_2019, 1, x_2018);
x_2020 = l_Lean_MessageData_ofSyntax(x_1);
x_2021 = l_Lean_indentD(x_2020);
x_2022 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2022, 0, x_2019);
lean_ctor_set(x_2022, 1, x_2021);
x_2023 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2024 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2024, 0, x_2022);
lean_ctor_set(x_2024, 1, x_2023);
x_2025 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2025, 0, x_2024);
lean_ctor_set(x_2025, 1, x_2017);
x_2026 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2027 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2027, 0, x_2025);
lean_ctor_set(x_2027, 1, x_2026);
x_2028 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2027, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2028;
}
else
{
lean_object* x_2029; 
lean_free_object(x_2012);
lean_dec(x_2007);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2029 = lean_ctor_get(x_2014, 0);
lean_inc(x_2029);
lean_dec_ref(x_2014);
lean_ctor_set(x_2010, 0, x_2029);
return x_2010;
}
}
else
{
lean_object* x_2030; 
x_2030 = lean_ctor_get(x_2012, 0);
lean_inc(x_2030);
lean_dec(x_2012);
if (lean_obj_tag(x_2030) == 0)
{
lean_object* x_2031; lean_object* x_2032; lean_object* x_2033; lean_object* x_2034; lean_object* x_2035; lean_object* x_2036; lean_object* x_2037; lean_object* x_2038; lean_object* x_2039; lean_object* x_2040; lean_object* x_2041; lean_object* x_2042; lean_object* x_2043; lean_object* x_2044; 
lean_free_object(x_2010);
x_2031 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2032 = l_Lean_MessageData_ofName(x_2007);
lean_inc_ref(x_2032);
x_2033 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2033, 0, x_2031);
lean_ctor_set(x_2033, 1, x_2032);
x_2034 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2035 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2035, 0, x_2033);
lean_ctor_set(x_2035, 1, x_2034);
x_2036 = l_Lean_MessageData_ofSyntax(x_1);
x_2037 = l_Lean_indentD(x_2036);
x_2038 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2038, 0, x_2035);
lean_ctor_set(x_2038, 1, x_2037);
x_2039 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2040 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2040, 0, x_2038);
lean_ctor_set(x_2040, 1, x_2039);
x_2041 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2041, 0, x_2040);
lean_ctor_set(x_2041, 1, x_2032);
x_2042 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2043 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2043, 0, x_2041);
lean_ctor_set(x_2043, 1, x_2042);
x_2044 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2043, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2044;
}
else
{
lean_object* x_2045; 
lean_dec(x_2007);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2045 = lean_ctor_get(x_2030, 0);
lean_inc(x_2045);
lean_dec_ref(x_2030);
lean_ctor_set(x_2010, 0, x_2045);
return x_2010;
}
}
}
else
{
lean_object* x_2046; lean_object* x_2047; lean_object* x_2048; 
x_2046 = lean_ctor_get(x_2010, 0);
lean_inc(x_2046);
lean_dec(x_2010);
x_2047 = lean_ctor_get(x_2046, 0);
lean_inc(x_2047);
if (lean_is_exclusive(x_2046)) {
 lean_ctor_release(x_2046, 0);
 lean_ctor_release(x_2046, 1);
 x_2048 = x_2046;
} else {
 lean_dec_ref(x_2046);
 x_2048 = lean_box(0);
}
if (lean_obj_tag(x_2047) == 0)
{
lean_object* x_2049; lean_object* x_2050; lean_object* x_2051; lean_object* x_2052; lean_object* x_2053; lean_object* x_2054; lean_object* x_2055; lean_object* x_2056; lean_object* x_2057; lean_object* x_2058; lean_object* x_2059; lean_object* x_2060; lean_object* x_2061; lean_object* x_2062; 
x_2049 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2050 = l_Lean_MessageData_ofName(x_2007);
lean_inc_ref(x_2050);
if (lean_is_scalar(x_2048)) {
 x_2051 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2051 = x_2048;
 lean_ctor_set_tag(x_2051, 7);
}
lean_ctor_set(x_2051, 0, x_2049);
lean_ctor_set(x_2051, 1, x_2050);
x_2052 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2053 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2053, 0, x_2051);
lean_ctor_set(x_2053, 1, x_2052);
x_2054 = l_Lean_MessageData_ofSyntax(x_1);
x_2055 = l_Lean_indentD(x_2054);
x_2056 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2056, 0, x_2053);
lean_ctor_set(x_2056, 1, x_2055);
x_2057 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2058 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2058, 0, x_2056);
lean_ctor_set(x_2058, 1, x_2057);
x_2059 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2059, 0, x_2058);
lean_ctor_set(x_2059, 1, x_2050);
x_2060 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2061 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2061, 0, x_2059);
lean_ctor_set(x_2061, 1, x_2060);
x_2062 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2061, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2062;
}
else
{
lean_object* x_2063; lean_object* x_2064; 
lean_dec(x_2048);
lean_dec(x_2007);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2063 = lean_ctor_get(x_2047, 0);
lean_inc(x_2063);
lean_dec_ref(x_2047);
x_2064 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2064, 0, x_2063);
return x_2064;
}
}
}
else
{
uint8_t x_2065; 
lean_dec(x_2007);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2065 = !lean_is_exclusive(x_2010);
if (x_2065 == 0)
{
return x_2010;
}
else
{
lean_object* x_2066; lean_object* x_2067; 
x_2066 = lean_ctor_get(x_2010, 0);
lean_inc(x_2066);
lean_dec(x_2010);
x_2067 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2067, 0, x_2066);
return x_2067;
}
}
}
else
{
lean_object* x_2068; lean_object* x_2069; lean_object* x_2070; uint8_t x_2071; 
x_2068 = lean_unsigned_to_nat(1u);
x_2069 = l_Lean_Syntax_getArg(x_1, x_2068);
x_2070 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__73));
lean_inc(x_2069);
x_2071 = l_Lean_Syntax_isOfKind(x_2069, x_2070);
if (x_2071 == 0)
{
lean_object* x_2072; lean_object* x_2073; lean_object* x_2074; lean_object* x_2075; lean_object* x_2076; lean_object* x_2077; lean_object* x_2078; 
lean_dec(x_2069);
x_2072 = lean_st_ref_get(x_7);
x_2073 = lean_ctor_get(x_2072, 0);
lean_inc_ref(x_2073);
lean_dec(x_2072);
x_2074 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_2075 = l_Lean_Syntax_getKind(x_1);
x_2076 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_2074, x_2073, x_2075);
x_2077 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_2078 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_2076, x_2077, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_2078) == 0)
{
uint8_t x_2079; 
x_2079 = !lean_is_exclusive(x_2078);
if (x_2079 == 0)
{
lean_object* x_2080; uint8_t x_2081; 
x_2080 = lean_ctor_get(x_2078, 0);
x_2081 = !lean_is_exclusive(x_2080);
if (x_2081 == 0)
{
lean_object* x_2082; lean_object* x_2083; 
x_2082 = lean_ctor_get(x_2080, 0);
x_2083 = lean_ctor_get(x_2080, 1);
lean_dec(x_2083);
if (lean_obj_tag(x_2082) == 0)
{
lean_object* x_2084; lean_object* x_2085; lean_object* x_2086; lean_object* x_2087; lean_object* x_2088; lean_object* x_2089; lean_object* x_2090; lean_object* x_2091; lean_object* x_2092; lean_object* x_2093; lean_object* x_2094; lean_object* x_2095; lean_object* x_2096; 
lean_free_object(x_2078);
x_2084 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2085 = l_Lean_MessageData_ofName(x_2075);
lean_inc_ref(x_2085);
lean_ctor_set_tag(x_2080, 7);
lean_ctor_set(x_2080, 1, x_2085);
lean_ctor_set(x_2080, 0, x_2084);
x_2086 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2087 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2087, 0, x_2080);
lean_ctor_set(x_2087, 1, x_2086);
x_2088 = l_Lean_MessageData_ofSyntax(x_1);
x_2089 = l_Lean_indentD(x_2088);
x_2090 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2090, 0, x_2087);
lean_ctor_set(x_2090, 1, x_2089);
x_2091 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2092 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2092, 0, x_2090);
lean_ctor_set(x_2092, 1, x_2091);
x_2093 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2093, 0, x_2092);
lean_ctor_set(x_2093, 1, x_2085);
x_2094 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2095 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2095, 0, x_2093);
lean_ctor_set(x_2095, 1, x_2094);
x_2096 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2095, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2096;
}
else
{
lean_object* x_2097; 
lean_free_object(x_2080);
lean_dec(x_2075);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2097 = lean_ctor_get(x_2082, 0);
lean_inc(x_2097);
lean_dec_ref(x_2082);
lean_ctor_set(x_2078, 0, x_2097);
return x_2078;
}
}
else
{
lean_object* x_2098; 
x_2098 = lean_ctor_get(x_2080, 0);
lean_inc(x_2098);
lean_dec(x_2080);
if (lean_obj_tag(x_2098) == 0)
{
lean_object* x_2099; lean_object* x_2100; lean_object* x_2101; lean_object* x_2102; lean_object* x_2103; lean_object* x_2104; lean_object* x_2105; lean_object* x_2106; lean_object* x_2107; lean_object* x_2108; lean_object* x_2109; lean_object* x_2110; lean_object* x_2111; lean_object* x_2112; 
lean_free_object(x_2078);
x_2099 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2100 = l_Lean_MessageData_ofName(x_2075);
lean_inc_ref(x_2100);
x_2101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2101, 0, x_2099);
lean_ctor_set(x_2101, 1, x_2100);
x_2102 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2103 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2103, 0, x_2101);
lean_ctor_set(x_2103, 1, x_2102);
x_2104 = l_Lean_MessageData_ofSyntax(x_1);
x_2105 = l_Lean_indentD(x_2104);
x_2106 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2106, 0, x_2103);
lean_ctor_set(x_2106, 1, x_2105);
x_2107 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2108 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2108, 0, x_2106);
lean_ctor_set(x_2108, 1, x_2107);
x_2109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2109, 0, x_2108);
lean_ctor_set(x_2109, 1, x_2100);
x_2110 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2111 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2111, 0, x_2109);
lean_ctor_set(x_2111, 1, x_2110);
x_2112 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2111, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2112;
}
else
{
lean_object* x_2113; 
lean_dec(x_2075);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2113 = lean_ctor_get(x_2098, 0);
lean_inc(x_2113);
lean_dec_ref(x_2098);
lean_ctor_set(x_2078, 0, x_2113);
return x_2078;
}
}
}
else
{
lean_object* x_2114; lean_object* x_2115; lean_object* x_2116; 
x_2114 = lean_ctor_get(x_2078, 0);
lean_inc(x_2114);
lean_dec(x_2078);
x_2115 = lean_ctor_get(x_2114, 0);
lean_inc(x_2115);
if (lean_is_exclusive(x_2114)) {
 lean_ctor_release(x_2114, 0);
 lean_ctor_release(x_2114, 1);
 x_2116 = x_2114;
} else {
 lean_dec_ref(x_2114);
 x_2116 = lean_box(0);
}
if (lean_obj_tag(x_2115) == 0)
{
lean_object* x_2117; lean_object* x_2118; lean_object* x_2119; lean_object* x_2120; lean_object* x_2121; lean_object* x_2122; lean_object* x_2123; lean_object* x_2124; lean_object* x_2125; lean_object* x_2126; lean_object* x_2127; lean_object* x_2128; lean_object* x_2129; lean_object* x_2130; 
x_2117 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2118 = l_Lean_MessageData_ofName(x_2075);
lean_inc_ref(x_2118);
if (lean_is_scalar(x_2116)) {
 x_2119 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2119 = x_2116;
 lean_ctor_set_tag(x_2119, 7);
}
lean_ctor_set(x_2119, 0, x_2117);
lean_ctor_set(x_2119, 1, x_2118);
x_2120 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2121 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2121, 0, x_2119);
lean_ctor_set(x_2121, 1, x_2120);
x_2122 = l_Lean_MessageData_ofSyntax(x_1);
x_2123 = l_Lean_indentD(x_2122);
x_2124 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2124, 0, x_2121);
lean_ctor_set(x_2124, 1, x_2123);
x_2125 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2126 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2126, 0, x_2124);
lean_ctor_set(x_2126, 1, x_2125);
x_2127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2127, 0, x_2126);
lean_ctor_set(x_2127, 1, x_2118);
x_2128 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2129 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2129, 0, x_2127);
lean_ctor_set(x_2129, 1, x_2128);
x_2130 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2129, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2130;
}
else
{
lean_object* x_2131; lean_object* x_2132; 
lean_dec(x_2116);
lean_dec(x_2075);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2131 = lean_ctor_get(x_2115, 0);
lean_inc(x_2131);
lean_dec_ref(x_2115);
x_2132 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2132, 0, x_2131);
return x_2132;
}
}
}
else
{
uint8_t x_2133; 
lean_dec(x_2075);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2133 = !lean_is_exclusive(x_2078);
if (x_2133 == 0)
{
return x_2078;
}
else
{
lean_object* x_2134; lean_object* x_2135; 
x_2134 = lean_ctor_get(x_2078, 0);
lean_inc(x_2134);
lean_dec(x_2078);
x_2135 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2135, 0, x_2134);
return x_2135;
}
}
}
else
{
lean_object* x_2136; uint8_t x_2137; 
x_2136 = l_Lean_Syntax_getArg(x_2069, x_2000);
lean_dec(x_2069);
lean_inc(x_2136);
x_2137 = l_Lean_Syntax_matchesNull(x_2136, x_2068);
if (x_2137 == 0)
{
lean_object* x_2138; lean_object* x_2139; lean_object* x_2140; lean_object* x_2141; lean_object* x_2142; lean_object* x_2143; lean_object* x_2144; 
lean_dec(x_2136);
x_2138 = lean_st_ref_get(x_7);
x_2139 = lean_ctor_get(x_2138, 0);
lean_inc_ref(x_2139);
lean_dec(x_2138);
x_2140 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_2141 = l_Lean_Syntax_getKind(x_1);
x_2142 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_2140, x_2139, x_2141);
x_2143 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_2144 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_2142, x_2143, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_2144) == 0)
{
uint8_t x_2145; 
x_2145 = !lean_is_exclusive(x_2144);
if (x_2145 == 0)
{
lean_object* x_2146; uint8_t x_2147; 
x_2146 = lean_ctor_get(x_2144, 0);
x_2147 = !lean_is_exclusive(x_2146);
if (x_2147 == 0)
{
lean_object* x_2148; lean_object* x_2149; 
x_2148 = lean_ctor_get(x_2146, 0);
x_2149 = lean_ctor_get(x_2146, 1);
lean_dec(x_2149);
if (lean_obj_tag(x_2148) == 0)
{
lean_object* x_2150; lean_object* x_2151; lean_object* x_2152; lean_object* x_2153; lean_object* x_2154; lean_object* x_2155; lean_object* x_2156; lean_object* x_2157; lean_object* x_2158; lean_object* x_2159; lean_object* x_2160; lean_object* x_2161; lean_object* x_2162; 
lean_free_object(x_2144);
x_2150 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2151 = l_Lean_MessageData_ofName(x_2141);
lean_inc_ref(x_2151);
lean_ctor_set_tag(x_2146, 7);
lean_ctor_set(x_2146, 1, x_2151);
lean_ctor_set(x_2146, 0, x_2150);
x_2152 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2153 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2153, 0, x_2146);
lean_ctor_set(x_2153, 1, x_2152);
x_2154 = l_Lean_MessageData_ofSyntax(x_1);
x_2155 = l_Lean_indentD(x_2154);
x_2156 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2156, 0, x_2153);
lean_ctor_set(x_2156, 1, x_2155);
x_2157 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2158 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2158, 0, x_2156);
lean_ctor_set(x_2158, 1, x_2157);
x_2159 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2159, 0, x_2158);
lean_ctor_set(x_2159, 1, x_2151);
x_2160 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2161 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2161, 0, x_2159);
lean_ctor_set(x_2161, 1, x_2160);
x_2162 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2161, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2162;
}
else
{
lean_object* x_2163; 
lean_free_object(x_2146);
lean_dec(x_2141);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2163 = lean_ctor_get(x_2148, 0);
lean_inc(x_2163);
lean_dec_ref(x_2148);
lean_ctor_set(x_2144, 0, x_2163);
return x_2144;
}
}
else
{
lean_object* x_2164; 
x_2164 = lean_ctor_get(x_2146, 0);
lean_inc(x_2164);
lean_dec(x_2146);
if (lean_obj_tag(x_2164) == 0)
{
lean_object* x_2165; lean_object* x_2166; lean_object* x_2167; lean_object* x_2168; lean_object* x_2169; lean_object* x_2170; lean_object* x_2171; lean_object* x_2172; lean_object* x_2173; lean_object* x_2174; lean_object* x_2175; lean_object* x_2176; lean_object* x_2177; lean_object* x_2178; 
lean_free_object(x_2144);
x_2165 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2166 = l_Lean_MessageData_ofName(x_2141);
lean_inc_ref(x_2166);
x_2167 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2167, 0, x_2165);
lean_ctor_set(x_2167, 1, x_2166);
x_2168 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2169 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2169, 0, x_2167);
lean_ctor_set(x_2169, 1, x_2168);
x_2170 = l_Lean_MessageData_ofSyntax(x_1);
x_2171 = l_Lean_indentD(x_2170);
x_2172 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2172, 0, x_2169);
lean_ctor_set(x_2172, 1, x_2171);
x_2173 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2174 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2174, 0, x_2172);
lean_ctor_set(x_2174, 1, x_2173);
x_2175 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2175, 0, x_2174);
lean_ctor_set(x_2175, 1, x_2166);
x_2176 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2177 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2177, 0, x_2175);
lean_ctor_set(x_2177, 1, x_2176);
x_2178 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2177, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2178;
}
else
{
lean_object* x_2179; 
lean_dec(x_2141);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2179 = lean_ctor_get(x_2164, 0);
lean_inc(x_2179);
lean_dec_ref(x_2164);
lean_ctor_set(x_2144, 0, x_2179);
return x_2144;
}
}
}
else
{
lean_object* x_2180; lean_object* x_2181; lean_object* x_2182; 
x_2180 = lean_ctor_get(x_2144, 0);
lean_inc(x_2180);
lean_dec(x_2144);
x_2181 = lean_ctor_get(x_2180, 0);
lean_inc(x_2181);
if (lean_is_exclusive(x_2180)) {
 lean_ctor_release(x_2180, 0);
 lean_ctor_release(x_2180, 1);
 x_2182 = x_2180;
} else {
 lean_dec_ref(x_2180);
 x_2182 = lean_box(0);
}
if (lean_obj_tag(x_2181) == 0)
{
lean_object* x_2183; lean_object* x_2184; lean_object* x_2185; lean_object* x_2186; lean_object* x_2187; lean_object* x_2188; lean_object* x_2189; lean_object* x_2190; lean_object* x_2191; lean_object* x_2192; lean_object* x_2193; lean_object* x_2194; lean_object* x_2195; lean_object* x_2196; 
x_2183 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2184 = l_Lean_MessageData_ofName(x_2141);
lean_inc_ref(x_2184);
if (lean_is_scalar(x_2182)) {
 x_2185 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2185 = x_2182;
 lean_ctor_set_tag(x_2185, 7);
}
lean_ctor_set(x_2185, 0, x_2183);
lean_ctor_set(x_2185, 1, x_2184);
x_2186 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2187 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2187, 0, x_2185);
lean_ctor_set(x_2187, 1, x_2186);
x_2188 = l_Lean_MessageData_ofSyntax(x_1);
x_2189 = l_Lean_indentD(x_2188);
x_2190 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2190, 0, x_2187);
lean_ctor_set(x_2190, 1, x_2189);
x_2191 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2192 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2192, 0, x_2190);
lean_ctor_set(x_2192, 1, x_2191);
x_2193 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2193, 0, x_2192);
lean_ctor_set(x_2193, 1, x_2184);
x_2194 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2195 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2195, 0, x_2193);
lean_ctor_set(x_2195, 1, x_2194);
x_2196 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2195, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2196;
}
else
{
lean_object* x_2197; lean_object* x_2198; 
lean_dec(x_2182);
lean_dec(x_2141);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2197 = lean_ctor_get(x_2181, 0);
lean_inc(x_2197);
lean_dec_ref(x_2181);
x_2198 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2198, 0, x_2197);
return x_2198;
}
}
}
else
{
uint8_t x_2199; 
lean_dec(x_2141);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2199 = !lean_is_exclusive(x_2144);
if (x_2199 == 0)
{
return x_2144;
}
else
{
lean_object* x_2200; lean_object* x_2201; 
x_2200 = lean_ctor_get(x_2144, 0);
lean_inc(x_2200);
lean_dec(x_2144);
x_2201 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2201, 0, x_2200);
return x_2201;
}
}
}
else
{
lean_object* x_2202; lean_object* x_2203; uint8_t x_2204; 
x_2202 = l_Lean_Syntax_getArg(x_2136, x_2000);
lean_dec(x_2136);
x_2203 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__75));
x_2204 = l_Lean_Syntax_isOfKind(x_2202, x_2203);
if (x_2204 == 0)
{
lean_object* x_2205; lean_object* x_2206; lean_object* x_2207; lean_object* x_2208; lean_object* x_2209; lean_object* x_2210; lean_object* x_2211; 
x_2205 = lean_st_ref_get(x_7);
x_2206 = lean_ctor_get(x_2205, 0);
lean_inc_ref(x_2206);
lean_dec(x_2205);
x_2207 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_2208 = l_Lean_Syntax_getKind(x_1);
x_2209 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_2207, x_2206, x_2208);
x_2210 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_2211 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_2209, x_2210, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_2211) == 0)
{
uint8_t x_2212; 
x_2212 = !lean_is_exclusive(x_2211);
if (x_2212 == 0)
{
lean_object* x_2213; uint8_t x_2214; 
x_2213 = lean_ctor_get(x_2211, 0);
x_2214 = !lean_is_exclusive(x_2213);
if (x_2214 == 0)
{
lean_object* x_2215; lean_object* x_2216; 
x_2215 = lean_ctor_get(x_2213, 0);
x_2216 = lean_ctor_get(x_2213, 1);
lean_dec(x_2216);
if (lean_obj_tag(x_2215) == 0)
{
lean_object* x_2217; lean_object* x_2218; lean_object* x_2219; lean_object* x_2220; lean_object* x_2221; lean_object* x_2222; lean_object* x_2223; lean_object* x_2224; lean_object* x_2225; lean_object* x_2226; lean_object* x_2227; lean_object* x_2228; lean_object* x_2229; 
lean_free_object(x_2211);
x_2217 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2218 = l_Lean_MessageData_ofName(x_2208);
lean_inc_ref(x_2218);
lean_ctor_set_tag(x_2213, 7);
lean_ctor_set(x_2213, 1, x_2218);
lean_ctor_set(x_2213, 0, x_2217);
x_2219 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2220 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2220, 0, x_2213);
lean_ctor_set(x_2220, 1, x_2219);
x_2221 = l_Lean_MessageData_ofSyntax(x_1);
x_2222 = l_Lean_indentD(x_2221);
x_2223 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2223, 0, x_2220);
lean_ctor_set(x_2223, 1, x_2222);
x_2224 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2225 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2225, 0, x_2223);
lean_ctor_set(x_2225, 1, x_2224);
x_2226 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2226, 0, x_2225);
lean_ctor_set(x_2226, 1, x_2218);
x_2227 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2228 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2228, 0, x_2226);
lean_ctor_set(x_2228, 1, x_2227);
x_2229 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2228, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2229;
}
else
{
lean_object* x_2230; 
lean_free_object(x_2213);
lean_dec(x_2208);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2230 = lean_ctor_get(x_2215, 0);
lean_inc(x_2230);
lean_dec_ref(x_2215);
lean_ctor_set(x_2211, 0, x_2230);
return x_2211;
}
}
else
{
lean_object* x_2231; 
x_2231 = lean_ctor_get(x_2213, 0);
lean_inc(x_2231);
lean_dec(x_2213);
if (lean_obj_tag(x_2231) == 0)
{
lean_object* x_2232; lean_object* x_2233; lean_object* x_2234; lean_object* x_2235; lean_object* x_2236; lean_object* x_2237; lean_object* x_2238; lean_object* x_2239; lean_object* x_2240; lean_object* x_2241; lean_object* x_2242; lean_object* x_2243; lean_object* x_2244; lean_object* x_2245; 
lean_free_object(x_2211);
x_2232 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2233 = l_Lean_MessageData_ofName(x_2208);
lean_inc_ref(x_2233);
x_2234 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2234, 0, x_2232);
lean_ctor_set(x_2234, 1, x_2233);
x_2235 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2236 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2236, 0, x_2234);
lean_ctor_set(x_2236, 1, x_2235);
x_2237 = l_Lean_MessageData_ofSyntax(x_1);
x_2238 = l_Lean_indentD(x_2237);
x_2239 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2239, 0, x_2236);
lean_ctor_set(x_2239, 1, x_2238);
x_2240 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2241 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2241, 0, x_2239);
lean_ctor_set(x_2241, 1, x_2240);
x_2242 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2242, 0, x_2241);
lean_ctor_set(x_2242, 1, x_2233);
x_2243 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2244 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2244, 0, x_2242);
lean_ctor_set(x_2244, 1, x_2243);
x_2245 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2244, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2245;
}
else
{
lean_object* x_2246; 
lean_dec(x_2208);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2246 = lean_ctor_get(x_2231, 0);
lean_inc(x_2246);
lean_dec_ref(x_2231);
lean_ctor_set(x_2211, 0, x_2246);
return x_2211;
}
}
}
else
{
lean_object* x_2247; lean_object* x_2248; lean_object* x_2249; 
x_2247 = lean_ctor_get(x_2211, 0);
lean_inc(x_2247);
lean_dec(x_2211);
x_2248 = lean_ctor_get(x_2247, 0);
lean_inc(x_2248);
if (lean_is_exclusive(x_2247)) {
 lean_ctor_release(x_2247, 0);
 lean_ctor_release(x_2247, 1);
 x_2249 = x_2247;
} else {
 lean_dec_ref(x_2247);
 x_2249 = lean_box(0);
}
if (lean_obj_tag(x_2248) == 0)
{
lean_object* x_2250; lean_object* x_2251; lean_object* x_2252; lean_object* x_2253; lean_object* x_2254; lean_object* x_2255; lean_object* x_2256; lean_object* x_2257; lean_object* x_2258; lean_object* x_2259; lean_object* x_2260; lean_object* x_2261; lean_object* x_2262; lean_object* x_2263; 
x_2250 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2251 = l_Lean_MessageData_ofName(x_2208);
lean_inc_ref(x_2251);
if (lean_is_scalar(x_2249)) {
 x_2252 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2252 = x_2249;
 lean_ctor_set_tag(x_2252, 7);
}
lean_ctor_set(x_2252, 0, x_2250);
lean_ctor_set(x_2252, 1, x_2251);
x_2253 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2254 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2254, 0, x_2252);
lean_ctor_set(x_2254, 1, x_2253);
x_2255 = l_Lean_MessageData_ofSyntax(x_1);
x_2256 = l_Lean_indentD(x_2255);
x_2257 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2257, 0, x_2254);
lean_ctor_set(x_2257, 1, x_2256);
x_2258 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2259 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2259, 0, x_2257);
lean_ctor_set(x_2259, 1, x_2258);
x_2260 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2260, 0, x_2259);
lean_ctor_set(x_2260, 1, x_2251);
x_2261 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2262 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2262, 0, x_2260);
lean_ctor_set(x_2262, 1, x_2261);
x_2263 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2262, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2263;
}
else
{
lean_object* x_2264; lean_object* x_2265; 
lean_dec(x_2249);
lean_dec(x_2208);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2264 = lean_ctor_get(x_2248, 0);
lean_inc(x_2264);
lean_dec_ref(x_2248);
x_2265 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2265, 0, x_2264);
return x_2265;
}
}
}
else
{
uint8_t x_2266; 
lean_dec(x_2208);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2266 = !lean_is_exclusive(x_2211);
if (x_2266 == 0)
{
return x_2211;
}
else
{
lean_object* x_2267; lean_object* x_2268; 
x_2267 = lean_ctor_get(x_2211, 0);
lean_inc(x_2267);
lean_dec(x_2211);
x_2268 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2268, 0, x_2267);
return x_2268;
}
}
}
else
{
lean_object* x_2269; lean_object* x_2270; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2269 = l_Lean_Elab_Do_ControlInfo_pure;
x_2270 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2270, 0, x_2269);
return x_2270;
}
}
}
}
}
}
else
{
lean_object* x_2271; lean_object* x_2272; lean_object* x_2273; uint8_t x_2274; 
x_2271 = lean_unsigned_to_nat(1u);
x_2272 = l_Lean_Syntax_getArg(x_1, x_2271);
x_2273 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
x_2274 = l_Lean_Syntax_isOfKind(x_2272, x_2273);
if (x_2274 == 0)
{
lean_object* x_2275; lean_object* x_2276; lean_object* x_2277; lean_object* x_2278; lean_object* x_2279; lean_object* x_2280; lean_object* x_2281; 
x_2275 = lean_st_ref_get(x_7);
x_2276 = lean_ctor_get(x_2275, 0);
lean_inc_ref(x_2276);
lean_dec(x_2275);
x_2277 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_2278 = l_Lean_Syntax_getKind(x_1);
x_2279 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_2277, x_2276, x_2278);
x_2280 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_2281 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_2279, x_2280, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_2281) == 0)
{
uint8_t x_2282; 
x_2282 = !lean_is_exclusive(x_2281);
if (x_2282 == 0)
{
lean_object* x_2283; uint8_t x_2284; 
x_2283 = lean_ctor_get(x_2281, 0);
x_2284 = !lean_is_exclusive(x_2283);
if (x_2284 == 0)
{
lean_object* x_2285; lean_object* x_2286; 
x_2285 = lean_ctor_get(x_2283, 0);
x_2286 = lean_ctor_get(x_2283, 1);
lean_dec(x_2286);
if (lean_obj_tag(x_2285) == 0)
{
lean_object* x_2287; lean_object* x_2288; lean_object* x_2289; lean_object* x_2290; lean_object* x_2291; lean_object* x_2292; lean_object* x_2293; lean_object* x_2294; lean_object* x_2295; lean_object* x_2296; lean_object* x_2297; lean_object* x_2298; lean_object* x_2299; 
lean_free_object(x_2281);
x_2287 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2288 = l_Lean_MessageData_ofName(x_2278);
lean_inc_ref(x_2288);
lean_ctor_set_tag(x_2283, 7);
lean_ctor_set(x_2283, 1, x_2288);
lean_ctor_set(x_2283, 0, x_2287);
x_2289 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2290 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2290, 0, x_2283);
lean_ctor_set(x_2290, 1, x_2289);
x_2291 = l_Lean_MessageData_ofSyntax(x_1);
x_2292 = l_Lean_indentD(x_2291);
x_2293 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2293, 0, x_2290);
lean_ctor_set(x_2293, 1, x_2292);
x_2294 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2295 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2295, 0, x_2293);
lean_ctor_set(x_2295, 1, x_2294);
x_2296 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2296, 0, x_2295);
lean_ctor_set(x_2296, 1, x_2288);
x_2297 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2298 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2298, 0, x_2296);
lean_ctor_set(x_2298, 1, x_2297);
x_2299 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2298, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2299;
}
else
{
lean_object* x_2300; 
lean_free_object(x_2283);
lean_dec(x_2278);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2300 = lean_ctor_get(x_2285, 0);
lean_inc(x_2300);
lean_dec_ref(x_2285);
lean_ctor_set(x_2281, 0, x_2300);
return x_2281;
}
}
else
{
lean_object* x_2301; 
x_2301 = lean_ctor_get(x_2283, 0);
lean_inc(x_2301);
lean_dec(x_2283);
if (lean_obj_tag(x_2301) == 0)
{
lean_object* x_2302; lean_object* x_2303; lean_object* x_2304; lean_object* x_2305; lean_object* x_2306; lean_object* x_2307; lean_object* x_2308; lean_object* x_2309; lean_object* x_2310; lean_object* x_2311; lean_object* x_2312; lean_object* x_2313; lean_object* x_2314; lean_object* x_2315; 
lean_free_object(x_2281);
x_2302 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2303 = l_Lean_MessageData_ofName(x_2278);
lean_inc_ref(x_2303);
x_2304 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2304, 0, x_2302);
lean_ctor_set(x_2304, 1, x_2303);
x_2305 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2306 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2306, 0, x_2304);
lean_ctor_set(x_2306, 1, x_2305);
x_2307 = l_Lean_MessageData_ofSyntax(x_1);
x_2308 = l_Lean_indentD(x_2307);
x_2309 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2309, 0, x_2306);
lean_ctor_set(x_2309, 1, x_2308);
x_2310 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2311 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2311, 0, x_2309);
lean_ctor_set(x_2311, 1, x_2310);
x_2312 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2312, 0, x_2311);
lean_ctor_set(x_2312, 1, x_2303);
x_2313 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2314 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2314, 0, x_2312);
lean_ctor_set(x_2314, 1, x_2313);
x_2315 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2314, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2315;
}
else
{
lean_object* x_2316; 
lean_dec(x_2278);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2316 = lean_ctor_get(x_2301, 0);
lean_inc(x_2316);
lean_dec_ref(x_2301);
lean_ctor_set(x_2281, 0, x_2316);
return x_2281;
}
}
}
else
{
lean_object* x_2317; lean_object* x_2318; lean_object* x_2319; 
x_2317 = lean_ctor_get(x_2281, 0);
lean_inc(x_2317);
lean_dec(x_2281);
x_2318 = lean_ctor_get(x_2317, 0);
lean_inc(x_2318);
if (lean_is_exclusive(x_2317)) {
 lean_ctor_release(x_2317, 0);
 lean_ctor_release(x_2317, 1);
 x_2319 = x_2317;
} else {
 lean_dec_ref(x_2317);
 x_2319 = lean_box(0);
}
if (lean_obj_tag(x_2318) == 0)
{
lean_object* x_2320; lean_object* x_2321; lean_object* x_2322; lean_object* x_2323; lean_object* x_2324; lean_object* x_2325; lean_object* x_2326; lean_object* x_2327; lean_object* x_2328; lean_object* x_2329; lean_object* x_2330; lean_object* x_2331; lean_object* x_2332; lean_object* x_2333; 
x_2320 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2321 = l_Lean_MessageData_ofName(x_2278);
lean_inc_ref(x_2321);
if (lean_is_scalar(x_2319)) {
 x_2322 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2322 = x_2319;
 lean_ctor_set_tag(x_2322, 7);
}
lean_ctor_set(x_2322, 0, x_2320);
lean_ctor_set(x_2322, 1, x_2321);
x_2323 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2324 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2324, 0, x_2322);
lean_ctor_set(x_2324, 1, x_2323);
x_2325 = l_Lean_MessageData_ofSyntax(x_1);
x_2326 = l_Lean_indentD(x_2325);
x_2327 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2327, 0, x_2324);
lean_ctor_set(x_2327, 1, x_2326);
x_2328 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2329 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2329, 0, x_2327);
lean_ctor_set(x_2329, 1, x_2328);
x_2330 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2330, 0, x_2329);
lean_ctor_set(x_2330, 1, x_2321);
x_2331 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2332 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2332, 0, x_2330);
lean_ctor_set(x_2332, 1, x_2331);
x_2333 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2332, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2333;
}
else
{
lean_object* x_2334; lean_object* x_2335; 
lean_dec(x_2319);
lean_dec(x_2278);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2334 = lean_ctor_get(x_2318, 0);
lean_inc(x_2334);
lean_dec_ref(x_2318);
x_2335 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2335, 0, x_2334);
return x_2335;
}
}
}
else
{
uint8_t x_2336; 
lean_dec(x_2278);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2336 = !lean_is_exclusive(x_2281);
if (x_2336 == 0)
{
return x_2281;
}
else
{
lean_object* x_2337; lean_object* x_2338; 
x_2337 = lean_ctor_get(x_2281, 0);
lean_inc(x_2337);
lean_dec(x_2281);
x_2338 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2338, 0, x_2337);
return x_2338;
}
}
}
else
{
lean_object* x_2339; lean_object* x_2340; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2339 = l_Lean_Elab_Do_ControlInfo_pure;
x_2340 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2340, 0, x_2339);
return x_2340;
}
}
}
else
{
lean_object* x_2341; lean_object* x_2342; uint8_t x_2343; 
x_2341 = lean_unsigned_to_nat(1u);
x_2342 = l_Lean_Syntax_getArg(x_1, x_2341);
x_2343 = l_Lean_Syntax_isNone(x_2342);
if (x_2343 == 0)
{
uint8_t x_2344; 
x_2344 = l_Lean_Syntax_matchesNull(x_2342, x_2341);
if (x_2344 == 0)
{
lean_object* x_2345; lean_object* x_2346; lean_object* x_2347; lean_object* x_2348; lean_object* x_2349; lean_object* x_2350; lean_object* x_2351; 
lean_dec(x_57);
x_2345 = lean_st_ref_get(x_7);
x_2346 = lean_ctor_get(x_2345, 0);
lean_inc_ref(x_2346);
lean_dec(x_2345);
x_2347 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_2348 = l_Lean_Syntax_getKind(x_1);
x_2349 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_2347, x_2346, x_2348);
x_2350 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_2351 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_2349, x_2350, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_2351) == 0)
{
uint8_t x_2352; 
x_2352 = !lean_is_exclusive(x_2351);
if (x_2352 == 0)
{
lean_object* x_2353; uint8_t x_2354; 
x_2353 = lean_ctor_get(x_2351, 0);
x_2354 = !lean_is_exclusive(x_2353);
if (x_2354 == 0)
{
lean_object* x_2355; lean_object* x_2356; 
x_2355 = lean_ctor_get(x_2353, 0);
x_2356 = lean_ctor_get(x_2353, 1);
lean_dec(x_2356);
if (lean_obj_tag(x_2355) == 0)
{
lean_object* x_2357; lean_object* x_2358; lean_object* x_2359; lean_object* x_2360; lean_object* x_2361; lean_object* x_2362; lean_object* x_2363; lean_object* x_2364; lean_object* x_2365; lean_object* x_2366; lean_object* x_2367; lean_object* x_2368; lean_object* x_2369; 
lean_free_object(x_2351);
x_2357 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2358 = l_Lean_MessageData_ofName(x_2348);
lean_inc_ref(x_2358);
lean_ctor_set_tag(x_2353, 7);
lean_ctor_set(x_2353, 1, x_2358);
lean_ctor_set(x_2353, 0, x_2357);
x_2359 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2360 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2360, 0, x_2353);
lean_ctor_set(x_2360, 1, x_2359);
x_2361 = l_Lean_MessageData_ofSyntax(x_1);
x_2362 = l_Lean_indentD(x_2361);
x_2363 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2363, 0, x_2360);
lean_ctor_set(x_2363, 1, x_2362);
x_2364 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2365 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2365, 0, x_2363);
lean_ctor_set(x_2365, 1, x_2364);
x_2366 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2366, 0, x_2365);
lean_ctor_set(x_2366, 1, x_2358);
x_2367 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2368 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2368, 0, x_2366);
lean_ctor_set(x_2368, 1, x_2367);
x_2369 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2368, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2369;
}
else
{
lean_object* x_2370; 
lean_free_object(x_2353);
lean_dec(x_2348);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2370 = lean_ctor_get(x_2355, 0);
lean_inc(x_2370);
lean_dec_ref(x_2355);
lean_ctor_set(x_2351, 0, x_2370);
return x_2351;
}
}
else
{
lean_object* x_2371; 
x_2371 = lean_ctor_get(x_2353, 0);
lean_inc(x_2371);
lean_dec(x_2353);
if (lean_obj_tag(x_2371) == 0)
{
lean_object* x_2372; lean_object* x_2373; lean_object* x_2374; lean_object* x_2375; lean_object* x_2376; lean_object* x_2377; lean_object* x_2378; lean_object* x_2379; lean_object* x_2380; lean_object* x_2381; lean_object* x_2382; lean_object* x_2383; lean_object* x_2384; lean_object* x_2385; 
lean_free_object(x_2351);
x_2372 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2373 = l_Lean_MessageData_ofName(x_2348);
lean_inc_ref(x_2373);
x_2374 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2374, 0, x_2372);
lean_ctor_set(x_2374, 1, x_2373);
x_2375 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2376 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2376, 0, x_2374);
lean_ctor_set(x_2376, 1, x_2375);
x_2377 = l_Lean_MessageData_ofSyntax(x_1);
x_2378 = l_Lean_indentD(x_2377);
x_2379 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2379, 0, x_2376);
lean_ctor_set(x_2379, 1, x_2378);
x_2380 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2381 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2381, 0, x_2379);
lean_ctor_set(x_2381, 1, x_2380);
x_2382 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2382, 0, x_2381);
lean_ctor_set(x_2382, 1, x_2373);
x_2383 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2384 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2384, 0, x_2382);
lean_ctor_set(x_2384, 1, x_2383);
x_2385 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2384, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2385;
}
else
{
lean_object* x_2386; 
lean_dec(x_2348);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2386 = lean_ctor_get(x_2371, 0);
lean_inc(x_2386);
lean_dec_ref(x_2371);
lean_ctor_set(x_2351, 0, x_2386);
return x_2351;
}
}
}
else
{
lean_object* x_2387; lean_object* x_2388; lean_object* x_2389; 
x_2387 = lean_ctor_get(x_2351, 0);
lean_inc(x_2387);
lean_dec(x_2351);
x_2388 = lean_ctor_get(x_2387, 0);
lean_inc(x_2388);
if (lean_is_exclusive(x_2387)) {
 lean_ctor_release(x_2387, 0);
 lean_ctor_release(x_2387, 1);
 x_2389 = x_2387;
} else {
 lean_dec_ref(x_2387);
 x_2389 = lean_box(0);
}
if (lean_obj_tag(x_2388) == 0)
{
lean_object* x_2390; lean_object* x_2391; lean_object* x_2392; lean_object* x_2393; lean_object* x_2394; lean_object* x_2395; lean_object* x_2396; lean_object* x_2397; lean_object* x_2398; lean_object* x_2399; lean_object* x_2400; lean_object* x_2401; lean_object* x_2402; lean_object* x_2403; 
x_2390 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2391 = l_Lean_MessageData_ofName(x_2348);
lean_inc_ref(x_2391);
if (lean_is_scalar(x_2389)) {
 x_2392 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2392 = x_2389;
 lean_ctor_set_tag(x_2392, 7);
}
lean_ctor_set(x_2392, 0, x_2390);
lean_ctor_set(x_2392, 1, x_2391);
x_2393 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2394 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2394, 0, x_2392);
lean_ctor_set(x_2394, 1, x_2393);
x_2395 = l_Lean_MessageData_ofSyntax(x_1);
x_2396 = l_Lean_indentD(x_2395);
x_2397 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2397, 0, x_2394);
lean_ctor_set(x_2397, 1, x_2396);
x_2398 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2399 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2399, 0, x_2397);
lean_ctor_set(x_2399, 1, x_2398);
x_2400 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2400, 0, x_2399);
lean_ctor_set(x_2400, 1, x_2391);
x_2401 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2402 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2402, 0, x_2400);
lean_ctor_set(x_2402, 1, x_2401);
x_2403 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2402, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2403;
}
else
{
lean_object* x_2404; lean_object* x_2405; 
lean_dec(x_2389);
lean_dec(x_2348);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2404 = lean_ctor_get(x_2388, 0);
lean_inc(x_2404);
lean_dec_ref(x_2388);
x_2405 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2405, 0, x_2404);
return x_2405;
}
}
}
else
{
uint8_t x_2406; 
lean_dec(x_2348);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2406 = !lean_is_exclusive(x_2351);
if (x_2406 == 0)
{
return x_2351;
}
else
{
lean_object* x_2407; lean_object* x_2408; 
x_2407 = lean_ctor_get(x_2351, 0);
lean_inc(x_2407);
lean_dec(x_2351);
x_2408 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2408, 0, x_2407);
return x_2408;
}
}
}
else
{
x_67 = x_2;
x_68 = x_3;
x_69 = x_4;
x_70 = x_5;
x_71 = x_6;
x_72 = x_7;
x_73 = lean_box(0);
goto block_144;
}
}
else
{
lean_dec(x_2342);
x_67 = x_2;
x_68 = x_3;
x_69 = x_4;
x_70 = x_5;
x_71 = x_6;
x_72 = x_7;
x_73 = lean_box(0);
goto block_144;
}
}
}
else
{
lean_object* x_2409; lean_object* x_2410; lean_object* x_2411; 
lean_dec(x_57);
x_2409 = lean_unsigned_to_nat(1u);
x_2410 = l_Lean_Syntax_getArg(x_1, x_2409);
lean_dec(x_1);
x_2411 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_2410, x_2, x_3, x_4, x_5, x_6, x_7);
return x_2411;
}
}
else
{
lean_object* x_2412; lean_object* x_2413; lean_object* x_2414; lean_object* x_2415; 
lean_dec(x_57);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2412 = lean_unsigned_to_nat(1u);
x_2413 = l_Lean_NameSet_empty;
x_2414 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_2414, 0, x_2412);
lean_ctor_set(x_2414, 1, x_2413);
lean_ctor_set_uint8(x_2414, sizeof(void*)*2, x_151);
lean_ctor_set_uint8(x_2414, sizeof(void*)*2 + 1, x_151);
lean_ctor_set_uint8(x_2414, sizeof(void*)*2 + 2, x_151);
x_2415 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2415, 0, x_2414);
return x_2415;
}
}
else
{
lean_object* x_2416; lean_object* x_2417; lean_object* x_2422; lean_object* x_2423; uint8_t x_2424; 
lean_dec(x_57);
x_2416 = lean_unsigned_to_nat(0u);
x_2422 = lean_unsigned_to_nat(1u);
x_2423 = l_Lean_Syntax_getArg(x_1, x_2422);
x_2424 = l_Lean_Syntax_isNone(x_2423);
if (x_2424 == 0)
{
uint8_t x_2425; 
x_2425 = l_Lean_Syntax_matchesNull(x_2423, x_2422);
if (x_2425 == 0)
{
lean_object* x_2426; lean_object* x_2427; lean_object* x_2428; lean_object* x_2429; lean_object* x_2430; lean_object* x_2431; lean_object* x_2432; 
x_2426 = lean_st_ref_get(x_7);
x_2427 = lean_ctor_get(x_2426, 0);
lean_inc_ref(x_2427);
lean_dec(x_2426);
x_2428 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_2429 = l_Lean_Syntax_getKind(x_1);
x_2430 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_2428, x_2427, x_2429);
x_2431 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_7);
lean_inc_ref(x_6);
lean_inc(x_5);
lean_inc_ref(x_4);
lean_inc(x_3);
lean_inc_ref(x_2);
lean_inc(x_1);
x_2432 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_2430, x_2431, x_2, x_3, x_4, x_5, x_6, x_7);
if (lean_obj_tag(x_2432) == 0)
{
uint8_t x_2433; 
x_2433 = !lean_is_exclusive(x_2432);
if (x_2433 == 0)
{
lean_object* x_2434; uint8_t x_2435; 
x_2434 = lean_ctor_get(x_2432, 0);
x_2435 = !lean_is_exclusive(x_2434);
if (x_2435 == 0)
{
lean_object* x_2436; lean_object* x_2437; 
x_2436 = lean_ctor_get(x_2434, 0);
x_2437 = lean_ctor_get(x_2434, 1);
lean_dec(x_2437);
if (lean_obj_tag(x_2436) == 0)
{
lean_object* x_2438; lean_object* x_2439; lean_object* x_2440; lean_object* x_2441; lean_object* x_2442; lean_object* x_2443; lean_object* x_2444; lean_object* x_2445; lean_object* x_2446; lean_object* x_2447; lean_object* x_2448; lean_object* x_2449; lean_object* x_2450; 
lean_free_object(x_2432);
x_2438 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2439 = l_Lean_MessageData_ofName(x_2429);
lean_inc_ref(x_2439);
lean_ctor_set_tag(x_2434, 7);
lean_ctor_set(x_2434, 1, x_2439);
lean_ctor_set(x_2434, 0, x_2438);
x_2440 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2441 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2441, 0, x_2434);
lean_ctor_set(x_2441, 1, x_2440);
x_2442 = l_Lean_MessageData_ofSyntax(x_1);
x_2443 = l_Lean_indentD(x_2442);
x_2444 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2444, 0, x_2441);
lean_ctor_set(x_2444, 1, x_2443);
x_2445 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2446 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2446, 0, x_2444);
lean_ctor_set(x_2446, 1, x_2445);
x_2447 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2447, 0, x_2446);
lean_ctor_set(x_2447, 1, x_2439);
x_2448 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2449 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2449, 0, x_2447);
lean_ctor_set(x_2449, 1, x_2448);
x_2450 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2449, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2450;
}
else
{
lean_object* x_2451; 
lean_free_object(x_2434);
lean_dec(x_2429);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2451 = lean_ctor_get(x_2436, 0);
lean_inc(x_2451);
lean_dec_ref(x_2436);
lean_ctor_set(x_2432, 0, x_2451);
return x_2432;
}
}
else
{
lean_object* x_2452; 
x_2452 = lean_ctor_get(x_2434, 0);
lean_inc(x_2452);
lean_dec(x_2434);
if (lean_obj_tag(x_2452) == 0)
{
lean_object* x_2453; lean_object* x_2454; lean_object* x_2455; lean_object* x_2456; lean_object* x_2457; lean_object* x_2458; lean_object* x_2459; lean_object* x_2460; lean_object* x_2461; lean_object* x_2462; lean_object* x_2463; lean_object* x_2464; lean_object* x_2465; lean_object* x_2466; 
lean_free_object(x_2432);
x_2453 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2454 = l_Lean_MessageData_ofName(x_2429);
lean_inc_ref(x_2454);
x_2455 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2455, 0, x_2453);
lean_ctor_set(x_2455, 1, x_2454);
x_2456 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2457 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2457, 0, x_2455);
lean_ctor_set(x_2457, 1, x_2456);
x_2458 = l_Lean_MessageData_ofSyntax(x_1);
x_2459 = l_Lean_indentD(x_2458);
x_2460 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2460, 0, x_2457);
lean_ctor_set(x_2460, 1, x_2459);
x_2461 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2462 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2462, 0, x_2460);
lean_ctor_set(x_2462, 1, x_2461);
x_2463 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2463, 0, x_2462);
lean_ctor_set(x_2463, 1, x_2454);
x_2464 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2465 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2465, 0, x_2463);
lean_ctor_set(x_2465, 1, x_2464);
x_2466 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2465, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2466;
}
else
{
lean_object* x_2467; 
lean_dec(x_2429);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2467 = lean_ctor_get(x_2452, 0);
lean_inc(x_2467);
lean_dec_ref(x_2452);
lean_ctor_set(x_2432, 0, x_2467);
return x_2432;
}
}
}
else
{
lean_object* x_2468; lean_object* x_2469; lean_object* x_2470; 
x_2468 = lean_ctor_get(x_2432, 0);
lean_inc(x_2468);
lean_dec(x_2432);
x_2469 = lean_ctor_get(x_2468, 0);
lean_inc(x_2469);
if (lean_is_exclusive(x_2468)) {
 lean_ctor_release(x_2468, 0);
 lean_ctor_release(x_2468, 1);
 x_2470 = x_2468;
} else {
 lean_dec_ref(x_2468);
 x_2470 = lean_box(0);
}
if (lean_obj_tag(x_2469) == 0)
{
lean_object* x_2471; lean_object* x_2472; lean_object* x_2473; lean_object* x_2474; lean_object* x_2475; lean_object* x_2476; lean_object* x_2477; lean_object* x_2478; lean_object* x_2479; lean_object* x_2480; lean_object* x_2481; lean_object* x_2482; lean_object* x_2483; lean_object* x_2484; 
x_2471 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_2472 = l_Lean_MessageData_ofName(x_2429);
lean_inc_ref(x_2472);
if (lean_is_scalar(x_2470)) {
 x_2473 = lean_alloc_ctor(7, 2, 0);
} else {
 x_2473 = x_2470;
 lean_ctor_set_tag(x_2473, 7);
}
lean_ctor_set(x_2473, 0, x_2471);
lean_ctor_set(x_2473, 1, x_2472);
x_2474 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_2475 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2475, 0, x_2473);
lean_ctor_set(x_2475, 1, x_2474);
x_2476 = l_Lean_MessageData_ofSyntax(x_1);
x_2477 = l_Lean_indentD(x_2476);
x_2478 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2478, 0, x_2475);
lean_ctor_set(x_2478, 1, x_2477);
x_2479 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_2480 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2480, 0, x_2478);
lean_ctor_set(x_2480, 1, x_2479);
x_2481 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2481, 0, x_2480);
lean_ctor_set(x_2481, 1, x_2472);
x_2482 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_2483 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_2483, 0, x_2481);
lean_ctor_set(x_2483, 1, x_2482);
x_2484 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2483, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
return x_2484;
}
else
{
lean_object* x_2485; lean_object* x_2486; 
lean_dec(x_2470);
lean_dec(x_2429);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2485 = lean_ctor_get(x_2469, 0);
lean_inc(x_2485);
lean_dec_ref(x_2469);
x_2486 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2486, 0, x_2485);
return x_2486;
}
}
}
else
{
uint8_t x_2487; 
lean_dec(x_2429);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2487 = !lean_is_exclusive(x_2432);
if (x_2487 == 0)
{
return x_2432;
}
else
{
lean_object* x_2488; lean_object* x_2489; 
x_2488 = lean_ctor_get(x_2432, 0);
lean_inc(x_2488);
lean_dec(x_2432);
x_2489 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2489, 0, x_2488);
return x_2489;
}
}
}
else
{
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2417 = lean_box(0);
goto block_2421;
}
}
else
{
lean_dec(x_2423);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2417 = lean_box(0);
goto block_2421;
}
block_2421:
{
lean_object* x_2418; lean_object* x_2419; lean_object* x_2420; 
x_2418 = l_Lean_NameSet_empty;
x_2419 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_2419, 0, x_2416);
lean_ctor_set(x_2419, 1, x_2418);
lean_ctor_set_uint8(x_2419, sizeof(void*)*2, x_149);
lean_ctor_set_uint8(x_2419, sizeof(void*)*2 + 1, x_149);
lean_ctor_set_uint8(x_2419, sizeof(void*)*2 + 2, x_147);
x_2420 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2420, 0, x_2419);
return x_2420;
}
}
}
else
{
lean_object* x_2490; lean_object* x_2491; lean_object* x_2492; lean_object* x_2493; 
lean_dec(x_57);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2490 = lean_unsigned_to_nat(0u);
x_2491 = l_Lean_NameSet_empty;
x_2492 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_2492, 0, x_2490);
lean_ctor_set(x_2492, 1, x_2491);
lean_ctor_set_uint8(x_2492, sizeof(void*)*2, x_146);
lean_ctor_set_uint8(x_2492, sizeof(void*)*2 + 1, x_147);
lean_ctor_set_uint8(x_2492, sizeof(void*)*2 + 2, x_146);
x_2493 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2493, 0, x_2492);
return x_2493;
}
}
else
{
lean_object* x_2494; lean_object* x_2495; 
lean_dec(x_57);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2494 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__76);
x_2495 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_2495, 0, x_2494);
return x_2495;
}
block_144:
{
lean_object* x_74; lean_object* x_75; lean_object* x_76; uint8_t x_77; 
x_74 = lean_unsigned_to_nat(2u);
x_75 = l_Lean_Syntax_getArg(x_1, x_74);
x_76 = ((lean_object*)(l_Lean_Elab_Do_InferControlInfo_ofElem___closed__1));
x_77 = l_Lean_Syntax_isOfKind(x_75, x_76);
if (x_77 == 0)
{
lean_object* x_78; lean_object* x_79; lean_object* x_80; lean_object* x_81; lean_object* x_82; lean_object* x_83; lean_object* x_84; 
lean_dec(x_57);
x_78 = lean_st_ref_get(x_72);
x_79 = lean_ctor_get(x_78, 0);
lean_inc_ref(x_79);
lean_dec(x_78);
x_80 = l_Lean_Elab_Do_controlInfoElemAttribute;
lean_inc(x_1);
x_81 = l_Lean_Syntax_getKind(x_1);
x_82 = l_Lean_KeyedDeclsAttribute_getEntries___redArg(x_80, x_79, x_81);
x_83 = ((lean_object*)(l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg___closed__0));
lean_inc(x_72);
lean_inc_ref(x_71);
lean_inc(x_70);
lean_inc_ref(x_69);
lean_inc(x_68);
lean_inc_ref(x_67);
lean_inc(x_1);
x_84 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_82, x_83, x_67, x_68, x_69, x_70, x_71, x_72);
if (lean_obj_tag(x_84) == 0)
{
uint8_t x_85; 
x_85 = !lean_is_exclusive(x_84);
if (x_85 == 0)
{
lean_object* x_86; uint8_t x_87; 
x_86 = lean_ctor_get(x_84, 0);
x_87 = !lean_is_exclusive(x_86);
if (x_87 == 0)
{
lean_object* x_88; lean_object* x_89; 
x_88 = lean_ctor_get(x_86, 0);
x_89 = lean_ctor_get(x_86, 1);
lean_dec(x_89);
if (lean_obj_tag(x_88) == 0)
{
lean_object* x_90; lean_object* x_91; lean_object* x_92; lean_object* x_93; lean_object* x_94; lean_object* x_95; lean_object* x_96; lean_object* x_97; lean_object* x_98; lean_object* x_99; lean_object* x_100; lean_object* x_101; lean_object* x_102; 
lean_free_object(x_84);
x_90 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_91 = l_Lean_MessageData_ofName(x_81);
lean_inc_ref(x_91);
lean_ctor_set_tag(x_86, 7);
lean_ctor_set(x_86, 1, x_91);
lean_ctor_set(x_86, 0, x_90);
x_92 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_93 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_93, 0, x_86);
lean_ctor_set(x_93, 1, x_92);
x_94 = l_Lean_MessageData_ofSyntax(x_1);
x_95 = l_Lean_indentD(x_94);
x_96 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_96, 0, x_93);
lean_ctor_set(x_96, 1, x_95);
x_97 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_98 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_98, 0, x_96);
lean_ctor_set(x_98, 1, x_97);
x_99 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_99, 0, x_98);
lean_ctor_set(x_99, 1, x_91);
x_100 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_101 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_101, 0, x_99);
lean_ctor_set(x_101, 1, x_100);
x_102 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_101, x_67, x_68, x_69, x_70, x_71, x_72);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
return x_102;
}
else
{
lean_object* x_103; 
lean_free_object(x_86);
lean_dec(x_81);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_1);
x_103 = lean_ctor_get(x_88, 0);
lean_inc(x_103);
lean_dec_ref(x_88);
lean_ctor_set(x_84, 0, x_103);
return x_84;
}
}
else
{
lean_object* x_104; 
x_104 = lean_ctor_get(x_86, 0);
lean_inc(x_104);
lean_dec(x_86);
if (lean_obj_tag(x_104) == 0)
{
lean_object* x_105; lean_object* x_106; lean_object* x_107; lean_object* x_108; lean_object* x_109; lean_object* x_110; lean_object* x_111; lean_object* x_112; lean_object* x_113; lean_object* x_114; lean_object* x_115; lean_object* x_116; lean_object* x_117; lean_object* x_118; 
lean_free_object(x_84);
x_105 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_106 = l_Lean_MessageData_ofName(x_81);
lean_inc_ref(x_106);
x_107 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_107, 0, x_105);
lean_ctor_set(x_107, 1, x_106);
x_108 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_109 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_109, 0, x_107);
lean_ctor_set(x_109, 1, x_108);
x_110 = l_Lean_MessageData_ofSyntax(x_1);
x_111 = l_Lean_indentD(x_110);
x_112 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_112, 0, x_109);
lean_ctor_set(x_112, 1, x_111);
x_113 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_114 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_114, 0, x_112);
lean_ctor_set(x_114, 1, x_113);
x_115 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_115, 0, x_114);
lean_ctor_set(x_115, 1, x_106);
x_116 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_117 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_117, 0, x_115);
lean_ctor_set(x_117, 1, x_116);
x_118 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_117, x_67, x_68, x_69, x_70, x_71, x_72);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
return x_118;
}
else
{
lean_object* x_119; 
lean_dec(x_81);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_1);
x_119 = lean_ctor_get(x_104, 0);
lean_inc(x_119);
lean_dec_ref(x_104);
lean_ctor_set(x_84, 0, x_119);
return x_84;
}
}
}
else
{
lean_object* x_120; lean_object* x_121; lean_object* x_122; 
x_120 = lean_ctor_get(x_84, 0);
lean_inc(x_120);
lean_dec(x_84);
x_121 = lean_ctor_get(x_120, 0);
lean_inc(x_121);
if (lean_is_exclusive(x_120)) {
 lean_ctor_release(x_120, 0);
 lean_ctor_release(x_120, 1);
 x_122 = x_120;
} else {
 lean_dec_ref(x_120);
 x_122 = lean_box(0);
}
if (lean_obj_tag(x_121) == 0)
{
lean_object* x_123; lean_object* x_124; lean_object* x_125; lean_object* x_126; lean_object* x_127; lean_object* x_128; lean_object* x_129; lean_object* x_130; lean_object* x_131; lean_object* x_132; lean_object* x_133; lean_object* x_134; lean_object* x_135; lean_object* x_136; 
x_123 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__3);
x_124 = l_Lean_MessageData_ofName(x_81);
lean_inc_ref(x_124);
if (lean_is_scalar(x_122)) {
 x_125 = lean_alloc_ctor(7, 2, 0);
} else {
 x_125 = x_122;
 lean_ctor_set_tag(x_125, 7);
}
lean_ctor_set(x_125, 0, x_123);
lean_ctor_set(x_125, 1, x_124);
x_126 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__5);
x_127 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_127, 0, x_125);
lean_ctor_set(x_127, 1, x_126);
x_128 = l_Lean_MessageData_ofSyntax(x_1);
x_129 = l_Lean_indentD(x_128);
x_130 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_130, 0, x_127);
lean_ctor_set(x_130, 1, x_129);
x_131 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__7);
x_132 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_132, 0, x_130);
lean_ctor_set(x_132, 1, x_131);
x_133 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_133, 0, x_132);
lean_ctor_set(x_133, 1, x_124);
x_134 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9, &l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9_once, _init_l_Lean_Elab_Do_InferControlInfo_ofElem___closed__9);
x_135 = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(x_135, 0, x_133);
lean_ctor_set(x_135, 1, x_134);
x_136 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_135, x_67, x_68, x_69, x_70, x_71, x_72);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
return x_136;
}
else
{
lean_object* x_137; lean_object* x_138; 
lean_dec(x_122);
lean_dec(x_81);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_1);
x_137 = lean_ctor_get(x_121, 0);
lean_inc(x_137);
lean_dec_ref(x_121);
x_138 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_138, 0, x_137);
return x_138;
}
}
}
else
{
uint8_t x_139; 
lean_dec(x_81);
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_1);
x_139 = !lean_is_exclusive(x_84);
if (x_139 == 0)
{
return x_84;
}
else
{
lean_object* x_140; lean_object* x_141; 
x_140 = lean_ctor_get(x_84, 0);
lean_inc(x_140);
lean_dec(x_84);
x_141 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_141, 0, x_140);
return x_141;
}
}
}
else
{
lean_object* x_142; lean_object* x_143; 
lean_dec(x_72);
lean_dec_ref(x_71);
lean_dec(x_70);
lean_dec_ref(x_69);
lean_dec(x_68);
lean_dec_ref(x_67);
lean_dec(x_1);
x_142 = l_Lean_Elab_Do_ControlInfo_pure;
if (lean_is_scalar(x_57)) {
 x_143 = lean_alloc_ctor(0, 1, 0);
} else {
 x_143 = x_57;
}
lean_ctor_set(x_143, 0, x_142);
return x_143;
}
}
}
}
else
{
uint8_t x_2496; 
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
lean_dec(x_1);
x_2496 = !lean_is_exclusive(x_55);
if (x_2496 == 0)
{
return x_55;
}
else
{
lean_object* x_2497; lean_object* x_2498; 
x_2497 = lean_ctor_get(x_55, 0);
lean_inc(x_2497);
lean_dec(x_55);
x_2498 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_2498, 0, x_2497);
return x_2498;
}
}
block_22:
{
lean_object* x_18; lean_object* x_19; lean_object* x_20; lean_object* x_21; 
x_18 = lean_obj_once(&l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6, &l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6_once, _init_l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___closed__6);
x_19 = lean_box(0);
x_20 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_20, 0, x_9);
x_21 = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(x_18, x_19, x_20, x_17, x_16, x_14, x_13, x_10, x_15, x_12);
return x_21;
}
block_39:
{
lean_object* x_30; lean_object* x_31; lean_object* x_32; lean_object* x_33; lean_object* x_34; 
x_30 = lean_unsigned_to_nat(6u);
x_31 = l_Lean_Syntax_getArg(x_1, x_30);
x_32 = lean_unsigned_to_nat(7u);
x_33 = l_Lean_Syntax_getArg(x_1, x_32);
lean_dec(x_1);
x_34 = l_Lean_Syntax_getOptional_x3f(x_33);
lean_dec(x_33);
if (lean_obj_tag(x_34) == 0)
{
lean_object* x_35; 
x_35 = lean_box(0);
x_9 = x_31;
x_10 = x_26;
x_11 = lean_box(0);
x_12 = x_28;
x_13 = x_25;
x_14 = x_24;
x_15 = x_27;
x_16 = x_23;
x_17 = x_35;
goto block_22;
}
else
{
uint8_t x_36; 
x_36 = !lean_is_exclusive(x_34);
if (x_36 == 0)
{
x_9 = x_31;
x_10 = x_26;
x_11 = lean_box(0);
x_12 = x_28;
x_13 = x_25;
x_14 = x_24;
x_15 = x_27;
x_16 = x_23;
x_17 = x_34;
goto block_22;
}
else
{
lean_object* x_37; lean_object* x_38; 
x_37 = lean_ctor_get(x_34, 0);
lean_inc(x_37);
lean_dec(x_34);
x_38 = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(x_38, 0, x_37);
x_9 = x_31;
x_10 = x_26;
x_11 = lean_box(0);
x_12 = x_28;
x_13 = x_25;
x_14 = x_24;
x_15 = x_27;
x_16 = x_23;
x_17 = x_38;
goto block_22;
}
}
}
block_45:
{
lean_object* x_43; lean_object* x_44; 
x_43 = l_Lean_Elab_Do_ControlInfo_alternative(x_40, x_41);
x_44 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_44, 0, x_43);
return x_44;
}
block_51:
{
lean_object* x_49; lean_object* x_50; 
x_49 = l_Lean_Elab_Do_ControlInfo_alternative(x_46, x_47);
x_50 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_50, 0, x_49);
return x_50;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(lean_object* x_1, size_t x_2, size_t x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
uint8_t x_12; 
x_12 = lean_usize_dec_lt(x_3, x_2);
if (x_12 == 0)
{
lean_object* x_13; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_13 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_13, 0, x_4);
return x_13;
}
else
{
uint8_t x_14; uint8_t x_15; uint8_t x_16; lean_object* x_17; lean_object* x_18; lean_object* x_19; uint8_t x_20; 
x_14 = lean_ctor_get_uint8(x_4, sizeof(void*)*2);
x_15 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 1);
x_16 = lean_ctor_get_uint8(x_4, sizeof(void*)*2 + 2);
x_17 = lean_ctor_get(x_4, 0);
x_18 = lean_ctor_get(x_4, 1);
x_19 = lean_unsigned_to_nat(0u);
x_20 = lean_nat_dec_eq(x_17, x_19);
if (x_20 == 0)
{
lean_object* x_21; lean_object* x_22; 
lean_inc(x_18);
lean_dec_ref(x_4);
x_21 = lean_array_uget_borrowed(x_1, x_3);
lean_inc(x_10);
lean_inc_ref(x_9);
lean_inc(x_8);
lean_inc_ref(x_7);
lean_inc(x_6);
lean_inc_ref(x_5);
lean_inc(x_21);
x_22 = l_Lean_Elab_Do_InferControlInfo_ofElem(x_21, x_5, x_6, x_7, x_8, x_9, x_10);
if (lean_obj_tag(x_22) == 0)
{
lean_object* x_23; uint8_t x_24; uint8_t x_25; uint8_t x_26; uint8_t x_41; uint8_t x_42; uint8_t x_45; 
x_23 = lean_ctor_get(x_22, 0);
lean_inc(x_23);
lean_dec_ref(x_22);
if (x_14 == 0)
{
uint8_t x_48; 
x_48 = lean_ctor_get_uint8(x_23, sizeof(void*)*2);
x_45 = x_48;
goto block_47;
}
else
{
x_45 = x_14;
goto block_47;
}
block_40:
{
uint8_t x_27; 
x_27 = !lean_is_exclusive(x_23);
if (x_27 == 0)
{
lean_object* x_28; lean_object* x_29; size_t x_30; size_t x_31; 
x_28 = lean_ctor_get(x_23, 1);
x_29 = l_Lean_NameSet_append(x_18, x_28);
lean_ctor_set(x_23, 1, x_29);
lean_ctor_set_uint8(x_23, sizeof(void*)*2, x_24);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 1, x_25);
lean_ctor_set_uint8(x_23, sizeof(void*)*2 + 2, x_26);
x_30 = 1;
x_31 = lean_usize_add(x_3, x_30);
x_3 = x_31;
x_4 = x_23;
goto _start;
}
else
{
lean_object* x_33; lean_object* x_34; lean_object* x_35; lean_object* x_36; size_t x_37; size_t x_38; 
x_33 = lean_ctor_get(x_23, 0);
x_34 = lean_ctor_get(x_23, 1);
lean_inc(x_34);
lean_inc(x_33);
lean_dec(x_23);
x_35 = l_Lean_NameSet_append(x_18, x_34);
x_36 = lean_alloc_ctor(0, 2, 3);
lean_ctor_set(x_36, 0, x_33);
lean_ctor_set(x_36, 1, x_35);
lean_ctor_set_uint8(x_36, sizeof(void*)*2, x_24);
lean_ctor_set_uint8(x_36, sizeof(void*)*2 + 1, x_25);
lean_ctor_set_uint8(x_36, sizeof(void*)*2 + 2, x_26);
x_37 = 1;
x_38 = lean_usize_add(x_3, x_37);
x_3 = x_38;
x_4 = x_36;
goto _start;
}
}
block_44:
{
if (x_16 == 0)
{
uint8_t x_43; 
x_43 = lean_ctor_get_uint8(x_23, sizeof(void*)*2 + 2);
x_24 = x_41;
x_25 = x_42;
x_26 = x_43;
goto block_40;
}
else
{
x_24 = x_41;
x_25 = x_42;
x_26 = x_16;
goto block_40;
}
}
block_47:
{
if (x_15 == 0)
{
uint8_t x_46; 
x_46 = lean_ctor_get_uint8(x_23, sizeof(void*)*2 + 1);
x_41 = x_45;
x_42 = x_46;
goto block_44;
}
else
{
x_41 = x_45;
x_42 = x_15;
goto block_44;
}
}
}
else
{
lean_dec(x_18);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
return x_22;
}
}
else
{
lean_object* x_49; 
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
x_49 = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(x_49, 0, x_4);
return x_49;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; lean_object* x_10; size_t x_11; size_t x_12; lean_object* x_13; 
x_9 = lean_obj_once(&l_Lean_Elab_Do_ControlInfo_pure___closed__0, &l_Lean_Elab_Do_ControlInfo_pure___closed__0_once, _init_l_Lean_Elab_Do_ControlInfo_pure___closed__0);
x_10 = l_Lean_Parser_Term_getDoElems(x_1);
x_11 = lean_array_size(x_10);
x_12 = 0;
x_13 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(x_10, x_11, x_12, x_9, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec_ref(x_10);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofOptionSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Do_InferControlInfo_ofOptionSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__5(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofSeq_spec__17(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassign(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__10(x_13, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
uint8_t x_13; size_t x_14; size_t x_15; lean_object* x_16; 
x_13 = lean_unbox(x_1);
x_14 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_15 = lean_unbox_usize(x_4);
lean_dec(x_4);
x_16 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__14(x_13, x_2, x_14, x_15, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec_ref(x_2);
return x_16;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
size_t x_12; size_t x_13; lean_object* x_14; 
x_12 = lean_unbox_usize(x_2);
lean_dec(x_2);
x_13 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_14 = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__11(x_1, x_12, x_13, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec_ref(x_1);
return x_14;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
uint8_t x_10; lean_object* x_11; 
x_10 = lean_unbox(x_1);
x_11 = l_Lean_Elab_Do_InferControlInfo_ofLetOrReassignArrow(x_10, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_InferControlInfo_ofElem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Do_InferControlInfo_ofElem(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___redArg();
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_throwUnsupportedSyntax___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___redArg(x_1, x_6);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_isTracingEnabledFor___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__1(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec_ref(x_4);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___redArg(x_2);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwMaxRecDepthAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__7(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___redArg(x_1, x_3, x_4, x_6, x_7, x_8, x_9, x_10, x_11);
return x_13;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11, lean_object* x_12) {
_start:
{
lean_object* x_13; 
x_13 = l_List_forIn_x27_loop___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10, x_11);
lean_dec(x_2);
return x_13;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___redArg(x_1, x_2, x_5, x_6, x_7, x_8);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_addTrace___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__2(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___redArg(x_2, x_3, x_5, x_6, x_7, x_8, x_9, x_10);
return x_12;
}
}
LEAN_EXPORT lean_object* l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10, lean_object* x_11) {
_start:
{
lean_object* x_12; 
x_12 = l_List_forIn_x27_loop___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__4(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9, x_10);
lean_dec(x_10);
lean_dec_ref(x_9);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_1);
return x_12;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___redArg(x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9, lean_object* x_10) {
_start:
{
lean_object* x_11; 
x_11 = l_Lean_throwErrorAt___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__6(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8, x_9);
lean_dec(x_9);
lean_dec(x_7);
lean_dec_ref(x_6);
lean_dec(x_5);
lean_dec(x_2);
return x_11;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___redArg(x_1, x_2, x_7);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8, lean_object* x_9) {
_start:
{
lean_object* x_10; 
x_10 = l_Lean_Elab_addMacroStack___at___00Lean_throwError___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__3_spec__12(x_1, x_2, x_3, x_4, x_5, x_6, x_7, x_8);
lean_dec(x_8);
lean_dec_ref(x_7);
lean_dec(x_6);
lean_dec_ref(x_5);
lean_dec(x_4);
lean_dec_ref(x_3);
return x_10;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec_ref(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
uint8_t x_4; lean_object* x_5; 
x_4 = l_Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27(x_1, x_2, x_3);
lean_dec_ref(x_3);
x_5 = lean_box(x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___redArg(x_2, x_3);
return x_4;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3) {
_start:
{
lean_object* x_4; 
x_4 = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__11_spec__30(x_1, x_2, x_3);
lean_dec(x_3);
lean_dec(x_2);
return x_4;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33(lean_object* x_1, lean_object* x_2, size_t x_3, lean_object* x_4) {
_start:
{
uint8_t x_5; 
x_5 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___redArg(x_2, x_3, x_4);
return x_5;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4) {
_start:
{
size_t x_5; uint8_t x_6; lean_object* x_7; 
x_5 = lean_unbox_usize(x_3);
lean_dec(x_3);
x_6 = l_Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33(x_1, x_2, x_5, x_4);
lean_dec_ref(x_4);
x_7 = lean_box(x_6);
return x_7;
}
}
LEAN_EXPORT uint8_t l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___redArg(x_2, x_5, x_6);
return x_7;
}
}
LEAN_EXPORT lean_object* l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6) {
_start:
{
uint8_t x_7; lean_object* x_8; 
x_7 = l_Lean_PersistentHashMap_containsAtAux___at___00Lean_PersistentHashMap_containsAux___at___00Lean_PersistentHashMap_contains___at___00__private_Lean_ExtraModUses_0__Lean_recordExtraModUseCore___at___00Lean_recordExtraModUseFromDecl___at___00Lean_Elab_liftMacroM___at___00Lean_Elab_Do_InferControlInfo_ofElem_spec__0_spec__3_spec__9_spec__27_spec__33_spec__37(x_1, x_2, x_3, x_4, x_5, x_6);
lean_dec_ref(x_6);
lean_dec_ref(x_3);
lean_dec_ref(x_2);
x_8 = lean_box(x_7);
return x_8;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Do_InferControlInfo_ofSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoSeq___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Do_inferControlInfoSeq(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Do_InferControlInfo_ofElem(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_Do_inferControlInfoElem___boxed(lean_object* x_1, lean_object* x_2, lean_object* x_3, lean_object* x_4, lean_object* x_5, lean_object* x_6, lean_object* x_7, lean_object* x_8) {
_start:
{
lean_object* x_9; 
x_9 = l_Lean_Elab_Do_inferControlInfoElem(x_1, x_2, x_3, x_4, x_5, x_6, x_7);
return x_9;
}
}
lean_object* initialize_Lean_Elab_Term(uint8_t builtin);
lean_object* initialize_Lean_Parser_Do(uint8_t builtin);
lean_object* initialize_Lean_Elab_Do_PatternVar(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_Do_InferControlInfo(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Elab_Term(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Parser_Do(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Do_PatternVar(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Elab_Do_instInhabitedControlInfo_default = _init_l_Lean_Elab_Do_instInhabitedControlInfo_default();
lean_mark_persistent(l_Lean_Elab_Do_instInhabitedControlInfo_default);
l_Lean_Elab_Do_instInhabitedControlInfo = _init_l_Lean_Elab_Do_instInhabitedControlInfo();
lean_mark_persistent(l_Lean_Elab_Do_instInhabitedControlInfo);
l_Lean_Elab_Do_ControlInfo_pure = _init_l_Lean_Elab_Do_ControlInfo_pure();
lean_mark_persistent(l_Lean_Elab_Do_ControlInfo_pure);
if (builtin) {res = l_Lean_Elab_Do_initFn_00___x40_Lean_Elab_Do_InferControlInfo_39974866____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_Do_controlInfoElemAttribute = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_Do_controlInfoElemAttribute);
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_docString__1();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}if (builtin) {res = l_Lean_Elab_Do_controlInfoElemAttribute___regBuiltin_Lean_Elab_Do_controlInfoElemAttribute_declRange__3();
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
}return lean_io_result_mk_ok(lean_box(0));
}
#ifdef __cplusplus
}
#endif
