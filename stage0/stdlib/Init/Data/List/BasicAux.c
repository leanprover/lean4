// Lean compiler output
// Module: Init.Data.List.BasicAux
// Imports: public import Init.GetElem public import Init.WFTactics import Init.ByCases import Init.Classical import Init.Data.Array.Basic import Init.Data.Nat.Linear
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
size_t lean_ptr_addr(lean_object*);
uint8_t lean_usize_dec_eq(size_t, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_to_list(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
lean_object* l_List_getLast___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_getD___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getD___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getD(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getD___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_getLast_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "Init.Data.List.BasicAux"};
static const lean_object* l_List_getLast_x21___redArg___closed__0 = (const lean_object*)&l_List_getLast_x21___redArg___closed__0_value;
static const lean_string_object l_List_getLast_x21___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "List.getLast!"};
static const lean_object* l_List_getLast_x21___redArg___closed__1 = (const lean_object*)&l_List_getLast_x21___redArg___closed__1_value;
static const lean_string_object l_List_getLast_x21___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "empty list"};
static const lean_object* l_List_getLast_x21___redArg___closed__2 = (const lean_object*)&l_List_getLast_x21___redArg___closed__2_value;
static lean_once_cell_t l_List_getLast_x21___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_getLast_x21___redArg___closed__3;
LEAN_EXPORT lean_object* l_List_getLast_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLast_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLast_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getLast_x21___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_head_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "List.head!"};
static const lean_object* l_List_head_x21___redArg___closed__0 = (const lean_object*)&l_List_head_x21___redArg___closed__0_value;
static lean_once_cell_t l_List_head_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_head_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_head_x21___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_head_x21(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_head_x21___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00List_tail_x21_spec__0___redArg(lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00List_tail_x21_spec__0(lean_object*, lean_object*);
static const lean_string_object l_List_tail_x21___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "List.tail!"};
static const lean_object* l_List_tail_x21___redArg___closed__0 = (const lean_object*)&l_List_tail_x21___redArg___closed__0_value;
static lean_once_cell_t l_List_tail_x21___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List_tail_x21___redArg___closed__1;
LEAN_EXPORT lean_object* l_List_tail_x21___redArg(lean_object*);
LEAN_EXPORT lean_object* l_List_tail_x21___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_tail_x21(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_tail_x21___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_List_partitionM___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_List_partitionM___redArg___closed__0 = (const lean_object*)&l_List_partitionM___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_List_partitionM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partitionM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionMap_go___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionMap_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partitionMap___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_partitionMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapMonoM___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapMonoM___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapMonoM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapMonoM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapMono___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapMono(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List_tacticSizeOf__list__dec___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "List"};
static const lean_object* l_List_tacticSizeOf__list__dec___closed__0 = (const lean_object*)&l_List_tacticSizeOf__list__dec___closed__0_value;
static const lean_string_object l_List_tacticSizeOf__list__dec___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "tacticSizeOf_list_dec"};
static const lean_object* l_List_tacticSizeOf__list__dec___closed__1 = (const lean_object*)&l_List_tacticSizeOf__list__dec___closed__1_value;
static const lean_ctor_object l_List_tacticSizeOf__list__dec___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_tacticSizeOf__list__dec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List_tacticSizeOf__list__dec___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List_tacticSizeOf__list__dec___closed__2_value_aux_0),((lean_object*)&l_List_tacticSizeOf__list__dec___closed__1_value),LEAN_SCALAR_PTR_LITERAL(142, 26, 166, 229, 218, 134, 190, 42)}};
static const lean_object* l_List_tacticSizeOf__list__dec___closed__2 = (const lean_object*)&l_List_tacticSizeOf__list__dec___closed__2_value;
static const lean_string_object l_List_tacticSizeOf__list__dec___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "sizeOf_list_dec"};
static const lean_object* l_List_tacticSizeOf__list__dec___closed__3 = (const lean_object*)&l_List_tacticSizeOf__list__dec___closed__3_value;
static const lean_ctor_object l_List_tacticSizeOf__list__dec___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 6}, .m_objs = {((lean_object*)&l_List_tacticSizeOf__list__dec___closed__3_value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_List_tacticSizeOf__list__dec___closed__4 = (const lean_object*)&l_List_tacticSizeOf__list__dec___closed__4_value;
static const lean_ctor_object l_List_tacticSizeOf__list__dec___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_List_tacticSizeOf__list__dec___closed__2_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_List_tacticSizeOf__list__dec___closed__4_value)}};
static const lean_object* l_List_tacticSizeOf__list__dec___closed__5 = (const lean_object*)&l_List_tacticSizeOf__list__dec___closed__5_value;
LEAN_EXPORT const lean_object* l_List_tacticSizeOf__list__dec = (const lean_object*)&l_List_tacticSizeOf__list__dec___closed__5_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "first"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__3 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__3_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(59, 232, 35, 17, 172, 62, 48, 174)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__5 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__5_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__6 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__6_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__7 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__7_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__8 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__8_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "|"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__9 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__9_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__10 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__10_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__12 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__12_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "withReducible"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__14 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__14_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__14_value),LEAN_SCALAR_PTR_LITERAL(197, 44, 223, 192, 8, 197, 146, 83)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "with_reducible"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__16 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__16_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__17 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__17_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "sizeOf_lt_of_mem"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19_value;
static lean_once_cell_t l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(62, 240, 33, 111, 18, 75, 77, 36)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__21 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__21_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_tacticSizeOf__list__dec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(40, 188, 81, 150, 88, 168, 235, 24)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__22_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__23 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__23_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__23_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__24 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__24_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__25 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__25_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "assumption"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__26 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__26_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__26_value),LEAN_SCALAR_PTR_LITERAL(240, 50, 167, 190, 65, 82, 149, 231)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "done"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__28 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__28_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__28_value),LEAN_SCALAR_PTR_LITERAL(113, 161, 179, 82, 204, 87, 48, 123)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__31 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__31_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__31_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "Nat.lt_of_lt_of_le"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__33 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__33_value;
static lean_once_cell_t l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__35 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__35_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "lt_of_lt_of_le"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__36 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__36_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__36_value),LEAN_SCALAR_PTR_LITERAL(6, 233, 240, 89, 98, 17, 244, 226)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__38 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__38_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__38_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__39 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__39_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__40 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__40_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__42 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__42_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__44 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__44_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__45 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__45_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__45_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__46 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__46_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__47 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__47_value;
static lean_once_cell_t l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List_tacticSizeOf__list__dec___closed__0_value),LEAN_SCALAR_PTR_LITERAL(245, 188, 225, 225, 165, 5, 251, 132)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__49 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__49_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__49_value)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__50 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__50_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__50_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__51 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__51_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "syntheticHole"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__52 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__52_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__52_value),LEAN_SCALAR_PTR_LITERAL(218, 189, 67, 60, 211, 196, 112, 165)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\?"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__54 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__54_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__55 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__55_value;
static lean_once_cell_t l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__55_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__57 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__57_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__58 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__58_value;
static lean_once_cell_t l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "case'"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__60 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__60_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(134, 21, 185, 205, 238, 88, 7, 106)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "caseArg"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__62 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__62_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(151, 119, 254, 229, 232, 21, 225, 201)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "binderIdent"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__64 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__64_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__64_value),LEAN_SCALAR_PTR_LITERAL(37, 194, 68, 106, 254, 181, 31, 191)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__66 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__66_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__67 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__67_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__69 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__69_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "configItem"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__71 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__71_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__71_value),LEAN_SCALAR_PTR_LITERAL(205, 9, 236, 192, 59, 252, 178, 140)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "posConfigItem"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__73 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__73_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_0),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_1),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value_aux_2),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__73_value),LEAN_SCALAR_PTR_LITERAL(232, 137, 50, 117, 152, 182, 155, 132)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__75 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__75_value;
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "arith"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__76 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__76_value;
static lean_once_cell_t l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(72, 221, 106, 103, 22, 21, 224, 51)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__78 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__78_value;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "tacticDecreasing_trivial"};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__0 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__0_value;
static const lean_ctor_object l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(214, 43, 154, 34, 2, 43, 185, 79)}};
static const lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__1 = (const lean_object*)&l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__1_value;
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_getD___redArg(lean_object* v_as_1_, lean_object* v_i_2_, lean_object* v_fallback_3_){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = l_List_get_x3fInternal___redArg(v_as_1_, v_i_2_);
if (lean_obj_tag(v___x_4_) == 0)
{
lean_inc(v_fallback_3_);
return v_fallback_3_;
}
else
{
lean_object* v_val_5_; 
v_val_5_ = lean_ctor_get(v___x_4_, 0);
lean_inc(v_val_5_);
lean_dec_ref(v___x_4_);
return v_val_5_;
}
}
}
LEAN_EXPORT lean_object* l_List_getD___redArg___boxed(lean_object* v_as_6_, lean_object* v_i_7_, lean_object* v_fallback_8_){
_start:
{
lean_object* v_res_9_; 
v_res_9_ = l_List_getD___redArg(v_as_6_, v_i_7_, v_fallback_8_);
lean_dec(v_fallback_8_);
lean_dec(v_as_6_);
return v_res_9_;
}
}
LEAN_EXPORT lean_object* l_List_getD(lean_object* v_00_u03b1_10_, lean_object* v_as_11_, lean_object* v_i_12_, lean_object* v_fallback_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_List_getD___redArg(v_as_11_, v_i_12_, v_fallback_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_List_getD___boxed(lean_object* v_00_u03b1_15_, lean_object* v_as_16_, lean_object* v_i_17_, lean_object* v_fallback_18_){
_start:
{
lean_object* v_res_19_; 
v_res_19_ = l_List_getD(v_00_u03b1_15_, v_as_16_, v_i_17_, v_fallback_18_);
lean_dec(v_fallback_18_);
lean_dec(v_as_16_);
return v_res_19_;
}
}
static lean_object* _init_l_List_getLast_x21___redArg___closed__3(void){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; 
v___x_23_ = ((lean_object*)(l_List_getLast_x21___redArg___closed__2));
v___x_24_ = lean_unsigned_to_nat(13u);
v___x_25_ = lean_unsigned_to_nat(64u);
v___x_26_ = ((lean_object*)(l_List_getLast_x21___redArg___closed__1));
v___x_27_ = ((lean_object*)(l_List_getLast_x21___redArg___closed__0));
v___x_28_ = l_mkPanicMessageWithDecl(v___x_27_, v___x_26_, v___x_25_, v___x_24_, v___x_23_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x21___redArg(lean_object* v_inst_29_, lean_object* v_x_30_){
_start:
{
if (lean_obj_tag(v_x_30_) == 0)
{
lean_object* v___x_31_; lean_object* v___x_32_; 
v___x_31_ = lean_obj_once(&l_List_getLast_x21___redArg___closed__3, &l_List_getLast_x21___redArg___closed__3_once, _init_l_List_getLast_x21___redArg___closed__3);
v___x_32_ = l_panic___redArg(v_inst_29_, v___x_31_);
return v___x_32_;
}
else
{
lean_object* v___x_33_; 
v___x_33_ = l_List_getLast___redArg(v_x_30_);
return v___x_33_;
}
}
}
LEAN_EXPORT lean_object* l_List_getLast_x21___redArg___boxed(lean_object* v_inst_34_, lean_object* v_x_35_){
_start:
{
lean_object* v_res_36_; 
v_res_36_ = l_List_getLast_x21___redArg(v_inst_34_, v_x_35_);
lean_dec(v_x_35_);
lean_dec(v_inst_34_);
return v_res_36_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x21(lean_object* v_00_u03b1_37_, lean_object* v_inst_38_, lean_object* v_x_39_){
_start:
{
lean_object* v___x_40_; 
v___x_40_ = l_List_getLast_x21___redArg(v_inst_38_, v_x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_List_getLast_x21___boxed(lean_object* v_00_u03b1_41_, lean_object* v_inst_42_, lean_object* v_x_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_List_getLast_x21(v_00_u03b1_41_, v_inst_42_, v_x_43_);
lean_dec(v_x_43_);
lean_dec(v_inst_42_);
return v_res_44_;
}
}
static lean_object* _init_l_List_head_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v___x_46_ = ((lean_object*)(l_List_getLast_x21___redArg___closed__2));
v___x_47_ = lean_unsigned_to_nat(12u);
v___x_48_ = lean_unsigned_to_nat(80u);
v___x_49_ = ((lean_object*)(l_List_head_x21___redArg___closed__0));
v___x_50_ = ((lean_object*)(l_List_getLast_x21___redArg___closed__0));
v___x_51_ = l_mkPanicMessageWithDecl(v___x_50_, v___x_49_, v___x_48_, v___x_47_, v___x_46_);
return v___x_51_;
}
}
LEAN_EXPORT lean_object* l_List_head_x21___redArg(lean_object* v_inst_52_, lean_object* v_x_53_){
_start:
{
if (lean_obj_tag(v_x_53_) == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
v___x_54_ = lean_obj_once(&l_List_head_x21___redArg___closed__1, &l_List_head_x21___redArg___closed__1_once, _init_l_List_head_x21___redArg___closed__1);
v___x_55_ = l_panic___redArg(v_inst_52_, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v_head_56_; 
v_head_56_ = lean_ctor_get(v_x_53_, 0);
lean_inc(v_head_56_);
return v_head_56_;
}
}
}
LEAN_EXPORT lean_object* l_List_head_x21___redArg___boxed(lean_object* v_inst_57_, lean_object* v_x_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l_List_head_x21___redArg(v_inst_57_, v_x_58_);
lean_dec(v_x_58_);
lean_dec(v_inst_57_);
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l_List_head_x21(lean_object* v_00_u03b1_60_, lean_object* v_inst_61_, lean_object* v_x_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_List_head_x21___redArg(v_inst_61_, v_x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_List_head_x21___boxed(lean_object* v_00_u03b1_64_, lean_object* v_inst_65_, lean_object* v_x_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_List_head_x21(v_00_u03b1_64_, v_inst_65_, v_x_66_);
lean_dec(v_x_66_);
lean_dec(v_inst_65_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00List_tail_x21_spec__0___redArg(lean_object* v_msg_68_){
_start:
{
lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_69_ = lean_box(0);
v___x_70_ = lean_panic_fn_borrowed(v___x_69_, v_msg_68_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00List_tail_x21_spec__0(lean_object* v_00_u03b1_71_, lean_object* v_msg_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_panic___at___00List_tail_x21_spec__0___redArg(v_msg_72_);
return v___x_73_;
}
}
static lean_object* _init_l_List_tail_x21___redArg___closed__1(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v___x_75_ = ((lean_object*)(l_List_getLast_x21___redArg___closed__2));
v___x_76_ = lean_unsigned_to_nat(13u);
v___x_77_ = lean_unsigned_to_nat(99u);
v___x_78_ = ((lean_object*)(l_List_tail_x21___redArg___closed__0));
v___x_79_ = ((lean_object*)(l_List_getLast_x21___redArg___closed__0));
v___x_80_ = l_mkPanicMessageWithDecl(v___x_79_, v___x_78_, v___x_77_, v___x_76_, v___x_75_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x21___redArg(lean_object* v_x_81_){
_start:
{
if (lean_obj_tag(v_x_81_) == 0)
{
lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_82_ = lean_obj_once(&l_List_tail_x21___redArg___closed__1, &l_List_tail_x21___redArg___closed__1_once, _init_l_List_tail_x21___redArg___closed__1);
v___x_83_ = l_panic___at___00List_tail_x21_spec__0___redArg(v___x_82_);
return v___x_83_;
}
else
{
lean_object* v_tail_84_; 
v_tail_84_ = lean_ctor_get(v_x_81_, 1);
lean_inc(v_tail_84_);
return v_tail_84_;
}
}
}
LEAN_EXPORT lean_object* l_List_tail_x21___redArg___boxed(lean_object* v_x_85_){
_start:
{
lean_object* v_res_86_; 
v_res_86_ = l_List_tail_x21___redArg(v_x_85_);
lean_dec(v_x_85_);
return v_res_86_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x21(lean_object* v_00_u03b1_87_, lean_object* v_x_88_){
_start:
{
lean_object* v___x_89_; 
v___x_89_ = l_List_tail_x21___redArg(v_x_88_);
return v___x_89_;
}
}
LEAN_EXPORT lean_object* l_List_tail_x21___boxed(lean_object* v_00_u03b1_90_, lean_object* v_x_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_List_tail_x21(v_00_u03b1_90_, v_x_91_);
lean_dec(v_x_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg___lam__0___boxed(lean_object* v_a_93_, lean_object* v_head_94_, lean_object* v_inst_95_, lean_object* v_p_96_, lean_object* v_tail_97_, lean_object* v_a_98_, lean_object* v_____do__lift_99_){
_start:
{
uint8_t v_____do__lift_97__boxed_100_; lean_object* v_res_101_; 
v_____do__lift_97__boxed_100_ = lean_unbox(v_____do__lift_99_);
v_res_101_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg___lam__0(v_a_93_, v_head_94_, v_inst_95_, v_p_96_, v_tail_97_, v_a_98_, v_____do__lift_97__boxed_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(lean_object* v_inst_102_, lean_object* v_p_103_, lean_object* v_a_104_, lean_object* v_a_105_, lean_object* v_a_106_){
_start:
{
if (lean_obj_tag(v_a_104_) == 0)
{
lean_object* v_toApplicative_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_118_; 
v_toApplicative_107_ = lean_ctor_get(v_inst_102_, 0);
lean_inc_ref(v_toApplicative_107_);
lean_dec(v_p_103_);
v_isSharedCheck_118_ = !lean_is_exclusive(v_inst_102_);
if (v_isSharedCheck_118_ == 0)
{
lean_object* v_unused_119_; lean_object* v_unused_120_; 
v_unused_119_ = lean_ctor_get(v_inst_102_, 1);
lean_dec(v_unused_119_);
v_unused_120_ = lean_ctor_get(v_inst_102_, 0);
lean_dec(v_unused_120_);
v___x_109_ = v_inst_102_;
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
else
{
lean_dec(v_inst_102_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_118_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v_toPure_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_115_; 
v_toPure_111_ = lean_ctor_get(v_toApplicative_107_, 1);
lean_inc(v_toPure_111_);
lean_dec_ref(v_toApplicative_107_);
v___x_112_ = lean_array_to_list(v_a_105_);
v___x_113_ = lean_array_to_list(v_a_106_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_113_);
lean_ctor_set(v___x_109_, 0, v___x_112_);
v___x_115_ = v___x_109_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_117_; 
v_reuseFailAlloc_117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_117_, 0, v___x_112_);
lean_ctor_set(v_reuseFailAlloc_117_, 1, v___x_113_);
v___x_115_ = v_reuseFailAlloc_117_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
lean_object* v___x_116_; 
v___x_116_ = lean_apply_2(v_toPure_111_, lean_box(0), v___x_115_);
return v___x_116_;
}
}
}
else
{
lean_object* v_toBind_121_; lean_object* v_head_122_; lean_object* v_tail_123_; lean_object* v___f_124_; lean_object* v___x_125_; lean_object* v___x_126_; 
v_toBind_121_ = lean_ctor_get(v_inst_102_, 1);
lean_inc(v_toBind_121_);
v_head_122_ = lean_ctor_get(v_a_104_, 0);
lean_inc_n(v_head_122_, 2);
v_tail_123_ = lean_ctor_get(v_a_104_, 1);
lean_inc(v_tail_123_);
lean_dec_ref(v_a_104_);
lean_inc(v_p_103_);
v___f_124_ = lean_alloc_closure((void*)(l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg___lam__0___boxed), 7, 6);
lean_closure_set(v___f_124_, 0, v_a_106_);
lean_closure_set(v___f_124_, 1, v_head_122_);
lean_closure_set(v___f_124_, 2, v_inst_102_);
lean_closure_set(v___f_124_, 3, v_p_103_);
lean_closure_set(v___f_124_, 4, v_tail_123_);
lean_closure_set(v___f_124_, 5, v_a_105_);
v___x_125_ = lean_apply_1(v_p_103_, v_head_122_);
v___x_126_ = lean_apply_4(v_toBind_121_, lean_box(0), lean_box(0), v___x_125_, v___f_124_);
return v___x_126_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg___lam__0(lean_object* v_a_127_, lean_object* v_head_128_, lean_object* v_inst_129_, lean_object* v_p_130_, lean_object* v_tail_131_, lean_object* v_a_132_, uint8_t v_____do__lift_133_){
_start:
{
if (v_____do__lift_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
v___x_134_ = lean_array_push(v_a_127_, v_head_128_);
v___x_135_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(v_inst_129_, v_p_130_, v_tail_131_, v_a_132_, v___x_134_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_array_push(v_a_132_, v_head_128_);
v___x_137_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(v_inst_129_, v_p_130_, v_tail_131_, v___x_136_, v_a_127_);
return v___x_137_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionM_go(lean_object* v_m_138_, lean_object* v_00_u03b1_139_, lean_object* v_inst_140_, lean_object* v_p_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(v_inst_140_, v_p_141_, v_a_142_, v_a_143_, v_a_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_List_partitionM___redArg(lean_object* v_inst_148_, lean_object* v_p_149_, lean_object* v_l_150_){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_List_partitionM___redArg___closed__0));
v___x_152_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(v_inst_148_, v_p_149_, v_l_150_, v___x_151_, v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_List_partitionM(lean_object* v_m_153_, lean_object* v_00_u03b1_154_, lean_object* v_inst_155_, lean_object* v_p_156_, lean_object* v_l_157_){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = ((lean_object*)(l_List_partitionM___redArg___closed__0));
v___x_159_ = l___private_Init_Data_List_BasicAux_0__List_partitionM_go___redArg(v_inst_155_, v_p_156_, v_l_157_, v___x_158_, v___x_158_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionMap_go___redArg(lean_object* v_f_160_, lean_object* v_a_161_, lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
if (lean_obj_tag(v_a_161_) == 0)
{
lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; 
lean_dec_ref(v_f_160_);
v___x_164_ = lean_array_to_list(v_a_162_);
v___x_165_ = lean_array_to_list(v_a_163_);
v___x_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
return v___x_166_;
}
else
{
lean_object* v_head_167_; lean_object* v_tail_168_; lean_object* v___x_169_; 
v_head_167_ = lean_ctor_get(v_a_161_, 0);
lean_inc(v_head_167_);
v_tail_168_ = lean_ctor_get(v_a_161_, 1);
lean_inc(v_tail_168_);
lean_dec_ref(v_a_161_);
lean_inc_ref(v_f_160_);
v___x_169_ = lean_apply_1(v_f_160_, v_head_167_);
if (lean_obj_tag(v___x_169_) == 0)
{
lean_object* v_val_170_; lean_object* v___x_171_; 
v_val_170_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_val_170_);
lean_dec_ref(v___x_169_);
v___x_171_ = lean_array_push(v_a_162_, v_val_170_);
v_a_161_ = v_tail_168_;
v_a_162_ = v___x_171_;
goto _start;
}
else
{
lean_object* v_val_173_; lean_object* v___x_174_; 
v_val_173_ = lean_ctor_get(v___x_169_, 0);
lean_inc(v_val_173_);
lean_dec_ref(v___x_169_);
v___x_174_ = lean_array_push(v_a_163_, v_val_173_);
v_a_161_ = v_tail_168_;
v_a_163_ = v___x_174_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_partitionMap_go(lean_object* v_00_u03b1_176_, lean_object* v_00_u03b2_177_, lean_object* v_00_u03b3_178_, lean_object* v_f_179_, lean_object* v_a_180_, lean_object* v_a_181_, lean_object* v_a_182_){
_start:
{
lean_object* v___x_183_; 
v___x_183_ = l___private_Init_Data_List_BasicAux_0__List_partitionMap_go___redArg(v_f_179_, v_a_180_, v_a_181_, v_a_182_);
return v___x_183_;
}
}
LEAN_EXPORT lean_object* l_List_partitionMap___redArg(lean_object* v_f_184_, lean_object* v_l_185_){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l_List_partitionM___redArg___closed__0));
v___x_187_ = l___private_Init_Data_List_BasicAux_0__List_partitionMap_go___redArg(v_f_184_, v_l_185_, v___x_186_, v___x_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_List_partitionMap(lean_object* v_00_u03b1_188_, lean_object* v_00_u03b2_189_, lean_object* v_00_u03b3_190_, lean_object* v_f_191_, lean_object* v_l_192_){
_start:
{
lean_object* v___x_193_; lean_object* v___x_194_; 
v___x_193_ = ((lean_object*)(l_List_partitionM___redArg___closed__0));
v___x_194_ = l___private_Init_Data_List_BasicAux_0__List_partitionMap_go___redArg(v_f_191_, v_l_192_, v___x_193_, v___x_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__0(lean_object* v_b_x27_195_, lean_object* v_toPure_196_, lean_object* v_as_197_, lean_object* v_head_198_, lean_object* v_tail_199_, lean_object* v_bs_x27_200_){
_start:
{
uint8_t v___y_202_; size_t v___x_206_; size_t v___x_207_; uint8_t v___x_208_; 
v___x_206_ = lean_ptr_addr(v_b_x27_195_);
v___x_207_ = lean_ptr_addr(v_head_198_);
v___x_208_ = lean_usize_dec_eq(v___x_206_, v___x_207_);
if (v___x_208_ == 0)
{
v___y_202_ = v___x_208_;
goto v___jp_201_;
}
else
{
size_t v___x_209_; size_t v___x_210_; uint8_t v___x_211_; 
v___x_209_ = lean_ptr_addr(v_bs_x27_200_);
v___x_210_ = lean_ptr_addr(v_tail_199_);
v___x_211_ = lean_usize_dec_eq(v___x_209_, v___x_210_);
v___y_202_ = v___x_211_;
goto v___jp_201_;
}
v___jp_201_:
{
if (v___y_202_ == 0)
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_dec(v_as_197_);
v___x_203_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_203_, 0, v_b_x27_195_);
lean_ctor_set(v___x_203_, 1, v_bs_x27_200_);
v___x_204_ = lean_apply_2(v_toPure_196_, lean_box(0), v___x_203_);
return v___x_204_;
}
else
{
lean_object* v___x_205_; 
lean_dec(v_bs_x27_200_);
lean_dec(v_b_x27_195_);
v___x_205_ = lean_apply_2(v_toPure_196_, lean_box(0), v_as_197_);
return v___x_205_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__0___boxed(lean_object* v_b_x27_212_, lean_object* v_toPure_213_, lean_object* v_as_214_, lean_object* v_head_215_, lean_object* v_tail_216_, lean_object* v_bs_x27_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__0(v_b_x27_212_, v_toPure_213_, v_as_214_, v_head_215_, v_tail_216_, v_bs_x27_217_);
lean_dec(v_tail_216_);
lean_dec(v_head_215_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg(lean_object* v_inst_219_, lean_object* v_as_220_, lean_object* v_f_221_){
_start:
{
if (lean_obj_tag(v_as_220_) == 0)
{
lean_object* v_toApplicative_222_; lean_object* v_toPure_223_; lean_object* v___x_224_; 
v_toApplicative_222_ = lean_ctor_get(v_inst_219_, 0);
lean_inc_ref(v_toApplicative_222_);
lean_dec(v_f_221_);
lean_dec_ref(v_inst_219_);
v_toPure_223_ = lean_ctor_get(v_toApplicative_222_, 1);
lean_inc(v_toPure_223_);
lean_dec_ref(v_toApplicative_222_);
v___x_224_ = lean_apply_2(v_toPure_223_, lean_box(0), v_as_220_);
return v___x_224_;
}
else
{
lean_object* v_toApplicative_225_; lean_object* v_toBind_226_; lean_object* v_toPure_227_; lean_object* v_head_228_; lean_object* v_tail_229_; lean_object* v___f_230_; lean_object* v___x_231_; lean_object* v___x_232_; 
v_toApplicative_225_ = lean_ctor_get(v_inst_219_, 0);
v_toBind_226_ = lean_ctor_get(v_inst_219_, 1);
lean_inc_n(v_toBind_226_, 2);
v_toPure_227_ = lean_ctor_get(v_toApplicative_225_, 1);
lean_inc(v_toPure_227_);
v_head_228_ = lean_ctor_get(v_as_220_, 0);
lean_inc_n(v_head_228_, 2);
v_tail_229_ = lean_ctor_get(v_as_220_, 1);
lean_inc(v_tail_229_);
lean_inc(v_f_221_);
v___f_230_ = lean_alloc_closure((void*)(l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__1), 8, 7);
lean_closure_set(v___f_230_, 0, v_toPure_227_);
lean_closure_set(v___f_230_, 1, v_as_220_);
lean_closure_set(v___f_230_, 2, v_head_228_);
lean_closure_set(v___f_230_, 3, v_tail_229_);
lean_closure_set(v___f_230_, 4, v_inst_219_);
lean_closure_set(v___f_230_, 5, v_f_221_);
lean_closure_set(v___f_230_, 6, v_toBind_226_);
v___x_231_ = lean_apply_1(v_f_221_, v_head_228_);
v___x_232_ = lean_apply_4(v_toBind_226_, lean_box(0), lean_box(0), v___x_231_, v___f_230_);
return v___x_232_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__1(lean_object* v_toPure_233_, lean_object* v_as_234_, lean_object* v_head_235_, lean_object* v_tail_236_, lean_object* v_inst_237_, lean_object* v_f_238_, lean_object* v_toBind_239_, lean_object* v_b_x27_240_){
_start:
{
lean_object* v___f_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_inc(v_tail_236_);
v___f_241_ = lean_alloc_closure((void*)(l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg___lam__0___boxed), 6, 5);
lean_closure_set(v___f_241_, 0, v_b_x27_240_);
lean_closure_set(v___f_241_, 1, v_toPure_233_);
lean_closure_set(v___f_241_, 2, v_as_234_);
lean_closure_set(v___f_241_, 3, v_head_235_);
lean_closure_set(v___f_241_, 4, v_tail_236_);
v___x_242_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg(v_inst_237_, v_tail_236_, v_f_238_);
v___x_243_ = lean_apply_4(v_toBind_239_, lean_box(0), lean_box(0), v___x_242_, v___f_241_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp(lean_object* v_m_244_, lean_object* v_00_u03b1_245_, lean_object* v_inst_246_, lean_object* v_as_247_, lean_object* v_f_248_){
_start:
{
lean_object* v___x_249_; 
v___x_249_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg(v_inst_246_, v_as_247_, v_f_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_List_mapMonoM___redArg___lam__0(lean_object* v_____do__lift_250_, lean_object* v_toPure_251_, lean_object* v_____do__lift_252_){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; 
v___x_253_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_253_, 0, v_____do__lift_250_);
lean_ctor_set(v___x_253_, 1, v_____do__lift_252_);
v___x_254_ = lean_apply_2(v_toPure_251_, lean_box(0), v___x_253_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_List_mapMonoM___redArg___lam__1(lean_object* v_toPure_255_, lean_object* v_inst_256_, lean_object* v_tail_257_, lean_object* v_f_258_, lean_object* v_toBind_259_, lean_object* v_____do__lift_260_){
_start:
{
lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___f_261_ = lean_alloc_closure((void*)(l_List_mapMonoM___redArg___lam__0), 3, 2);
lean_closure_set(v___f_261_, 0, v_____do__lift_260_);
lean_closure_set(v___f_261_, 1, v_toPure_255_);
v___x_262_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___redArg(v_inst_256_, v_tail_257_, v_f_258_);
v___x_263_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v___x_262_, v___f_261_);
return v___x_263_;
}
}
LEAN_EXPORT lean_object* l_List_mapMonoM___redArg(lean_object* v_inst_264_, lean_object* v_as_265_, lean_object* v_f_266_){
_start:
{
if (lean_obj_tag(v_as_265_) == 0)
{
lean_object* v_toApplicative_267_; lean_object* v_toPure_268_; lean_object* v___x_269_; 
v_toApplicative_267_ = lean_ctor_get(v_inst_264_, 0);
lean_inc_ref(v_toApplicative_267_);
lean_dec(v_f_266_);
lean_dec_ref(v_inst_264_);
v_toPure_268_ = lean_ctor_get(v_toApplicative_267_, 1);
lean_inc(v_toPure_268_);
lean_dec_ref(v_toApplicative_267_);
v___x_269_ = lean_apply_2(v_toPure_268_, lean_box(0), v_as_265_);
return v___x_269_;
}
else
{
lean_object* v_toApplicative_270_; lean_object* v_toBind_271_; lean_object* v_toPure_272_; lean_object* v_head_273_; lean_object* v_tail_274_; lean_object* v___f_275_; lean_object* v___x_276_; lean_object* v___x_277_; 
v_toApplicative_270_ = lean_ctor_get(v_inst_264_, 0);
v_toBind_271_ = lean_ctor_get(v_inst_264_, 1);
lean_inc_n(v_toBind_271_, 2);
v_toPure_272_ = lean_ctor_get(v_toApplicative_270_, 1);
lean_inc(v_toPure_272_);
v_head_273_ = lean_ctor_get(v_as_265_, 0);
lean_inc(v_head_273_);
v_tail_274_ = lean_ctor_get(v_as_265_, 1);
lean_inc(v_tail_274_);
lean_dec_ref(v_as_265_);
lean_inc(v_f_266_);
v___f_275_ = lean_alloc_closure((void*)(l_List_mapMonoM___redArg___lam__1), 6, 5);
lean_closure_set(v___f_275_, 0, v_toPure_272_);
lean_closure_set(v___f_275_, 1, v_inst_264_);
lean_closure_set(v___f_275_, 2, v_tail_274_);
lean_closure_set(v___f_275_, 3, v_f_266_);
lean_closure_set(v___f_275_, 4, v_toBind_271_);
v___x_276_ = lean_apply_1(v_f_266_, v_head_273_);
v___x_277_ = lean_apply_4(v_toBind_271_, lean_box(0), lean_box(0), v___x_276_, v___f_275_);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapMonoM(lean_object* v_m_278_, lean_object* v_00_u03b1_279_, lean_object* v_inst_280_, lean_object* v_as_281_, lean_object* v_f_282_){
_start:
{
lean_object* v___x_283_; 
v___x_283_ = l_List_mapMonoM___redArg(v_inst_280_, v_as_281_, v_f_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(lean_object* v_f_284_, lean_object* v_as_285_){
_start:
{
if (lean_obj_tag(v_as_285_) == 0)
{
lean_dec(v_f_284_);
return v_as_285_;
}
else
{
lean_object* v_head_286_; lean_object* v_tail_287_; lean_object* v___x_288_; lean_object* v___x_289_; uint8_t v___y_291_; size_t v___x_301_; size_t v___x_302_; uint8_t v___x_303_; 
v_head_286_ = lean_ctor_get(v_as_285_, 0);
v_tail_287_ = lean_ctor_get(v_as_285_, 1);
lean_inc(v_f_284_);
lean_inc(v_head_286_);
v___x_288_ = lean_apply_1(v_f_284_, v_head_286_);
lean_inc(v_tail_287_);
v___x_289_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(v_f_284_, v_tail_287_);
v___x_301_ = lean_ptr_addr(v___x_288_);
v___x_302_ = lean_ptr_addr(v_head_286_);
v___x_303_ = lean_usize_dec_eq(v___x_301_, v___x_302_);
if (v___x_303_ == 0)
{
v___y_291_ = v___x_303_;
goto v___jp_290_;
}
else
{
size_t v___x_304_; size_t v___x_305_; uint8_t v___x_306_; 
v___x_304_ = lean_ptr_addr(v___x_289_);
v___x_305_ = lean_ptr_addr(v_tail_287_);
v___x_306_ = lean_usize_dec_eq(v___x_304_, v___x_305_);
v___y_291_ = v___x_306_;
goto v___jp_290_;
}
v___jp_290_:
{
if (v___y_291_ == 0)
{
lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_298_; 
v_isSharedCheck_298_ = !lean_is_exclusive(v_as_285_);
if (v_isSharedCheck_298_ == 0)
{
lean_object* v_unused_299_; lean_object* v_unused_300_; 
v_unused_299_ = lean_ctor_get(v_as_285_, 1);
lean_dec(v_unused_299_);
v_unused_300_ = lean_ctor_get(v_as_285_, 0);
lean_dec(v_unused_300_);
v___x_293_ = v_as_285_;
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
else
{
lean_dec(v_as_285_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_298_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_289_);
lean_ctor_set(v___x_293_, 0, v___x_288_);
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_297_; 
v_reuseFailAlloc_297_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_297_, 0, v___x_288_);
lean_ctor_set(v_reuseFailAlloc_297_, 1, v___x_289_);
v___x_296_ = v_reuseFailAlloc_297_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
return v___x_296_;
}
}
}
else
{
lean_dec(v___x_289_);
lean_dec(v___x_288_);
return v_as_285_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapMono___redArg(lean_object* v_as_307_, lean_object* v_f_308_){
_start:
{
lean_object* v___x_309_; 
v___x_309_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(v_f_308_, v_as_307_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_List_mapMono(lean_object* v_00_u03b1_310_, lean_object* v_as_311_, lean_object* v_f_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(v_f_312_, v_as_311_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0(lean_object* v_00_u03b1_314_, lean_object* v_f_315_, lean_object* v_as_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l___private_Init_Data_List_BasicAux_0__List_mapMonoMImp___at___00List_mapMono_spec__0___redArg(v_f_315_, v_as_316_);
return v___x_317_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20(void){
_start:
{
lean_object* v___x_374_; lean_object* v___x_375_; 
v___x_374_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__19));
v___x_375_ = l_String_toRawSubstring_x27(v___x_374_);
return v___x_375_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34(void){
_start:
{
lean_object* v___x_408_; lean_object* v___x_409_; 
v___x_408_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__33));
v___x_409_ = l_String_toRawSubstring_x27(v___x_408_);
return v___x_409_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48(void){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__47));
v___x_439_ = l_String_toRawSubstring_x27(v___x_438_);
return v___x_439_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56(void){
_start:
{
lean_object* v___x_455_; lean_object* v___x_456_; 
v___x_455_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__55));
v___x_456_ = l_String_toRawSubstring_x27(v___x_455_);
return v___x_456_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59(void){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Array_mkArray0(lean_box(0));
return v___x_460_;
}
}
static lean_object* _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77(void){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__76));
v___x_505_ = l_String_toRawSubstring_x27(v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1(lean_object* v_x_508_, lean_object* v_a_509_, lean_object* v_a_510_){
_start:
{
lean_object* v___x_511_; uint8_t v___x_512_; 
v___x_511_ = ((lean_object*)(l_List_tacticSizeOf__list__dec___closed__2));
v___x_512_ = l_Lean_Syntax_isOfKind(v_x_508_, v___x_511_);
if (v___x_512_ == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
v___x_513_ = lean_box(1);
v___x_514_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_514_, 0, v___x_513_);
lean_ctor_set(v___x_514_, 1, v_a_510_);
return v___x_514_;
}
else
{
lean_object* v_quotContext_515_; lean_object* v_currMacroScope_516_; lean_object* v_ref_517_; uint8_t v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_quotContext_515_ = lean_ctor_get(v_a_509_, 1);
v_currMacroScope_516_ = lean_ctor_get(v_a_509_, 2);
v_ref_517_ = lean_ctor_get(v_a_509_, 5);
v___x_518_ = 0;
v___x_519_ = l_Lean_SourceInfo_fromRef(v_ref_517_, v___x_518_);
v___x_520_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__3));
v___x_521_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__4));
lean_inc_n(v___x_519_, 61);
v___x_522_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_519_);
lean_ctor_set(v___x_522_, 1, v___x_520_);
v___x_523_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__6));
v___x_524_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__8));
v___x_525_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__9));
v___x_526_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_526_, 0, v___x_519_);
lean_ctor_set(v___x_526_, 1, v___x_525_);
v___x_527_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__11));
v___x_528_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__13));
v___x_529_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__15));
v___x_530_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__16));
v___x_531_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_531_, 0, v___x_519_);
lean_ctor_set(v___x_531_, 1, v___x_530_);
v___x_532_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__17));
v___x_533_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__18));
v___x_534_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_534_, 0, v___x_519_);
lean_ctor_set(v___x_534_, 1, v___x_532_);
v___x_535_ = lean_obj_once(&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20, &l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20_once, _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__20);
v___x_536_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__21));
lean_inc_n(v_currMacroScope_516_, 5);
lean_inc_n(v_quotContext_515_, 5);
v___x_537_ = l_Lean_addMacroScope(v_quotContext_515_, v___x_536_, v_currMacroScope_516_);
v___x_538_ = lean_box(0);
v___x_539_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__24));
v___x_540_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_540_, 0, v___x_519_);
lean_ctor_set(v___x_540_, 1, v___x_535_);
lean_ctor_set(v___x_540_, 2, v___x_537_);
lean_ctor_set(v___x_540_, 3, v___x_539_);
lean_inc_ref(v___x_540_);
lean_inc_ref(v___x_534_);
v___x_541_ = l_Lean_Syntax_node2(v___x_519_, v___x_533_, v___x_534_, v___x_540_);
v___x_542_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__25));
v___x_543_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_543_, 0, v___x_519_);
lean_ctor_set(v___x_543_, 1, v___x_542_);
v___x_544_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__26));
v___x_545_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__27));
v___x_546_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_546_, 0, v___x_519_);
lean_ctor_set(v___x_546_, 1, v___x_544_);
v___x_547_ = l_Lean_Syntax_node1(v___x_519_, v___x_545_, v___x_546_);
v___x_548_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__28));
v___x_549_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__29));
v___x_550_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_550_, 0, v___x_519_);
lean_ctor_set(v___x_550_, 1, v___x_548_);
v___x_551_ = l_Lean_Syntax_node1(v___x_519_, v___x_549_, v___x_550_);
lean_inc(v___x_547_);
lean_inc_ref(v___x_543_);
v___x_552_ = l_Lean_Syntax_node5(v___x_519_, v___x_523_, v___x_541_, v___x_543_, v___x_547_, v___x_543_, v___x_551_);
v___x_553_ = l_Lean_Syntax_node1(v___x_519_, v___x_528_, v___x_552_);
v___x_554_ = l_Lean_Syntax_node1(v___x_519_, v___x_527_, v___x_553_);
lean_inc_ref(v___x_531_);
v___x_555_ = l_Lean_Syntax_node2(v___x_519_, v___x_529_, v___x_531_, v___x_554_);
v___x_556_ = l_Lean_Syntax_node1(v___x_519_, v___x_523_, v___x_555_);
v___x_557_ = l_Lean_Syntax_node1(v___x_519_, v___x_528_, v___x_556_);
v___x_558_ = l_Lean_Syntax_node1(v___x_519_, v___x_527_, v___x_557_);
lean_inc_ref(v___x_526_);
v___x_559_ = l_Lean_Syntax_node2(v___x_519_, v___x_524_, v___x_526_, v___x_558_);
v___x_560_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__32));
v___x_561_ = lean_obj_once(&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34, &l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34_once, _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__34);
v___x_562_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__37));
v___x_563_ = l_Lean_addMacroScope(v_quotContext_515_, v___x_562_, v_currMacroScope_516_);
v___x_564_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__39));
v___x_565_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_565_, 0, v___x_519_);
lean_ctor_set(v___x_565_, 1, v___x_561_);
lean_ctor_set(v___x_565_, 2, v___x_563_);
lean_ctor_set(v___x_565_, 3, v___x_564_);
v___x_566_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__41));
v___x_567_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__43));
v___x_568_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__44));
v___x_569_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_569_, 0, v___x_519_);
lean_ctor_set(v___x_569_, 1, v___x_568_);
v___x_570_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__46));
v___x_571_ = lean_obj_once(&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48, &l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48_once, _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__48);
v___x_572_ = lean_box(0);
v___x_573_ = l_Lean_addMacroScope(v_quotContext_515_, v___x_572_, v_currMacroScope_516_);
v___x_574_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__51));
v___x_575_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_575_, 0, v___x_519_);
lean_ctor_set(v___x_575_, 1, v___x_571_);
lean_ctor_set(v___x_575_, 2, v___x_573_);
lean_ctor_set(v___x_575_, 3, v___x_574_);
v___x_576_ = l_Lean_Syntax_node1(v___x_519_, v___x_570_, v___x_575_);
v___x_577_ = l_Lean_Syntax_node2(v___x_519_, v___x_567_, v___x_569_, v___x_576_);
v___x_578_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__53));
v___x_579_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__54));
v___x_580_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_580_, 0, v___x_519_);
lean_ctor_set(v___x_580_, 1, v___x_579_);
v___x_581_ = lean_obj_once(&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56, &l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56_once, _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__56);
v___x_582_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__57));
v___x_583_ = l_Lean_addMacroScope(v_quotContext_515_, v___x_582_, v_currMacroScope_516_);
v___x_584_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_584_, 0, v___x_519_);
lean_ctor_set(v___x_584_, 1, v___x_581_);
lean_ctor_set(v___x_584_, 2, v___x_583_);
lean_ctor_set(v___x_584_, 3, v___x_538_);
lean_inc_ref(v___x_584_);
v___x_585_ = l_Lean_Syntax_node2(v___x_519_, v___x_578_, v___x_580_, v___x_584_);
v___x_586_ = l_Lean_Syntax_node1(v___x_519_, v___x_523_, v___x_585_);
v___x_587_ = l_Lean_Syntax_node2(v___x_519_, v___x_560_, v___x_540_, v___x_586_);
v___x_588_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__58));
v___x_589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_519_);
lean_ctor_set(v___x_589_, 1, v___x_588_);
v___x_590_ = l_Lean_Syntax_node3(v___x_519_, v___x_566_, v___x_577_, v___x_587_, v___x_589_);
v___x_591_ = l_Lean_Syntax_node1(v___x_519_, v___x_523_, v___x_590_);
v___x_592_ = l_Lean_Syntax_node2(v___x_519_, v___x_560_, v___x_565_, v___x_591_);
v___x_593_ = l_Lean_Syntax_node2(v___x_519_, v___x_533_, v___x_534_, v___x_592_);
v___x_594_ = lean_obj_once(&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59, &l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59_once, _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__59);
v___x_595_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_595_, 0, v___x_519_);
lean_ctor_set(v___x_595_, 1, v___x_523_);
lean_ctor_set(v___x_595_, 2, v___x_594_);
v___x_596_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__60));
v___x_597_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__61));
v___x_598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_519_);
lean_ctor_set(v___x_598_, 1, v___x_596_);
v___x_599_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__63));
v___x_600_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__65));
v___x_601_ = l_Lean_Syntax_node1(v___x_519_, v___x_600_, v___x_584_);
lean_inc_ref_n(v___x_595_, 6);
v___x_602_ = l_Lean_Syntax_node2(v___x_519_, v___x_599_, v___x_601_, v___x_595_);
v___x_603_ = l_Lean_Syntax_node1(v___x_519_, v___x_523_, v___x_602_);
v___x_604_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__66));
v___x_605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_519_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Lean_Syntax_node1(v___x_519_, v___x_523_, v___x_547_);
v___x_607_ = l_Lean_Syntax_node1(v___x_519_, v___x_528_, v___x_606_);
v___x_608_ = l_Lean_Syntax_node1(v___x_519_, v___x_527_, v___x_607_);
v___x_609_ = l_Lean_Syntax_node4(v___x_519_, v___x_597_, v___x_598_, v___x_603_, v___x_605_, v___x_608_);
v___x_610_ = l_Lean_Syntax_node3(v___x_519_, v___x_523_, v___x_593_, v___x_595_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node1(v___x_519_, v___x_528_, v___x_610_);
v___x_612_ = l_Lean_Syntax_node1(v___x_519_, v___x_527_, v___x_611_);
v___x_613_ = l_Lean_Syntax_node2(v___x_519_, v___x_529_, v___x_531_, v___x_612_);
v___x_614_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__67));
v___x_615_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__68));
v___x_616_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_519_);
lean_ctor_set(v___x_616_, 1, v___x_614_);
v___x_617_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__70));
v___x_618_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__72));
v___x_619_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__74));
v___x_620_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__75));
v___x_621_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_621_, 0, v___x_519_);
lean_ctor_set(v___x_621_, 1, v___x_620_);
v___x_622_ = lean_obj_once(&l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77, &l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77_once, _init_l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__77);
v___x_623_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___closed__78));
v___x_624_ = l_Lean_addMacroScope(v_quotContext_515_, v___x_623_, v_currMacroScope_516_);
v___x_625_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_625_, 0, v___x_519_);
lean_ctor_set(v___x_625_, 1, v___x_622_);
lean_ctor_set(v___x_625_, 2, v___x_624_);
lean_ctor_set(v___x_625_, 3, v___x_538_);
v___x_626_ = l_Lean_Syntax_node2(v___x_519_, v___x_619_, v___x_621_, v___x_625_);
v___x_627_ = l_Lean_Syntax_node1(v___x_519_, v___x_618_, v___x_626_);
v___x_628_ = l_Lean_Syntax_node1(v___x_519_, v___x_523_, v___x_627_);
v___x_629_ = l_Lean_Syntax_node1(v___x_519_, v___x_617_, v___x_628_);
v___x_630_ = l_Lean_Syntax_node6(v___x_519_, v___x_615_, v___x_616_, v___x_629_, v___x_595_, v___x_595_, v___x_595_, v___x_595_);
v___x_631_ = l_Lean_Syntax_node3(v___x_519_, v___x_523_, v___x_613_, v___x_595_, v___x_630_);
v___x_632_ = l_Lean_Syntax_node1(v___x_519_, v___x_528_, v___x_631_);
v___x_633_ = l_Lean_Syntax_node1(v___x_519_, v___x_527_, v___x_632_);
v___x_634_ = l_Lean_Syntax_node2(v___x_519_, v___x_524_, v___x_526_, v___x_633_);
v___x_635_ = l_Lean_Syntax_node2(v___x_519_, v___x_523_, v___x_559_, v___x_634_);
v___x_636_ = l_Lean_Syntax_node2(v___x_519_, v___x_521_, v___x_522_, v___x_635_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_a_510_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1___boxed(lean_object* v_x_638_, lean_object* v_a_639_, lean_object* v_a_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_List___aux__Init__Data__List__BasicAux______macroRules__List__tacticSizeOf__list__dec__1(v_x_638_, v_a_639_, v_a_640_);
lean_dec_ref(v_a_639_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1(lean_object* v_x_645_, lean_object* v_a_646_, lean_object* v_a_647_){
_start:
{
lean_object* v___x_648_; uint8_t v___x_649_; 
v___x_648_ = ((lean_object*)(l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___closed__1));
v___x_649_ = l_Lean_Syntax_isOfKind(v_x_645_, v___x_648_);
if (v___x_649_ == 0)
{
lean_object* v___x_650_; lean_object* v___x_651_; 
v___x_650_ = lean_box(1);
v___x_651_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_651_, 0, v___x_650_);
lean_ctor_set(v___x_651_, 1, v_a_647_);
return v___x_651_;
}
else
{
lean_object* v_ref_652_; uint8_t v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; 
v_ref_652_ = lean_ctor_get(v_a_646_, 5);
v___x_653_ = 0;
v___x_654_ = l_Lean_SourceInfo_fromRef(v_ref_652_, v___x_653_);
v___x_655_ = ((lean_object*)(l_List_tacticSizeOf__list__dec___closed__2));
v___x_656_ = ((lean_object*)(l_List_tacticSizeOf__list__dec___closed__3));
lean_inc(v___x_654_);
v___x_657_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_657_, 0, v___x_654_);
lean_ctor_set(v___x_657_, 1, v___x_656_);
v___x_658_ = l_Lean_Syntax_node1(v___x_654_, v___x_655_, v___x_657_);
v___x_659_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_658_);
lean_ctor_set(v___x_659_, 1, v_a_647_);
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1___boxed(lean_object* v_x_660_, lean_object* v_a_661_, lean_object* v_a_662_){
_start:
{
lean_object* v_res_663_; 
v_res_663_ = l_List___aux__Init__Data__List__BasicAux______macroRules__tacticDecreasing__trivial__1(v_x_660_, v_a_661_, v_a_662_);
lean_dec_ref(v_a_661_);
return v_res_663_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter___redArg(lean_object* v_x_664_, lean_object* v_x_665_, lean_object* v_h__1_666_, lean_object* v_h__2_667_){
_start:
{
lean_object* v_head_668_; lean_object* v_tail_669_; lean_object* v_zero_670_; uint8_t v_isZero_671_; 
v_head_668_ = lean_ctor_get(v_x_664_, 0);
lean_inc(v_head_668_);
v_tail_669_ = lean_ctor_get(v_x_664_, 1);
lean_inc(v_tail_669_);
lean_dec(v_x_664_);
v_zero_670_ = lean_unsigned_to_nat(0u);
v_isZero_671_ = lean_nat_dec_eq(v_x_665_, v_zero_670_);
if (v_isZero_671_ == 1)
{
lean_object* v___x_672_; 
lean_dec(v_h__2_667_);
v___x_672_ = lean_apply_3(v_h__1_666_, v_head_668_, v_tail_669_, lean_box(0));
return v___x_672_;
}
else
{
lean_object* v_one_673_; lean_object* v_n_674_; lean_object* v___x_675_; 
lean_dec(v_h__1_666_);
v_one_673_ = lean_unsigned_to_nat(1u);
v_n_674_ = lean_nat_sub(v_x_665_, v_one_673_);
v___x_675_ = lean_apply_4(v_h__2_667_, v_head_668_, v_tail_669_, v_n_674_, lean_box(0));
return v___x_675_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter___redArg___boxed(lean_object* v_x_676_, lean_object* v_x_677_, lean_object* v_h__1_678_, lean_object* v_h__2_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter___redArg(v_x_676_, v_x_677_, v_h__1_678_, v_h__2_679_);
lean_dec(v_x_677_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter(lean_object* v_00_u03b1_681_, lean_object* v_motive_682_, lean_object* v_x_683_, lean_object* v_x_684_, lean_object* v_h__1_685_, lean_object* v_h__2_686_){
_start:
{
lean_object* v_head_687_; lean_object* v_tail_688_; lean_object* v_zero_689_; uint8_t v_isZero_690_; 
v_head_687_ = lean_ctor_get(v_x_683_, 0);
lean_inc(v_head_687_);
v_tail_688_ = lean_ctor_get(v_x_683_, 1);
lean_inc(v_tail_688_);
lean_dec(v_x_683_);
v_zero_689_ = lean_unsigned_to_nat(0u);
v_isZero_690_ = lean_nat_dec_eq(v_x_684_, v_zero_689_);
if (v_isZero_690_ == 1)
{
lean_object* v___x_691_; 
lean_dec(v_h__2_686_);
v___x_691_ = lean_apply_3(v_h__1_685_, v_head_687_, v_tail_688_, lean_box(0));
return v___x_691_;
}
else
{
lean_object* v_one_692_; lean_object* v_n_693_; lean_object* v___x_694_; 
lean_dec(v_h__1_685_);
v_one_692_ = lean_unsigned_to_nat(1u);
v_n_693_ = lean_nat_sub(v_x_684_, v_one_692_);
v___x_694_ = lean_apply_4(v_h__2_686_, v_head_687_, v_tail_688_, v_n_693_, lean_box(0));
return v___x_694_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter___boxed(lean_object* v_00_u03b1_695_, lean_object* v_motive_696_, lean_object* v_x_697_, lean_object* v_x_698_, lean_object* v_h__1_699_, lean_object* v_h__2_700_){
_start:
{
lean_object* v_res_701_; 
v_res_701_ = l___private_Init_Data_List_BasicAux_0__List_get_match__1_splitter(v_00_u03b1_695_, v_motive_696_, v_x_697_, v_x_698_, v_h__1_699_, v_h__2_700_);
lean_dec(v_x_698_);
return v_res_701_;
}
}
lean_object* runtime_initialize_Init_GetElem(uint8_t builtin);
lean_object* runtime_initialize_Init_WFTactics(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Classical(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_List_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_List_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_GetElem(uint8_t builtin);
lean_object* initialize_Init_WFTactics(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Classical(uint8_t builtin);
lean_object* initialize_Init_Data_Array_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Linear(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_List_BasicAux(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_GetElem(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_WFTactics(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Classical(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Array_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Linear(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_List_BasicAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_List_BasicAux(builtin);
}
#ifdef __cplusplus
}
#endif
