// Lean compiler output
// Module: Init.Data.SInt.Lemmas
// Imports: import all Init.Data.Nat.Bitwise.Basic public import Init.Data.SInt.Basic import all Init.Data.SInt.Basic import all Init.Data.BitVec.Basic import all Init.Data.UInt.Basic public import Init.Data.BitVec.Lemmas public import Init.Data.Int.Order import Init.ByCases import Init.Data.BitVec.Bitblast import Init.Data.BitVec.Bootstrap import Init.Data.Int.DivMod.Lemmas import Init.Data.Int.LemmasAux import Init.Data.Int.Pow import Init.Data.UInt.Lemmas import Init.System.Platform
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* lean_mk_syntax_ident(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_commandDeclare__int__theorems_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "commandDeclare_int_theorems__"};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__0 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__0_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 239, 52, 0, 96, 209, 11, 62)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__1 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__1_value;
static const lean_string_object l_commandDeclare__int__theorems_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__2 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__2_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__3 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__3_value;
static const lean_string_object l_commandDeclare__int__theorems_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "declare_int_theorems"};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__4 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__4_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__4_value)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__5 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__5_value;
static const lean_string_object l_commandDeclare__int__theorems_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__6 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__6_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__7 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__7_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__7_value)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__8 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__8_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__3_value),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__5_value),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__8_value)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__9 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__9_value;
static const lean_string_object l_commandDeclare__int__theorems_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__10 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__10_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__11 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__11_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__11_value),((lean_object*)(((size_t)(1023) << 1) | 1))}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__12 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__12_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__3_value),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__9_value),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__12_value)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__13 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__13_value;
static const lean_ctor_object l_commandDeclare__int__theorems_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_commandDeclare__int__theorems_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_commandDeclare__int__theorems_____00__closed__13_value)}};
static const lean_object* l_commandDeclare__int__theorems_____00__closed__14 = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__14_value;
LEAN_EXPORT const lean_object* l_commandDeclare__int__theorems____ = (const lean_object*)&l_commandDeclare__int__theorems_____00__closed__14_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__3 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__3_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(254, 132, 206, 38, 133, 164, 145, 139)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__4 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__4_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__5 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__5_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__6 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__6_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__7;
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ISize"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(110, 52, 237, 35, 121, 142, 86, 222)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(84, 17, 124, 142, 243, 161, 231, 243)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(238, 116, 137, 74, 194, 103, 58, 54)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__11_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "le_iff_toBitVec_sle"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(224, 98, 156, 243, 176, 144, 13, 23)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__19_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_↔_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(220, 124, 41, 198, 228, 162, 237, 244)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≤_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__34_value),LEAN_SCALAR_PTR_LITERAL(111, 3, 61, 112, 38, 138, 106, 121)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≤"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "↔"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__38_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "a.toBitVec.sle"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "sle"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__43_value),LEAN_SCALAR_PTR_LITERAL(229, 214, 5, 189, 16, 107, 180, 166)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "b.toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(6, 235, 47, 200, 31, 68, 206, 165)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__48_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Iff.rfl"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Iff"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(197, 85, 193, 93, 217, 248, 54, 49)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__56_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__57_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "lt_iff_toBitVec_slt"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59_value),LEAN_SCALAR_PTR_LITERAL(7, 125, 217, 200, 188, 3, 210, 9)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_<_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__62_value),LEAN_SCALAR_PTR_LITERAL(192, 242, 106, 74, 199, 131, 133, 95)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "<"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "a.toBitVec.slt"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "slt"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(216, 157, 226, 89, 27, 108, 130, 144)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_inj"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(89, 245, 252, 212, 180, 248, 61, 129)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_=_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__72_value),LEAN_SCALAR_PTR_LITERAL(167, 251, 107, 62, 223, 239, 203, 78)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "a.toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__78_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec.inj"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "inj"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(130, 88, 94, 113, 144, 209, 170, 121)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__83_value),LEAN_SCALAR_PTR_LITERAL(3, 10, 226, 202, 47, 118, 47, 253)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__88_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__91_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "subst"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__95_value),LEAN_SCALAR_PTR_LITERAL(169, 13, 108, 115, 152, 155, 29, 181)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "cdot"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__97_value),LEAN_SCALAR_PTR_LITERAL(215, 94, 65, 66, 49, 100, 151, 85)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 1, .m_data = "·"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "▸"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "ofBitVec_inj"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105_value),LEAN_SCALAR_PTR_LITERAL(221, 185, 57, 244, 153, 117, 189, 185)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "BitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ofBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111_value),LEAN_SCALAR_PTR_LITERAL(109, 13, 70, 115, 31, 141, 156, 173)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__114_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__118_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__120_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "tactic_<;>_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__122_value),LEAN_SCALAR_PTR_LITERAL(31, 118, 44, 159, 195, 11, 47, 176)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "apply"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124_value),LEAN_SCALAR_PTR_LITERAL(202, 125, 237, 78, 179, 140, 218, 80)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Iff.intro"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "intro"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__53_value),LEAN_SCALAR_PTR_LITERAL(19, 54, 203, 28, 77, 25, 163, 137)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__128_value),LEAN_SCALAR_PTR_LITERAL(176, 155, 85, 49, 105, 137, 67, 168)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<;>"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__86_value),LEAN_SCALAR_PTR_LITERAL(117, 253, 122, 28, 77, 248, 149, 120)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "rintro"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132_value),LEAN_SCALAR_PTR_LITERAL(170, 254, 242, 235, 94, 162, 254, 146)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rintroPat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "one"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__134_value),LEAN_SCALAR_PTR_LITERAL(120, 93, 179, 129, 121, 199, 215, 253)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value_aux_3),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135_value),LEAN_SCALAR_PTR_LITERAL(40, 214, 202, 122, 59, 249, 35, 61)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "rcasesPat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__137_value),LEAN_SCALAR_PTR_LITERAL(162, 181, 165, 225, 136, 177, 169, 19)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value_aux_3),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__135_value),LEAN_SCALAR_PTR_LITERAL(186, 152, 172, 228, 11, 240, 156, 168)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "h"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139_value),LEAN_SCALAR_PTR_LITERAL(176, 181, 207, 77, 197, 87, 68, 121)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ";"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "cases"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143_value),LEAN_SCALAR_PTR_LITERAL(197, 49, 98, 208, 150, 151, 163, 74)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "elimTarget"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__145_value),LEAN_SCALAR_PTR_LITERAL(136, 63, 46, 91, 99, 29, 205, 171)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticRfl"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__147_value),LEAN_SCALAR_PTR_LITERAL(201, 188, 173, 198, 169, 252, 183, 45)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_iff_ofBitVec_eq"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149_value),LEAN_SCALAR_PTR_LITERAL(204, 182, 120, 87, 208, 6, 5, 44)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "ofBitVec_inj.symm"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "symm"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105_value),LEAN_SCALAR_PTR_LITERAL(221, 185, 57, 244, 153, 117, 189, 185)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154_value),LEAN_SCALAR_PTR_LITERAL(22, 209, 90, 41, 119, 255, 106, 147)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ne_iff_ofBitVec_ne"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156_value),LEAN_SCALAR_PTR_LITERAL(177, 124, 199, 96, 100, 166, 4, 189)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 7, .m_data = "term_≠_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__159_value),LEAN_SCALAR_PTR_LITERAL(120, 22, 203, 44, 60, 124, 87, 95)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "≠"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__164_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__167_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "eq_iff_toBitVec_eq"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170_value),LEAN_SCALAR_PTR_LITERAL(204, 196, 118, 25, 1, 164, 248, 180)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "toBitVec_inj.symm"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69_value),LEAN_SCALAR_PTR_LITERAL(89, 245, 252, 212, 180, 248, 61, 129)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__154_value),LEAN_SCALAR_PTR_LITERAL(66, 49, 95, 225, 222, 165, 83, 187)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "ne_iff_toBitVec_ne"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176_value),LEAN_SCALAR_PTR_LITERAL(166, 231, 164, 53, 49, 215, 3, 212)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__179_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Decidable.not_iff_not"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "Decidable"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "not_iff_not"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__183_value),LEAN_SCALAR_PTR_LITERAL(87, 187, 205, 215, 218, 218, 68, 60)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__184_value),LEAN_SCALAR_PTR_LITERAL(72, 176, 176, 135, 176, 196, 69, 82)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "fieldIdx"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__187_value),LEAN_SCALAR_PTR_LITERAL(243, 141, 165, 29, 238, 211, 61, 163)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__190_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__193_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__195_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162_value),LEAN_SCALAR_PTR_LITERAL(167, 64, 108, 103, 216, 152, 33, 14)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "toBitVec_ofNat'"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199_value),LEAN_SCALAR_PTR_LITERAL(16, 207, 149, 240, 11, 231, 225, 30)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "n"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202_value),LEAN_SCALAR_PTR_LITERAL(85, 67, 188, 79, 172, 243, 130, 138)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Nat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205_value),LEAN_SCALAR_PTR_LITERAL(155, 221, 223, 104, 58, 13, 204, 158)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(130, 88, 94, 113, 144, 209, 170, 121)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ofNat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210_value),LEAN_SCALAR_PTR_LITERAL(190, 214, 116, 82, 37, 136, 167, 32)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "BitVec.ofNat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108_value),LEAN_SCALAR_PTR_LITERAL(108, 178, 58, 132, 143, 189, 222, 74)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210_value),LEAN_SCALAR_PTR_LITERAL(101, 105, 192, 171, 214, 131, 43, 105)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "hole"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__216_value),LEAN_SCALAR_PTR_LITERAL(135, 134, 219, 115, 97, 130, 74, 55)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toBitVec_ofNat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219_value),LEAN_SCALAR_PTR_LITERAL(48, 40, 156, 211, 194, 107, 54, 55)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "noindex"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__222_value),LEAN_SCALAR_PTR_LITERAL(0, 143, 63, 201, 38, 174, 32, 127)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "no_index"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "OfNat.ofNat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "OfNat"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__227_value),LEAN_SCALAR_PTR_LITERAL(135, 241, 166, 108, 243, 216, 193, 244)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210_value),LEAN_SCALAR_PTR_LITERAL(2, 108, 58, 34, 100, 49, 50, 216)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "protected"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229_value),LEAN_SCALAR_PTR_LITERAL(33, 80, 123, 180, 50, 194, 119, 199)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_add"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231_value),LEAN_SCALAR_PTR_LITERAL(54, 148, 186, 80, 123, 86, 181, 153)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_+_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__234_value),LEAN_SCALAR_PTR_LITERAL(57, 160, 89, 154, 247, 230, 95, 119)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "+"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_sub"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237_value),LEAN_SCALAR_PTR_LITERAL(11, 9, 230, 95, 126, 235, 121, 31)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_-_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__240_value),LEAN_SCALAR_PTR_LITERAL(92, 98, 183, 241, 65, 154, 192, 109)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_mul"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243_value),LEAN_SCALAR_PTR_LITERAL(78, 183, 160, 166, 105, 95, 150, 56)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_*_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__246_value),LEAN_SCALAR_PTR_LITERAL(166, 30, 182, 203, 156, 152, 64, 201)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "*"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_div"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249_value),LEAN_SCALAR_PTR_LITERAL(237, 243, 123, 229, 238, 121, 75, 82)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_/_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__252_value),LEAN_SCALAR_PTR_LITERAL(210, 175, 43, 55, 191, 201, 132, 176)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "/"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "a.toBitVec.sdiv"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "sdiv"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__257_value),LEAN_SCALAR_PTR_LITERAL(12, 106, 63, 230, 239, 115, 94, 188)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_mod"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259_value),LEAN_SCALAR_PTR_LITERAL(128, 222, 30, 228, 150, 168, 215, 197)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_%_"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__262_value),LEAN_SCALAR_PTR_LITERAL(223, 214, 140, 105, 32, 178, 232, 218)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "%"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "a.toBitVec.srem"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "srem"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__267_value),LEAN_SCALAR_PTR_LITERAL(106, 212, 48, 197, 204, 217, 39, 75)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268_value;
static const lean_array_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*10, .m_other = 0, .m_tag = 246}, .m_size = 10, .m_capacity = 10, .m_data = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15_value),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61_value),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172_value),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178_value),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221_value),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233_value),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239_value),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245_value),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251_value),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261_value)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273_value;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_value_aux_0),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_value_aux_1),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__197_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_value_aux_2),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__273_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274_value;
static const lean_string_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "int_toBitVec"};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275_value;
static lean_once_cell_t l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276;
static const lean_ctor_object l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275_value),LEAN_SCALAR_PTR_LITERAL(86, 82, 181, 235, 29, 69, 188, 18)}};
static const lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277 = (const lean_object*)&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__0(lean_object* v_____do__lift_34_, lean_object* v___y_35_, lean_object* v___y_36_){
_start:
{
uint8_t v___x_37_; lean_object* v___x_38_; lean_object* v___x_39_; 
v___x_37_ = 0;
v___x_38_ = l_Lean_SourceInfo_fromRef(v_____do__lift_34_, v___x_37_);
v___x_39_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_39_, 0, v___x_38_);
lean_ctor_set(v___x_39_, 1, v___y_36_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__0___boxed(lean_object* v_____do__lift_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__0(v_____do__lift_40_, v___y_41_, v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v_____do__lift_40_);
return v_res_43_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__7(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Array_mkArray0(lean_box(0));
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1(lean_object* v___f_57_, lean_object* v_typeName_58_, lean_object* v_____r_59_, lean_object* v_cmds_60_, lean_object* v___y_61_, lean_object* v___y_62_){
_start:
{
lean_object* v_ref_63_; lean_object* v___x_64_; 
v_ref_63_ = lean_ctor_get(v___y_61_, 5);
lean_inc_ref(v___y_61_);
lean_inc(v_ref_63_);
v___x_64_ = lean_apply_3(v___f_57_, v_ref_63_, v___y_61_, v___y_62_);
if (lean_obj_tag(v___x_64_) == 0)
{
lean_object* v_a_65_; lean_object* v_a_66_; lean_object* v___x_68_; uint8_t v_isShared_69_; uint8_t v_isSharedCheck_84_; 
v_a_65_ = lean_ctor_get(v___x_64_, 0);
v_a_66_ = lean_ctor_get(v___x_64_, 1);
v_isSharedCheck_84_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_84_ == 0)
{
v___x_68_ = v___x_64_;
v_isShared_69_ = v_isSharedCheck_84_;
goto v_resetjp_67_;
}
else
{
lean_inc(v_a_66_);
lean_inc(v_a_65_);
lean_dec(v___x_64_);
v___x_68_ = lean_box(0);
v_isShared_69_ = v_isSharedCheck_84_;
goto v_resetjp_67_;
}
v_resetjp_67_:
{
lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_82_; 
v___x_70_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__3));
v___x_71_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__4));
lean_inc_n(v_a_65_, 3);
v___x_72_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_72_, 0, v_a_65_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
v___x_73_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__6));
v___x_74_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__7, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__7_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__7);
v___x_75_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_75_, 0, v_a_65_);
lean_ctor_set(v___x_75_, 1, v___x_73_);
lean_ctor_set(v___x_75_, 2, v___x_74_);
v___x_76_ = l_Lean_Syntax_node2(v_a_65_, v___x_73_, v_typeName_58_, v___x_75_);
v___x_77_ = l_Lean_Syntax_node2(v_a_65_, v___x_71_, v___x_72_, v___x_76_);
v___x_78_ = lean_array_push(v_cmds_60_, v___x_77_);
v___x_79_ = lean_box(2);
v___x_80_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_73_);
lean_ctor_set(v___x_80_, 2, v___x_78_);
if (v_isShared_69_ == 0)
{
lean_ctor_set(v___x_68_, 0, v___x_80_);
v___x_82_ = v___x_68_;
goto v_reusejp_81_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v___x_80_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v_a_66_);
v___x_82_ = v_reuseFailAlloc_83_;
goto v_reusejp_81_;
}
v_reusejp_81_:
{
return v___x_82_;
}
}
}
else
{
lean_object* v_a_85_; lean_object* v_a_86_; lean_object* v___x_88_; uint8_t v_isShared_89_; uint8_t v_isSharedCheck_93_; 
lean_dec_ref(v_cmds_60_);
lean_dec(v_typeName_58_);
v_a_85_ = lean_ctor_get(v___x_64_, 0);
v_a_86_ = lean_ctor_get(v___x_64_, 1);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_64_);
if (v_isSharedCheck_93_ == 0)
{
v___x_88_ = v___x_64_;
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
else
{
lean_inc(v_a_86_);
lean_inc(v_a_85_);
lean_dec(v___x_64_);
v___x_88_ = lean_box(0);
v_isShared_89_ = v_isSharedCheck_93_;
goto v_resetjp_87_;
}
v_resetjp_87_:
{
lean_object* v___x_91_; 
if (v_isShared_89_ == 0)
{
v___x_91_ = v___x_88_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v_a_85_);
lean_ctor_set(v_reuseFailAlloc_92_, 1, v_a_86_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___boxed(lean_object* v___f_94_, lean_object* v_typeName_95_, lean_object* v_____r_96_, lean_object* v_cmds_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1(v___f_94_, v_typeName_95_, v_____r_96_, v_cmds_97_, v___y_98_, v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1_spec__0(lean_object* v___x_101_, size_t v_sz_102_, size_t v_i_103_, lean_object* v_bs_104_){
_start:
{
uint8_t v___x_105_; 
v___x_105_ = lean_usize_dec_lt(v_i_103_, v_sz_102_);
if (v___x_105_ == 0)
{
lean_dec(v___x_101_);
return v_bs_104_;
}
else
{
lean_object* v_v_106_; lean_object* v___x_107_; lean_object* v_bs_x27_108_; lean_object* v___x_109_; lean_object* v___x_110_; size_t v___x_111_; size_t v___x_112_; lean_object* v___x_113_; 
v_v_106_ = lean_array_uget(v_bs_104_, v_i_103_);
v___x_107_ = lean_unsigned_to_nat(0u);
v_bs_x27_108_ = lean_array_uset(v_bs_104_, v_i_103_, v___x_107_);
lean_inc(v___x_101_);
v___x_109_ = l_Lean_Name_append(v___x_101_, v_v_106_);
v___x_110_ = lean_mk_syntax_ident(v___x_109_);
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_add(v_i_103_, v___x_111_);
v___x_113_ = lean_array_uset(v_bs_x27_108_, v_i_103_, v___x_110_);
v_i_103_ = v___x_112_;
v_bs_104_ = v___x_113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1_spec__0___boxed(lean_object* v___x_115_, lean_object* v_sz_116_, lean_object* v_i_117_, lean_object* v_bs_118_){
_start:
{
size_t v_sz_boxed_119_; size_t v_i_boxed_120_; lean_object* v_res_121_; 
v_sz_boxed_119_ = lean_unbox_usize(v_sz_116_);
lean_dec(v_sz_116_);
v_i_boxed_120_ = lean_unbox_usize(v_i_117_);
lean_dec(v_i_117_);
v_res_121_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1_spec__0(v___x_115_, v_sz_boxed_119_, v_i_boxed_120_, v_bs_118_);
return v_res_121_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__13));
v___x_158_ = l_String_toRawSubstring_x27(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__22));
v___x_177_ = l_String_toRawSubstring_x27(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26(void){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__25));
v___x_182_ = l_String_toRawSubstring_x27(v___x_181_);
return v___x_182_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41(void){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__40));
v___x_209_ = l_String_toRawSubstring_x27(v___x_208_);
return v___x_209_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46(void){
_start:
{
lean_object* v___x_217_; lean_object* v___x_218_; 
v___x_217_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__45));
v___x_218_ = l_String_toRawSubstring_x27(v___x_217_);
return v___x_218_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52(void){
_start:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_230_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__51));
v___x_231_ = l_String_toRawSubstring_x27(v___x_230_);
return v___x_231_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60(void){
_start:
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__59));
v___x_246_ = l_String_toRawSubstring_x27(v___x_245_);
return v___x_246_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__65));
v___x_255_ = l_String_toRawSubstring_x27(v___x_254_);
return v___x_255_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70(void){
_start:
{
lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_262_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__69));
v___x_263_ = l_String_toRawSubstring_x27(v___x_262_);
return v___x_263_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75(void){
_start:
{
lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_270_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__74));
v___x_271_ = l_String_toRawSubstring_x27(v___x_270_);
return v___x_271_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82(void){
_start:
{
lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_284_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__81));
v___x_285_ = l_String_toRawSubstring_x27(v___x_284_);
return v___x_285_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__93));
v___x_309_ = l_String_toRawSubstring_x27(v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101(void){
_start:
{
lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_324_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54));
v___x_325_ = l_String_toRawSubstring_x27(v___x_324_);
return v___x_325_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106(void){
_start:
{
lean_object* v___x_331_; lean_object* v___x_332_; 
v___x_331_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__105));
v___x_332_ = l_String_toRawSubstring_x27(v___x_331_);
return v___x_332_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109(void){
_start:
{
lean_object* v___x_336_; lean_object* v___x_337_; 
v___x_336_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__108));
v___x_337_ = l_String_toRawSubstring_x27(v___x_336_);
return v___x_337_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112(void){
_start:
{
lean_object* v___x_341_; lean_object* v___x_342_; 
v___x_341_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__111));
v___x_342_ = l_String_toRawSubstring_x27(v___x_341_);
return v___x_342_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127(void){
_start:
{
lean_object* v___x_378_; lean_object* v___x_379_; 
v___x_378_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__126));
v___x_379_ = l_String_toRawSubstring_x27(v___x_378_);
return v___x_379_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140(void){
_start:
{
lean_object* v___x_412_; lean_object* v___x_413_; 
v___x_412_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__139));
v___x_413_ = l_String_toRawSubstring_x27(v___x_412_);
return v___x_413_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150(void){
_start:
{
lean_object* v___x_436_; lean_object* v___x_437_; 
v___x_436_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__149));
v___x_437_ = l_String_toRawSubstring_x27(v___x_436_);
return v___x_437_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153(void){
_start:
{
lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_441_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__152));
v___x_442_ = l_String_toRawSubstring_x27(v___x_441_);
return v___x_442_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157(void){
_start:
{
lean_object* v___x_448_; lean_object* v___x_449_; 
v___x_448_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__156));
v___x_449_ = l_String_toRawSubstring_x27(v___x_448_);
return v___x_449_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171(void){
_start:
{
lean_object* v___x_477_; lean_object* v___x_478_; 
v___x_477_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__170));
v___x_478_ = l_String_toRawSubstring_x27(v___x_477_);
return v___x_478_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174(void){
_start:
{
lean_object* v___x_482_; lean_object* v___x_483_; 
v___x_482_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__173));
v___x_483_ = l_String_toRawSubstring_x27(v___x_482_);
return v___x_483_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177(void){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__176));
v___x_489_ = l_String_toRawSubstring_x27(v___x_488_);
return v___x_489_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182(void){
_start:
{
lean_object* v___x_499_; lean_object* v___x_500_; 
v___x_499_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__181));
v___x_500_ = l_String_toRawSubstring_x27(v___x_499_);
return v___x_500_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200(void){
_start:
{
lean_object* v___x_537_; lean_object* v___x_538_; 
v___x_537_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__199));
v___x_538_ = l_String_toRawSubstring_x27(v___x_537_);
return v___x_538_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203(void){
_start:
{
lean_object* v___x_542_; lean_object* v___x_543_; 
v___x_542_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__202));
v___x_543_ = l_String_toRawSubstring_x27(v___x_542_);
return v___x_543_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__205));
v___x_548_ = l_String_toRawSubstring_x27(v___x_547_);
return v___x_548_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208(void){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__42));
v___x_552_ = l_String_toRawSubstring_x27(v___x_551_);
return v___x_552_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211(void){
_start:
{
lean_object* v___x_556_; lean_object* v___x_557_; 
v___x_556_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__210));
v___x_557_ = l_String_toRawSubstring_x27(v___x_556_);
return v___x_557_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214(void){
_start:
{
lean_object* v___x_561_; lean_object* v___x_562_; 
v___x_561_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__213));
v___x_562_ = l_String_toRawSubstring_x27(v___x_561_);
return v___x_562_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220(void){
_start:
{
lean_object* v___x_574_; lean_object* v___x_575_; 
v___x_574_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__219));
v___x_575_ = l_String_toRawSubstring_x27(v___x_574_);
return v___x_575_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226(void){
_start:
{
lean_object* v___x_586_; lean_object* v___x_587_; 
v___x_586_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__225));
v___x_587_ = l_String_toRawSubstring_x27(v___x_586_);
return v___x_587_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232(void){
_start:
{
lean_object* v___x_599_; lean_object* v___x_600_; 
v___x_599_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__231));
v___x_600_ = l_String_toRawSubstring_x27(v___x_599_);
return v___x_600_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238(void){
_start:
{
lean_object* v___x_608_; lean_object* v___x_609_; 
v___x_608_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__237));
v___x_609_ = l_String_toRawSubstring_x27(v___x_608_);
return v___x_609_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244(void){
_start:
{
lean_object* v___x_617_; lean_object* v___x_618_; 
v___x_617_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__243));
v___x_618_ = l_String_toRawSubstring_x27(v___x_617_);
return v___x_618_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250(void){
_start:
{
lean_object* v___x_626_; lean_object* v___x_627_; 
v___x_626_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__249));
v___x_627_ = l_String_toRawSubstring_x27(v___x_626_);
return v___x_627_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256(void){
_start:
{
lean_object* v___x_635_; lean_object* v___x_636_; 
v___x_635_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__255));
v___x_636_ = l_String_toRawSubstring_x27(v___x_635_);
return v___x_636_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260(void){
_start:
{
lean_object* v___x_643_; lean_object* v___x_644_; 
v___x_643_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__259));
v___x_644_ = l_String_toRawSubstring_x27(v___x_643_);
return v___x_644_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266(void){
_start:
{
lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_652_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__265));
v___x_653_ = l_String_toRawSubstring_x27(v___x_652_);
return v___x_653_;
}
}
static size_t _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270(void){
_start:
{
lean_object* v___x_681_; size_t v_sz_682_; 
v___x_681_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269));
v_sz_682_ = lean_array_size(v___x_681_);
return v_sz_682_;
}
}
static lean_object* _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__275));
v___x_697_ = l_String_toRawSubstring_x27(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1(lean_object* v_x_700_, lean_object* v_a_701_, lean_object* v_a_702_){
_start:
{
lean_object* v___y_704_; lean_object* v___x_723_; uint8_t v___x_724_; 
v___x_723_ = ((lean_object*)(l_commandDeclare__int__theorems_____00__closed__1));
lean_inc(v_x_700_);
v___x_724_ = l_Lean_Syntax_isOfKind(v_x_700_, v___x_723_);
if (v___x_724_ == 0)
{
lean_object* v___x_725_; lean_object* v___x_726_; 
lean_dec(v_x_700_);
v___x_725_ = lean_box(1);
v___x_726_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_726_, 0, v___x_725_);
lean_ctor_set(v___x_726_, 1, v_a_702_);
return v___x_726_;
}
else
{
lean_object* v_ref_727_; lean_object* v___f_728_; lean_object* v___x_729_; lean_object* v_typeName_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; uint8_t v_isISize_735_; uint8_t v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; lean_object* v___x_879_; lean_object* v___x_880_; lean_object* v___x_881_; lean_object* v___x_882_; lean_object* v___x_883_; lean_object* v___x_884_; lean_object* v___x_885_; lean_object* v___x_886_; lean_object* v___x_887_; lean_object* v___x_888_; lean_object* v___x_889_; lean_object* v___x_890_; lean_object* v___x_891_; lean_object* v___x_892_; lean_object* v___x_893_; lean_object* v___x_894_; lean_object* v___x_895_; lean_object* v___x_896_; lean_object* v___x_897_; lean_object* v___x_898_; lean_object* v___x_899_; lean_object* v___x_900_; lean_object* v___x_901_; lean_object* v___x_902_; lean_object* v___x_903_; lean_object* v___x_904_; lean_object* v___x_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v___x_910_; lean_object* v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; lean_object* v___x_988_; lean_object* v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; lean_object* v___x_1013_; lean_object* v___x_1014_; lean_object* v___x_1015_; lean_object* v___x_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; lean_object* v___x_1019_; lean_object* v___x_1020_; lean_object* v___x_1021_; lean_object* v___x_1022_; lean_object* v___x_1023_; lean_object* v___x_1024_; lean_object* v___x_1025_; lean_object* v___x_1026_; lean_object* v___x_1027_; lean_object* v___x_1028_; lean_object* v___x_1029_; lean_object* v___x_1030_; lean_object* v___x_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; lean_object* v___x_1034_; lean_object* v___x_1035_; lean_object* v___x_1036_; lean_object* v___x_1037_; lean_object* v___x_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; lean_object* v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; lean_object* v___x_1069_; lean_object* v___x_1070_; lean_object* v___x_1071_; lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; lean_object* v___x_1100_; lean_object* v___x_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; lean_object* v___x_1108_; lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; lean_object* v___x_1112_; lean_object* v___x_1113_; lean_object* v___x_1114_; lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v___x_1123_; lean_object* v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; lean_object* v___x_1131_; lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; lean_object* v___x_1135_; lean_object* v___x_1136_; lean_object* v___x_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; lean_object* v___x_1146_; lean_object* v___x_1147_; lean_object* v___x_1148_; lean_object* v___x_1149_; lean_object* v___x_1150_; lean_object* v___x_1151_; lean_object* v___x_1152_; lean_object* v___x_1153_; lean_object* v___x_1154_; lean_object* v___x_1155_; lean_object* v___x_1156_; lean_object* v___x_1157_; lean_object* v___x_1158_; lean_object* v___x_1159_; lean_object* v___x_1160_; lean_object* v___x_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; lean_object* v___x_1164_; lean_object* v___x_1165_; lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; lean_object* v___x_1172_; lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; lean_object* v___x_1176_; lean_object* v___x_1177_; lean_object* v___x_1178_; lean_object* v___x_1179_; lean_object* v___x_1180_; lean_object* v___x_1181_; lean_object* v___x_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; lean_object* v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; lean_object* v___x_1207_; lean_object* v___x_1208_; lean_object* v___x_1209_; lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; lean_object* v___x_1213_; lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; 
v_ref_727_ = lean_ctor_get(v_a_701_, 5);
v___f_728_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__0));
v___x_729_ = lean_unsigned_to_nat(1u);
v_typeName_730_ = l_Lean_Syntax_getArg(v_x_700_, v___x_729_);
v___x_731_ = lean_unsigned_to_nat(2u);
v___x_732_ = l_Lean_Syntax_getArg(v_x_700_, v___x_731_);
lean_dec(v_x_700_);
v___x_733_ = l_Lean_TSyntax_getId(v_typeName_730_);
v___x_734_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__2));
v_isISize_735_ = lean_name_eq(v___x_733_, v___x_734_);
v___x_736_ = 0;
v___x_737_ = l_Lean_SourceInfo_fromRef(v_ref_727_, v___x_736_);
v___x_738_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__6));
v___x_739_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__3));
v___x_740_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__4));
lean_inc_n(v___x_737_, 292);
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_737_);
lean_ctor_set(v___x_741_, 1, v___x_739_);
lean_inc_n(v_typeName_730_, 2);
v___x_742_ = l_Lean_Syntax_node2(v___x_737_, v___x_740_, v___x_741_, v_typeName_730_);
v___x_743_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__6));
v___x_744_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__8));
v___x_745_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__7, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__7_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1___closed__7);
v___x_746_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_746_, 0, v___x_737_);
lean_ctor_set(v___x_746_, 1, v___x_738_);
lean_ctor_set(v___x_746_, 2, v___x_745_);
lean_inc_ref_n(v___x_746_, 56);
v___x_747_ = l_Lean_Syntax_node7(v___x_737_, v___x_744_, v___x_746_, v___x_746_, v___x_746_, v___x_746_, v___x_746_, v___x_746_, v___x_746_);
v___x_748_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__9));
v___x_749_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__10));
v___x_750_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_737_);
lean_ctor_set(v___x_750_, 1, v___x_748_);
v___x_751_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__12));
v___x_752_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__14);
v___x_753_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__15));
v___x_754_ = lean_box(0);
v___x_755_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_755_, 0, v___x_737_);
lean_ctor_set(v___x_755_, 1, v___x_752_);
lean_ctor_set(v___x_755_, 2, v___x_753_);
lean_ctor_set(v___x_755_, 3, v___x_754_);
v___x_756_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_755_, v___x_746_);
v___x_757_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__17));
v___x_758_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__20));
v___x_759_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__21));
v___x_760_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_760_, 0, v___x_737_);
lean_ctor_set(v___x_760_, 1, v___x_759_);
v___x_761_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__23);
v___x_762_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__24));
v___x_763_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_763_, 0, v___x_737_);
lean_ctor_set(v___x_763_, 1, v___x_761_);
lean_ctor_set(v___x_763_, 2, v___x_762_);
lean_ctor_set(v___x_763_, 3, v___x_754_);
v___x_764_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__26);
v___x_765_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__27));
v___x_766_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_766_, 0, v___x_737_);
lean_ctor_set(v___x_766_, 1, v___x_764_);
lean_ctor_set(v___x_766_, 2, v___x_765_);
lean_ctor_set(v___x_766_, 3, v___x_754_);
lean_inc_ref_n(v___x_766_, 10);
lean_inc_ref_n(v___x_763_, 10);
v___x_767_ = l_Lean_Syntax_node2(v___x_737_, v___x_738_, v___x_763_, v___x_766_);
v___x_768_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__28));
v___x_769_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_769_, 0, v___x_737_);
lean_ctor_set(v___x_769_, 1, v___x_768_);
lean_inc_ref_n(v___x_769_, 17);
v___x_770_ = l_Lean_Syntax_node2(v___x_737_, v___x_738_, v___x_769_, v_typeName_730_);
v___x_771_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__29));
v___x_772_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_737_);
lean_ctor_set(v___x_772_, 1, v___x_771_);
lean_inc_ref_n(v___x_772_, 2);
lean_inc(v___x_767_);
lean_inc_ref_n(v___x_760_, 2);
v___x_773_ = l_Lean_Syntax_node4(v___x_737_, v___x_758_, v___x_760_, v___x_767_, v___x_770_, v___x_772_);
v___x_774_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_773_);
v___x_775_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__31));
v___x_776_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__33));
v___x_777_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__35));
v___x_778_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__36));
v___x_779_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_779_, 0, v___x_737_);
lean_ctor_set(v___x_779_, 1, v___x_778_);
v___x_780_ = l_Lean_Syntax_node3(v___x_737_, v___x_777_, v___x_763_, v___x_779_, v___x_766_);
v___x_781_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__37));
v___x_782_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_782_, 0, v___x_737_);
lean_ctor_set(v___x_782_, 1, v___x_781_);
v___x_783_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__39));
v___x_784_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__41);
v___x_785_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__44));
v___x_786_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_786_, 0, v___x_737_);
lean_ctor_set(v___x_786_, 1, v___x_784_);
lean_ctor_set(v___x_786_, 2, v___x_785_);
lean_ctor_set(v___x_786_, 3, v___x_754_);
v___x_787_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__46);
v___x_788_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__47));
v___x_789_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_789_, 0, v___x_737_);
lean_ctor_set(v___x_789_, 1, v___x_787_);
lean_ctor_set(v___x_789_, 2, v___x_788_);
lean_ctor_set(v___x_789_, 3, v___x_754_);
lean_inc_ref_n(v___x_789_, 5);
v___x_790_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_789_);
lean_inc_n(v___x_790_, 3);
v___x_791_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_786_, v___x_790_);
lean_inc_ref_n(v___x_782_, 7);
v___x_792_ = l_Lean_Syntax_node3(v___x_737_, v___x_776_, v___x_780_, v___x_782_, v___x_791_);
v___x_793_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_792_);
lean_inc_n(v___x_774_, 9);
v___x_794_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_774_, v___x_793_);
v___x_795_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__49));
v___x_796_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__50));
v___x_797_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_797_, 0, v___x_737_);
lean_ctor_set(v___x_797_, 1, v___x_796_);
v___x_798_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__52);
v___x_799_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__54));
v___x_800_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__55));
v___x_801_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_801_, 0, v___x_737_);
lean_ctor_set(v___x_801_, 1, v___x_798_);
lean_ctor_set(v___x_801_, 2, v___x_800_);
lean_ctor_set(v___x_801_, 3, v___x_754_);
v___x_802_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__58));
v___x_803_ = l_Lean_Syntax_node2(v___x_737_, v___x_802_, v___x_746_, v___x_746_);
lean_inc_n(v___x_803_, 7);
lean_inc_ref_n(v___x_797_, 7);
v___x_804_ = l_Lean_Syntax_node4(v___x_737_, v___x_795_, v___x_797_, v___x_801_, v___x_803_, v___x_746_);
lean_inc(v___x_804_);
lean_inc_ref_n(v___x_750_, 14);
v___x_805_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_756_, v___x_794_, v___x_804_);
lean_inc_n(v___x_747_, 7);
v___x_806_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_747_, v___x_805_);
v___x_807_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__60);
v___x_808_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__61));
v___x_809_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_809_, 0, v___x_737_);
lean_ctor_set(v___x_809_, 1, v___x_807_);
lean_ctor_set(v___x_809_, 2, v___x_808_);
lean_ctor_set(v___x_809_, 3, v___x_754_);
v___x_810_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_809_, v___x_746_);
v___x_811_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__63));
v___x_812_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__64));
v___x_813_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_813_, 0, v___x_737_);
lean_ctor_set(v___x_813_, 1, v___x_812_);
v___x_814_ = l_Lean_Syntax_node3(v___x_737_, v___x_811_, v___x_763_, v___x_813_, v___x_766_);
v___x_815_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__66);
v___x_816_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__68));
v___x_817_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_817_, 0, v___x_737_);
lean_ctor_set(v___x_817_, 1, v___x_815_);
lean_ctor_set(v___x_817_, 2, v___x_816_);
lean_ctor_set(v___x_817_, 3, v___x_754_);
v___x_818_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_817_, v___x_790_);
v___x_819_ = l_Lean_Syntax_node3(v___x_737_, v___x_776_, v___x_814_, v___x_782_, v___x_818_);
v___x_820_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_819_);
v___x_821_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_774_, v___x_820_);
v___x_822_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_810_, v___x_821_, v___x_804_);
v___x_823_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_747_, v___x_822_);
v___x_824_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__70);
v___x_825_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__71));
v___x_826_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_826_, 0, v___x_737_);
lean_ctor_set(v___x_826_, 1, v___x_824_);
lean_ctor_set(v___x_826_, 2, v___x_825_);
lean_ctor_set(v___x_826_, 3, v___x_754_);
v___x_827_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_826_, v___x_746_);
v___x_828_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__73));
v___x_829_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__75);
v___x_830_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__76));
v___x_831_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_831_, 0, v___x_737_);
lean_ctor_set(v___x_831_, 1, v___x_829_);
lean_ctor_set(v___x_831_, 2, v___x_830_);
lean_ctor_set(v___x_831_, 3, v___x_754_);
v___x_832_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__77));
v___x_833_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_737_);
lean_ctor_set(v___x_833_, 1, v___x_832_);
lean_inc_ref_n(v___x_833_, 9);
lean_inc_ref_n(v___x_831_, 4);
v___x_834_ = l_Lean_Syntax_node3(v___x_737_, v___x_828_, v___x_831_, v___x_833_, v___x_789_);
v___x_835_ = l_Lean_Syntax_node3(v___x_737_, v___x_828_, v___x_763_, v___x_833_, v___x_766_);
lean_inc_n(v___x_835_, 3);
lean_inc(v___x_834_);
v___x_836_ = l_Lean_Syntax_node3(v___x_737_, v___x_776_, v___x_834_, v___x_782_, v___x_835_);
v___x_837_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_836_);
v___x_838_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_774_, v___x_837_);
v___x_839_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__79));
v___x_840_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__80));
v___x_841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_737_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__82);
v___x_843_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__84));
v___x_844_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_844_, 0, v___x_737_);
lean_ctor_set(v___x_844_, 1, v___x_842_);
lean_ctor_set(v___x_844_, 2, v___x_843_);
lean_ctor_set(v___x_844_, 3, v___x_754_);
v___x_845_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__85));
v___x_846_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_846_, 0, v___x_737_);
lean_ctor_set(v___x_846_, 1, v___x_845_);
v___x_847_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__87));
v___x_848_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__89));
v___x_849_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__90));
v___x_850_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_850_, 0, v___x_737_);
lean_ctor_set(v___x_850_, 1, v___x_849_);
v___x_851_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__92));
v___x_852_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__94);
v___x_853_ = lean_box(0);
v___x_854_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_854_, 0, v___x_737_);
lean_ctor_set(v___x_854_, 1, v___x_852_);
lean_ctor_set(v___x_854_, 2, v___x_853_);
lean_ctor_set(v___x_854_, 3, v___x_754_);
v___x_855_ = l_Lean_Syntax_node1(v___x_737_, v___x_851_, v___x_854_);
lean_inc(v___x_855_);
lean_inc_ref(v___x_850_);
v___x_856_ = l_Lean_Syntax_node2(v___x_737_, v___x_848_, v___x_850_, v___x_855_);
v___x_857_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__96));
v___x_858_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__98));
v___x_859_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__99));
v___x_860_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_737_);
lean_ctor_set(v___x_860_, 1, v___x_859_);
v___x_861_ = l_Lean_Syntax_node2(v___x_737_, v___x_858_, v___x_860_, v___x_855_);
v___x_862_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__100));
v___x_863_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_863_, 0, v___x_737_);
lean_ctor_set(v___x_863_, 1, v___x_862_);
v___x_864_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__101);
v___x_865_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__102));
v___x_866_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_866_, 0, v___x_737_);
lean_ctor_set(v___x_866_, 1, v___x_864_);
lean_ctor_set(v___x_866_, 2, v___x_865_);
lean_ctor_set(v___x_866_, 3, v___x_754_);
lean_inc_ref(v___x_866_);
v___x_867_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_866_);
v___x_868_ = l_Lean_Syntax_node3(v___x_737_, v___x_857_, v___x_861_, v___x_863_, v___x_867_);
v___x_869_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__103));
v___x_870_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_870_, 0, v___x_737_);
lean_ctor_set(v___x_870_, 1, v___x_869_);
lean_inc_ref_n(v___x_870_, 10);
lean_inc_n(v___x_856_, 9);
v___x_871_ = l_Lean_Syntax_node3(v___x_737_, v___x_847_, v___x_856_, v___x_868_, v___x_870_);
v___x_872_ = l_Lean_Syntax_node3(v___x_737_, v___x_738_, v___x_844_, v___x_846_, v___x_871_);
v___x_873_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__104));
v___x_874_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_874_, 0, v___x_737_);
lean_ctor_set(v___x_874_, 1, v___x_873_);
v___x_875_ = l_Lean_Syntax_node3(v___x_737_, v___x_839_, v___x_841_, v___x_872_, v___x_874_);
v___x_876_ = l_Lean_Syntax_node4(v___x_737_, v___x_795_, v___x_797_, v___x_875_, v___x_803_, v___x_746_);
v___x_877_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_827_, v___x_838_, v___x_876_);
v___x_878_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_747_, v___x_877_);
v___x_879_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__106);
v___x_880_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__107));
v___x_881_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_881_, 0, v___x_737_);
lean_ctor_set(v___x_881_, 1, v___x_879_);
lean_ctor_set(v___x_881_, 2, v___x_880_);
lean_ctor_set(v___x_881_, 3, v___x_754_);
lean_inc_ref(v___x_881_);
v___x_882_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_881_, v___x_746_);
v___x_883_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__109);
v___x_884_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__110));
v___x_885_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_885_, 0, v___x_737_);
lean_ctor_set(v___x_885_, 1, v___x_883_);
lean_ctor_set(v___x_885_, 2, v___x_884_);
lean_ctor_set(v___x_885_, 3, v___x_754_);
v___x_886_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_732_);
v___x_887_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_885_, v___x_886_);
v___x_888_ = l_Lean_Syntax_node2(v___x_737_, v___x_738_, v___x_769_, v___x_887_);
v___x_889_ = l_Lean_Syntax_node4(v___x_737_, v___x_758_, v___x_760_, v___x_767_, v___x_888_, v___x_772_);
v___x_890_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_889_);
v___x_891_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__112);
v___x_892_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__113));
v___x_893_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_893_, 0, v___x_737_);
lean_ctor_set(v___x_893_, 1, v___x_891_);
lean_ctor_set(v___x_893_, 2, v___x_892_);
lean_ctor_set(v___x_893_, 3, v___x_754_);
v___x_894_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_763_);
lean_inc_ref(v___x_893_);
v___x_895_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_893_, v___x_894_);
v___x_896_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_766_);
v___x_897_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_893_, v___x_896_);
lean_inc(v___x_897_);
lean_inc(v___x_895_);
v___x_898_ = l_Lean_Syntax_node3(v___x_737_, v___x_828_, v___x_895_, v___x_833_, v___x_897_);
lean_inc(v___x_898_);
v___x_899_ = l_Lean_Syntax_node3(v___x_737_, v___x_776_, v___x_898_, v___x_782_, v___x_835_);
v___x_900_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_899_);
lean_inc_n(v___x_890_, 2);
v___x_901_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_890_, v___x_900_);
v___x_902_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__115));
v___x_903_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__116));
v___x_904_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_904_, 0, v___x_737_);
lean_ctor_set(v___x_904_, 1, v___x_903_);
v___x_905_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__119));
v___x_906_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__121));
v___x_907_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__123));
v___x_908_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__124));
v___x_909_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__125));
v___x_910_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_910_, 0, v___x_737_);
lean_ctor_set(v___x_910_, 1, v___x_908_);
v___x_911_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__127);
v___x_912_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__129));
v___x_913_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_913_, 0, v___x_737_);
lean_ctor_set(v___x_913_, 1, v___x_911_);
lean_ctor_set(v___x_913_, 2, v___x_912_);
lean_ctor_set(v___x_913_, 3, v___x_754_);
v___x_914_ = l_Lean_Syntax_node2(v___x_737_, v___x_909_, v___x_910_, v___x_913_);
v___x_915_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__130));
v___x_916_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_916_, 0, v___x_737_);
lean_ctor_set(v___x_916_, 1, v___x_915_);
v___x_917_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__131));
v___x_918_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__132));
v___x_919_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__133));
v___x_920_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_920_, 0, v___x_737_);
lean_ctor_set(v___x_920_, 1, v___x_918_);
v___x_921_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__136));
v___x_922_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__138));
v___x_923_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__140);
v___x_924_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__141));
v___x_925_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_925_, 0, v___x_737_);
lean_ctor_set(v___x_925_, 1, v___x_923_);
lean_ctor_set(v___x_925_, 2, v___x_924_);
lean_ctor_set(v___x_925_, 3, v___x_754_);
lean_inc_ref(v___x_925_);
v___x_926_ = l_Lean_Syntax_node1(v___x_737_, v___x_922_, v___x_925_);
v___x_927_ = l_Lean_Syntax_node1(v___x_737_, v___x_921_, v___x_926_);
v___x_928_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_927_);
v___x_929_ = l_Lean_Syntax_node3(v___x_737_, v___x_919_, v___x_920_, v___x_928_, v___x_746_);
v___x_930_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__142));
v___x_931_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_931_, 0, v___x_737_);
lean_ctor_set(v___x_931_, 1, v___x_930_);
v___x_932_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__143));
v___x_933_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__144));
v___x_934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_737_);
lean_ctor_set(v___x_934_, 1, v___x_932_);
v___x_935_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__146));
v___x_936_ = l_Lean_Syntax_node2(v___x_737_, v___x_935_, v___x_746_, v___x_925_);
v___x_937_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_936_);
v___x_938_ = l_Lean_Syntax_node4(v___x_737_, v___x_933_, v___x_934_, v___x_937_, v___x_746_, v___x_746_);
v___x_939_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__148));
v___x_940_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_940_, 0, v___x_737_);
lean_ctor_set(v___x_940_, 1, v___x_799_);
v___x_941_ = l_Lean_Syntax_node1(v___x_737_, v___x_939_, v___x_940_);
lean_inc_ref(v___x_931_);
v___x_942_ = l_Lean_Syntax_node5(v___x_737_, v___x_738_, v___x_929_, v___x_931_, v___x_938_, v___x_931_, v___x_941_);
v___x_943_ = l_Lean_Syntax_node1(v___x_737_, v___x_906_, v___x_942_);
v___x_944_ = l_Lean_Syntax_node1(v___x_737_, v___x_905_, v___x_943_);
v___x_945_ = l_Lean_Syntax_node3(v___x_737_, v___x_917_, v___x_850_, v___x_944_, v___x_870_);
v___x_946_ = l_Lean_Syntax_node3(v___x_737_, v___x_907_, v___x_914_, v___x_916_, v___x_945_);
v___x_947_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_946_);
v___x_948_ = l_Lean_Syntax_node1(v___x_737_, v___x_906_, v___x_947_);
v___x_949_ = l_Lean_Syntax_node1(v___x_737_, v___x_905_, v___x_948_);
lean_inc_ref(v___x_904_);
v___x_950_ = l_Lean_Syntax_node2(v___x_737_, v___x_902_, v___x_904_, v___x_949_);
v___x_951_ = l_Lean_Syntax_node4(v___x_737_, v___x_795_, v___x_797_, v___x_950_, v___x_803_, v___x_746_);
v___x_952_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_882_, v___x_901_, v___x_951_);
v___x_953_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_747_, v___x_952_);
v___x_954_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__150);
v___x_955_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__151));
v___x_956_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_956_, 0, v___x_737_);
lean_ctor_set(v___x_956_, 1, v___x_954_);
lean_ctor_set(v___x_956_, 2, v___x_955_);
lean_ctor_set(v___x_956_, 3, v___x_754_);
v___x_957_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_956_, v___x_746_);
v___x_958_ = l_Lean_Syntax_node3(v___x_737_, v___x_776_, v___x_835_, v___x_782_, v___x_898_);
v___x_959_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_958_);
v___x_960_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_890_, v___x_959_);
v___x_961_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__153);
v___x_962_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__155));
v___x_963_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_963_, 0, v___x_737_);
lean_ctor_set(v___x_963_, 1, v___x_961_);
lean_ctor_set(v___x_963_, 2, v___x_962_);
lean_ctor_set(v___x_963_, 3, v___x_754_);
v___x_964_ = l_Lean_Syntax_node4(v___x_737_, v___x_795_, v___x_797_, v___x_963_, v___x_803_, v___x_746_);
v___x_965_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_957_, v___x_960_, v___x_964_);
v___x_966_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_747_, v___x_965_);
v___x_967_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__157);
v___x_968_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__158));
v___x_969_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_969_, 0, v___x_737_);
lean_ctor_set(v___x_969_, 1, v___x_967_);
lean_ctor_set(v___x_969_, 2, v___x_968_);
lean_ctor_set(v___x_969_, 3, v___x_754_);
v___x_970_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_969_, v___x_746_);
v___x_971_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__160));
v___x_972_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__161));
v___x_973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_737_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
lean_inc_ref_n(v___x_973_, 2);
v___x_974_ = l_Lean_Syntax_node3(v___x_737_, v___x_971_, v___x_763_, v___x_973_, v___x_766_);
v___x_975_ = l_Lean_Syntax_node3(v___x_737_, v___x_971_, v___x_895_, v___x_973_, v___x_897_);
lean_inc(v___x_974_);
v___x_976_ = l_Lean_Syntax_node3(v___x_737_, v___x_776_, v___x_974_, v___x_782_, v___x_975_);
v___x_977_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_976_);
v___x_978_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_890_, v___x_977_);
v___x_979_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__162));
v___x_980_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__163));
v___x_981_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_981_, 0, v___x_737_);
lean_ctor_set(v___x_981_, 1, v___x_979_);
v___x_982_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__165));
v___x_983_ = l_Lean_Syntax_node1(v___x_737_, v___x_982_, v___x_746_);
v___x_984_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__166));
v___x_985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_737_);
lean_ctor_set(v___x_985_, 1, v___x_984_);
v___x_986_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__168));
v___x_987_ = l_Lean_Syntax_node3(v___x_737_, v___x_986_, v___x_746_, v___x_746_, v___x_881_);
v___x_988_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_987_);
v___x_989_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__169));
v___x_990_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_990_, 0, v___x_737_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
lean_inc_ref(v___x_990_);
v___x_991_ = l_Lean_Syntax_node3(v___x_737_, v___x_738_, v___x_985_, v___x_988_, v___x_990_);
lean_inc_ref(v___x_981_);
v___x_992_ = l_Lean_Syntax_node6(v___x_737_, v___x_980_, v___x_981_, v___x_983_, v___x_746_, v___x_746_, v___x_991_, v___x_746_);
v___x_993_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_992_);
v___x_994_ = l_Lean_Syntax_node1(v___x_737_, v___x_906_, v___x_993_);
v___x_995_ = l_Lean_Syntax_node1(v___x_737_, v___x_905_, v___x_994_);
v___x_996_ = l_Lean_Syntax_node2(v___x_737_, v___x_902_, v___x_904_, v___x_995_);
v___x_997_ = l_Lean_Syntax_node4(v___x_737_, v___x_795_, v___x_797_, v___x_996_, v___x_803_, v___x_746_);
v___x_998_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_970_, v___x_978_, v___x_997_);
v___x_999_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_747_, v___x_998_);
v___x_1000_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__171);
v___x_1001_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__172));
v___x_1002_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1002_, 0, v___x_737_);
lean_ctor_set(v___x_1002_, 1, v___x_1000_);
lean_ctor_set(v___x_1002_, 2, v___x_1001_);
lean_ctor_set(v___x_1002_, 3, v___x_754_);
lean_inc_ref(v___x_1002_);
v___x_1003_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_1002_, v___x_746_);
v___x_1004_ = l_Lean_Syntax_node3(v___x_737_, v___x_776_, v___x_835_, v___x_782_, v___x_834_);
v___x_1005_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_1004_);
v___x_1006_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_774_, v___x_1005_);
v___x_1007_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__174);
v___x_1008_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__175));
v___x_1009_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1009_, 0, v___x_737_);
lean_ctor_set(v___x_1009_, 1, v___x_1007_);
lean_ctor_set(v___x_1009_, 2, v___x_1008_);
lean_ctor_set(v___x_1009_, 3, v___x_754_);
v___x_1010_ = l_Lean_Syntax_node4(v___x_737_, v___x_795_, v___x_797_, v___x_1009_, v___x_803_, v___x_746_);
v___x_1011_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_1003_, v___x_1006_, v___x_1010_);
v___x_1012_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_747_, v___x_1011_);
v___x_1013_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__177);
v___x_1014_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__178));
v___x_1015_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1015_, 0, v___x_737_);
lean_ctor_set(v___x_1015_, 1, v___x_1013_);
lean_ctor_set(v___x_1015_, 2, v___x_1014_);
lean_ctor_set(v___x_1015_, 3, v___x_754_);
v___x_1016_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_1015_, v___x_746_);
v___x_1017_ = l_Lean_Syntax_node3(v___x_737_, v___x_971_, v___x_831_, v___x_973_, v___x_789_);
v___x_1018_ = l_Lean_Syntax_node3(v___x_737_, v___x_776_, v___x_974_, v___x_782_, v___x_1017_);
v___x_1019_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_1018_);
v___x_1020_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_774_, v___x_1019_);
v___x_1021_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__180));
v___x_1022_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__182);
v___x_1023_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__185));
v___x_1024_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1024_, 0, v___x_737_);
lean_ctor_set(v___x_1024_, 1, v___x_1022_);
lean_ctor_set(v___x_1024_, 2, v___x_1023_);
lean_ctor_set(v___x_1024_, 3, v___x_754_);
v___x_1025_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__186));
v___x_1026_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1026_, 0, v___x_737_);
lean_ctor_set(v___x_1026_, 1, v___x_1025_);
v___x_1027_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__188));
v___x_1028_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__189));
v___x_1029_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1029_, 0, v___x_737_);
lean_ctor_set(v___x_1029_, 1, v___x_1028_);
v___x_1030_ = l_Lean_Syntax_node1(v___x_737_, v___x_1027_, v___x_1029_);
lean_inc_ref_n(v___x_1026_, 5);
v___x_1031_ = l_Lean_Syntax_node3(v___x_737_, v___x_1021_, v___x_1024_, v___x_1026_, v___x_1030_);
v___x_1032_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_1002_);
v___x_1033_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_1031_, v___x_1032_);
v___x_1034_ = l_Lean_Syntax_node4(v___x_737_, v___x_795_, v___x_797_, v___x_1033_, v___x_803_, v___x_746_);
v___x_1035_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_1016_, v___x_1020_, v___x_1034_);
v___x_1036_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_747_, v___x_1035_);
v___x_1037_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__191));
v___x_1038_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__192));
v___x_1039_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1039_, 0, v___x_737_);
lean_ctor_set(v___x_1039_, 1, v___x_1038_);
v___x_1040_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__194));
v___x_1041_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__196));
v___x_1042_ = l_Lean_Syntax_node1(v___x_737_, v___x_1041_, v___x_746_);
v___x_1043_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__198));
v___x_1044_ = l_Lean_Syntax_node4(v___x_737_, v___x_1043_, v___x_981_, v___x_746_, v___x_746_, v___x_746_);
v___x_1045_ = l_Lean_Syntax_node2(v___x_737_, v___x_1040_, v___x_1042_, v___x_1044_);
v___x_1046_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_1045_);
v___x_1047_ = l_Lean_Syntax_node3(v___x_737_, v___x_1037_, v___x_1039_, v___x_1046_, v___x_990_);
v___x_1048_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_1047_);
lean_inc(v___x_1048_);
v___x_1049_ = l_Lean_Syntax_node7(v___x_737_, v___x_744_, v___x_746_, v___x_1048_, v___x_746_, v___x_746_, v___x_746_, v___x_746_, v___x_746_);
v___x_1050_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__200);
v___x_1051_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__201));
v___x_1052_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1052_, 0, v___x_737_);
lean_ctor_set(v___x_1052_, 1, v___x_1050_);
lean_ctor_set(v___x_1052_, 2, v___x_1051_);
lean_ctor_set(v___x_1052_, 3, v___x_754_);
v___x_1053_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_1052_, v___x_746_);
v___x_1054_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__203);
v___x_1055_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__204));
v___x_1056_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1056_, 0, v___x_737_);
lean_ctor_set(v___x_1056_, 1, v___x_1054_);
lean_ctor_set(v___x_1056_, 2, v___x_1055_);
lean_ctor_set(v___x_1056_, 3, v___x_754_);
lean_inc_ref(v___x_1056_);
v___x_1057_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_1056_);
v___x_1058_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__206);
v___x_1059_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__207));
v___x_1060_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1060_, 0, v___x_737_);
lean_ctor_set(v___x_1060_, 1, v___x_1058_);
lean_ctor_set(v___x_1060_, 2, v___x_1059_);
lean_ctor_set(v___x_1060_, 3, v___x_754_);
v___x_1061_ = l_Lean_Syntax_node2(v___x_737_, v___x_738_, v___x_769_, v___x_1060_);
lean_inc_n(v___x_1057_, 2);
v___x_1062_ = l_Lean_Syntax_node4(v___x_737_, v___x_758_, v___x_760_, v___x_1057_, v___x_1061_, v___x_772_);
v___x_1063_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_1062_);
v___x_1064_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__208);
v___x_1065_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__209));
v___x_1066_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1066_, 0, v___x_737_);
lean_ctor_set(v___x_1066_, 1, v___x_1064_);
lean_ctor_set(v___x_1066_, 2, v___x_1065_);
lean_ctor_set(v___x_1066_, 3, v___x_754_);
v___x_1067_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__211);
v___x_1068_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__212));
v___x_1069_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1069_, 0, v___x_737_);
lean_ctor_set(v___x_1069_, 1, v___x_1067_);
lean_ctor_set(v___x_1069_, 2, v___x_1068_);
lean_ctor_set(v___x_1069_, 3, v___x_754_);
v___x_1070_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_1069_, v___x_1057_);
v___x_1071_ = l_Lean_Syntax_node3(v___x_737_, v___x_847_, v___x_856_, v___x_1070_, v___x_870_);
v___x_1072_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_1071_);
lean_inc_ref_n(v___x_1066_, 6);
v___x_1073_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_1066_, v___x_1072_);
v___x_1074_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__214);
v___x_1075_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__215));
v___x_1076_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1076_, 0, v___x_737_);
lean_ctor_set(v___x_1076_, 1, v___x_1074_);
lean_ctor_set(v___x_1076_, 2, v___x_1075_);
lean_ctor_set(v___x_1076_, 3, v___x_754_);
v___x_1077_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__217));
v___x_1078_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__218));
v___x_1079_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_737_);
lean_ctor_set(v___x_1079_, 1, v___x_1078_);
v___x_1080_ = l_Lean_Syntax_node1(v___x_737_, v___x_1077_, v___x_1079_);
v___x_1081_ = l_Lean_Syntax_node2(v___x_737_, v___x_738_, v___x_1080_, v___x_1056_);
v___x_1082_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_1076_, v___x_1081_);
v___x_1083_ = l_Lean_Syntax_node3(v___x_737_, v___x_828_, v___x_1073_, v___x_833_, v___x_1082_);
v___x_1084_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_1083_);
lean_inc(v___x_1063_);
v___x_1085_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_1063_, v___x_1084_);
v___x_1086_ = l_Lean_Syntax_node3(v___x_737_, v___x_847_, v___x_856_, v___x_866_, v___x_870_);
v___x_1087_ = l_Lean_Syntax_node4(v___x_737_, v___x_795_, v___x_797_, v___x_1086_, v___x_803_, v___x_746_);
lean_inc_n(v___x_1087_, 6);
v___x_1088_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_1053_, v___x_1085_, v___x_1087_);
lean_inc(v___x_1049_);
v___x_1089_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_1049_, v___x_1088_);
v___x_1090_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__220);
v___x_1091_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__221));
v___x_1092_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1092_, 0, v___x_737_);
lean_ctor_set(v___x_1092_, 1, v___x_1090_);
lean_ctor_set(v___x_1092_, 2, v___x_1091_);
lean_ctor_set(v___x_1092_, 3, v___x_754_);
v___x_1093_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_1092_, v___x_746_);
v___x_1094_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__223));
v___x_1095_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__224));
v___x_1096_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1096_, 0, v___x_737_);
lean_ctor_set(v___x_1096_, 1, v___x_1095_);
v___x_1097_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__226);
v___x_1098_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__228));
v___x_1099_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1099_, 0, v___x_737_);
lean_ctor_set(v___x_1099_, 1, v___x_1097_);
lean_ctor_set(v___x_1099_, 2, v___x_1098_);
lean_ctor_set(v___x_1099_, 3, v___x_754_);
v___x_1100_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_1099_, v___x_1057_);
lean_inc(v___x_1100_);
v___x_1101_ = l_Lean_Syntax_node3(v___x_737_, v___x_847_, v___x_856_, v___x_1100_, v___x_870_);
v___x_1102_ = l_Lean_Syntax_node2(v___x_737_, v___x_1094_, v___x_1096_, v___x_1101_);
v___x_1103_ = l_Lean_Syntax_node3(v___x_737_, v___x_847_, v___x_856_, v___x_1102_, v___x_870_);
v___x_1104_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_1103_);
v___x_1105_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_1066_, v___x_1104_);
v___x_1106_ = l_Lean_Syntax_node3(v___x_737_, v___x_828_, v___x_1105_, v___x_833_, v___x_1100_);
v___x_1107_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_1106_);
v___x_1108_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_1063_, v___x_1107_);
v___x_1109_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_1093_, v___x_1108_, v___x_1087_);
v___x_1110_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_1049_, v___x_1109_);
v___x_1111_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__229));
v___x_1112_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__230));
v___x_1113_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1113_, 0, v___x_737_);
lean_ctor_set(v___x_1113_, 1, v___x_1111_);
v___x_1114_ = l_Lean_Syntax_node1(v___x_737_, v___x_1112_, v___x_1113_);
v___x_1115_ = l_Lean_Syntax_node1(v___x_737_, v___x_738_, v___x_1114_);
v___x_1116_ = l_Lean_Syntax_node7(v___x_737_, v___x_744_, v___x_746_, v___x_1048_, v___x_746_, v___x_1115_, v___x_746_, v___x_746_, v___x_746_);
v___x_1117_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__232);
v___x_1118_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__233));
v___x_1119_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1119_, 0, v___x_737_);
lean_ctor_set(v___x_1119_, 1, v___x_1117_);
lean_ctor_set(v___x_1119_, 2, v___x_1118_);
lean_ctor_set(v___x_1119_, 3, v___x_754_);
v___x_1120_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_1119_, v___x_746_);
v___x_1121_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__235));
v___x_1122_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__236));
v___x_1123_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1123_, 0, v___x_737_);
lean_ctor_set(v___x_1123_, 1, v___x_1122_);
lean_inc_ref(v___x_1123_);
v___x_1124_ = l_Lean_Syntax_node3(v___x_737_, v___x_1121_, v___x_763_, v___x_1123_, v___x_766_);
v___x_1125_ = l_Lean_Syntax_node3(v___x_737_, v___x_847_, v___x_856_, v___x_1124_, v___x_870_);
v___x_1126_ = l_Lean_Syntax_node3(v___x_737_, v___x_1021_, v___x_1125_, v___x_1026_, v___x_1066_);
v___x_1127_ = l_Lean_Syntax_node3(v___x_737_, v___x_1121_, v___x_831_, v___x_1123_, v___x_789_);
v___x_1128_ = l_Lean_Syntax_node3(v___x_737_, v___x_828_, v___x_1126_, v___x_833_, v___x_1127_);
v___x_1129_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_1128_);
v___x_1130_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_774_, v___x_1129_);
v___x_1131_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_1120_, v___x_1130_, v___x_1087_);
lean_inc_n(v___x_1116_, 4);
v___x_1132_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_1116_, v___x_1131_);
v___x_1133_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__238);
v___x_1134_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__239));
v___x_1135_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1135_, 0, v___x_737_);
lean_ctor_set(v___x_1135_, 1, v___x_1133_);
lean_ctor_set(v___x_1135_, 2, v___x_1134_);
lean_ctor_set(v___x_1135_, 3, v___x_754_);
v___x_1136_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_1135_, v___x_746_);
v___x_1137_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__241));
v___x_1138_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__242));
v___x_1139_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1139_, 0, v___x_737_);
lean_ctor_set(v___x_1139_, 1, v___x_1138_);
lean_inc_ref(v___x_1139_);
v___x_1140_ = l_Lean_Syntax_node3(v___x_737_, v___x_1137_, v___x_763_, v___x_1139_, v___x_766_);
v___x_1141_ = l_Lean_Syntax_node3(v___x_737_, v___x_847_, v___x_856_, v___x_1140_, v___x_870_);
v___x_1142_ = l_Lean_Syntax_node3(v___x_737_, v___x_1021_, v___x_1141_, v___x_1026_, v___x_1066_);
v___x_1143_ = l_Lean_Syntax_node3(v___x_737_, v___x_1137_, v___x_831_, v___x_1139_, v___x_789_);
v___x_1144_ = l_Lean_Syntax_node3(v___x_737_, v___x_828_, v___x_1142_, v___x_833_, v___x_1143_);
v___x_1145_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_1144_);
v___x_1146_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_774_, v___x_1145_);
v___x_1147_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_1136_, v___x_1146_, v___x_1087_);
v___x_1148_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_1116_, v___x_1147_);
v___x_1149_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__244);
v___x_1150_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__245));
v___x_1151_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1151_, 0, v___x_737_);
lean_ctor_set(v___x_1151_, 1, v___x_1149_);
lean_ctor_set(v___x_1151_, 2, v___x_1150_);
lean_ctor_set(v___x_1151_, 3, v___x_754_);
v___x_1152_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_1151_, v___x_746_);
v___x_1153_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__247));
v___x_1154_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__248));
v___x_1155_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1155_, 0, v___x_737_);
lean_ctor_set(v___x_1155_, 1, v___x_1154_);
lean_inc_ref(v___x_1155_);
v___x_1156_ = l_Lean_Syntax_node3(v___x_737_, v___x_1153_, v___x_763_, v___x_1155_, v___x_766_);
v___x_1157_ = l_Lean_Syntax_node3(v___x_737_, v___x_847_, v___x_856_, v___x_1156_, v___x_870_);
v___x_1158_ = l_Lean_Syntax_node3(v___x_737_, v___x_1021_, v___x_1157_, v___x_1026_, v___x_1066_);
v___x_1159_ = l_Lean_Syntax_node3(v___x_737_, v___x_1153_, v___x_831_, v___x_1155_, v___x_789_);
v___x_1160_ = l_Lean_Syntax_node3(v___x_737_, v___x_828_, v___x_1158_, v___x_833_, v___x_1159_);
v___x_1161_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_1160_);
v___x_1162_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_774_, v___x_1161_);
v___x_1163_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_1152_, v___x_1162_, v___x_1087_);
v___x_1164_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_1116_, v___x_1163_);
v___x_1165_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__250);
v___x_1166_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__251));
v___x_1167_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1167_, 0, v___x_737_);
lean_ctor_set(v___x_1167_, 1, v___x_1165_);
lean_ctor_set(v___x_1167_, 2, v___x_1166_);
lean_ctor_set(v___x_1167_, 3, v___x_754_);
v___x_1168_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_1167_, v___x_746_);
v___x_1169_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__253));
v___x_1170_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__254));
v___x_1171_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1171_, 0, v___x_737_);
lean_ctor_set(v___x_1171_, 1, v___x_1170_);
v___x_1172_ = l_Lean_Syntax_node3(v___x_737_, v___x_1169_, v___x_763_, v___x_1171_, v___x_766_);
v___x_1173_ = l_Lean_Syntax_node3(v___x_737_, v___x_847_, v___x_856_, v___x_1172_, v___x_870_);
v___x_1174_ = l_Lean_Syntax_node3(v___x_737_, v___x_1021_, v___x_1173_, v___x_1026_, v___x_1066_);
v___x_1175_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__256);
v___x_1176_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__258));
v___x_1177_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1177_, 0, v___x_737_);
lean_ctor_set(v___x_1177_, 1, v___x_1175_);
lean_ctor_set(v___x_1177_, 2, v___x_1176_);
lean_ctor_set(v___x_1177_, 3, v___x_754_);
v___x_1178_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_1177_, v___x_790_);
v___x_1179_ = l_Lean_Syntax_node3(v___x_737_, v___x_828_, v___x_1174_, v___x_833_, v___x_1178_);
v___x_1180_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_1179_);
v___x_1181_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_774_, v___x_1180_);
v___x_1182_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_1168_, v___x_1181_, v___x_1087_);
v___x_1183_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_1116_, v___x_1182_);
v___x_1184_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__260);
v___x_1185_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__261));
v___x_1186_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1186_, 0, v___x_737_);
lean_ctor_set(v___x_1186_, 1, v___x_1184_);
lean_ctor_set(v___x_1186_, 2, v___x_1185_);
lean_ctor_set(v___x_1186_, 3, v___x_754_);
v___x_1187_ = l_Lean_Syntax_node2(v___x_737_, v___x_751_, v___x_1186_, v___x_746_);
v___x_1188_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__263));
v___x_1189_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__264));
v___x_1190_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1190_, 0, v___x_737_);
lean_ctor_set(v___x_1190_, 1, v___x_1189_);
v___x_1191_ = l_Lean_Syntax_node3(v___x_737_, v___x_1188_, v___x_763_, v___x_1190_, v___x_766_);
v___x_1192_ = l_Lean_Syntax_node3(v___x_737_, v___x_847_, v___x_856_, v___x_1191_, v___x_870_);
v___x_1193_ = l_Lean_Syntax_node3(v___x_737_, v___x_1021_, v___x_1192_, v___x_1026_, v___x_1066_);
v___x_1194_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__266);
v___x_1195_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__268));
v___x_1196_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1196_, 0, v___x_737_);
lean_ctor_set(v___x_1196_, 1, v___x_1194_);
lean_ctor_set(v___x_1196_, 2, v___x_1195_);
lean_ctor_set(v___x_1196_, 3, v___x_754_);
v___x_1197_ = l_Lean_Syntax_node2(v___x_737_, v___x_783_, v___x_1196_, v___x_790_);
v___x_1198_ = l_Lean_Syntax_node3(v___x_737_, v___x_828_, v___x_1193_, v___x_833_, v___x_1197_);
v___x_1199_ = l_Lean_Syntax_node2(v___x_737_, v___x_775_, v___x_769_, v___x_1198_);
v___x_1200_ = l_Lean_Syntax_node2(v___x_737_, v___x_757_, v___x_774_, v___x_1199_);
v___x_1201_ = l_Lean_Syntax_node4(v___x_737_, v___x_749_, v___x_750_, v___x_1187_, v___x_1200_, v___x_1087_);
v___x_1202_ = l_Lean_Syntax_node2(v___x_737_, v___x_743_, v___x_1116_, v___x_1201_);
v___x_1203_ = lean_unsigned_to_nat(16u);
v___x_1204_ = lean_mk_empty_array_with_capacity(v___x_1203_);
v___x_1205_ = lean_array_push(v___x_1204_, v___x_742_);
v___x_1206_ = lean_array_push(v___x_1205_, v___x_806_);
v___x_1207_ = lean_array_push(v___x_1206_, v___x_823_);
v___x_1208_ = lean_array_push(v___x_1207_, v___x_878_);
v___x_1209_ = lean_array_push(v___x_1208_, v___x_953_);
v___x_1210_ = lean_array_push(v___x_1209_, v___x_966_);
v___x_1211_ = lean_array_push(v___x_1210_, v___x_999_);
v___x_1212_ = lean_array_push(v___x_1211_, v___x_1012_);
v___x_1213_ = lean_array_push(v___x_1212_, v___x_1036_);
v___x_1214_ = lean_array_push(v___x_1213_, v___x_1089_);
v___x_1215_ = lean_array_push(v___x_1214_, v___x_1110_);
v___x_1216_ = lean_array_push(v___x_1215_, v___x_1132_);
v___x_1217_ = lean_array_push(v___x_1216_, v___x_1148_);
v___x_1218_ = lean_array_push(v___x_1217_, v___x_1164_);
v___x_1219_ = lean_array_push(v___x_1218_, v___x_1183_);
v___x_1220_ = lean_array_push(v___x_1219_, v___x_1202_);
v___x_1221_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1221_, 0, v___x_737_);
lean_ctor_set(v___x_1221_, 1, v___x_738_);
lean_ctor_set(v___x_1221_, 2, v___x_1220_);
v___x_1222_ = l_Lean_Syntax_getArgs(v___x_1221_);
lean_dec_ref_known(v___x_1221_, 3);
if (v_isISize_735_ == 0)
{
lean_object* v___x_1223_; lean_object* v_a_1224_; lean_object* v_a_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1255_; 
v___x_1223_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__0(v_ref_727_, v_a_701_, v_a_702_);
v_a_1224_ = lean_ctor_get(v___x_1223_, 0);
v_a_1225_ = lean_ctor_get(v___x_1223_, 1);
v_isSharedCheck_1255_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1255_ == 0)
{
v___x_1227_ = v___x_1223_;
v_isShared_1228_ = v_isSharedCheck_1255_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_a_1225_);
lean_inc(v_a_1224_);
lean_dec(v___x_1223_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1255_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v___x_1229_; size_t v_sz_1230_; size_t v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1236_; 
v___x_1229_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__269));
v_sz_1230_ = lean_usize_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__270);
v___x_1231_ = ((size_t)0ULL);
v___x_1232_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1_spec__0(v___x_733_, v_sz_1230_, v___x_1231_, v___x_1229_);
v___x_1233_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__271));
v___x_1234_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__272));
lean_inc(v_a_1224_);
if (v_isShared_1228_ == 0)
{
lean_ctor_set_tag(v___x_1227_, 2);
lean_ctor_set(v___x_1227_, 1, v___x_1233_);
v___x_1236_ = v___x_1227_;
goto v_reusejp_1235_;
}
else
{
lean_object* v_reuseFailAlloc_1254_; 
v_reuseFailAlloc_1254_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1254_, 0, v_a_1224_);
lean_ctor_set(v_reuseFailAlloc_1254_, 1, v___x_1233_);
v___x_1236_ = v_reuseFailAlloc_1254_;
goto v_reusejp_1235_;
}
v_reusejp_1235_:
{
lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; lean_object* v___x_1248_; lean_object* v___x_1249_; lean_object* v___x_1250_; lean_object* v___x_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; 
lean_inc_n(v_a_1224_, 9);
v___x_1237_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1237_, 0, v_a_1224_);
lean_ctor_set(v___x_1237_, 1, v___x_984_);
v___x_1238_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1238_, 0, v_a_1224_);
lean_ctor_set(v___x_1238_, 1, v___x_738_);
lean_ctor_set(v___x_1238_, 2, v___x_745_);
lean_inc_ref(v___x_1238_);
v___x_1239_ = l_Lean_Syntax_node1(v_a_1224_, v___x_1041_, v___x_1238_);
v___x_1240_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__274));
v___x_1241_ = lean_obj_once(&l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276, &l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276_once, _init_l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__276);
v___x_1242_ = ((lean_object*)(l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___closed__277));
v___x_1243_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1243_, 0, v_a_1224_);
lean_ctor_set(v___x_1243_, 1, v___x_1241_);
lean_ctor_set(v___x_1243_, 2, v___x_1242_);
lean_ctor_set(v___x_1243_, 3, v___x_754_);
v___x_1244_ = l_Lean_Syntax_node2(v_a_1224_, v___x_1240_, v___x_1243_, v___x_1238_);
v___x_1245_ = l_Lean_Syntax_node2(v_a_1224_, v___x_1040_, v___x_1239_, v___x_1244_);
v___x_1246_ = l_Lean_Syntax_node1(v_a_1224_, v___x_738_, v___x_1245_);
v___x_1247_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1247_, 0, v_a_1224_);
lean_ctor_set(v___x_1247_, 1, v___x_989_);
v___x_1248_ = l_Array_append___redArg(v___x_745_, v___x_1232_);
lean_dec_ref(v___x_1232_);
v___x_1249_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_1249_, 0, v_a_1224_);
lean_ctor_set(v___x_1249_, 1, v___x_738_);
lean_ctor_set(v___x_1249_, 2, v___x_1248_);
v___x_1250_ = l_Lean_Syntax_node5(v_a_1224_, v___x_1234_, v___x_1236_, v___x_1237_, v___x_1246_, v___x_1247_, v___x_1249_);
v___x_1251_ = lean_array_push(v___x_1222_, v___x_1250_);
v___x_1252_ = lean_box(0);
v___x_1253_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1(v___f_728_, v_typeName_730_, v___x_1252_, v___x_1251_, v_a_701_, v_a_1225_);
v___y_704_ = v___x_1253_;
goto v___jp_703_;
}
}
}
else
{
lean_object* v___x_1256_; lean_object* v___x_1257_; 
lean_dec(v___x_733_);
v___x_1256_ = lean_box(0);
v___x_1257_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___lam__1(v___f_728_, v_typeName_730_, v___x_1256_, v___x_1222_, v_a_701_, v_a_702_);
v___y_704_ = v___x_1257_;
goto v___jp_703_;
}
}
v___jp_703_:
{
if (lean_obj_tag(v___y_704_) == 0)
{
lean_object* v_a_705_; lean_object* v_a_706_; lean_object* v___x_708_; uint8_t v_isShared_709_; uint8_t v_isSharedCheck_713_; 
v_a_705_ = lean_ctor_get(v___y_704_, 0);
v_a_706_ = lean_ctor_get(v___y_704_, 1);
v_isSharedCheck_713_ = !lean_is_exclusive(v___y_704_);
if (v_isSharedCheck_713_ == 0)
{
v___x_708_ = v___y_704_;
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
else
{
lean_inc(v_a_706_);
lean_inc(v_a_705_);
lean_dec(v___y_704_);
v___x_708_ = lean_box(0);
v_isShared_709_ = v_isSharedCheck_713_;
goto v_resetjp_707_;
}
v_resetjp_707_:
{
lean_object* v___x_711_; 
if (v_isShared_709_ == 0)
{
v___x_711_ = v___x_708_;
goto v_reusejp_710_;
}
else
{
lean_object* v_reuseFailAlloc_712_; 
v_reuseFailAlloc_712_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_712_, 0, v_a_705_);
lean_ctor_set(v_reuseFailAlloc_712_, 1, v_a_706_);
v___x_711_ = v_reuseFailAlloc_712_;
goto v_reusejp_710_;
}
v_reusejp_710_:
{
return v___x_711_;
}
}
}
else
{
lean_object* v_a_714_; lean_object* v_a_715_; lean_object* v___x_717_; uint8_t v_isShared_718_; uint8_t v_isSharedCheck_722_; 
v_a_714_ = lean_ctor_get(v___y_704_, 0);
v_a_715_ = lean_ctor_get(v___y_704_, 1);
v_isSharedCheck_722_ = !lean_is_exclusive(v___y_704_);
if (v_isSharedCheck_722_ == 0)
{
v___x_717_ = v___y_704_;
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
else
{
lean_inc(v_a_715_);
lean_inc(v_a_714_);
lean_dec(v___y_704_);
v___x_717_ = lean_box(0);
v_isShared_718_ = v_isSharedCheck_722_;
goto v_resetjp_716_;
}
v_resetjp_716_:
{
lean_object* v___x_720_; 
if (v_isShared_718_ == 0)
{
v___x_720_ = v___x_717_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v_a_714_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_a_715_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1___boxed(lean_object* v_x_1258_, lean_object* v_a_1259_, lean_object* v_a_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l___aux__Init__Data__SInt__Lemmas______macroRules__commandDeclare__int__theorems______1(v_x_1258_, v_a_1259_, v_a_1260_);
lean_dec_ref(v_a_1259_);
return v_res_1261_;
}
}
lean_object* runtime_initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bitblast(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_SInt_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_SInt_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Nat_Bitwise_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_SInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bitblast(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Int_DivMod_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_LemmasAux(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Pow(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_SInt_Lemmas(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Nat_Bitwise_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_SInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bitblast(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_DivMod_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_LemmasAux(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Pow(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_SInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_SInt_Lemmas(builtin);
}
#ifdef __cplusplus
}
#endif
