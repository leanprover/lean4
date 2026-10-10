// Lean compiler output
// Module: Init.Data.UInt.Bitwise
// Imports: import all Init.Data.BitVec.Basic import all Init.Data.UInt.Basic public import Init.Data.Nat.Bitwise public import Init.Data.Nat.Lemmas public import Init.Data.UInt.Basic public import Init.Ext import Init.Data.BitVec.Bootstrap import Init.Data.BitVec.Lemmas import Init.Data.Fin.Bitwise import Init.Data.UInt.Lemmas import Init.System.Platform
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
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_mkIdent(lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_TSyntax_getId(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node7(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node6(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
static const lean_string_object l_commandDeclare__bitwise__uint__theorems_____00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 39, .m_capacity = 39, .m_length = 38, .m_data = "commandDeclare_bitwise_uint_theorems__"};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__0 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__0_value;
static const lean_ctor_object l_commandDeclare__bitwise__uint__theorems_____00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(231, 222, 49, 96, 74, 98, 78, 17)}};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__1 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__1_value;
static const lean_string_object l_commandDeclare__bitwise__uint__theorems_____00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__2 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__2_value;
static const lean_ctor_object l_commandDeclare__bitwise__uint__theorems_____00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__3 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__3_value;
static const lean_string_object l_commandDeclare__bitwise__uint__theorems_____00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = "declare_bitwise_uint_theorems"};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__4 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__4_value;
static const lean_ctor_object l_commandDeclare__bitwise__uint__theorems_____00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__4_value)}};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__5 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__5_value;
static const lean_string_object l_commandDeclare__bitwise__uint__theorems_____00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__6 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__6_value;
static const lean_ctor_object l_commandDeclare__bitwise__uint__theorems_____00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__7 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__7_value;
static const lean_ctor_object l_commandDeclare__bitwise__uint__theorems_____00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__7_value)}};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__8 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__8_value;
static const lean_ctor_object l_commandDeclare__bitwise__uint__theorems_____00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__3_value),((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__5_value),((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__8_value)}};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__9 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__9_value;
static const lean_string_object l_commandDeclare__bitwise__uint__theorems_____00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__10 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__10_value;
static const lean_ctor_object l_commandDeclare__bitwise__uint__theorems_____00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__10_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__11 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__11_value;
static const lean_ctor_object l_commandDeclare__bitwise__uint__theorems_____00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__11_value),((lean_object*)(((size_t)(1023) << 1) | 1))}};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__12 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__12_value;
static const lean_ctor_object l_commandDeclare__bitwise__uint__theorems_____00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__3_value),((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__9_value),((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__12_value)}};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__13 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__13_value;
static const lean_ctor_object l_commandDeclare__bitwise__uint__theorems_____00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__1_value),((lean_object*)(((size_t)(1022) << 1) | 1)),((lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__13_value)}};
static const lean_object* l_commandDeclare__bitwise__uint__theorems_____00__closed__14 = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__14_value;
LEAN_EXPORT const lean_object* l_commandDeclare__bitwise__uint__theorems____ = (const lean_object*)&l_commandDeclare__bitwise__uint__theorems_____00__closed__14_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Command"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "end"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__3 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__3_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(254, 132, 206, 38, 133, 164, 145, 139)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__4 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__4_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__5 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__5_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__6 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__6_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__7;
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__0___boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__0 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__0_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "USize"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__1 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__1_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(109, 217, 26, 131, 232, 198, 207, 245)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "namespace"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(84, 17, 124, 142, 243, 161, 231, 243)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "declaration"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__5 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__5_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__5_value),LEAN_SCALAR_PTR_LITERAL(157, 246, 223, 221, 242, 35, 238, 117)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declModifiers"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__7 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__7_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(0, 165, 146, 53, 36, 89, 7, 202)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "attributes"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(66, 184, 196, 169, 25, 125, 40, 35)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "@["};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "attrInstance"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__13 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__13_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(241, 75, 242, 110, 47, 5, 20, 104)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "attrKind"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__15 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__15_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(32, 164, 20, 104, 12, 221, 204, 110)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Attr"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "simp"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__18 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__18_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(167, 64, 108, 103, 216, 152, 33, 14)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "]"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__20 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__20_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "protected"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__21 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__21_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__21_value),LEAN_SCALAR_PTR_LITERAL(33, 80, 123, 180, 50, 194, 119, 199)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "theorem"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__23 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__23_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__23_value),LEAN_SCALAR_PTR_LITERAL(238, 116, 137, 74, 194, 103, 58, 54)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "declId"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(243, 92, 136, 33, 216, 98, 92, 25)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_not"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__27 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__27_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__28_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__28;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__29_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__27_value),LEAN_SCALAR_PTR_LITERAL(4, 183, 142, 241, 137, 246, 36, 132)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__29 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__29_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__30_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "declSig"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__30 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__30_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__30_value),LEAN_SCALAR_PTR_LITERAL(22, 101, 130, 251, 183, 19, 113, 82)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__32_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "implicitBinder"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__32 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__32_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__32_value),LEAN_SCALAR_PTR_LITERAL(39, 181, 62, 102, 86, 14, 161, 96)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__34_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "{"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__34 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__34_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "a"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__36_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__36;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__37_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__37 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__37_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__38_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ":"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__38 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__38_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__39_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "}"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__39 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__39_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "typeSpec"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__40_value),LEAN_SCALAR_PTR_LITERAL(77, 126, 241, 117, 174, 189, 108, 62)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_=_"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__43_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__42_value),LEAN_SCALAR_PTR_LITERAL(167, 251, 107, 62, 223, 239, 203, 78)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__43 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__43_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__44_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "proj"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__44 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__44_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__44_value),LEAN_SCALAR_PTR_LITERAL(103, 149, 207, 196, 17, 4, 77, 74)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__46_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__46 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__46_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__46_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__48_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__48 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__48_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__48_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__51_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__51 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__51_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__52_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__51_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__52 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__52_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__53_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__53 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__53_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__55_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "term~~~_"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__55 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__55_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__55_value),LEAN_SCALAR_PTR_LITERAL(77, 157, 31, 78, 77, 225, 98, 3)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__57_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "~~~"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__57 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__57_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__59_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__59 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__59_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__60_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toBitVec"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__60 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__60_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__61_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__61;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__62_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(130, 88, 94, 113, 144, 209, 170, 121)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__62 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__62_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__63_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "="};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__63 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__63_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__64_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "a.toBitVec"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__64 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__64_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__65_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__65;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__66_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__66_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__66_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(238, 90, 95, 221, 27, 118, 9, 223)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__66 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__66_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__67_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "declValSimple"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__67 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__67_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__67_value),LEAN_SCALAR_PTR_LITERAL(228, 117, 47, 248, 145, 185, 135, 188)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__69_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ":="};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__69 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__69_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__70_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "rfl"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__70 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__70_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__71_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__71;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__72_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__70_value),LEAN_SCALAR_PTR_LITERAL(77, 42, 253, 71, 61, 132, 173, 240)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__72 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__72_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__73_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "Termination"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__73 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__73_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__74_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "suffix"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__74 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__74_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__73_value),LEAN_SCALAR_PTR_LITERAL(128, 225, 226, 49, 186, 161, 212, 105)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__74_value),LEAN_SCALAR_PTR_LITERAL(245, 187, 99, 45, 217, 244, 244, 120)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__76_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_and"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__76 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__76_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__78_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__76_value),LEAN_SCALAR_PTR_LITERAL(114, 9, 190, 33, 169, 157, 178, 61)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__78 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__78_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__79_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "explicitBinder"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__79 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__79_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__79_value),LEAN_SCALAR_PTR_LITERAL(49, 119, 193, 23, 170, 93, 183, 238)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__81_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "b"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__81 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__81_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__82_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__82;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__83_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__81_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__83 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__83_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_&&&_"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__85_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__84_value),LEAN_SCALAR_PTR_LITERAL(193, 99, 184, 216, 31, 112, 180, 172)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__85 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__85_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__86_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "&&&"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__86 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__86_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__87_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "b.toBitVec"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__87 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__87_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__88_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__88;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__81_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__60_value),LEAN_SCALAR_PTR_LITERAL(6, 235, 47, 200, 31, 68, 206, 165)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "toBitVec_or"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__92_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90_value),LEAN_SCALAR_PTR_LITERAL(84, 192, 11, 42, 238, 76, 177, 131)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__92 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__92_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__93_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_|||_"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__93 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__93_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__94_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__93_value),LEAN_SCALAR_PTR_LITERAL(235, 153, 6, 35, 60, 189, 128, 63)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__94 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__94_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__95_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "|||"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__95 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__95_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__96_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "toBitVec_xor"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__96 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__96_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__98_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__96_value),LEAN_SCALAR_PTR_LITERAL(134, 92, 36, 213, 197, 9, 127, 37)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__98 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__98_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__99_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_^^^_"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__99 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__99_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__100_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__99_value),LEAN_SCALAR_PTR_LITERAL(80, 193, 94, 25, 196, 159, 89, 59)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__100 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__100_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__101_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "^^^"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__101 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__101_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__102_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "toBitVec_shiftLeft"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__102 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__102_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__103_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__103;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__104_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__102_value),LEAN_SCALAR_PTR_LITERAL(67, 94, 183, 134, 188, 119, 20, 251)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__104 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__104_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__105_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_<<<_"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__105 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__105_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__106_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__105_value),LEAN_SCALAR_PTR_LITERAL(165, 87, 195, 47, 75, 199, 87, 179)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__106 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__106_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__107_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "<<<"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__107 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__107_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__108_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_%_"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__108 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__108_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__109_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__108_value),LEAN_SCALAR_PTR_LITERAL(223, 214, 140, 105, 32, 178, 232, 218)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__109 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__109_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__110_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "%"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__110 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__110_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__111_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "toBitVec_shiftRight"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__111 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__111_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__113_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__111_value),LEAN_SCALAR_PTR_LITERAL(93, 43, 133, 175, 145, 37, 127, 56)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__113 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__113_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__114_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_>>>_"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__114 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__114_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__115_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__114_value),LEAN_SCALAR_PTR_LITERAL(42, 229, 82, 200, 78, 65, 60, 50)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__115 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__115_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__116_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = ">>>"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__116 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__116_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__117_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toNat_and"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__117 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__117_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__118_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__118;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__119_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__117_value),LEAN_SCALAR_PTR_LITERAL(242, 27, 174, 146, 5, 148, 205, 209)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__119 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__119_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "toNat"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__122_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120_value),LEAN_SCALAR_PTR_LITERAL(149, 151, 87, 92, 55, 159, 230, 117)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__122 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__122_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__123_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "a.toNat"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__123 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__123_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__124_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__124;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__125_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35_value),LEAN_SCALAR_PTR_LITERAL(247, 80, 99, 121, 74, 33, 203, 108)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__125_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__125_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120_value),LEAN_SCALAR_PTR_LITERAL(209, 225, 17, 45, 167, 18, 17, 41)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__125 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__125_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__126_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "b.toNat"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__126 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__126_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__128_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__81_value),LEAN_SCALAR_PTR_LITERAL(47, 22, 244, 233, 226, 169, 241, 142)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__128_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__128_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120_value),LEAN_SCALAR_PTR_LITERAL(185, 81, 53, 123, 96, 114, 95, 216)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__128 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__128_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__129_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__129 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__129_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__9_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__129_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__131_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__131 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__131_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__133_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__133 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__133_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__133_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__135_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__135 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__135_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__135_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__18_value),LEAN_SCALAR_PTR_LITERAL(50, 13, 241, 145, 67, 153, 105, 177)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__138_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "optConfig"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__138 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__138_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__138_value),LEAN_SCALAR_PTR_LITERAL(137, 208, 10, 74, 108, 50, 106, 48)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__140_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "["};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__140 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__140_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpLemma"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__141_value),LEAN_SCALAR_PTR_LITERAL(38, 215, 101, 250, 181, 108, 118, 102)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__144_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "simpErase"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__144 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__144_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__132_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__144_value),LEAN_SCALAR_PTR_LITERAL(216, 24, 229, 171, 59, 186, 144, 157)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "-"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__147_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "toNat_toBitVec"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__147 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__147_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__149_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__147_value),LEAN_SCALAR_PTR_LITERAL(11, 24, 125, 251, 131, 10, 0, 114)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__149 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__149_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__150_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "toNat_or"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__150 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__150_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__152_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__150_value),LEAN_SCALAR_PTR_LITERAL(30, 143, 54, 213, 119, 130, 156, 175)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__152 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__152_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "toNat_xor"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__154_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__154;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__155_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153_value),LEAN_SCALAR_PTR_LITERAL(70, 164, 140, 165, 174, 74, 243, 41)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__155 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__155_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__156_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "toNat_shiftLeft"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__156 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__156_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__157_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__157;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__158_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__156_value),LEAN_SCALAR_PTR_LITERAL(98, 105, 243, 177, 121, 160, 63, 171)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__158 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__158_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__159_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "term_^_"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__159 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__159_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__160_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__159_value),LEAN_SCALAR_PTR_LITERAL(71, 186, 108, 193, 152, 123, 33, 175)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__160 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__160_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__161_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "num"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__161 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__161_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__162_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__161_value),LEAN_SCALAR_PTR_LITERAL(227, 68, 22, 222, 47, 51, 204, 84)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__162 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__162_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__163_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "2"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__163 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__163_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__164_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "^"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__164 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__164_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__165_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "toNat_shiftRight"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__165 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__165_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__166_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__166;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__167_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__165_value),LEAN_SCALAR_PTR_LITERAL(188, 114, 52, 139, 72, 220, 102, 19)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__167 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__167_value;
static const lean_array_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__168_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*6, .m_other = 0, .m_tag = 246}, .m_size = 6, .m_capacity = 6, .m_data = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__29_value),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__78_value),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__92_value),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__98_value),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__104_value),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__113_value)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__168 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__168_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__169_once = LEAN_ONCE_CELL_INITIALIZER;
static size_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__169;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__170_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "attribute"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__170 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__170_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(214, 208, 105, 11, 221, 56, 173, 240)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__170_value),LEAN_SCALAR_PTR_LITERAL(79, 30, 18, 84, 71, 173, 185, 159)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__172_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "simple"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__172 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__172_value;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173_value_aux_0),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173_value_aux_1),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(7, 175, 252, 195, 22, 42, 161, 63)}};
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173_value_aux_2),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__172_value),LEAN_SCALAR_PTR_LITERAL(107, 67, 254, 234, 65, 174, 209, 53)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173_value;
static const lean_string_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__174_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "int_toBitVec"};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__174 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__174_value;
static lean_once_cell_t l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__175_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__175;
static const lean_ctor_object l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__176_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__174_value),LEAN_SCALAR_PTR_LITERAL(86, 82, 181, 235, 29, 69, 188, 18)}};
static const lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__176 = (const lean_object*)&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__176_value;
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__0(lean_object* v_____do__lift_34_, lean_object* v___y_35_, lean_object* v___y_36_){
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
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__0___boxed(lean_object* v_____do__lift_40_, lean_object* v___y_41_, lean_object* v___y_42_){
_start:
{
lean_object* v_res_43_; 
v_res_43_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__0(v_____do__lift_40_, v___y_41_, v___y_42_);
lean_dec_ref(v___y_41_);
lean_dec(v_____do__lift_40_);
return v_res_43_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__7(void){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_Array_mkArray0___redArg();
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1(lean_object* v___f_57_, lean_object* v_typeName_58_, lean_object* v_____r_59_, lean_object* v_cmds_60_, lean_object* v___y_61_, lean_object* v___y_62_){
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
v___x_70_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__3));
v___x_71_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__4));
lean_inc_n(v_a_65_, 3);
v___x_72_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_72_, 0, v_a_65_);
lean_ctor_set(v___x_72_, 1, v___x_70_);
v___x_73_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__6));
v___x_74_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__7, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__7_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__7);
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
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___boxed(lean_object* v___f_94_, lean_object* v_typeName_95_, lean_object* v_____r_96_, lean_object* v_cmds_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1(v___f_94_, v_typeName_95_, v_____r_96_, v_cmds_97_, v___y_98_, v___y_99_);
lean_dec_ref(v___y_98_);
return v_res_100_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1_spec__0(lean_object* v___x_101_, size_t v_sz_102_, size_t v_i_103_, lean_object* v_bs_104_){
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
v___x_110_ = l_Lean_mkIdent(v___x_109_);
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_add(v_i_103_, v___x_111_);
v___x_113_ = lean_array_uset(v_bs_x27_108_, v_i_103_, v___x_110_);
v_i_103_ = v___x_112_;
v_bs_104_ = v___x_113_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_101_ = stack[0].m_obj;
size_t v_sz_102_ = stack[1].m_num;
size_t v_i_103_ = stack[2].m_num;
lean_object* v_bs_104_ = stack[3].m_obj;
lean_object* v_res_115_;
v_res_115_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1_spec__0(v___x_101_, v_sz_102_, v_i_103_, v_bs_104_);
stack->m_obj
 = v_res_115_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1_spec__0___boxed(lean_object* v___x_116_, lean_object* v_sz_117_, lean_object* v_i_118_, lean_object* v_bs_119_){
_start:
{
size_t v_sz_boxed_120_; size_t v_i_boxed_121_; lean_object* v_res_122_; 
v_sz_boxed_120_ = lean_unbox_usize(v_sz_117_);
lean_dec(v_sz_117_);
v_i_boxed_121_ = lean_unbox_usize(v_i_118_);
lean_dec(v_i_118_);
v_res_122_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1_spec__0(v___x_116_, v_sz_boxed_120_, v_i_boxed_121_, v_bs_119_);
return v_res_122_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__28(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__27));
v___x_193_ = l_String_toRawSubstring_x27(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__36(void){
_start:
{
lean_object* v___x_210_; lean_object* v___x_211_; 
v___x_210_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__35));
v___x_211_ = l_String_toRawSubstring_x27(v___x_210_);
return v___x_211_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54(void){
_start:
{
lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_248_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__53));
v___x_249_ = l_String_toRawSubstring_x27(v___x_248_);
return v___x_249_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__61(void){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; 
v___x_257_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__60));
v___x_258_ = l_String_toRawSubstring_x27(v___x_257_);
return v___x_258_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__65(void){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__64));
v___x_264_ = l_String_toRawSubstring_x27(v___x_263_);
return v___x_264_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__71(void){
_start:
{
lean_object* v___x_276_; lean_object* v___x_277_; 
v___x_276_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__70));
v___x_277_ = l_String_toRawSubstring_x27(v___x_276_);
return v___x_277_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77(void){
_start:
{
lean_object* v___x_288_; lean_object* v___x_289_; 
v___x_288_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__76));
v___x_289_ = l_String_toRawSubstring_x27(v___x_288_);
return v___x_289_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__82(void){
_start:
{
lean_object* v___x_299_; lean_object* v___x_300_; 
v___x_299_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__81));
v___x_300_ = l_String_toRawSubstring_x27(v___x_299_);
return v___x_300_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__88(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__87));
v___x_309_ = l_String_toRawSubstring_x27(v___x_308_);
return v___x_309_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91(void){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__90));
v___x_315_ = l_String_toRawSubstring_x27(v___x_314_);
return v___x_315_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97(void){
_start:
{
lean_object* v___x_323_; lean_object* v___x_324_; 
v___x_323_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__96));
v___x_324_ = l_String_toRawSubstring_x27(v___x_323_);
return v___x_324_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__103(void){
_start:
{
lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_332_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__102));
v___x_333_ = l_String_toRawSubstring_x27(v___x_332_);
return v___x_333_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112(void){
_start:
{
lean_object* v___x_345_; lean_object* v___x_346_; 
v___x_345_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__111));
v___x_346_ = l_String_toRawSubstring_x27(v___x_345_);
return v___x_346_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__118(void){
_start:
{
lean_object* v___x_354_; lean_object* v___x_355_; 
v___x_354_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__117));
v___x_355_ = l_String_toRawSubstring_x27(v___x_354_);
return v___x_355_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121(void){
_start:
{
lean_object* v___x_359_; lean_object* v___x_360_; 
v___x_359_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__120));
v___x_360_ = l_String_toRawSubstring_x27(v___x_359_);
return v___x_360_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__124(void){
_start:
{
lean_object* v___x_364_; lean_object* v___x_365_; 
v___x_364_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__123));
v___x_365_ = l_String_toRawSubstring_x27(v___x_364_);
return v___x_365_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127(void){
_start:
{
lean_object* v___x_370_; lean_object* v___x_371_; 
v___x_370_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__126));
v___x_371_ = l_String_toRawSubstring_x27(v___x_370_);
return v___x_371_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148(void){
_start:
{
lean_object* v___x_422_; lean_object* v___x_423_; 
v___x_422_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__147));
v___x_423_ = l_String_toRawSubstring_x27(v___x_422_);
return v___x_423_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151(void){
_start:
{
lean_object* v___x_427_; lean_object* v___x_428_; 
v___x_427_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__150));
v___x_428_ = l_String_toRawSubstring_x27(v___x_427_);
return v___x_428_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__154(void){
_start:
{
lean_object* v___x_432_; lean_object* v___x_433_; 
v___x_432_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__153));
v___x_433_ = l_String_toRawSubstring_x27(v___x_432_);
return v___x_433_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__157(void){
_start:
{
lean_object* v___x_437_; lean_object* v___x_438_; 
v___x_437_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__156));
v___x_438_ = l_String_toRawSubstring_x27(v___x_437_);
return v___x_438_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__166(void){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__165));
v___x_451_ = l_String_toRawSubstring_x27(v___x_450_);
return v___x_451_;
}
}
static size_t _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__169(void){
_start:
{
lean_object* v___x_468_; size_t v_sz_469_; 
v___x_468_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__168));
v_sz_469_ = lean_array_size(v___x_468_);
return v_sz_469_;
}
}
static lean_object* _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__175(void){
_start:
{
lean_object* v___x_483_; lean_object* v___x_484_; 
v___x_483_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__174));
v___x_484_ = l_String_toRawSubstring_x27(v___x_483_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1(lean_object* v_x_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___y_491_; lean_object* v___x_510_; uint8_t v___x_511_; 
v___x_510_ = ((lean_object*)(l_commandDeclare__bitwise__uint__theorems_____00__closed__1));
lean_inc(v_x_487_);
v___x_511_ = l_Lean_Syntax_isOfKind(v_x_487_, v___x_510_);
if (v___x_511_ == 0)
{
lean_object* v___x_512_; lean_object* v___x_513_; 
lean_dec(v_x_487_);
v___x_512_ = lean_box(1);
v___x_513_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_512_);
lean_ctor_set(v___x_513_, 1, v_a_489_);
return v___x_513_;
}
else
{
lean_object* v_ref_514_; lean_object* v___f_515_; lean_object* v___x_516_; lean_object* v_typeName_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; lean_object* v___x_521_; uint8_t v_isUSize_522_; uint8_t v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; lean_object* v___x_530_; lean_object* v___x_531_; lean_object* v___x_532_; lean_object* v___x_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; lean_object* v___x_540_; lean_object* v___x_541_; lean_object* v___x_542_; lean_object* v___x_543_; lean_object* v___x_544_; lean_object* v___x_545_; lean_object* v___x_546_; lean_object* v___x_547_; lean_object* v___x_548_; lean_object* v___x_549_; lean_object* v___x_550_; lean_object* v___x_551_; lean_object* v___x_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; lean_object* v___x_558_; lean_object* v___x_559_; lean_object* v___x_560_; lean_object* v___x_561_; lean_object* v___x_562_; lean_object* v___x_563_; lean_object* v___x_564_; lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; lean_object* v___x_570_; lean_object* v___x_571_; lean_object* v___x_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v___x_664_; lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; lean_object* v___x_677_; lean_object* v___x_678_; lean_object* v___x_679_; lean_object* v___x_680_; lean_object* v___x_681_; lean_object* v___x_682_; lean_object* v___x_683_; lean_object* v___x_684_; lean_object* v___x_685_; lean_object* v___x_686_; lean_object* v___x_687_; lean_object* v___x_688_; lean_object* v___x_689_; lean_object* v___x_690_; lean_object* v___x_691_; lean_object* v___x_692_; lean_object* v___x_693_; lean_object* v___x_694_; lean_object* v___x_695_; lean_object* v___x_696_; lean_object* v___x_697_; lean_object* v___x_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; lean_object* v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v___x_736_; lean_object* v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v___x_756_; lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; lean_object* v___x_767_; lean_object* v___x_768_; lean_object* v___x_769_; lean_object* v___x_770_; lean_object* v___x_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v___x_776_; lean_object* v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; 
v_ref_514_ = lean_ctor_get(v_a_488_, 5);
v___f_515_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__0));
v___x_516_ = lean_unsigned_to_nat(1u);
v_typeName_517_ = l_Lean_Syntax_getArg(v_x_487_, v___x_516_);
v___x_518_ = lean_unsigned_to_nat(2u);
v___x_519_ = l_Lean_Syntax_getArg(v_x_487_, v___x_518_);
lean_dec(v_x_487_);
v___x_520_ = l_Lean_TSyntax_getId(v_typeName_517_);
v___x_521_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__2));
v_isUSize_522_ = lean_name_eq(v___x_520_, v___x_521_);
v___x_523_ = 0;
v___x_524_ = l_Lean_SourceInfo_fromRef(v_ref_514_, v___x_523_);
v___x_525_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__6));
v___x_526_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__3));
v___x_527_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__4));
lean_inc_n(v___x_524_, 190);
v___x_528_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_528_, 0, v___x_524_);
lean_ctor_set(v___x_528_, 1, v___x_526_);
lean_inc_n(v_typeName_517_, 2);
v___x_529_ = l_Lean_Syntax_node2(v___x_524_, v___x_527_, v___x_528_, v_typeName_517_);
v___x_530_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__6));
v___x_531_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__8));
v___x_532_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__7, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__7_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1___closed__7);
v___x_533_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_533_, 0, v___x_524_);
lean_ctor_set(v___x_533_, 1, v___x_525_);
lean_ctor_set(v___x_533_, 2, v___x_532_);
v___x_534_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__11));
v___x_535_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__12));
v___x_536_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_536_, 0, v___x_524_);
lean_ctor_set(v___x_536_, 1, v___x_535_);
v___x_537_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__14));
v___x_538_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__16));
lean_inc_ref_n(v___x_533_, 30);
v___x_539_ = l_Lean_Syntax_node1(v___x_524_, v___x_538_, v___x_533_);
v___x_540_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__18));
v___x_541_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__19));
v___x_542_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_542_, 0, v___x_524_);
lean_ctor_set(v___x_542_, 1, v___x_540_);
lean_inc_ref(v___x_542_);
v___x_543_ = l_Lean_Syntax_node4(v___x_524_, v___x_541_, v___x_542_, v___x_533_, v___x_533_, v___x_533_);
v___x_544_ = l_Lean_Syntax_node2(v___x_524_, v___x_537_, v___x_539_, v___x_543_);
v___x_545_ = l_Lean_Syntax_node1(v___x_524_, v___x_525_, v___x_544_);
v___x_546_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__20));
v___x_547_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_547_, 0, v___x_524_);
lean_ctor_set(v___x_547_, 1, v___x_546_);
lean_inc_ref(v___x_547_);
v___x_548_ = l_Lean_Syntax_node3(v___x_524_, v___x_534_, v___x_536_, v___x_545_, v___x_547_);
v___x_549_ = l_Lean_Syntax_node1(v___x_524_, v___x_525_, v___x_548_);
v___x_550_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__21));
v___x_551_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__22));
v___x_552_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_552_, 0, v___x_524_);
lean_ctor_set(v___x_552_, 1, v___x_550_);
v___x_553_ = l_Lean_Syntax_node1(v___x_524_, v___x_551_, v___x_552_);
v___x_554_ = l_Lean_Syntax_node1(v___x_524_, v___x_525_, v___x_553_);
v___x_555_ = l_Lean_Syntax_node7(v___x_524_, v___x_531_, v___x_533_, v___x_549_, v___x_533_, v___x_554_, v___x_533_, v___x_533_, v___x_533_);
v___x_556_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__23));
v___x_557_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__24));
v___x_558_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_558_, 0, v___x_524_);
lean_ctor_set(v___x_558_, 1, v___x_556_);
v___x_559_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__26));
v___x_560_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__28, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__28_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__28);
v___x_561_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__29));
v___x_562_ = lean_box(0);
v___x_563_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_563_, 0, v___x_524_);
lean_ctor_set(v___x_563_, 1, v___x_560_);
lean_ctor_set(v___x_563_, 2, v___x_561_);
lean_ctor_set(v___x_563_, 3, v___x_562_);
v___x_564_ = l_Lean_Syntax_node2(v___x_524_, v___x_559_, v___x_563_, v___x_533_);
v___x_565_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__31));
v___x_566_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__33));
v___x_567_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__34));
v___x_568_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_524_);
lean_ctor_set(v___x_568_, 1, v___x_567_);
v___x_569_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__36, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__36_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__36);
v___x_570_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__37));
v___x_571_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_571_, 0, v___x_524_);
lean_ctor_set(v___x_571_, 1, v___x_569_);
lean_ctor_set(v___x_571_, 2, v___x_570_);
lean_ctor_set(v___x_571_, 3, v___x_562_);
lean_inc_ref_n(v___x_571_, 7);
v___x_572_ = l_Lean_Syntax_node1(v___x_524_, v___x_525_, v___x_571_);
v___x_573_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__38));
v___x_574_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_574_, 0, v___x_524_);
lean_ctor_set(v___x_574_, 1, v___x_573_);
lean_inc_ref_n(v___x_574_, 11);
v___x_575_ = l_Lean_Syntax_node2(v___x_524_, v___x_525_, v___x_574_, v_typeName_517_);
v___x_576_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__39));
v___x_577_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_577_, 0, v___x_524_);
lean_ctor_set(v___x_577_, 1, v___x_576_);
lean_inc(v___x_575_);
v___x_578_ = l_Lean_Syntax_node4(v___x_524_, v___x_566_, v___x_568_, v___x_572_, v___x_575_, v___x_577_);
v___x_579_ = l_Lean_Syntax_node1(v___x_524_, v___x_525_, v___x_578_);
v___x_580_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__41));
v___x_581_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__43));
v___x_582_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__45));
v___x_583_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__47));
v___x_584_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__49));
v___x_585_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__50));
v___x_586_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_586_, 0, v___x_524_);
lean_ctor_set(v___x_586_, 1, v___x_585_);
v___x_587_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__52));
v___x_588_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__54);
v___x_589_ = lean_box(0);
v___x_590_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_590_, 0, v___x_524_);
lean_ctor_set(v___x_590_, 1, v___x_588_);
lean_ctor_set(v___x_590_, 2, v___x_589_);
lean_ctor_set(v___x_590_, 3, v___x_562_);
v___x_591_ = l_Lean_Syntax_node1(v___x_524_, v___x_587_, v___x_590_);
lean_inc_ref(v___x_586_);
v___x_592_ = l_Lean_Syntax_node2(v___x_524_, v___x_584_, v___x_586_, v___x_591_);
v___x_593_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__56));
v___x_594_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__57));
v___x_595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_524_);
lean_ctor_set(v___x_595_, 1, v___x_594_);
lean_inc_ref(v___x_595_);
v___x_596_ = l_Lean_Syntax_node2(v___x_524_, v___x_593_, v___x_595_, v___x_571_);
v___x_597_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__58));
v___x_598_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_598_, 0, v___x_524_);
lean_ctor_set(v___x_598_, 1, v___x_597_);
lean_inc_ref_n(v___x_598_, 9);
lean_inc_n(v___x_592_, 8);
v___x_599_ = l_Lean_Syntax_node3(v___x_524_, v___x_583_, v___x_592_, v___x_596_, v___x_598_);
v___x_600_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__59));
v___x_601_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_601_, 0, v___x_524_);
lean_ctor_set(v___x_601_, 1, v___x_600_);
v___x_602_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__61, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__61_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__61);
v___x_603_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__62));
v___x_604_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_604_, 0, v___x_524_);
lean_ctor_set(v___x_604_, 1, v___x_602_);
lean_ctor_set(v___x_604_, 2, v___x_603_);
lean_ctor_set(v___x_604_, 3, v___x_562_);
lean_inc_ref_n(v___x_604_, 5);
lean_inc_ref_n(v___x_601_, 10);
v___x_605_ = l_Lean_Syntax_node3(v___x_524_, v___x_582_, v___x_599_, v___x_601_, v___x_604_);
v___x_606_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__63));
v___x_607_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_524_);
lean_ctor_set(v___x_607_, 1, v___x_606_);
v___x_608_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__65, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__65_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__65);
v___x_609_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__66));
v___x_610_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_610_, 0, v___x_524_);
lean_ctor_set(v___x_610_, 1, v___x_608_);
lean_ctor_set(v___x_610_, 2, v___x_609_);
lean_ctor_set(v___x_610_, 3, v___x_562_);
lean_inc_ref_n(v___x_610_, 5);
v___x_611_ = l_Lean_Syntax_node2(v___x_524_, v___x_593_, v___x_595_, v___x_610_);
lean_inc_ref_n(v___x_607_, 10);
v___x_612_ = l_Lean_Syntax_node3(v___x_524_, v___x_581_, v___x_605_, v___x_607_, v___x_611_);
v___x_613_ = l_Lean_Syntax_node2(v___x_524_, v___x_580_, v___x_574_, v___x_612_);
v___x_614_ = l_Lean_Syntax_node2(v___x_524_, v___x_565_, v___x_579_, v___x_613_);
v___x_615_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__68));
v___x_616_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__69));
v___x_617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_524_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__71, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__71_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__71);
v___x_619_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__72));
v___x_620_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_620_, 0, v___x_524_);
lean_ctor_set(v___x_620_, 1, v___x_618_);
lean_ctor_set(v___x_620_, 2, v___x_619_);
lean_ctor_set(v___x_620_, 3, v___x_562_);
v___x_621_ = l_Lean_Syntax_node3(v___x_524_, v___x_583_, v___x_592_, v___x_620_, v___x_598_);
v___x_622_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__75));
v___x_623_ = l_Lean_Syntax_node2(v___x_524_, v___x_622_, v___x_533_, v___x_533_);
lean_inc(v___x_623_);
lean_inc_ref(v___x_617_);
v___x_624_ = l_Lean_Syntax_node4(v___x_524_, v___x_615_, v___x_617_, v___x_621_, v___x_623_, v___x_533_);
lean_inc_n(v___x_624_, 5);
lean_inc_ref_n(v___x_558_, 10);
v___x_625_ = l_Lean_Syntax_node4(v___x_524_, v___x_557_, v___x_558_, v___x_564_, v___x_614_, v___x_624_);
lean_inc_n(v___x_555_, 10);
v___x_626_ = l_Lean_Syntax_node2(v___x_524_, v___x_530_, v___x_555_, v___x_625_);
v___x_627_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__77);
v___x_628_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__78));
v___x_629_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_629_, 0, v___x_524_);
lean_ctor_set(v___x_629_, 1, v___x_627_);
lean_ctor_set(v___x_629_, 2, v___x_628_);
lean_ctor_set(v___x_629_, 3, v___x_562_);
v___x_630_ = l_Lean_Syntax_node2(v___x_524_, v___x_559_, v___x_629_, v___x_533_);
v___x_631_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__80));
v___x_632_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__82, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__82_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__82);
v___x_633_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__83));
v___x_634_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_634_, 0, v___x_524_);
lean_ctor_set(v___x_634_, 1, v___x_632_);
lean_ctor_set(v___x_634_, 2, v___x_633_);
lean_ctor_set(v___x_634_, 3, v___x_562_);
lean_inc_ref_n(v___x_634_, 5);
v___x_635_ = l_Lean_Syntax_node2(v___x_524_, v___x_525_, v___x_571_, v___x_634_);
v___x_636_ = l_Lean_Syntax_node5(v___x_524_, v___x_631_, v___x_586_, v___x_635_, v___x_575_, v___x_533_, v___x_598_);
v___x_637_ = l_Lean_Syntax_node1(v___x_524_, v___x_525_, v___x_636_);
v___x_638_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__85));
v___x_639_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__86));
v___x_640_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_640_, 0, v___x_524_);
lean_ctor_set(v___x_640_, 1, v___x_639_);
lean_inc_ref_n(v___x_640_, 2);
v___x_641_ = l_Lean_Syntax_node3(v___x_524_, v___x_638_, v___x_571_, v___x_640_, v___x_634_);
v___x_642_ = l_Lean_Syntax_node3(v___x_524_, v___x_583_, v___x_592_, v___x_641_, v___x_598_);
lean_inc(v___x_642_);
v___x_643_ = l_Lean_Syntax_node3(v___x_524_, v___x_582_, v___x_642_, v___x_601_, v___x_604_);
v___x_644_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__88, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__88_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__88);
v___x_645_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__89));
v___x_646_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_646_, 0, v___x_524_);
lean_ctor_set(v___x_646_, 1, v___x_644_);
lean_ctor_set(v___x_646_, 2, v___x_645_);
lean_ctor_set(v___x_646_, 3, v___x_562_);
lean_inc_ref_n(v___x_646_, 3);
v___x_647_ = l_Lean_Syntax_node3(v___x_524_, v___x_638_, v___x_610_, v___x_640_, v___x_646_);
v___x_648_ = l_Lean_Syntax_node3(v___x_524_, v___x_581_, v___x_643_, v___x_607_, v___x_647_);
v___x_649_ = l_Lean_Syntax_node2(v___x_524_, v___x_580_, v___x_574_, v___x_648_);
lean_inc_n(v___x_637_, 9);
v___x_650_ = l_Lean_Syntax_node2(v___x_524_, v___x_565_, v___x_637_, v___x_649_);
v___x_651_ = l_Lean_Syntax_node4(v___x_524_, v___x_557_, v___x_558_, v___x_630_, v___x_650_, v___x_624_);
v___x_652_ = l_Lean_Syntax_node2(v___x_524_, v___x_530_, v___x_555_, v___x_651_);
v___x_653_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__91);
v___x_654_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__92));
v___x_655_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_655_, 0, v___x_524_);
lean_ctor_set(v___x_655_, 1, v___x_653_);
lean_ctor_set(v___x_655_, 2, v___x_654_);
lean_ctor_set(v___x_655_, 3, v___x_562_);
v___x_656_ = l_Lean_Syntax_node2(v___x_524_, v___x_559_, v___x_655_, v___x_533_);
v___x_657_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__94));
v___x_658_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__95));
v___x_659_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_659_, 0, v___x_524_);
lean_ctor_set(v___x_659_, 1, v___x_658_);
lean_inc_ref_n(v___x_659_, 2);
v___x_660_ = l_Lean_Syntax_node3(v___x_524_, v___x_657_, v___x_571_, v___x_659_, v___x_634_);
v___x_661_ = l_Lean_Syntax_node3(v___x_524_, v___x_583_, v___x_592_, v___x_660_, v___x_598_);
lean_inc(v___x_661_);
v___x_662_ = l_Lean_Syntax_node3(v___x_524_, v___x_582_, v___x_661_, v___x_601_, v___x_604_);
v___x_663_ = l_Lean_Syntax_node3(v___x_524_, v___x_657_, v___x_610_, v___x_659_, v___x_646_);
v___x_664_ = l_Lean_Syntax_node3(v___x_524_, v___x_581_, v___x_662_, v___x_607_, v___x_663_);
v___x_665_ = l_Lean_Syntax_node2(v___x_524_, v___x_580_, v___x_574_, v___x_664_);
v___x_666_ = l_Lean_Syntax_node2(v___x_524_, v___x_565_, v___x_637_, v___x_665_);
v___x_667_ = l_Lean_Syntax_node4(v___x_524_, v___x_557_, v___x_558_, v___x_656_, v___x_666_, v___x_624_);
v___x_668_ = l_Lean_Syntax_node2(v___x_524_, v___x_530_, v___x_555_, v___x_667_);
v___x_669_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__97);
v___x_670_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__98));
v___x_671_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_671_, 0, v___x_524_);
lean_ctor_set(v___x_671_, 1, v___x_669_);
lean_ctor_set(v___x_671_, 2, v___x_670_);
lean_ctor_set(v___x_671_, 3, v___x_562_);
v___x_672_ = l_Lean_Syntax_node2(v___x_524_, v___x_559_, v___x_671_, v___x_533_);
v___x_673_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__100));
v___x_674_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__101));
v___x_675_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_675_, 0, v___x_524_);
lean_ctor_set(v___x_675_, 1, v___x_674_);
lean_inc_ref_n(v___x_675_, 2);
v___x_676_ = l_Lean_Syntax_node3(v___x_524_, v___x_673_, v___x_571_, v___x_675_, v___x_634_);
v___x_677_ = l_Lean_Syntax_node3(v___x_524_, v___x_583_, v___x_592_, v___x_676_, v___x_598_);
lean_inc(v___x_677_);
v___x_678_ = l_Lean_Syntax_node3(v___x_524_, v___x_582_, v___x_677_, v___x_601_, v___x_604_);
v___x_679_ = l_Lean_Syntax_node3(v___x_524_, v___x_673_, v___x_610_, v___x_675_, v___x_646_);
v___x_680_ = l_Lean_Syntax_node3(v___x_524_, v___x_581_, v___x_678_, v___x_607_, v___x_679_);
v___x_681_ = l_Lean_Syntax_node2(v___x_524_, v___x_580_, v___x_574_, v___x_680_);
v___x_682_ = l_Lean_Syntax_node2(v___x_524_, v___x_565_, v___x_637_, v___x_681_);
v___x_683_ = l_Lean_Syntax_node4(v___x_524_, v___x_557_, v___x_558_, v___x_672_, v___x_682_, v___x_624_);
v___x_684_ = l_Lean_Syntax_node2(v___x_524_, v___x_530_, v___x_555_, v___x_683_);
v___x_685_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__103, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__103_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__103);
v___x_686_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__104));
v___x_687_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_687_, 0, v___x_524_);
lean_ctor_set(v___x_687_, 1, v___x_685_);
lean_ctor_set(v___x_687_, 2, v___x_686_);
lean_ctor_set(v___x_687_, 3, v___x_562_);
v___x_688_ = l_Lean_Syntax_node2(v___x_524_, v___x_559_, v___x_687_, v___x_533_);
v___x_689_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__106));
v___x_690_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__107));
v___x_691_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_691_, 0, v___x_524_);
lean_ctor_set(v___x_691_, 1, v___x_690_);
lean_inc_ref_n(v___x_691_, 2);
v___x_692_ = l_Lean_Syntax_node3(v___x_524_, v___x_689_, v___x_571_, v___x_691_, v___x_634_);
v___x_693_ = l_Lean_Syntax_node3(v___x_524_, v___x_583_, v___x_592_, v___x_692_, v___x_598_);
lean_inc(v___x_693_);
v___x_694_ = l_Lean_Syntax_node3(v___x_524_, v___x_582_, v___x_693_, v___x_601_, v___x_604_);
v___x_695_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__109));
v___x_696_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__110));
v___x_697_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_697_, 0, v___x_524_);
lean_ctor_set(v___x_697_, 1, v___x_696_);
lean_inc_n(v___x_519_, 2);
lean_inc_ref_n(v___x_697_, 2);
v___x_698_ = l_Lean_Syntax_node3(v___x_524_, v___x_695_, v___x_646_, v___x_697_, v___x_519_);
v___x_699_ = l_Lean_Syntax_node3(v___x_524_, v___x_583_, v___x_592_, v___x_698_, v___x_598_);
lean_inc(v___x_699_);
v___x_700_ = l_Lean_Syntax_node3(v___x_524_, v___x_689_, v___x_610_, v___x_691_, v___x_699_);
v___x_701_ = l_Lean_Syntax_node3(v___x_524_, v___x_581_, v___x_694_, v___x_607_, v___x_700_);
v___x_702_ = l_Lean_Syntax_node2(v___x_524_, v___x_580_, v___x_574_, v___x_701_);
v___x_703_ = l_Lean_Syntax_node2(v___x_524_, v___x_565_, v___x_637_, v___x_702_);
v___x_704_ = l_Lean_Syntax_node4(v___x_524_, v___x_557_, v___x_558_, v___x_688_, v___x_703_, v___x_624_);
v___x_705_ = l_Lean_Syntax_node2(v___x_524_, v___x_530_, v___x_555_, v___x_704_);
v___x_706_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__112);
v___x_707_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__113));
v___x_708_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_708_, 0, v___x_524_);
lean_ctor_set(v___x_708_, 1, v___x_706_);
lean_ctor_set(v___x_708_, 2, v___x_707_);
lean_ctor_set(v___x_708_, 3, v___x_562_);
v___x_709_ = l_Lean_Syntax_node2(v___x_524_, v___x_559_, v___x_708_, v___x_533_);
v___x_710_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__115));
v___x_711_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__116));
v___x_712_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_712_, 0, v___x_524_);
lean_ctor_set(v___x_712_, 1, v___x_711_);
lean_inc_ref_n(v___x_712_, 2);
v___x_713_ = l_Lean_Syntax_node3(v___x_524_, v___x_710_, v___x_571_, v___x_712_, v___x_634_);
v___x_714_ = l_Lean_Syntax_node3(v___x_524_, v___x_583_, v___x_592_, v___x_713_, v___x_598_);
lean_inc(v___x_714_);
v___x_715_ = l_Lean_Syntax_node3(v___x_524_, v___x_582_, v___x_714_, v___x_601_, v___x_604_);
v___x_716_ = l_Lean_Syntax_node3(v___x_524_, v___x_710_, v___x_610_, v___x_712_, v___x_699_);
v___x_717_ = l_Lean_Syntax_node3(v___x_524_, v___x_581_, v___x_715_, v___x_607_, v___x_716_);
v___x_718_ = l_Lean_Syntax_node2(v___x_524_, v___x_580_, v___x_574_, v___x_717_);
v___x_719_ = l_Lean_Syntax_node2(v___x_524_, v___x_565_, v___x_637_, v___x_718_);
v___x_720_ = l_Lean_Syntax_node4(v___x_524_, v___x_557_, v___x_558_, v___x_709_, v___x_719_, v___x_624_);
v___x_721_ = l_Lean_Syntax_node2(v___x_524_, v___x_530_, v___x_555_, v___x_720_);
v___x_722_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__118, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__118_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__118);
v___x_723_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__119));
v___x_724_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_724_, 0, v___x_524_);
lean_ctor_set(v___x_724_, 1, v___x_722_);
lean_ctor_set(v___x_724_, 2, v___x_723_);
lean_ctor_set(v___x_724_, 3, v___x_562_);
v___x_725_ = l_Lean_Syntax_node2(v___x_524_, v___x_559_, v___x_724_, v___x_533_);
v___x_726_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__121);
v___x_727_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__122));
v___x_728_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_728_, 0, v___x_524_);
lean_ctor_set(v___x_728_, 1, v___x_726_);
lean_ctor_set(v___x_728_, 2, v___x_727_);
lean_ctor_set(v___x_728_, 3, v___x_562_);
lean_inc_ref_n(v___x_728_, 5);
v___x_729_ = l_Lean_Syntax_node3(v___x_524_, v___x_582_, v___x_642_, v___x_601_, v___x_728_);
v___x_730_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__124, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__124_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__124);
v___x_731_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__125));
v___x_732_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_732_, 0, v___x_524_);
lean_ctor_set(v___x_732_, 1, v___x_730_);
lean_ctor_set(v___x_732_, 2, v___x_731_);
lean_ctor_set(v___x_732_, 3, v___x_562_);
v___x_733_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__127);
v___x_734_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__128));
v___x_735_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_735_, 0, v___x_524_);
lean_ctor_set(v___x_735_, 1, v___x_733_);
lean_ctor_set(v___x_735_, 2, v___x_734_);
lean_ctor_set(v___x_735_, 3, v___x_562_);
lean_inc_ref_n(v___x_735_, 3);
lean_inc_ref_n(v___x_732_, 4);
v___x_736_ = l_Lean_Syntax_node3(v___x_524_, v___x_638_, v___x_732_, v___x_640_, v___x_735_);
v___x_737_ = l_Lean_Syntax_node3(v___x_524_, v___x_581_, v___x_729_, v___x_607_, v___x_736_);
v___x_738_ = l_Lean_Syntax_node2(v___x_524_, v___x_580_, v___x_574_, v___x_737_);
v___x_739_ = l_Lean_Syntax_node2(v___x_524_, v___x_565_, v___x_637_, v___x_738_);
v___x_740_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__130));
v___x_741_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__131));
v___x_742_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_742_, 0, v___x_524_);
lean_ctor_set(v___x_742_, 1, v___x_741_);
v___x_743_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__134));
v___x_744_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__136));
v___x_745_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__137));
v___x_746_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__139));
v___x_747_ = l_Lean_Syntax_node1(v___x_524_, v___x_746_, v___x_533_);
v___x_748_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__140));
v___x_749_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_749_, 0, v___x_524_);
lean_ctor_set(v___x_749_, 1, v___x_748_);
v___x_750_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__142));
v___x_751_ = l_Lean_Syntax_node3(v___x_524_, v___x_750_, v___x_533_, v___x_533_, v___x_728_);
v___x_752_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__143));
v___x_753_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_524_);
lean_ctor_set(v___x_753_, 1, v___x_752_);
v___x_754_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__145));
v___x_755_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__146));
v___x_756_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_524_);
lean_ctor_set(v___x_756_, 1, v___x_755_);
v___x_757_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__148);
v___x_758_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__149));
v___x_759_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_759_, 0, v___x_524_);
lean_ctor_set(v___x_759_, 1, v___x_757_);
lean_ctor_set(v___x_759_, 2, v___x_758_);
lean_ctor_set(v___x_759_, 3, v___x_562_);
v___x_760_ = l_Lean_Syntax_node2(v___x_524_, v___x_754_, v___x_756_, v___x_759_);
v___x_761_ = l_Lean_Syntax_node3(v___x_524_, v___x_525_, v___x_751_, v___x_753_, v___x_760_);
v___x_762_ = l_Lean_Syntax_node3(v___x_524_, v___x_525_, v___x_749_, v___x_761_, v___x_547_);
v___x_763_ = l_Lean_Syntax_node6(v___x_524_, v___x_745_, v___x_542_, v___x_747_, v___x_533_, v___x_533_, v___x_762_, v___x_533_);
v___x_764_ = l_Lean_Syntax_node1(v___x_524_, v___x_525_, v___x_763_);
v___x_765_ = l_Lean_Syntax_node1(v___x_524_, v___x_744_, v___x_764_);
v___x_766_ = l_Lean_Syntax_node1(v___x_524_, v___x_743_, v___x_765_);
v___x_767_ = l_Lean_Syntax_node2(v___x_524_, v___x_740_, v___x_742_, v___x_766_);
v___x_768_ = l_Lean_Syntax_node4(v___x_524_, v___x_615_, v___x_617_, v___x_767_, v___x_623_, v___x_533_);
lean_inc_n(v___x_768_, 4);
v___x_769_ = l_Lean_Syntax_node4(v___x_524_, v___x_557_, v___x_558_, v___x_725_, v___x_739_, v___x_768_);
v___x_770_ = l_Lean_Syntax_node2(v___x_524_, v___x_530_, v___x_555_, v___x_769_);
v___x_771_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__151);
v___x_772_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__152));
v___x_773_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_773_, 0, v___x_524_);
lean_ctor_set(v___x_773_, 1, v___x_771_);
lean_ctor_set(v___x_773_, 2, v___x_772_);
lean_ctor_set(v___x_773_, 3, v___x_562_);
v___x_774_ = l_Lean_Syntax_node2(v___x_524_, v___x_559_, v___x_773_, v___x_533_);
v___x_775_ = l_Lean_Syntax_node3(v___x_524_, v___x_582_, v___x_661_, v___x_601_, v___x_728_);
v___x_776_ = l_Lean_Syntax_node3(v___x_524_, v___x_657_, v___x_732_, v___x_659_, v___x_735_);
v___x_777_ = l_Lean_Syntax_node3(v___x_524_, v___x_581_, v___x_775_, v___x_607_, v___x_776_);
v___x_778_ = l_Lean_Syntax_node2(v___x_524_, v___x_580_, v___x_574_, v___x_777_);
v___x_779_ = l_Lean_Syntax_node2(v___x_524_, v___x_565_, v___x_637_, v___x_778_);
v___x_780_ = l_Lean_Syntax_node4(v___x_524_, v___x_557_, v___x_558_, v___x_774_, v___x_779_, v___x_768_);
v___x_781_ = l_Lean_Syntax_node2(v___x_524_, v___x_530_, v___x_555_, v___x_780_);
v___x_782_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__154, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__154_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__154);
v___x_783_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__155));
v___x_784_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_784_, 0, v___x_524_);
lean_ctor_set(v___x_784_, 1, v___x_782_);
lean_ctor_set(v___x_784_, 2, v___x_783_);
lean_ctor_set(v___x_784_, 3, v___x_562_);
v___x_785_ = l_Lean_Syntax_node2(v___x_524_, v___x_559_, v___x_784_, v___x_533_);
v___x_786_ = l_Lean_Syntax_node3(v___x_524_, v___x_582_, v___x_677_, v___x_601_, v___x_728_);
v___x_787_ = l_Lean_Syntax_node3(v___x_524_, v___x_673_, v___x_732_, v___x_675_, v___x_735_);
v___x_788_ = l_Lean_Syntax_node3(v___x_524_, v___x_581_, v___x_786_, v___x_607_, v___x_787_);
v___x_789_ = l_Lean_Syntax_node2(v___x_524_, v___x_580_, v___x_574_, v___x_788_);
v___x_790_ = l_Lean_Syntax_node2(v___x_524_, v___x_565_, v___x_637_, v___x_789_);
v___x_791_ = l_Lean_Syntax_node4(v___x_524_, v___x_557_, v___x_558_, v___x_785_, v___x_790_, v___x_768_);
v___x_792_ = l_Lean_Syntax_node2(v___x_524_, v___x_530_, v___x_555_, v___x_791_);
v___x_793_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__157, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__157_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__157);
v___x_794_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__158));
v___x_795_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_795_, 0, v___x_524_);
lean_ctor_set(v___x_795_, 1, v___x_793_);
lean_ctor_set(v___x_795_, 2, v___x_794_);
lean_ctor_set(v___x_795_, 3, v___x_562_);
v___x_796_ = l_Lean_Syntax_node2(v___x_524_, v___x_559_, v___x_795_, v___x_533_);
v___x_797_ = l_Lean_Syntax_node3(v___x_524_, v___x_582_, v___x_693_, v___x_601_, v___x_728_);
v___x_798_ = l_Lean_Syntax_node3(v___x_524_, v___x_695_, v___x_735_, v___x_697_, v___x_519_);
v___x_799_ = l_Lean_Syntax_node3(v___x_524_, v___x_583_, v___x_592_, v___x_798_, v___x_598_);
lean_inc(v___x_799_);
v___x_800_ = l_Lean_Syntax_node3(v___x_524_, v___x_689_, v___x_732_, v___x_691_, v___x_799_);
v___x_801_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__160));
v___x_802_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__162));
v___x_803_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__163));
v___x_804_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_524_);
lean_ctor_set(v___x_804_, 1, v___x_803_);
v___x_805_ = l_Lean_Syntax_node1(v___x_524_, v___x_802_, v___x_804_);
v___x_806_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__164));
v___x_807_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_807_, 0, v___x_524_);
lean_ctor_set(v___x_807_, 1, v___x_806_);
v___x_808_ = l_Lean_Syntax_node3(v___x_524_, v___x_801_, v___x_805_, v___x_807_, v___x_519_);
v___x_809_ = l_Lean_Syntax_node3(v___x_524_, v___x_695_, v___x_800_, v___x_697_, v___x_808_);
v___x_810_ = l_Lean_Syntax_node3(v___x_524_, v___x_581_, v___x_797_, v___x_607_, v___x_809_);
v___x_811_ = l_Lean_Syntax_node2(v___x_524_, v___x_580_, v___x_574_, v___x_810_);
v___x_812_ = l_Lean_Syntax_node2(v___x_524_, v___x_565_, v___x_637_, v___x_811_);
v___x_813_ = l_Lean_Syntax_node4(v___x_524_, v___x_557_, v___x_558_, v___x_796_, v___x_812_, v___x_768_);
v___x_814_ = l_Lean_Syntax_node2(v___x_524_, v___x_530_, v___x_555_, v___x_813_);
v___x_815_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__166, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__166_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__166);
v___x_816_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__167));
v___x_817_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_817_, 0, v___x_524_);
lean_ctor_set(v___x_817_, 1, v___x_815_);
lean_ctor_set(v___x_817_, 2, v___x_816_);
lean_ctor_set(v___x_817_, 3, v___x_562_);
v___x_818_ = l_Lean_Syntax_node2(v___x_524_, v___x_559_, v___x_817_, v___x_533_);
v___x_819_ = l_Lean_Syntax_node3(v___x_524_, v___x_582_, v___x_714_, v___x_601_, v___x_728_);
v___x_820_ = l_Lean_Syntax_node3(v___x_524_, v___x_710_, v___x_732_, v___x_712_, v___x_799_);
v___x_821_ = l_Lean_Syntax_node3(v___x_524_, v___x_581_, v___x_819_, v___x_607_, v___x_820_);
v___x_822_ = l_Lean_Syntax_node2(v___x_524_, v___x_580_, v___x_574_, v___x_821_);
v___x_823_ = l_Lean_Syntax_node2(v___x_524_, v___x_565_, v___x_637_, v___x_822_);
v___x_824_ = l_Lean_Syntax_node4(v___x_524_, v___x_557_, v___x_558_, v___x_818_, v___x_823_, v___x_768_);
v___x_825_ = l_Lean_Syntax_node2(v___x_524_, v___x_530_, v___x_555_, v___x_824_);
v___x_826_ = lean_unsigned_to_nat(12u);
v___x_827_ = lean_mk_empty_array_with_capacity(v___x_826_);
v___x_828_ = lean_array_push(v___x_827_, v___x_529_);
v___x_829_ = lean_array_push(v___x_828_, v___x_626_);
v___x_830_ = lean_array_push(v___x_829_, v___x_652_);
v___x_831_ = lean_array_push(v___x_830_, v___x_668_);
v___x_832_ = lean_array_push(v___x_831_, v___x_684_);
v___x_833_ = lean_array_push(v___x_832_, v___x_705_);
v___x_834_ = lean_array_push(v___x_833_, v___x_721_);
v___x_835_ = lean_array_push(v___x_834_, v___x_770_);
v___x_836_ = lean_array_push(v___x_835_, v___x_781_);
v___x_837_ = lean_array_push(v___x_836_, v___x_792_);
v___x_838_ = lean_array_push(v___x_837_, v___x_814_);
v___x_839_ = lean_array_push(v___x_838_, v___x_825_);
v___x_840_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_840_, 0, v___x_524_);
lean_ctor_set(v___x_840_, 1, v___x_525_);
lean_ctor_set(v___x_840_, 2, v___x_839_);
v___x_841_ = l_Lean_Syntax_getArgs(v___x_840_);
lean_dec_ref_known(v___x_840_, 3);
if (v_isUSize_522_ == 0)
{
lean_object* v___x_842_; lean_object* v_a_843_; lean_object* v_a_844_; lean_object* v___x_846_; uint8_t v_isShared_847_; uint8_t v_isSharedCheck_874_; 
v___x_842_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__0(v_ref_514_, v_a_488_, v_a_489_);
v_a_843_ = lean_ctor_get(v___x_842_, 0);
v_a_844_ = lean_ctor_get(v___x_842_, 1);
v_isSharedCheck_874_ = !lean_is_exclusive(v___x_842_);
if (v_isSharedCheck_874_ == 0)
{
v___x_846_ = v___x_842_;
v_isShared_847_ = v_isSharedCheck_874_;
goto v_resetjp_845_;
}
else
{
lean_inc(v_a_844_);
lean_inc(v_a_843_);
lean_dec(v___x_842_);
v___x_846_ = lean_box(0);
v_isShared_847_ = v_isSharedCheck_874_;
goto v_resetjp_845_;
}
v_resetjp_845_:
{
lean_object* v___x_848_; size_t v_sz_849_; size_t v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_855_; 
v___x_848_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__168));
v_sz_849_ = lean_usize_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__169, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__169_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__169);
v___x_850_ = ((size_t)0ULL);
v___x_851_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1_spec__0(v___x_520_, v_sz_849_, v___x_850_, v___x_848_);
v___x_852_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__170));
v___x_853_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__171));
lean_inc(v_a_843_);
if (v_isShared_847_ == 0)
{
lean_ctor_set_tag(v___x_846_, 2);
lean_ctor_set(v___x_846_, 1, v___x_852_);
v___x_855_ = v___x_846_;
goto v_reusejp_854_;
}
else
{
lean_object* v_reuseFailAlloc_873_; 
v_reuseFailAlloc_873_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_873_, 0, v_a_843_);
lean_ctor_set(v_reuseFailAlloc_873_, 1, v___x_852_);
v___x_855_ = v_reuseFailAlloc_873_;
goto v_reusejp_854_;
}
v_reusejp_854_:
{
lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; 
lean_inc_n(v_a_843_, 9);
v___x_856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_856_, 0, v_a_843_);
lean_ctor_set(v___x_856_, 1, v___x_748_);
v___x_857_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_857_, 0, v_a_843_);
lean_ctor_set(v___x_857_, 1, v___x_525_);
lean_ctor_set(v___x_857_, 2, v___x_532_);
lean_inc_ref(v___x_857_);
v___x_858_ = l_Lean_Syntax_node1(v_a_843_, v___x_538_, v___x_857_);
v___x_859_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__173));
v___x_860_ = lean_obj_once(&l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__175, &l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__175_once, _init_l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__175);
v___x_861_ = ((lean_object*)(l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___closed__176));
v___x_862_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_862_, 0, v_a_843_);
lean_ctor_set(v___x_862_, 1, v___x_860_);
lean_ctor_set(v___x_862_, 2, v___x_861_);
lean_ctor_set(v___x_862_, 3, v___x_562_);
v___x_863_ = l_Lean_Syntax_node2(v_a_843_, v___x_859_, v___x_862_, v___x_857_);
v___x_864_ = l_Lean_Syntax_node2(v_a_843_, v___x_537_, v___x_858_, v___x_863_);
v___x_865_ = l_Lean_Syntax_node1(v_a_843_, v___x_525_, v___x_864_);
v___x_866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_866_, 0, v_a_843_);
lean_ctor_set(v___x_866_, 1, v___x_546_);
v___x_867_ = l_Array_append___redArg(v___x_532_, v___x_851_);
lean_dec_ref(v___x_851_);
v___x_868_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_868_, 0, v_a_843_);
lean_ctor_set(v___x_868_, 1, v___x_525_);
lean_ctor_set(v___x_868_, 2, v___x_867_);
v___x_869_ = l_Lean_Syntax_node5(v_a_843_, v___x_853_, v___x_855_, v___x_856_, v___x_865_, v___x_866_, v___x_868_);
v___x_870_ = lean_array_push(v___x_841_, v___x_869_);
v___x_871_ = lean_box(0);
v___x_872_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1(v___f_515_, v_typeName_517_, v___x_871_, v___x_870_, v_a_488_, v_a_844_);
v___y_491_ = v___x_872_;
goto v___jp_490_;
}
}
}
else
{
lean_object* v___x_875_; lean_object* v___x_876_; 
lean_dec(v___x_520_);
v___x_875_ = lean_box(0);
v___x_876_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___lam__1(v___f_515_, v_typeName_517_, v___x_875_, v___x_841_, v_a_488_, v_a_489_);
v___y_491_ = v___x_876_;
goto v___jp_490_;
}
}
v___jp_490_:
{
if (lean_obj_tag(v___y_491_) == 0)
{
lean_object* v_a_492_; lean_object* v_a_493_; lean_object* v___x_495_; uint8_t v_isShared_496_; uint8_t v_isSharedCheck_500_; 
v_a_492_ = lean_ctor_get(v___y_491_, 0);
v_a_493_ = lean_ctor_get(v___y_491_, 1);
v_isSharedCheck_500_ = !lean_is_exclusive(v___y_491_);
if (v_isSharedCheck_500_ == 0)
{
v___x_495_ = v___y_491_;
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
else
{
lean_inc(v_a_493_);
lean_inc(v_a_492_);
lean_dec(v___y_491_);
v___x_495_ = lean_box(0);
v_isShared_496_ = v_isSharedCheck_500_;
goto v_resetjp_494_;
}
v_resetjp_494_:
{
lean_object* v___x_498_; 
if (v_isShared_496_ == 0)
{
v___x_498_ = v___x_495_;
goto v_reusejp_497_;
}
else
{
lean_object* v_reuseFailAlloc_499_; 
v_reuseFailAlloc_499_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_499_, 0, v_a_492_);
lean_ctor_set(v_reuseFailAlloc_499_, 1, v_a_493_);
v___x_498_ = v_reuseFailAlloc_499_;
goto v_reusejp_497_;
}
v_reusejp_497_:
{
return v___x_498_;
}
}
}
else
{
lean_object* v_a_501_; lean_object* v_a_502_; lean_object* v___x_504_; uint8_t v_isShared_505_; uint8_t v_isSharedCheck_509_; 
v_a_501_ = lean_ctor_get(v___y_491_, 0);
v_a_502_ = lean_ctor_get(v___y_491_, 1);
v_isSharedCheck_509_ = !lean_is_exclusive(v___y_491_);
if (v_isSharedCheck_509_ == 0)
{
v___x_504_ = v___y_491_;
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
else
{
lean_inc(v_a_502_);
lean_inc(v_a_501_);
lean_dec(v___y_491_);
v___x_504_ = lean_box(0);
v_isShared_505_ = v_isSharedCheck_509_;
goto v_resetjp_503_;
}
v_resetjp_503_:
{
lean_object* v___x_507_; 
if (v_isShared_505_ == 0)
{
v___x_507_ = v___x_504_;
goto v_reusejp_506_;
}
else
{
lean_object* v_reuseFailAlloc_508_; 
v_reuseFailAlloc_508_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_508_, 0, v_a_501_);
lean_ctor_set(v_reuseFailAlloc_508_, 1, v_a_502_);
v___x_507_ = v_reuseFailAlloc_508_;
goto v_reusejp_506_;
}
v_reusejp_506_:
{
return v___x_507_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1___boxed(lean_object* v_x_877_, lean_object* v_a_878_, lean_object* v_a_879_){
_start:
{
lean_object* v_res_880_; 
v_res_880_ = l___aux__Init__Data__UInt__Bitwise______macroRules__commandDeclare__bitwise__uint__theorems______1(v_x_877_, v_a_878_, v_a_879_);
lean_dec_ref(v_a_878_);
return v_res_880_;
}
}
lean_object* runtime_initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Ext(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Fin_Bitwise(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_System_Platform(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_UInt_Bitwise(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Fin_Bitwise(builtin);
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
LEAN_EXPORT lean_object* meta_initialize_Init_Data_UInt_Bitwise(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_BitVec_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Bitwise(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Basic(uint8_t builtin);
lean_object* initialize_Init_Ext(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_BitVec_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Fin_Bitwise(uint8_t builtin);
lean_object* initialize_Init_Data_UInt_Lemmas(uint8_t builtin);
lean_object* initialize_Init_System_Platform(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_UInt_Bitwise(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_BitVec_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Ext(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_BitVec_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Fin_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_UInt_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_System_Platform(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_UInt_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_UInt_Bitwise(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_UInt_Bitwise(builtin);
}
#ifdef __cplusplus
}
#endif
