// Lean compiler output
// Module: Std.Do.PostCond
// Imports: public import Std.Do.SPred
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
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_SPred_pure___redArg(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_SPred_and(lean_object*, lean_object*, lean_object*);
lean_object* l_Std_Do_SVal_curry___redArg(lean_object*, lean_object*);
lean_object* l_Std_Do_SPred_imp(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
lean_object* l_Array_mkArray0___redArg();
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorIdx___impl(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_pure_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_pure_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_arg_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_arg_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_except_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_except_elim(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_args(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_args___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_true(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_false(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedExceptConds(lean_object*);
static const lean_string_object l_Std_Do_term___u22a2_u2091___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "Std"};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__0 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value;
static const lean_string_object l_Std_Do_term___u22a2_u2091___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "Do"};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__1 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value;
static const lean_string_object l_Std_Do_term___u22a2_u2091___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 8, .m_data = "term_⊢ₑ_"};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__2 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__2_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term___u22a2_u2091___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__3_value_aux_1),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(47, 206, 144, 176, 166, 201, 195, 83)}};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__3 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__3_value;
static const lean_string_object l_Std_Do_term___u22a2_u2091___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__4 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__4_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u2091___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__5 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value;
static const lean_string_object l_Std_Do_term___u22a2_u2091___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 4, .m_data = " ⊢ₑ "};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__6 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__6_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u2091___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__6_value)}};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__7 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__7_value;
static const lean_string_object l_Std_Do_term___u22a2_u2091___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__8 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__8_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u2091___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__8_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__9 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__9_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u2091___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__9_value),((lean_object*)(((size_t)(25) << 1) | 1))}};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__10 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__10_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u2091___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__7_value),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__10_value)}};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__11 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__11_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u2091___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__3_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__11_value)}};
static const lean_object* l_Std_Do_term___u22a2_u2091___00__closed__12 = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__12_value;
LEAN_EXPORT const lean_object* l_Std_Do_term___u22a2_u2091__ = (const lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__12_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "ExceptConds.entails"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "ExceptConds"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "entails"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(139, 147, 12, 12, 50, 62, 178, 236)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(163, 170, 0, 37, 49, 213, 239, 188)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(72, 205, 41, 157, 129, 142, 231, 99)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__10_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__12_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__11_value),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__13_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__15_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_ExceptConds_entails_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_ExceptConds_entails_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_PostShape_args_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_PostShape_args_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_term___u2227_u2091___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 8, .m_data = "term_∧ₑ_"};
static const lean_object* l_Std_Do_term___u2227_u2091___00__closed__0 = (const lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__0_value;
static const lean_ctor_object l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term___u2227_u2091___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__1_value_aux_1),((lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(250, 243, 110, 99, 134, 58, 50, 162)}};
static const lean_object* l_Std_Do_term___u2227_u2091___00__closed__1 = (const lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__1_value;
static const lean_string_object l_Std_Do_term___u2227_u2091___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 4, .m_data = " ∧ₑ "};
static const lean_object* l_Std_Do_term___u2227_u2091___00__closed__2 = (const lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__2_value;
static const lean_ctor_object l_Std_Do_term___u2227_u2091___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__2_value)}};
static const lean_object* l_Std_Do_term___u2227_u2091___00__closed__3 = (const lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__3_value;
static const lean_ctor_object l_Std_Do_term___u2227_u2091___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__9_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_Std_Do_term___u2227_u2091___00__closed__4 = (const lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__4_value;
static const lean_ctor_object l_Std_Do_term___u2227_u2091___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__3_value),((lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__4_value)}};
static const lean_object* l_Std_Do_term___u2227_u2091___00__closed__5 = (const lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__5_value;
static const lean_ctor_object l_Std_Do_term___u2227_u2091___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__1_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__5_value)}};
static const lean_object* l_Std_Do_term___u2227_u2091___00__closed__6 = (const lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__6_value;
LEAN_EXPORT const lean_object* l_Std_Do_term___u2227_u2091__ = (const lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__6_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ExceptConds.and"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "and"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(139, 147, 12, 12, 50, 62, 178, 236)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(37, 171, 244, 94, 98, 193, 51, 0)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(198, 204, 155, 110, 221, 209, 121, 119)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_term___u2192_u2091___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 8, .m_data = "term_→ₑ_"};
static const lean_object* l_Std_Do_term___u2192_u2091___00__closed__0 = (const lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__0_value;
static const lean_ctor_object l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term___u2192_u2091___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__1_value_aux_1),((lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(81, 210, 122, 78, 230, 243, 132, 61)}};
static const lean_object* l_Std_Do_term___u2192_u2091___00__closed__1 = (const lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__1_value;
static const lean_string_object l_Std_Do_term___u2192_u2091___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 4, .m_data = " →ₑ "};
static const lean_object* l_Std_Do_term___u2192_u2091___00__closed__2 = (const lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__2_value;
static const lean_ctor_object l_Std_Do_term___u2192_u2091___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__2_value)}};
static const lean_object* l_Std_Do_term___u2192_u2091___00__closed__3 = (const lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__3_value;
static const lean_ctor_object l_Std_Do_term___u2192_u2091___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__3_value),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__10_value)}};
static const lean_object* l_Std_Do_term___u2192_u2091___00__closed__4 = (const lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__4_value;
static const lean_ctor_object l_Std_Do_term___u2192_u2091___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__1_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__4_value)}};
static const lean_object* l_Std_Do_term___u2192_u2091___00__closed__5 = (const lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Do_term___u2192_u2091__ = (const lean_object*)&l_Std_Do_term___u2192_u2091___00__closed__5_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 16, .m_capacity = 16, .m_length = 15, .m_data = "ExceptConds.imp"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "imp"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(139, 147, 12, 12, 50, 62, 178, 236)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(219, 146, 133, 30, 156, 110, 110, 59)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(244, 224, 84, 66, 133, 22, 35, 247)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(16, 202, 249, 243, 130, 82, 177, 96)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 13, .m_data = "termPost⟨_,,⟩"};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0_value;
static const lean_ctor_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value_aux_1),((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__0_value),LEAN_SCALAR_PTR_LITERAL(117, 45, 176, 130, 225, 239, 187, 245)}};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value;
static const lean_string_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 5, .m_data = "post⟨"};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2_value;
static const lean_ctor_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__2_value)}};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3_value;
static const lean_ctor_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value;
static const lean_string_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5_value;
static const lean_string_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6_value;
static const lean_ctor_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__6_value)}};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7_value;
static const lean_ctor_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 11}, .m_objs = {((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value),((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5_value),((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__7_value),LEAN_SCALAR_PTR_LITERAL(1, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8_value;
static const lean_ctor_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__3_value),((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__8_value)}};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9_value;
static const lean_string_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟩"};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10_value;
static const lean_ctor_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10_value)}};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11_value;
static const lean_ctor_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__9_value),((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__11_value)}};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12_value;
static const lean_ctor_object l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__12_value)}};
static const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13_value;
LEAN_EXPORT const lean_object* l_Std_Do_termPost_u27e8___x2c_x2c_u27e9 = (const lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__13_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "byTactic"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 150, 238, 148, 228, 221, 116, 224)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "by"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Tactic"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "tacticSeq"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__4_value),LEAN_SCALAR_PTR_LITERAL(212, 140, 85, 215, 241, 69, 7, 118)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "tacticSeq1Indented"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__6_value),LEAN_SCALAR_PTR_LITERAL(223, 90, 160, 238, 133, 180, 23, 239)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "exact"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(166, 58, 35, 182, 187, 130, 147, 254)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(108, 106, 111, 83, 219, 207, 32, 208)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "anonymousCtor"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(56, 53, 154, 97, 179, 232, 94, 186)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⟨"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "PUnit.unit"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "PUnit"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "unit"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__16_value),LEAN_SCALAR_PTR_LITERAL(23, 153, 158, 141, 176, 162, 235, 153)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__17_value),LEAN_SCALAR_PTR_LITERAL(146, 91, 82, 196, 249, 72, 203, 194)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__20_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__19_value),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__21_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_noThrow___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_noThrow(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 10, .m_data = "term_⇓_=>_"};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__0 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__0_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value_aux_1),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(1, 118, 219, 9, 44, 173, 117, 117)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__1 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value;
static const lean_string_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "group"};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__2 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__2_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(206, 113, 20, 57, 188, 177, 187, 30)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__3 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__3_value;
static const lean_string_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "ppAllowUngrouped"};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__4 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__4_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__4_value),LEAN_SCALAR_PTR_LITERAL(254, 56, 209, 55, 154, 125, 240, 2)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__5 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__5_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__5_value)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__6 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__6_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__3_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__6_value)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__7 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value;
static const lean_string_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 1, .m_data = "⇓"};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__8 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__8_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__8_value)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__9 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__9_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__9_value)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__10 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__10_value;
static const lean_string_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "many1"};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__11 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__11_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__11_value),LEAN_SCALAR_PTR_LITERAL(55, 136, 52, 6, 12, 19, 78, 239)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__12 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__12_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__9_value),((lean_object*)(((size_t)(1024) << 1) | 1))}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__13 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__13_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__12_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__13_value)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__14 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__10_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__15 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__15_value;
static const lean_string_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " => "};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__16 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__16_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__16_value)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__17 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__15_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__18 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__18_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__18_value),((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__19 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__19_value;
static const lean_ctor_object l_Std_Do_term___u21d3___x3d_x3e___00__closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__19_value)}};
static const lean_object* l_Std_Do_term___u21d3___x3d_x3e___00__closed__20 = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__20_value;
LEAN_EXPORT const lean_object* l_Std_Do_term___u21d3___x3d_x3e__ = (const lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__20_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "PostCond.noThrow"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "PostCond"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "noThrow"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 150, 138, 197, 137, 5, 150, 182)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(219, 88, 117, 139, 154, 102, 4, 51)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(124, 92, 27, 8, 188, 224, 25, 47)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(16, 55, 64, 24, 30, 138, 86, 160)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__6_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "paren"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(124, 9, 161, 194, 227, 100, 20, 110)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "hygienicLParen"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__10_value),LEAN_SCALAR_PTR_LITERAL(41, 104, 206, 51, 21, 254, 100, 101)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "("};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "hygieneInfo"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__13_value),LEAN_SCALAR_PTR_LITERAL(27, 64, 36, 144, 170, 151, 255, 136)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__17_value)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__18_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "fun"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20_value),LEAN_SCALAR_PTR_LITERAL(249, 155, 133, 242, 71, 132, 191, 97)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "basicFun"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__22_value),LEAN_SCALAR_PTR_LITERAL(209, 134, 40, 160, 122, 195, 31, 223)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "=>"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "termSpred(_)"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__25_value),LEAN_SCALAR_PTR_LITERAL(76, 240, 91, 148, 237, 191, 255, 193)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "spred("};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ")"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_mayThrow___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_mayThrow(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 11, .m_data = "term_⇓\?_=>_"};
static const lean_object* l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0 = (const lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0_value;
static const lean_ctor_object l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value_aux_1),((lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(84, 52, 46, 60, 233, 87, 205, 70)}};
static const lean_object* l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1 = (const lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value;
static const lean_string_object l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 2, .m_data = "⇓\?"};
static const lean_object* l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2 = (const lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2_value;
static const lean_ctor_object l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__2_value)}};
static const lean_object* l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3 = (const lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3_value;
static const lean_ctor_object l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__7_value),((lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__3_value)}};
static const lean_object* l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4 = (const lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4_value;
static const lean_ctor_object l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__4_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__14_value)}};
static const lean_object* l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5 = (const lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5_value;
static const lean_ctor_object l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__5_value),((lean_object*)&l_Std_Do_term___u21d3___x3d_x3e___00__closed__17_value)}};
static const lean_object* l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6 = (const lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6_value;
static const lean_ctor_object l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__6_value),((lean_object*)&l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__4_value)}};
static const lean_object* l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7 = (const lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7_value;
static const lean_ctor_object l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 3}, .m_objs = {((lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1_value),((lean_object*)(((size_t)(1024) << 1) | 1)),((lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__7_value)}};
static const lean_object* l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8 = (const lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8_value;
LEAN_EXPORT const lean_object* l_Std_Do_term___u21d3_x3f___x3d_x3e__ = (const lean_object*)&l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__8_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "PostCond.mayThrow"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "mayThrow"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 150, 138, 197, 137, 5, 150, 182)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 252, 207, 107, 212, 83, 11, 103)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(124, 92, 27, 8, 188, 224, 25, 47)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 136, 136, 54, 72, 103, 208, 40)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond(lean_object*, lean_object*);
static const lean_string_object l_Std_Do_term___u22a2_u209a___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 8, .m_data = "term_⊢ₚ_"};
static const lean_object* l_Std_Do_term___u22a2_u209a___00__closed__0 = (const lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__0_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term___u22a2_u209a___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__1_value_aux_1),((lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(187, 141, 203, 215, 39, 237, 75, 8)}};
static const lean_object* l_Std_Do_term___u22a2_u209a___00__closed__1 = (const lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__1_value;
static const lean_string_object l_Std_Do_term___u22a2_u209a___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 4, .m_data = " ⊢ₚ "};
static const lean_object* l_Std_Do_term___u22a2_u209a___00__closed__2 = (const lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__2_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u209a___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__2_value)}};
static const lean_object* l_Std_Do_term___u22a2_u209a___00__closed__3 = (const lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__3_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u209a___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__3_value),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__10_value)}};
static const lean_object* l_Std_Do_term___u22a2_u209a___00__closed__4 = (const lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__4_value;
static const lean_ctor_object l_Std_Do_term___u22a2_u209a___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__1_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__4_value)}};
static const lean_object* l_Std_Do_term___u22a2_u209a___00__closed__5 = (const lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Do_term___u22a2_u209a__ = (const lean_object*)&l_Std_Do_term___u22a2_u209a___00__closed__5_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "PostCond.entails"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 150, 138, 197, 137, 5, 150, 182)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(203, 216, 242, 84, 80, 15, 12, 233)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(124, 92, 27, 8, 188, 224, 25, 47)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(32, 111, 255, 27, 103, 9, 244, 9)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_term___u2227_u209a___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 8, .m_data = "term_∧ₚ_"};
static const lean_object* l_Std_Do_term___u2227_u209a___00__closed__0 = (const lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__0_value;
static const lean_ctor_object l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term___u2227_u209a___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__1_value_aux_1),((lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(86, 60, 122, 170, 196, 154, 227, 219)}};
static const lean_object* l_Std_Do_term___u2227_u209a___00__closed__1 = (const lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__1_value;
static const lean_string_object l_Std_Do_term___u2227_u209a___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 4, .m_data = " ∧ₚ "};
static const lean_object* l_Std_Do_term___u2227_u209a___00__closed__2 = (const lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__2_value;
static const lean_ctor_object l_Std_Do_term___u2227_u209a___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__2_value)}};
static const lean_object* l_Std_Do_term___u2227_u209a___00__closed__3 = (const lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__3_value;
static const lean_ctor_object l_Std_Do_term___u2227_u209a___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__3_value),((lean_object*)&l_Std_Do_term___u2227_u2091___00__closed__4_value)}};
static const lean_object* l_Std_Do_term___u2227_u209a___00__closed__4 = (const lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__4_value;
static const lean_ctor_object l_Std_Do_term___u2227_u209a___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__1_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__4_value)}};
static const lean_object* l_Std_Do_term___u2227_u209a___00__closed__5 = (const lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Do_term___u2227_u209a__ = (const lean_object*)&l_Std_Do_term___u2227_u209a___00__closed__5_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PostCond.and"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 150, 138, 197, 137, 5, 150, 182)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(77, 217, 234, 155, 212, 82, 211, 216)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(124, 92, 27, 8, 188, 224, 25, 47)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(158, 14, 254, 237, 73, 234, 208, 136)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Std_Do_term___u2192_u209a___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 8, .m_data = "term_→ₚ_"};
static const lean_object* l_Std_Do_term___u2192_u209a___00__closed__0 = (const lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__0_value;
static const lean_ctor_object l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do_term___u2192_u209a___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__1_value_aux_1),((lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 152, 37, 89, 170, 148, 214, 40)}};
static const lean_object* l_Std_Do_term___u2192_u209a___00__closed__1 = (const lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__1_value;
static const lean_string_object l_Std_Do_term___u2192_u209a___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 4, .m_data = " →ₚ "};
static const lean_object* l_Std_Do_term___u2192_u209a___00__closed__2 = (const lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__2_value;
static const lean_ctor_object l_Std_Do_term___u2192_u209a___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__2_value)}};
static const lean_object* l_Std_Do_term___u2192_u209a___00__closed__3 = (const lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__3_value;
static const lean_ctor_object l_Std_Do_term___u2192_u209a___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__5_value),((lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__3_value),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__10_value)}};
static const lean_object* l_Std_Do_term___u2192_u209a___00__closed__4 = (const lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__4_value;
static const lean_ctor_object l_Std_Do_term___u2192_u209a___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__1_value),((lean_object*)(((size_t)(25) << 1) | 1)),((lean_object*)(((size_t)(26) << 1) | 1)),((lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__4_value)}};
static const lean_object* l_Std_Do_term___u2192_u209a___00__closed__5 = (const lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__5_value;
LEAN_EXPORT const lean_object* l_Std_Do_term___u2192_u209a__ = (const lean_object*)&l_Std_Do_term___u2192_u209a___00__closed__5_value;
static const lean_string_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "PostCond.imp"};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0_value;
static lean_once_cell_t l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(3, 150, 138, 197, 137, 5, 150, 182)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value_aux_0),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(179, 188, 154, 150, 86, 220, 24, 91)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(48, 144, 193, 124, 159, 137, 91, 218)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_0),((lean_object*)&l_Std_Do_term___u22a2_u2091___00__closed__1_value),LEAN_SCALAR_PTR_LITERAL(0, 110, 135, 113, 195, 226, 80, 101)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_1),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(124, 92, 27, 8, 188, 224, 25, 47)}};
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value_aux_2),((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(56, 224, 179, 90, 89, 14, 202, 155)}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4_value;
static const lean_ctor_object l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5 = (const lean_object*)&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5_value;
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorIdx___impl(lean_object* v_x_1_){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_obj_tag_nat(v_x_1_);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorIdx___impl___boxed(lean_object* v_x_3_){
_start:
{
lean_object* v_res_4_; 
v_res_4_ = l_Std_Do_PostShape_ctorIdx___impl(v_x_3_);
lean_dec(v_x_3_);
return v_res_4_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorElim___redArg(lean_object* v_t_5_, lean_object* v_k_6_){
_start:
{
if (lean_obj_tag(v_t_5_) == 0)
{
return v_k_6_;
}
else
{
lean_object* v_a_7_; lean_object* v___x_8_; 
v_a_7_ = lean_ctor_get(v_t_5_, 0);
lean_inc(v_a_7_);
lean_dec(v_t_5_);
v___x_8_ = lean_apply_2(v_k_6_, lean_box(0), v_a_7_);
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorElim(lean_object* v_motive_9_, lean_object* v_ctorIdx_10_, lean_object* v_t_11_, lean_object* v_h_12_, lean_object* v_k_13_){
_start:
{
lean_object* v___x_14_; 
v___x_14_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_11_, v_k_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorElim___boxed(lean_object* v_motive_15_, lean_object* v_ctorIdx_16_, lean_object* v_t_17_, lean_object* v_h_18_, lean_object* v_k_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l_Std_Do_PostShape_ctorElim(v_motive_15_, v_ctorIdx_16_, v_t_17_, v_h_18_, v_k_19_);
lean_dec(v_ctorIdx_16_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_pure_elim___redArg(lean_object* v_t_21_, lean_object* v_pure_22_){
_start:
{
lean_object* v___x_23_; 
v___x_23_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_21_, v_pure_22_);
return v___x_23_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_pure_elim(lean_object* v_motive_24_, lean_object* v_t_25_, lean_object* v_h_26_, lean_object* v_pure_27_){
_start:
{
lean_object* v___x_28_; 
v___x_28_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_25_, v_pure_27_);
return v___x_28_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_arg_elim___redArg(lean_object* v_t_29_, lean_object* v_arg_30_){
_start:
{
lean_object* v___x_31_; 
v___x_31_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_29_, v_arg_30_);
return v___x_31_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_arg_elim(lean_object* v_motive_32_, lean_object* v_t_33_, lean_object* v_h_34_, lean_object* v_arg_35_){
_start:
{
lean_object* v___x_36_; 
v___x_36_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_33_, v_arg_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_except_elim___redArg(lean_object* v_t_37_, lean_object* v_except_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_37_, v_except_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_except_elim(lean_object* v_motive_40_, lean_object* v_t_41_, lean_object* v_h_42_, lean_object* v_except_43_){
_start:
{
lean_object* v___x_44_; 
v___x_44_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_41_, v_except_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_args(lean_object* v_x_45_){
_start:
{
switch(lean_obj_tag(v_x_45_))
{
case 0:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
case 1:
{
lean_object* v_a_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v_a_47_ = lean_ctor_get(v_x_45_, 0);
v___x_48_ = l_Std_Do_PostShape_args(v_a_47_);
v___x_49_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_49_, 0, lean_box(0));
lean_ctor_set(v___x_49_, 1, v___x_48_);
return v___x_49_;
}
default: 
{
lean_object* v_a_50_; 
v_a_50_ = lean_ctor_get(v_x_45_, 0);
v_x_45_ = v_a_50_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_args___boxed(lean_object* v_x_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Std_Do_PostShape_args(v_x_52_);
lean_dec(v_x_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const___redArg___lam__0(lean_object* v_a_54_, lean_object* v_00___u03b5_55_){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_56_ = l_Std_Do_PostShape_args(v_a_54_);
v___x_57_ = l_Std_Do_SPred_pure___redArg(v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const___redArg___lam__0___boxed(lean_object* v_a_58_, lean_object* v_00___u03b5_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l_Std_Do_ExceptConds_const___redArg___lam__0(v_a_58_, v_00___u03b5_59_);
lean_dec(v_00___u03b5_59_);
lean_dec(v_a_58_);
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const___redArg(lean_object* v_ps_61_){
_start:
{
switch(lean_obj_tag(v_ps_61_))
{
case 0:
{
lean_object* v___x_62_; 
v___x_62_ = lean_box(0);
return v___x_62_;
}
case 1:
{
lean_object* v_a_63_; 
v_a_63_ = lean_ctor_get(v_ps_61_, 0);
lean_inc(v_a_63_);
lean_dec_ref_known(v_ps_61_, 1);
v_ps_61_ = v_a_63_;
goto _start;
}
default: 
{
lean_object* v_a_65_; lean_object* v___f_66_; lean_object* v___x_67_; lean_object* v___x_68_; 
v_a_65_ = lean_ctor_get(v_ps_61_, 0);
lean_inc_n(v_a_65_, 2);
lean_dec_ref_known(v_ps_61_, 1);
v___f_66_ = lean_alloc_closure((void*)(l_Std_Do_ExceptConds_const___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_66_, 0, v_a_65_);
v___x_67_ = l_Std_Do_ExceptConds_const___redArg(v_a_65_);
v___x_68_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_68_, 0, v___f_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
return v___x_68_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const(lean_object* v_ps_69_, lean_object* v_p_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = l_Std_Do_ExceptConds_const___redArg(v_ps_69_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_true(lean_object* v_ps_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Std_Do_ExceptConds_const___redArg(v_ps_72_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_false(lean_object* v_ps_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Std_Do_ExceptConds_const___redArg(v_ps_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedExceptConds(lean_object* v_ps_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Std_Do_ExceptConds_const___redArg(v_ps_76_);
return v___x_77_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6(void){
_start:
{
lean_object* v___x_117_; lean_object* v___x_118_; 
v___x_117_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5));
v___x_118_ = l_String_toRawSubstring_x27(v___x_117_);
return v___x_118_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1(lean_object* v_x_143_, lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
lean_object* v___x_146_; uint8_t v___x_147_; 
v___x_146_ = ((lean_object*)(l_Std_Do_term___u22a2_u2091___00__closed__3));
lean_inc(v_x_143_);
v___x_147_ = l_Lean_Syntax_isOfKind(v_x_143_, v___x_146_);
if (v___x_147_ == 0)
{
lean_object* v___x_148_; lean_object* v___x_149_; 
lean_dec(v_x_143_);
v___x_148_ = lean_box(1);
v___x_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_148_);
lean_ctor_set(v___x_149_, 1, v_a_145_);
return v___x_149_;
}
else
{
lean_object* v_quotContext_150_; lean_object* v_currMacroScope_151_; lean_object* v_ref_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v_quotContext_150_ = lean_ctor_get(v_a_144_, 1);
v_currMacroScope_151_ = lean_ctor_get(v_a_144_, 2);
v_ref_152_ = lean_ctor_get(v_a_144_, 5);
v___x_153_ = lean_unsigned_to_nat(0u);
v___x_154_ = l_Lean_Syntax_getArg(v_x_143_, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(2u);
v___x_156_ = l_Lean_Syntax_getArg(v_x_143_, v___x_155_);
lean_dec(v_x_143_);
v___x_157_ = 0;
v___x_158_ = l_Lean_SourceInfo_fromRef(v_ref_152_, v___x_157_);
v___x_159_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_160_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6);
v___x_161_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9));
lean_inc(v_currMacroScope_151_);
lean_inc(v_quotContext_150_);
v___x_162_ = l_Lean_addMacroScope(v_quotContext_150_, v___x_161_, v_currMacroScope_151_);
v___x_163_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14));
lean_inc_n(v___x_158_, 2);
v___x_164_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_164_, 0, v___x_158_);
lean_ctor_set(v___x_164_, 1, v___x_160_);
lean_ctor_set(v___x_164_, 2, v___x_162_);
lean_ctor_set(v___x_164_, 3, v___x_163_);
v___x_165_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_166_ = l_Lean_Syntax_node2(v___x_158_, v___x_165_, v___x_154_, v___x_156_);
v___x_167_ = l_Lean_Syntax_node2(v___x_158_, v___x_159_, v___x_164_, v___x_166_);
v___x_168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_167_);
lean_ctor_set(v___x_168_, 1, v_a_145_);
return v___x_168_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___boxed(lean_object* v_x_169_, lean_object* v_a_170_, lean_object* v_a_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1(v_x_169_, v_a_170_, v_a_171_);
lean_dec_ref(v_a_170_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1(lean_object* v_x_176_, lean_object* v_a_177_, lean_object* v_a_178_){
_start:
{
lean_object* v___x_179_; uint8_t v___x_180_; 
v___x_179_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_176_);
v___x_180_ = l_Lean_Syntax_isOfKind(v_x_176_, v___x_179_);
if (v___x_180_ == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_x_176_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_182_, 0, v___x_181_);
lean_ctor_set(v___x_182_, 1, v_a_178_);
return v___x_182_;
}
else
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_185_; uint8_t v___x_186_; 
v___x_183_ = lean_unsigned_to_nat(0u);
v___x_184_ = l_Lean_Syntax_getArg(v_x_176_, v___x_183_);
v___x_185_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_184_);
v___x_186_ = l_Lean_Syntax_isOfKind(v___x_184_, v___x_185_);
if (v___x_186_ == 0)
{
lean_object* v___x_187_; lean_object* v___x_188_; 
lean_dec(v___x_184_);
lean_dec(v_x_176_);
v___x_187_ = lean_box(0);
v___x_188_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v_a_178_);
return v___x_188_;
}
else
{
lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; uint8_t v___x_192_; 
v___x_189_ = lean_unsigned_to_nat(1u);
v___x_190_ = l_Lean_Syntax_getArg(v_x_176_, v___x_189_);
lean_dec(v_x_176_);
v___x_191_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_190_);
v___x_192_ = l_Lean_Syntax_matchesNull(v___x_190_, v___x_191_);
if (v___x_192_ == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v___x_190_);
lean_dec(v___x_184_);
v___x_193_ = lean_box(0);
v___x_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_194_, 0, v___x_193_);
lean_ctor_set(v___x_194_, 1, v_a_178_);
return v___x_194_;
}
else
{
lean_object* v___x_195_; lean_object* v___x_196_; lean_object* v_ref_197_; uint8_t v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_195_ = l_Lean_Syntax_getArg(v___x_190_, v___x_183_);
v___x_196_ = l_Lean_Syntax_getArg(v___x_190_, v___x_189_);
lean_dec(v___x_190_);
v_ref_197_ = l_Lean_replaceRef(v___x_184_, v_a_177_);
lean_dec(v___x_184_);
v___x_198_ = 0;
v___x_199_ = l_Lean_SourceInfo_fromRef(v_ref_197_, v___x_198_);
lean_dec(v_ref_197_);
v___x_200_ = ((lean_object*)(l_Std_Do_term___u22a2_u2091___00__closed__3));
v___x_201_ = ((lean_object*)(l_Std_Do_term___u22a2_u2091___00__closed__6));
lean_inc(v___x_199_);
v___x_202_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_199_);
lean_ctor_set(v___x_202_, 1, v___x_201_);
v___x_203_ = l_Lean_Syntax_node3(v___x_199_, v___x_200_, v___x_195_, v___x_202_, v___x_196_);
v___x_204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_204_, 0, v___x_203_);
lean_ctor_set(v___x_204_, 1, v_a_178_);
return v___x_204_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___boxed(lean_object* v_x_205_, lean_object* v_a_206_, lean_object* v_a_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1(v_x_205_, v_a_206_, v_a_207_);
lean_dec(v_a_206_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_ExceptConds_entails_match__1_splitter___redArg(lean_object* v_ps_209_, lean_object* v_x_210_, lean_object* v_y_211_, lean_object* v_h__1_212_, lean_object* v_h__2_213_, lean_object* v_h__3_214_){
_start:
{
switch(lean_obj_tag(v_ps_209_))
{
case 0:
{
lean_object* v___x_215_; 
lean_dec(v_h__3_214_);
lean_dec(v_h__2_213_);
v___x_215_ = lean_apply_2(v_h__1_212_, v_x_210_, v_y_211_);
return v___x_215_;
}
case 1:
{
lean_object* v_a_216_; lean_object* v___x_217_; 
lean_dec(v_h__3_214_);
lean_dec(v_h__1_212_);
v_a_216_ = lean_ctor_get(v_ps_209_, 0);
lean_inc(v_a_216_);
lean_dec_ref_known(v_ps_209_, 1);
v___x_217_ = lean_apply_4(v_h__2_213_, lean_box(0), v_a_216_, v_x_210_, v_y_211_);
return v___x_217_;
}
default: 
{
lean_object* v_a_218_; lean_object* v___x_219_; 
lean_dec(v_h__2_213_);
lean_dec(v_h__1_212_);
v_a_218_ = lean_ctor_get(v_ps_209_, 0);
lean_inc(v_a_218_);
lean_dec_ref_known(v_ps_209_, 1);
v___x_219_ = lean_apply_4(v_h__3_214_, lean_box(0), v_a_218_, v_x_210_, v_y_211_);
return v___x_219_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_ExceptConds_entails_match__1_splitter(lean_object* v_motive_220_, lean_object* v_ps_221_, lean_object* v_x_222_, lean_object* v_y_223_, lean_object* v_h__1_224_, lean_object* v_h__2_225_, lean_object* v_h__3_226_){
_start:
{
switch(lean_obj_tag(v_ps_221_))
{
case 0:
{
lean_object* v___x_227_; 
lean_dec(v_h__3_226_);
lean_dec(v_h__2_225_);
v___x_227_ = lean_apply_2(v_h__1_224_, v_x_222_, v_y_223_);
return v___x_227_;
}
case 1:
{
lean_object* v_a_228_; lean_object* v___x_229_; 
lean_dec(v_h__3_226_);
lean_dec(v_h__1_224_);
v_a_228_ = lean_ctor_get(v_ps_221_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v_ps_221_, 1);
v___x_229_ = lean_apply_4(v_h__2_225_, lean_box(0), v_a_228_, v_x_222_, v_y_223_);
return v___x_229_;
}
default: 
{
lean_object* v_a_230_; lean_object* v___x_231_; 
lean_dec(v_h__2_225_);
lean_dec(v_h__1_224_);
v_a_230_ = lean_ctor_get(v_ps_221_, 0);
lean_inc(v_a_230_);
lean_dec_ref_known(v_ps_221_, 1);
v___x_231_ = lean_apply_4(v_h__3_226_, lean_box(0), v_a_230_, v_x_222_, v_y_223_);
return v___x_231_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_PostShape_args_match__1_splitter___redArg(lean_object* v_x_232_, lean_object* v_h__1_233_, lean_object* v_h__2_234_, lean_object* v_h__3_235_){
_start:
{
switch(lean_obj_tag(v_x_232_))
{
case 0:
{
lean_object* v___x_236_; lean_object* v___x_237_; 
lean_dec(v_h__3_235_);
lean_dec(v_h__2_234_);
v___x_236_ = lean_box(0);
v___x_237_ = lean_apply_1(v_h__1_233_, v___x_236_);
return v___x_237_;
}
case 1:
{
lean_object* v_a_238_; lean_object* v___x_239_; 
lean_dec(v_h__3_235_);
lean_dec(v_h__1_233_);
v_a_238_ = lean_ctor_get(v_x_232_, 0);
lean_inc(v_a_238_);
lean_dec_ref_known(v_x_232_, 1);
v___x_239_ = lean_apply_2(v_h__2_234_, lean_box(0), v_a_238_);
return v___x_239_;
}
default: 
{
lean_object* v_a_240_; lean_object* v___x_241_; 
lean_dec(v_h__2_234_);
lean_dec(v_h__1_233_);
v_a_240_ = lean_ctor_get(v_x_232_, 0);
lean_inc(v_a_240_);
lean_dec_ref_known(v_x_232_, 1);
v___x_241_ = lean_apply_2(v_h__3_235_, lean_box(0), v_a_240_);
return v___x_241_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_PostShape_args_match__1_splitter(lean_object* v_motive_242_, lean_object* v_x_243_, lean_object* v_h__1_244_, lean_object* v_h__2_245_, lean_object* v_h__3_246_){
_start:
{
switch(lean_obj_tag(v_x_243_))
{
case 0:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
lean_dec(v_h__3_246_);
lean_dec(v_h__2_245_);
v___x_247_ = lean_box(0);
v___x_248_ = lean_apply_1(v_h__1_244_, v___x_247_);
return v___x_248_;
}
case 1:
{
lean_object* v_a_249_; lean_object* v___x_250_; 
lean_dec(v_h__3_246_);
lean_dec(v_h__1_244_);
v_a_249_ = lean_ctor_get(v_x_243_, 0);
lean_inc(v_a_249_);
lean_dec_ref_known(v_x_243_, 1);
v___x_250_ = lean_apply_2(v_h__2_245_, lean_box(0), v_a_249_);
return v___x_250_;
}
default: 
{
lean_object* v_a_251_; lean_object* v___x_252_; 
lean_dec(v_h__2_245_);
lean_dec(v_h__1_244_);
v_a_251_ = lean_ctor_get(v_x_243_, 0);
lean_inc(v_a_251_);
lean_dec_ref_known(v_x_243_, 1);
v___x_252_ = lean_apply_2(v_h__3_246_, lean_box(0), v_a_251_);
return v___x_252_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and___lam__0(lean_object* v_a_253_, lean_object* v_fst_254_, lean_object* v_fst_255_, lean_object* v_e_256_){
_start:
{
lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_257_ = l_Std_Do_PostShape_args(v_a_253_);
lean_inc(v_e_256_);
v___x_258_ = lean_apply_1(v_fst_254_, v_e_256_);
v___x_259_ = lean_apply_1(v_fst_255_, v_e_256_);
v___x_260_ = l_Std_Do_SPred_and(v___x_257_, v___x_258_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and___lam__0___boxed(lean_object* v_a_261_, lean_object* v_fst_262_, lean_object* v_fst_263_, lean_object* v_e_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_Do_ExceptConds_and___lam__0(v_a_261_, v_fst_262_, v_fst_263_, v_e_264_);
lean_dec(v_a_261_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and(lean_object* v_ps_266_, lean_object* v_x_267_, lean_object* v_y_268_){
_start:
{
switch(lean_obj_tag(v_ps_266_))
{
case 0:
{
lean_object* v___x_269_; 
lean_dec(v_y_268_);
lean_dec(v_x_267_);
v___x_269_ = lean_box(0);
return v___x_269_;
}
case 1:
{
lean_object* v_a_270_; 
v_a_270_ = lean_ctor_get(v_ps_266_, 0);
lean_inc(v_a_270_);
lean_dec_ref_known(v_ps_266_, 1);
v_ps_266_ = v_a_270_;
goto _start;
}
default: 
{
lean_object* v_a_272_; lean_object* v_fst_273_; lean_object* v_snd_274_; lean_object* v_fst_275_; lean_object* v_snd_276_; lean_object* v___x_278_; uint8_t v_isShared_279_; uint8_t v_isSharedCheck_285_; 
v_a_272_ = lean_ctor_get(v_ps_266_, 0);
lean_inc(v_a_272_);
lean_dec_ref_known(v_ps_266_, 1);
v_fst_273_ = lean_ctor_get(v_x_267_, 0);
lean_inc(v_fst_273_);
v_snd_274_ = lean_ctor_get(v_x_267_, 1);
lean_inc(v_snd_274_);
lean_dec(v_x_267_);
v_fst_275_ = lean_ctor_get(v_y_268_, 0);
v_snd_276_ = lean_ctor_get(v_y_268_, 1);
v_isSharedCheck_285_ = !lean_is_exclusive(v_y_268_);
if (v_isSharedCheck_285_ == 0)
{
v___x_278_ = v_y_268_;
v_isShared_279_ = v_isSharedCheck_285_;
goto v_resetjp_277_;
}
else
{
lean_inc(v_snd_276_);
lean_inc(v_fst_275_);
lean_dec(v_y_268_);
v___x_278_ = lean_box(0);
v_isShared_279_ = v_isSharedCheck_285_;
goto v_resetjp_277_;
}
v_resetjp_277_:
{
lean_object* v___f_280_; lean_object* v___x_281_; lean_object* v___x_283_; 
lean_inc(v_a_272_);
v___f_280_ = lean_alloc_closure((void*)(l_Std_Do_ExceptConds_and___lam__0___boxed), 4, 3);
lean_closure_set(v___f_280_, 0, v_a_272_);
lean_closure_set(v___f_280_, 1, v_fst_273_);
lean_closure_set(v___f_280_, 2, v_fst_275_);
v___x_281_ = l_Std_Do_ExceptConds_and(v_a_272_, v_snd_274_, v_snd_276_);
if (v_isShared_279_ == 0)
{
lean_ctor_set(v___x_278_, 1, v___x_281_);
lean_ctor_set(v___x_278_, 0, v___f_280_);
v___x_283_ = v___x_278_;
goto v_reusejp_282_;
}
else
{
lean_object* v_reuseFailAlloc_284_; 
v_reuseFailAlloc_284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_284_, 0, v___f_280_);
lean_ctor_set(v_reuseFailAlloc_284_, 1, v___x_281_);
v___x_283_ = v_reuseFailAlloc_284_;
goto v_reusejp_282_;
}
v_reusejp_282_:
{
return v___x_283_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1(void){
_start:
{
lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_308_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0));
v___x_309_ = l_String_toRawSubstring_x27(v___x_308_);
return v___x_309_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1(lean_object* v_x_325_, lean_object* v_a_326_, lean_object* v_a_327_){
_start:
{
lean_object* v___x_328_; uint8_t v___x_329_; 
v___x_328_ = ((lean_object*)(l_Std_Do_term___u2227_u2091___00__closed__1));
lean_inc(v_x_325_);
v___x_329_ = l_Lean_Syntax_isOfKind(v_x_325_, v___x_328_);
if (v___x_329_ == 0)
{
lean_object* v___x_330_; lean_object* v___x_331_; 
lean_dec(v_x_325_);
v___x_330_ = lean_box(1);
v___x_331_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_330_);
lean_ctor_set(v___x_331_, 1, v_a_327_);
return v___x_331_;
}
else
{
lean_object* v_quotContext_332_; lean_object* v_currMacroScope_333_; lean_object* v_ref_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; uint8_t v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; 
v_quotContext_332_ = lean_ctor_get(v_a_326_, 1);
v_currMacroScope_333_ = lean_ctor_get(v_a_326_, 2);
v_ref_334_ = lean_ctor_get(v_a_326_, 5);
v___x_335_ = lean_unsigned_to_nat(0u);
v___x_336_ = l_Lean_Syntax_getArg(v_x_325_, v___x_335_);
v___x_337_ = lean_unsigned_to_nat(2u);
v___x_338_ = l_Lean_Syntax_getArg(v_x_325_, v___x_337_);
lean_dec(v_x_325_);
v___x_339_ = 0;
v___x_340_ = l_Lean_SourceInfo_fromRef(v_ref_334_, v___x_339_);
v___x_341_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_342_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1);
v___x_343_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3));
lean_inc(v_currMacroScope_333_);
lean_inc(v_quotContext_332_);
v___x_344_ = l_Lean_addMacroScope(v_quotContext_332_, v___x_343_, v_currMacroScope_333_);
v___x_345_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6));
lean_inc_n(v___x_340_, 2);
v___x_346_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_346_, 0, v___x_340_);
lean_ctor_set(v___x_346_, 1, v___x_342_);
lean_ctor_set(v___x_346_, 2, v___x_344_);
lean_ctor_set(v___x_346_, 3, v___x_345_);
v___x_347_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_348_ = l_Lean_Syntax_node2(v___x_340_, v___x_347_, v___x_336_, v___x_338_);
v___x_349_ = l_Lean_Syntax_node2(v___x_340_, v___x_341_, v___x_346_, v___x_348_);
v___x_350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_349_);
lean_ctor_set(v___x_350_, 1, v_a_327_);
return v___x_350_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___boxed(lean_object* v_x_351_, lean_object* v_a_352_, lean_object* v_a_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1(v_x_351_, v_a_352_, v_a_353_);
lean_dec_ref(v_a_352_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1(lean_object* v_x_355_, lean_object* v_a_356_, lean_object* v_a_357_){
_start:
{
lean_object* v___x_358_; uint8_t v___x_359_; 
v___x_358_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_355_);
v___x_359_ = l_Lean_Syntax_isOfKind(v_x_355_, v___x_358_);
if (v___x_359_ == 0)
{
lean_object* v___x_360_; lean_object* v___x_361_; 
lean_dec(v_x_355_);
v___x_360_ = lean_box(0);
v___x_361_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_360_);
lean_ctor_set(v___x_361_, 1, v_a_357_);
return v___x_361_;
}
else
{
lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; uint8_t v___x_365_; 
v___x_362_ = lean_unsigned_to_nat(0u);
v___x_363_ = l_Lean_Syntax_getArg(v_x_355_, v___x_362_);
v___x_364_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_363_);
v___x_365_ = l_Lean_Syntax_isOfKind(v___x_363_, v___x_364_);
if (v___x_365_ == 0)
{
lean_object* v___x_366_; lean_object* v___x_367_; 
lean_dec(v___x_363_);
lean_dec(v_x_355_);
v___x_366_ = lean_box(0);
v___x_367_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_367_, 0, v___x_366_);
lean_ctor_set(v___x_367_, 1, v_a_357_);
return v___x_367_;
}
else
{
lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; uint8_t v___x_371_; 
v___x_368_ = lean_unsigned_to_nat(1u);
v___x_369_ = l_Lean_Syntax_getArg(v_x_355_, v___x_368_);
lean_dec(v_x_355_);
v___x_370_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_369_);
v___x_371_ = l_Lean_Syntax_matchesNull(v___x_369_, v___x_370_);
if (v___x_371_ == 0)
{
lean_object* v___x_372_; lean_object* v___x_373_; 
lean_dec(v___x_369_);
lean_dec(v___x_363_);
v___x_372_ = lean_box(0);
v___x_373_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v_a_357_);
return v___x_373_;
}
else
{
lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v_ref_376_; uint8_t v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; 
v___x_374_ = l_Lean_Syntax_getArg(v___x_369_, v___x_362_);
v___x_375_ = l_Lean_Syntax_getArg(v___x_369_, v___x_368_);
lean_dec(v___x_369_);
v_ref_376_ = l_Lean_replaceRef(v___x_363_, v_a_356_);
lean_dec(v___x_363_);
v___x_377_ = 0;
v___x_378_ = l_Lean_SourceInfo_fromRef(v_ref_376_, v___x_377_);
lean_dec(v_ref_376_);
v___x_379_ = ((lean_object*)(l_Std_Do_term___u2227_u2091___00__closed__1));
v___x_380_ = ((lean_object*)(l_Std_Do_term___u2227_u2091___00__closed__2));
lean_inc(v___x_378_);
v___x_381_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_381_, 0, v___x_378_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v___x_382_ = l_Lean_Syntax_node3(v___x_378_, v___x_379_, v___x_374_, v___x_381_, v___x_375_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v___x_382_);
lean_ctor_set(v___x_383_, 1, v_a_357_);
return v___x_383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1___boxed(lean_object* v_x_384_, lean_object* v_a_385_, lean_object* v_a_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1(v_x_384_, v_a_385_, v_a_386_);
lean_dec(v_a_385_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp___lam__0(lean_object* v_a_388_, lean_object* v_fst_389_, lean_object* v_fst_390_, lean_object* v_e_391_){
_start:
{
lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; 
v___x_392_ = l_Std_Do_PostShape_args(v_a_388_);
lean_inc(v_e_391_);
v___x_393_ = lean_apply_1(v_fst_389_, v_e_391_);
v___x_394_ = lean_apply_1(v_fst_390_, v_e_391_);
v___x_395_ = l_Std_Do_SPred_imp(v___x_392_, v___x_393_, v___x_394_);
return v___x_395_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp___lam__0___boxed(lean_object* v_a_396_, lean_object* v_fst_397_, lean_object* v_fst_398_, lean_object* v_e_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l_Std_Do_ExceptConds_imp___lam__0(v_a_396_, v_fst_397_, v_fst_398_, v_e_399_);
lean_dec(v_a_396_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp(lean_object* v_ps_401_, lean_object* v_x_402_, lean_object* v_y_403_){
_start:
{
switch(lean_obj_tag(v_ps_401_))
{
case 0:
{
lean_object* v___x_404_; 
lean_dec(v_y_403_);
lean_dec(v_x_402_);
v___x_404_ = lean_box(0);
return v___x_404_;
}
case 1:
{
lean_object* v_a_405_; 
v_a_405_ = lean_ctor_get(v_ps_401_, 0);
lean_inc(v_a_405_);
lean_dec_ref_known(v_ps_401_, 1);
v_ps_401_ = v_a_405_;
goto _start;
}
default: 
{
lean_object* v_a_407_; lean_object* v_fst_408_; lean_object* v_snd_409_; lean_object* v_fst_410_; lean_object* v_snd_411_; lean_object* v___x_413_; uint8_t v_isShared_414_; uint8_t v_isSharedCheck_420_; 
v_a_407_ = lean_ctor_get(v_ps_401_, 0);
lean_inc(v_a_407_);
lean_dec_ref_known(v_ps_401_, 1);
v_fst_408_ = lean_ctor_get(v_x_402_, 0);
lean_inc(v_fst_408_);
v_snd_409_ = lean_ctor_get(v_x_402_, 1);
lean_inc(v_snd_409_);
lean_dec(v_x_402_);
v_fst_410_ = lean_ctor_get(v_y_403_, 0);
v_snd_411_ = lean_ctor_get(v_y_403_, 1);
v_isSharedCheck_420_ = !lean_is_exclusive(v_y_403_);
if (v_isSharedCheck_420_ == 0)
{
v___x_413_ = v_y_403_;
v_isShared_414_ = v_isSharedCheck_420_;
goto v_resetjp_412_;
}
else
{
lean_inc(v_snd_411_);
lean_inc(v_fst_410_);
lean_dec(v_y_403_);
v___x_413_ = lean_box(0);
v_isShared_414_ = v_isSharedCheck_420_;
goto v_resetjp_412_;
}
v_resetjp_412_:
{
lean_object* v___f_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
lean_inc(v_a_407_);
v___f_415_ = lean_alloc_closure((void*)(l_Std_Do_ExceptConds_imp___lam__0___boxed), 4, 3);
lean_closure_set(v___f_415_, 0, v_a_407_);
lean_closure_set(v___f_415_, 1, v_fst_408_);
lean_closure_set(v___f_415_, 2, v_fst_410_);
v___x_416_ = l_Std_Do_ExceptConds_imp(v_a_407_, v_snd_409_, v_snd_411_);
if (v_isShared_414_ == 0)
{
lean_ctor_set(v___x_413_, 1, v___x_416_);
lean_ctor_set(v___x_413_, 0, v___f_415_);
v___x_418_ = v___x_413_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_419_; 
v_reuseFailAlloc_419_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_419_, 0, v___f_415_);
lean_ctor_set(v_reuseFailAlloc_419_, 1, v___x_416_);
v___x_418_ = v_reuseFailAlloc_419_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
return v___x_418_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1(void){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; 
v___x_440_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0));
v___x_441_ = l_String_toRawSubstring_x27(v___x_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1(lean_object* v_x_457_, lean_object* v_a_458_, lean_object* v_a_459_){
_start:
{
lean_object* v___x_460_; uint8_t v___x_461_; 
v___x_460_ = ((lean_object*)(l_Std_Do_term___u2192_u2091___00__closed__1));
lean_inc(v_x_457_);
v___x_461_ = l_Lean_Syntax_isOfKind(v_x_457_, v___x_460_);
if (v___x_461_ == 0)
{
lean_object* v___x_462_; lean_object* v___x_463_; 
lean_dec(v_x_457_);
v___x_462_ = lean_box(1);
v___x_463_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_463_, 0, v___x_462_);
lean_ctor_set(v___x_463_, 1, v_a_459_);
return v___x_463_;
}
else
{
lean_object* v_quotContext_464_; lean_object* v_currMacroScope_465_; lean_object* v_ref_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; lean_object* v___x_478_; lean_object* v___x_479_; lean_object* v___x_480_; lean_object* v___x_481_; lean_object* v___x_482_; 
v_quotContext_464_ = lean_ctor_get(v_a_458_, 1);
v_currMacroScope_465_ = lean_ctor_get(v_a_458_, 2);
v_ref_466_ = lean_ctor_get(v_a_458_, 5);
v___x_467_ = lean_unsigned_to_nat(0u);
v___x_468_ = l_Lean_Syntax_getArg(v_x_457_, v___x_467_);
v___x_469_ = lean_unsigned_to_nat(2u);
v___x_470_ = l_Lean_Syntax_getArg(v_x_457_, v___x_469_);
lean_dec(v_x_457_);
v___x_471_ = 0;
v___x_472_ = l_Lean_SourceInfo_fromRef(v_ref_466_, v___x_471_);
v___x_473_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_474_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1);
v___x_475_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3));
lean_inc(v_currMacroScope_465_);
lean_inc(v_quotContext_464_);
v___x_476_ = l_Lean_addMacroScope(v_quotContext_464_, v___x_475_, v_currMacroScope_465_);
v___x_477_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6));
lean_inc_n(v___x_472_, 2);
v___x_478_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_478_, 0, v___x_472_);
lean_ctor_set(v___x_478_, 1, v___x_474_);
lean_ctor_set(v___x_478_, 2, v___x_476_);
lean_ctor_set(v___x_478_, 3, v___x_477_);
v___x_479_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_480_ = l_Lean_Syntax_node2(v___x_472_, v___x_479_, v___x_468_, v___x_470_);
v___x_481_ = l_Lean_Syntax_node2(v___x_472_, v___x_473_, v___x_478_, v___x_480_);
v___x_482_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_482_, 0, v___x_481_);
lean_ctor_set(v___x_482_, 1, v_a_459_);
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___boxed(lean_object* v_x_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1(v_x_483_, v_a_484_, v_a_485_);
lean_dec_ref(v_a_484_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1(lean_object* v_x_487_, lean_object* v_a_488_, lean_object* v_a_489_){
_start:
{
lean_object* v___x_490_; uint8_t v___x_491_; 
v___x_490_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_487_);
v___x_491_ = l_Lean_Syntax_isOfKind(v_x_487_, v___x_490_);
if (v___x_491_ == 0)
{
lean_object* v___x_492_; lean_object* v___x_493_; 
lean_dec(v_x_487_);
v___x_492_ = lean_box(0);
v___x_493_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_493_, 0, v___x_492_);
lean_ctor_set(v___x_493_, 1, v_a_489_);
return v___x_493_;
}
else
{
lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; uint8_t v___x_497_; 
v___x_494_ = lean_unsigned_to_nat(0u);
v___x_495_ = l_Lean_Syntax_getArg(v_x_487_, v___x_494_);
v___x_496_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_495_);
v___x_497_ = l_Lean_Syntax_isOfKind(v___x_495_, v___x_496_);
if (v___x_497_ == 0)
{
lean_object* v___x_498_; lean_object* v___x_499_; 
lean_dec(v___x_495_);
lean_dec(v_x_487_);
v___x_498_ = lean_box(0);
v___x_499_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_499_, 0, v___x_498_);
lean_ctor_set(v___x_499_, 1, v_a_489_);
return v___x_499_;
}
else
{
lean_object* v___x_500_; lean_object* v___x_501_; lean_object* v___x_502_; uint8_t v___x_503_; 
v___x_500_ = lean_unsigned_to_nat(1u);
v___x_501_ = l_Lean_Syntax_getArg(v_x_487_, v___x_500_);
lean_dec(v_x_487_);
v___x_502_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_501_);
v___x_503_ = l_Lean_Syntax_matchesNull(v___x_501_, v___x_502_);
if (v___x_503_ == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v___x_501_);
lean_dec(v___x_495_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_505_, 0, v___x_504_);
lean_ctor_set(v___x_505_, 1, v_a_489_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; lean_object* v_ref_508_; uint8_t v___x_509_; lean_object* v___x_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; lean_object* v___x_514_; lean_object* v___x_515_; 
v___x_506_ = l_Lean_Syntax_getArg(v___x_501_, v___x_494_);
v___x_507_ = l_Lean_Syntax_getArg(v___x_501_, v___x_500_);
lean_dec(v___x_501_);
v_ref_508_ = l_Lean_replaceRef(v___x_495_, v_a_488_);
lean_dec(v___x_495_);
v___x_509_ = 0;
v___x_510_ = l_Lean_SourceInfo_fromRef(v_ref_508_, v___x_509_);
lean_dec(v_ref_508_);
v___x_511_ = ((lean_object*)(l_Std_Do_term___u2192_u2091___00__closed__1));
v___x_512_ = ((lean_object*)(l_Std_Do_term___u2192_u2091___00__closed__2));
lean_inc(v___x_510_);
v___x_513_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_513_, 0, v___x_510_);
lean_ctor_set(v___x_513_, 1, v___x_512_);
v___x_514_ = l_Lean_Syntax_node3(v___x_510_, v___x_511_, v___x_506_, v___x_513_, v___x_507_);
v___x_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_515_, 0, v___x_514_);
lean_ctor_set(v___x_515_, 1, v_a_489_);
return v___x_515_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1___boxed(lean_object* v_x_516_, lean_object* v_a_517_, lean_object* v_a_518_){
_start:
{
lean_object* v_res_519_; 
v_res_519_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1(v_x_516_, v_a_517_, v_a_518_);
lean_dec(v_a_517_);
return v_res_519_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13(void){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_Array_mkArray0___redArg();
return v___x_589_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15(void){
_start:
{
lean_object* v___x_591_; lean_object* v___x_592_; 
v___x_591_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14));
v___x_592_ = l_String_toRawSubstring_x27(v___x_591_);
return v___x_592_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1(lean_object* v_x_609_, lean_object* v_a_610_, lean_object* v_a_611_){
_start:
{
lean_object* v___x_612_; uint8_t v___x_613_; 
v___x_612_ = ((lean_object*)(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1));
lean_inc(v_x_609_);
v___x_613_ = l_Lean_Syntax_isOfKind(v_x_609_, v___x_612_);
if (v___x_613_ == 0)
{
lean_object* v___x_614_; lean_object* v___x_615_; 
lean_dec(v_x_609_);
v___x_614_ = lean_box(1);
v___x_615_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_615_, 0, v___x_614_);
lean_ctor_set(v___x_615_, 1, v_a_611_);
return v___x_615_;
}
else
{
lean_object* v_quotContext_616_; lean_object* v_currMacroScope_617_; lean_object* v_ref_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; uint8_t v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; lean_object* v___x_643_; lean_object* v___x_644_; lean_object* v___x_645_; lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v___x_648_; lean_object* v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; lean_object* v___x_656_; 
v_quotContext_616_ = lean_ctor_get(v_a_610_, 1);
v_currMacroScope_617_ = lean_ctor_get(v_a_610_, 2);
v_ref_618_ = lean_ctor_get(v_a_610_, 5);
v___x_619_ = lean_unsigned_to_nat(1u);
v___x_620_ = l_Lean_Syntax_getArg(v_x_609_, v___x_619_);
lean_dec(v_x_609_);
v___x_621_ = ((lean_object*)(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5));
v___x_622_ = l_Lean_Syntax_getArgs(v___x_620_);
lean_dec(v___x_620_);
v___x_623_ = 0;
v___x_624_ = l_Lean_SourceInfo_fromRef(v_ref_618_, v___x_623_);
v___x_625_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1));
v___x_626_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2));
lean_inc_n(v___x_624_, 12);
v___x_627_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_627_, 0, v___x_624_);
lean_ctor_set(v___x_627_, 1, v___x_626_);
v___x_628_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5));
v___x_629_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7));
v___x_630_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_631_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8));
v___x_632_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9));
v___x_633_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_624_);
lean_ctor_set(v___x_633_, 1, v___x_631_);
v___x_634_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11));
v___x_635_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12));
v___x_636_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_636_, 0, v___x_624_);
lean_ctor_set(v___x_636_, 1, v___x_635_);
v___x_637_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
v___x_638_ = l_Array_append___redArg(v___x_637_, v___x_622_);
lean_dec_ref(v___x_622_);
v___x_639_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_624_);
lean_ctor_set(v___x_639_, 1, v___x_621_);
v___x_640_ = lean_array_push(v___x_638_, v___x_639_);
v___x_641_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15);
v___x_642_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18));
lean_inc(v_currMacroScope_617_);
lean_inc(v_quotContext_616_);
v___x_643_ = l_Lean_addMacroScope(v_quotContext_616_, v___x_642_, v_currMacroScope_617_);
v___x_644_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22));
v___x_645_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_645_, 0, v___x_624_);
lean_ctor_set(v___x_645_, 1, v___x_641_);
lean_ctor_set(v___x_645_, 2, v___x_643_);
lean_ctor_set(v___x_645_, 3, v___x_644_);
v___x_646_ = lean_array_push(v___x_640_, v___x_645_);
v___x_647_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_647_, 0, v___x_624_);
lean_ctor_set(v___x_647_, 1, v___x_630_);
lean_ctor_set(v___x_647_, 2, v___x_646_);
v___x_648_ = ((lean_object*)(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10));
v___x_649_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_624_);
lean_ctor_set(v___x_649_, 1, v___x_648_);
v___x_650_ = l_Lean_Syntax_node3(v___x_624_, v___x_634_, v___x_636_, v___x_647_, v___x_649_);
v___x_651_ = l_Lean_Syntax_node2(v___x_624_, v___x_632_, v___x_633_, v___x_650_);
v___x_652_ = l_Lean_Syntax_node1(v___x_624_, v___x_630_, v___x_651_);
v___x_653_ = l_Lean_Syntax_node1(v___x_624_, v___x_629_, v___x_652_);
v___x_654_ = l_Lean_Syntax_node1(v___x_624_, v___x_628_, v___x_653_);
v___x_655_ = l_Lean_Syntax_node2(v___x_624_, v___x_625_, v___x_627_, v___x_654_);
v___x_656_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_656_, 0, v___x_655_);
lean_ctor_set(v___x_656_, 1, v_a_611_);
return v___x_656_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___boxed(lean_object* v_x_657_, lean_object* v_a_658_, lean_object* v_a_659_){
_start:
{
lean_object* v_res_660_; 
v_res_660_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1(v_x_657_, v_a_658_, v_a_659_);
lean_dec_ref(v_a_658_);
return v_res_660_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_noThrow___redArg(lean_object* v_ps_661_, lean_object* v_p_662_){
_start:
{
lean_object* v___x_663_; lean_object* v___x_664_; 
v___x_663_ = l_Std_Do_ExceptConds_const___redArg(v_ps_661_);
v___x_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_664_, 0, v_p_662_);
lean_ctor_set(v___x_664_, 1, v___x_663_);
return v___x_664_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_noThrow(lean_object* v_00_u03b1_665_, lean_object* v_ps_666_, lean_object* v_p_667_){
_start:
{
lean_object* v___x_668_; lean_object* v___x_669_; 
v___x_668_ = l_Std_Do_ExceptConds_const___redArg(v_ps_666_);
v___x_669_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_669_, 0, v_p_667_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
return v___x_669_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(size_t v_sz_722_, size_t v_i_723_, lean_object* v_bs_724_){
_start:
{
uint8_t v___x_725_; 
v___x_725_ = lean_usize_dec_lt(v_i_723_, v_sz_722_);
if (v___x_725_ == 0)
{
return v_bs_724_;
}
else
{
lean_object* v_v_726_; lean_object* v___x_727_; lean_object* v_bs_x27_728_; size_t v___x_729_; size_t v___x_730_; lean_object* v___x_731_; 
v_v_726_ = lean_array_uget(v_bs_724_, v_i_723_);
v___x_727_ = lean_unsigned_to_nat(0u);
v_bs_x27_728_ = lean_array_uset(v_bs_724_, v_i_723_, v___x_727_);
v___x_729_ = ((size_t)1ULL);
v___x_730_ = lean_usize_add(v_i_723_, v___x_729_);
v___x_731_ = lean_array_uset(v_bs_x27_728_, v_i_723_, v_v_726_);
v_i_723_ = v___x_730_;
v_bs_724_ = v___x_731_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0___boxed(lean_object* v_sz_733_, lean_object* v_i_734_, lean_object* v_bs_735_){
_start:
{
size_t v_sz_boxed_736_; size_t v_i_boxed_737_; lean_object* v_res_738_; 
v_sz_boxed_736_ = lean_unbox_usize(v_sz_733_);
lean_dec(v_sz_733_);
v_i_boxed_737_ = lean_unbox_usize(v_i_734_);
lean_dec(v_i_734_);
v_res_738_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_boxed_736_, v_i_boxed_737_, v_bs_735_);
return v_res_738_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_740_; lean_object* v___x_741_; 
v___x_740_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0));
v___x_741_ = l_String_toRawSubstring_x27(v___x_740_);
return v___x_741_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16(void){
_start:
{
lean_object* v___x_775_; lean_object* v___x_776_; 
v___x_775_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15));
v___x_776_ = l_String_toRawSubstring_x27(v___x_775_);
return v___x_776_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1(lean_object* v_x_805_, lean_object* v_a_806_, lean_object* v_a_807_){
_start:
{
lean_object* v___x_808_; uint8_t v___x_809_; 
v___x_808_ = ((lean_object*)(l_Std_Do_term___u21d3___x3d_x3e___00__closed__1));
lean_inc(v_x_805_);
v___x_809_ = l_Lean_Syntax_isOfKind(v_x_805_, v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; lean_object* v___x_811_; 
lean_dec(v_x_805_);
v___x_810_ = lean_box(1);
v___x_811_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v_a_807_);
return v___x_811_;
}
else
{
lean_object* v_quotContext_812_; lean_object* v_currMacroScope_813_; lean_object* v_ref_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v_xs_819_; uint8_t v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; size_t v_sz_854_; size_t v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; lean_object* v___x_859_; lean_object* v___x_860_; lean_object* v___x_861_; lean_object* v___x_862_; lean_object* v___x_863_; lean_object* v___x_864_; lean_object* v___x_865_; lean_object* v___x_866_; lean_object* v___x_867_; lean_object* v___x_868_; lean_object* v___x_869_; lean_object* v___x_870_; lean_object* v___x_871_; lean_object* v___x_872_; lean_object* v___x_873_; lean_object* v___x_874_; lean_object* v___x_875_; lean_object* v___x_876_; lean_object* v___x_877_; lean_object* v___x_878_; 
v_quotContext_812_ = lean_ctor_get(v_a_806_, 1);
v_currMacroScope_813_ = lean_ctor_get(v_a_806_, 2);
v_ref_814_ = lean_ctor_get(v_a_806_, 5);
v___x_815_ = lean_unsigned_to_nat(2u);
v___x_816_ = l_Lean_Syntax_getArg(v_x_805_, v___x_815_);
v___x_817_ = lean_unsigned_to_nat(4u);
v___x_818_ = l_Lean_Syntax_getArg(v_x_805_, v___x_817_);
lean_dec(v_x_805_);
v_xs_819_ = l_Lean_Syntax_getArgs(v___x_816_);
lean_dec(v___x_816_);
v___x_820_ = 0;
v___x_821_ = l_Lean_SourceInfo_fromRef(v_ref_814_, v___x_820_);
v___x_822_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_823_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1);
v___x_824_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4));
lean_inc_n(v_currMacroScope_813_, 2);
lean_inc_n(v_quotContext_812_, 2);
v___x_825_ = l_Lean_addMacroScope(v_quotContext_812_, v___x_824_, v_currMacroScope_813_);
v___x_826_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7));
lean_inc_n(v___x_821_, 23);
v___x_827_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_827_, 0, v___x_821_);
lean_ctor_set(v___x_827_, 1, v___x_823_);
lean_ctor_set(v___x_827_, 2, v___x_825_);
lean_ctor_set(v___x_827_, 3, v___x_826_);
v___x_828_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_829_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9));
v___x_830_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11));
v___x_831_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12));
v___x_832_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_832_, 0, v___x_821_);
lean_ctor_set(v___x_832_, 1, v___x_831_);
v___x_833_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14));
v___x_834_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16);
v___x_835_ = lean_box(0);
v___x_836_ = l_Lean_addMacroScope(v_quotContext_812_, v___x_835_, v_currMacroScope_813_);
v___x_837_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19));
v___x_838_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_838_, 0, v___x_821_);
lean_ctor_set(v___x_838_, 1, v___x_834_);
lean_ctor_set(v___x_838_, 2, v___x_836_);
lean_ctor_set(v___x_838_, 3, v___x_837_);
v___x_839_ = l_Lean_Syntax_node1(v___x_821_, v___x_833_, v___x_838_);
v___x_840_ = l_Lean_Syntax_node2(v___x_821_, v___x_830_, v___x_832_, v___x_839_);
v___x_841_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1));
v___x_842_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2));
v___x_843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_821_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
v___x_844_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5));
v___x_845_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7));
v___x_846_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8));
v___x_847_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9));
v___x_848_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_821_);
lean_ctor_set(v___x_848_, 1, v___x_846_);
v___x_849_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20));
v___x_850_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21));
v___x_851_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_851_, 0, v___x_821_);
lean_ctor_set(v___x_851_, 1, v___x_849_);
v___x_852_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23));
v___x_853_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
v_sz_854_ = lean_array_size(v_xs_819_);
v___x_855_ = ((size_t)0ULL);
v___x_856_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_854_, v___x_855_, v_xs_819_);
v___x_857_ = l_Array_append___redArg(v___x_853_, v___x_856_);
lean_dec_ref(v___x_856_);
v___x_858_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_858_, 0, v___x_821_);
lean_ctor_set(v___x_858_, 1, v___x_828_);
lean_ctor_set(v___x_858_, 2, v___x_857_);
v___x_859_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_859_, 0, v___x_821_);
lean_ctor_set(v___x_859_, 1, v___x_828_);
lean_ctor_set(v___x_859_, 2, v___x_853_);
v___x_860_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24));
v___x_861_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_821_);
lean_ctor_set(v___x_861_, 1, v___x_860_);
v___x_862_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26));
v___x_863_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27));
v___x_864_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_864_, 0, v___x_821_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
v___x_865_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28));
v___x_866_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_866_, 0, v___x_821_);
lean_ctor_set(v___x_866_, 1, v___x_865_);
lean_inc_ref(v___x_866_);
v___x_867_ = l_Lean_Syntax_node3(v___x_821_, v___x_862_, v___x_864_, v___x_818_, v___x_866_);
v___x_868_ = l_Lean_Syntax_node4(v___x_821_, v___x_852_, v___x_858_, v___x_859_, v___x_861_, v___x_867_);
v___x_869_ = l_Lean_Syntax_node2(v___x_821_, v___x_850_, v___x_851_, v___x_868_);
v___x_870_ = l_Lean_Syntax_node2(v___x_821_, v___x_847_, v___x_848_, v___x_869_);
v___x_871_ = l_Lean_Syntax_node1(v___x_821_, v___x_828_, v___x_870_);
v___x_872_ = l_Lean_Syntax_node1(v___x_821_, v___x_845_, v___x_871_);
v___x_873_ = l_Lean_Syntax_node1(v___x_821_, v___x_844_, v___x_872_);
v___x_874_ = l_Lean_Syntax_node2(v___x_821_, v___x_841_, v___x_843_, v___x_873_);
v___x_875_ = l_Lean_Syntax_node3(v___x_821_, v___x_829_, v___x_840_, v___x_874_, v___x_866_);
v___x_876_ = l_Lean_Syntax_node1(v___x_821_, v___x_828_, v___x_875_);
v___x_877_ = l_Lean_Syntax_node2(v___x_821_, v___x_822_, v___x_827_, v___x_876_);
v___x_878_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_878_, 0, v___x_877_);
lean_ctor_set(v___x_878_, 1, v_a_807_);
return v___x_878_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___boxed(lean_object* v_x_879_, lean_object* v_a_880_, lean_object* v_a_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1(v_x_879_, v_a_880_, v_a_881_);
lean_dec_ref(v_a_880_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_mayThrow___redArg(lean_object* v_ps_883_, lean_object* v_p_884_){
_start:
{
lean_object* v___x_885_; lean_object* v___x_886_; 
v___x_885_ = l_Std_Do_ExceptConds_const___redArg(v_ps_883_);
v___x_886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_886_, 0, v_p_884_);
lean_ctor_set(v___x_886_, 1, v___x_885_);
return v___x_886_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_mayThrow(lean_object* v_00_u03b1_887_, lean_object* v_ps_888_, lean_object* v_p_889_){
_start:
{
lean_object* v___x_890_; lean_object* v___x_891_; 
v___x_890_ = l_Std_Do_ExceptConds_const___redArg(v_ps_888_);
v___x_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_891_, 0, v_p_889_);
lean_ctor_set(v___x_891_, 1, v___x_890_);
return v___x_891_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_922_; lean_object* v___x_923_; 
v___x_922_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0));
v___x_923_ = l_String_toRawSubstring_x27(v___x_922_);
return v___x_923_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1(lean_object* v_x_939_, lean_object* v_a_940_, lean_object* v_a_941_){
_start:
{
lean_object* v___x_942_; uint8_t v___x_943_; 
v___x_942_ = ((lean_object*)(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1));
lean_inc(v_x_939_);
v___x_943_ = l_Lean_Syntax_isOfKind(v_x_939_, v___x_942_);
if (v___x_943_ == 0)
{
lean_object* v___x_944_; lean_object* v___x_945_; 
lean_dec(v_x_939_);
v___x_944_ = lean_box(1);
v___x_945_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_945_, 0, v___x_944_);
lean_ctor_set(v___x_945_, 1, v_a_941_);
return v___x_945_;
}
else
{
lean_object* v_quotContext_946_; lean_object* v_currMacroScope_947_; lean_object* v_ref_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v_xs_953_; uint8_t v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; lean_object* v___x_986_; lean_object* v___x_987_; size_t v_sz_988_; size_t v___x_989_; lean_object* v___x_990_; lean_object* v___x_991_; lean_object* v___x_992_; lean_object* v___x_993_; lean_object* v___x_994_; lean_object* v___x_995_; lean_object* v___x_996_; lean_object* v___x_997_; lean_object* v___x_998_; lean_object* v___x_999_; lean_object* v___x_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; lean_object* v___x_1003_; lean_object* v___x_1004_; lean_object* v___x_1005_; lean_object* v___x_1006_; lean_object* v___x_1007_; lean_object* v___x_1008_; lean_object* v___x_1009_; lean_object* v___x_1010_; lean_object* v___x_1011_; lean_object* v___x_1012_; 
v_quotContext_946_ = lean_ctor_get(v_a_940_, 1);
v_currMacroScope_947_ = lean_ctor_get(v_a_940_, 2);
v_ref_948_ = lean_ctor_get(v_a_940_, 5);
v___x_949_ = lean_unsigned_to_nat(2u);
v___x_950_ = l_Lean_Syntax_getArg(v_x_939_, v___x_949_);
v___x_951_ = lean_unsigned_to_nat(4u);
v___x_952_ = l_Lean_Syntax_getArg(v_x_939_, v___x_951_);
lean_dec(v_x_939_);
v_xs_953_ = l_Lean_Syntax_getArgs(v___x_950_);
lean_dec(v___x_950_);
v___x_954_ = 0;
v___x_955_ = l_Lean_SourceInfo_fromRef(v_ref_948_, v___x_954_);
v___x_956_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_957_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1);
v___x_958_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3));
lean_inc_n(v_currMacroScope_947_, 2);
lean_inc_n(v_quotContext_946_, 2);
v___x_959_ = l_Lean_addMacroScope(v_quotContext_946_, v___x_958_, v_currMacroScope_947_);
v___x_960_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6));
lean_inc_n(v___x_955_, 23);
v___x_961_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_961_, 0, v___x_955_);
lean_ctor_set(v___x_961_, 1, v___x_957_);
lean_ctor_set(v___x_961_, 2, v___x_959_);
lean_ctor_set(v___x_961_, 3, v___x_960_);
v___x_962_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_963_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9));
v___x_964_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11));
v___x_965_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12));
v___x_966_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_966_, 0, v___x_955_);
lean_ctor_set(v___x_966_, 1, v___x_965_);
v___x_967_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14));
v___x_968_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16);
v___x_969_ = lean_box(0);
v___x_970_ = l_Lean_addMacroScope(v_quotContext_946_, v___x_969_, v_currMacroScope_947_);
v___x_971_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19));
v___x_972_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_972_, 0, v___x_955_);
lean_ctor_set(v___x_972_, 1, v___x_968_);
lean_ctor_set(v___x_972_, 2, v___x_970_);
lean_ctor_set(v___x_972_, 3, v___x_971_);
v___x_973_ = l_Lean_Syntax_node1(v___x_955_, v___x_967_, v___x_972_);
v___x_974_ = l_Lean_Syntax_node2(v___x_955_, v___x_964_, v___x_966_, v___x_973_);
v___x_975_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1));
v___x_976_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2));
v___x_977_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_977_, 0, v___x_955_);
lean_ctor_set(v___x_977_, 1, v___x_976_);
v___x_978_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5));
v___x_979_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7));
v___x_980_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8));
v___x_981_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9));
v___x_982_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_982_, 0, v___x_955_);
lean_ctor_set(v___x_982_, 1, v___x_980_);
v___x_983_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20));
v___x_984_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21));
v___x_985_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_955_);
lean_ctor_set(v___x_985_, 1, v___x_983_);
v___x_986_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23));
v___x_987_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
v_sz_988_ = lean_array_size(v_xs_953_);
v___x_989_ = ((size_t)0ULL);
v___x_990_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_988_, v___x_989_, v_xs_953_);
v___x_991_ = l_Array_append___redArg(v___x_987_, v___x_990_);
lean_dec_ref(v___x_990_);
v___x_992_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_992_, 0, v___x_955_);
lean_ctor_set(v___x_992_, 1, v___x_962_);
lean_ctor_set(v___x_992_, 2, v___x_991_);
v___x_993_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_993_, 0, v___x_955_);
lean_ctor_set(v___x_993_, 1, v___x_962_);
lean_ctor_set(v___x_993_, 2, v___x_987_);
v___x_994_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24));
v___x_995_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_995_, 0, v___x_955_);
lean_ctor_set(v___x_995_, 1, v___x_994_);
v___x_996_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26));
v___x_997_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27));
v___x_998_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_998_, 0, v___x_955_);
lean_ctor_set(v___x_998_, 1, v___x_997_);
v___x_999_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28));
v___x_1000_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1000_, 0, v___x_955_);
lean_ctor_set(v___x_1000_, 1, v___x_999_);
lean_inc_ref(v___x_1000_);
v___x_1001_ = l_Lean_Syntax_node3(v___x_955_, v___x_996_, v___x_998_, v___x_952_, v___x_1000_);
v___x_1002_ = l_Lean_Syntax_node4(v___x_955_, v___x_986_, v___x_992_, v___x_993_, v___x_995_, v___x_1001_);
v___x_1003_ = l_Lean_Syntax_node2(v___x_955_, v___x_984_, v___x_985_, v___x_1002_);
v___x_1004_ = l_Lean_Syntax_node2(v___x_955_, v___x_981_, v___x_982_, v___x_1003_);
v___x_1005_ = l_Lean_Syntax_node1(v___x_955_, v___x_962_, v___x_1004_);
v___x_1006_ = l_Lean_Syntax_node1(v___x_955_, v___x_979_, v___x_1005_);
v___x_1007_ = l_Lean_Syntax_node1(v___x_955_, v___x_978_, v___x_1006_);
v___x_1008_ = l_Lean_Syntax_node2(v___x_955_, v___x_975_, v___x_977_, v___x_1007_);
v___x_1009_ = l_Lean_Syntax_node3(v___x_955_, v___x_963_, v___x_974_, v___x_1008_, v___x_1000_);
v___x_1010_ = l_Lean_Syntax_node1(v___x_955_, v___x_962_, v___x_1009_);
v___x_1011_ = l_Lean_Syntax_node2(v___x_955_, v___x_956_, v___x_961_, v___x_1010_);
v___x_1012_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1012_, 0, v___x_1011_);
lean_ctor_set(v___x_1012_, 1, v_a_941_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___boxed(lean_object* v_x_1013_, lean_object* v_a_1014_, lean_object* v_a_1015_){
_start:
{
lean_object* v_res_1016_; 
v_res_1016_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1(v_x_1013_, v_a_1014_, v_a_1015_);
lean_dec_ref(v_a_1014_);
return v_res_1016_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__0(lean_object* v_x_1017_){
_start:
{
lean_object* v___x_1018_; 
v___x_1018_ = lean_box(0);
return v___x_1018_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__0___boxed(lean_object* v_x_1019_){
_start:
{
lean_object* v_res_1020_; 
v_res_1020_ = l_Std_Do_instInhabitedPostCond___redArg___lam__0(v_x_1019_);
lean_dec(v_x_1019_);
return v_res_1020_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__1(lean_object* v_ps_1021_, lean_object* v___f_1022_, lean_object* v_x_1023_){
_start:
{
lean_object* v___x_1024_; lean_object* v___x_1025_; 
v___x_1024_ = l_Std_Do_PostShape_args(v_ps_1021_);
v___x_1025_ = l_Std_Do_SVal_curry___redArg(v___x_1024_, lean_box(0));
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__1___boxed(lean_object* v_ps_1026_, lean_object* v___f_1027_, lean_object* v_x_1028_){
_start:
{
lean_object* v_res_1029_; 
v_res_1029_ = l_Std_Do_instInhabitedPostCond___redArg___lam__1(v_ps_1026_, v___f_1027_, v_x_1028_);
lean_dec(v_x_1028_);
lean_dec(v_ps_1026_);
return v_res_1029_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg(lean_object* v_ps_1030_){
_start:
{
lean_object* v___f_1031_; lean_object* v___x_1032_; lean_object* v___x_1033_; 
lean_inc(v_ps_1030_);
v___f_1031_ = lean_alloc_closure((void*)(l_Std_Do_instInhabitedPostCond___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1031_, 0, v_ps_1030_);
lean_closure_set(v___f_1031_, 1, lean_box(0));
v___x_1032_ = l_Std_Do_ExceptConds_const___redArg(v_ps_1030_);
v___x_1033_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1033_, 0, v___f_1031_);
lean_ctor_set(v___x_1033_, 1, v___x_1032_);
return v___x_1033_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond(lean_object* v_ps_1034_, lean_object* v_00_u03b1_1035_){
_start:
{
lean_object* v___x_1036_; 
v___x_1036_ = l_Std_Do_instInhabitedPostCond___redArg(v_ps_1034_);
return v___x_1036_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1(void){
_start:
{
lean_object* v___x_1056_; lean_object* v___x_1057_; 
v___x_1056_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0));
v___x_1057_ = l_String_toRawSubstring_x27(v___x_1056_);
return v___x_1057_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1(lean_object* v_x_1072_, lean_object* v_a_1073_, lean_object* v_a_1074_){
_start:
{
lean_object* v___x_1075_; uint8_t v___x_1076_; 
v___x_1075_ = ((lean_object*)(l_Std_Do_term___u22a2_u209a___00__closed__1));
lean_inc(v_x_1072_);
v___x_1076_ = l_Lean_Syntax_isOfKind(v_x_1072_, v___x_1075_);
if (v___x_1076_ == 0)
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec(v_x_1072_);
v___x_1077_ = lean_box(1);
v___x_1078_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1078_, 0, v___x_1077_);
lean_ctor_set(v___x_1078_, 1, v_a_1074_);
return v___x_1078_;
}
else
{
lean_object* v_quotContext_1079_; lean_object* v_currMacroScope_1080_; lean_object* v_ref_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; uint8_t v___x_1086_; lean_object* v___x_1087_; lean_object* v___x_1088_; lean_object* v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; lean_object* v___x_1096_; lean_object* v___x_1097_; 
v_quotContext_1079_ = lean_ctor_get(v_a_1073_, 1);
v_currMacroScope_1080_ = lean_ctor_get(v_a_1073_, 2);
v_ref_1081_ = lean_ctor_get(v_a_1073_, 5);
v___x_1082_ = lean_unsigned_to_nat(0u);
v___x_1083_ = l_Lean_Syntax_getArg(v_x_1072_, v___x_1082_);
v___x_1084_ = lean_unsigned_to_nat(2u);
v___x_1085_ = l_Lean_Syntax_getArg(v_x_1072_, v___x_1084_);
lean_dec(v_x_1072_);
v___x_1086_ = 0;
v___x_1087_ = l_Lean_SourceInfo_fromRef(v_ref_1081_, v___x_1086_);
v___x_1088_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_1089_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1);
v___x_1090_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2));
lean_inc(v_currMacroScope_1080_);
lean_inc(v_quotContext_1079_);
v___x_1091_ = l_Lean_addMacroScope(v_quotContext_1079_, v___x_1090_, v_currMacroScope_1080_);
v___x_1092_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5));
lean_inc_n(v___x_1087_, 2);
v___x_1093_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1087_);
lean_ctor_set(v___x_1093_, 1, v___x_1089_);
lean_ctor_set(v___x_1093_, 2, v___x_1091_);
lean_ctor_set(v___x_1093_, 3, v___x_1092_);
v___x_1094_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_1095_ = l_Lean_Syntax_node2(v___x_1087_, v___x_1094_, v___x_1083_, v___x_1085_);
v___x_1096_ = l_Lean_Syntax_node2(v___x_1087_, v___x_1088_, v___x_1093_, v___x_1095_);
v___x_1097_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1097_, 0, v___x_1096_);
lean_ctor_set(v___x_1097_, 1, v_a_1074_);
return v___x_1097_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___boxed(lean_object* v_x_1098_, lean_object* v_a_1099_, lean_object* v_a_1100_){
_start:
{
lean_object* v_res_1101_; 
v_res_1101_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1(v_x_1098_, v_a_1099_, v_a_1100_);
lean_dec_ref(v_a_1099_);
return v_res_1101_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1(lean_object* v_x_1102_, lean_object* v_a_1103_, lean_object* v_a_1104_){
_start:
{
lean_object* v___x_1105_; uint8_t v___x_1106_; 
v___x_1105_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_1102_);
v___x_1106_ = l_Lean_Syntax_isOfKind(v_x_1102_, v___x_1105_);
if (v___x_1106_ == 0)
{
lean_object* v___x_1107_; lean_object* v___x_1108_; 
lean_dec(v_x_1102_);
v___x_1107_ = lean_box(0);
v___x_1108_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1108_, 0, v___x_1107_);
lean_ctor_set(v___x_1108_, 1, v_a_1104_);
return v___x_1108_;
}
else
{
lean_object* v___x_1109_; lean_object* v___x_1110_; lean_object* v___x_1111_; uint8_t v___x_1112_; 
v___x_1109_ = lean_unsigned_to_nat(0u);
v___x_1110_ = l_Lean_Syntax_getArg(v_x_1102_, v___x_1109_);
v___x_1111_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_1110_);
v___x_1112_ = l_Lean_Syntax_isOfKind(v___x_1110_, v___x_1111_);
if (v___x_1112_ == 0)
{
lean_object* v___x_1113_; lean_object* v___x_1114_; 
lean_dec(v___x_1110_);
lean_dec(v_x_1102_);
v___x_1113_ = lean_box(0);
v___x_1114_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1114_, 0, v___x_1113_);
lean_ctor_set(v___x_1114_, 1, v_a_1104_);
return v___x_1114_;
}
else
{
lean_object* v___x_1115_; lean_object* v___x_1116_; lean_object* v___x_1117_; uint8_t v___x_1118_; 
v___x_1115_ = lean_unsigned_to_nat(1u);
v___x_1116_ = l_Lean_Syntax_getArg(v_x_1102_, v___x_1115_);
lean_dec(v_x_1102_);
v___x_1117_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1116_);
v___x_1118_ = l_Lean_Syntax_matchesNull(v___x_1116_, v___x_1117_);
if (v___x_1118_ == 0)
{
lean_object* v___x_1119_; lean_object* v___x_1120_; 
lean_dec(v___x_1116_);
lean_dec(v___x_1110_);
v___x_1119_ = lean_box(0);
v___x_1120_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1120_, 0, v___x_1119_);
lean_ctor_set(v___x_1120_, 1, v_a_1104_);
return v___x_1120_;
}
else
{
lean_object* v___x_1121_; lean_object* v___x_1122_; lean_object* v_ref_1123_; uint8_t v___x_1124_; lean_object* v___x_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; lean_object* v___x_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1121_ = l_Lean_Syntax_getArg(v___x_1116_, v___x_1109_);
v___x_1122_ = l_Lean_Syntax_getArg(v___x_1116_, v___x_1115_);
lean_dec(v___x_1116_);
v_ref_1123_ = l_Lean_replaceRef(v___x_1110_, v_a_1103_);
lean_dec(v___x_1110_);
v___x_1124_ = 0;
v___x_1125_ = l_Lean_SourceInfo_fromRef(v_ref_1123_, v___x_1124_);
lean_dec(v_ref_1123_);
v___x_1126_ = ((lean_object*)(l_Std_Do_term___u22a2_u209a___00__closed__1));
v___x_1127_ = ((lean_object*)(l_Std_Do_term___u22a2_u209a___00__closed__2));
lean_inc(v___x_1125_);
v___x_1128_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1125_);
lean_ctor_set(v___x_1128_, 1, v___x_1127_);
v___x_1129_ = l_Lean_Syntax_node3(v___x_1125_, v___x_1126_, v___x_1121_, v___x_1128_, v___x_1122_);
v___x_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1130_, 0, v___x_1129_);
lean_ctor_set(v___x_1130_, 1, v_a_1104_);
return v___x_1130_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1___boxed(lean_object* v_x_1131_, lean_object* v_a_1132_, lean_object* v_a_1133_){
_start:
{
lean_object* v_res_1134_; 
v_res_1134_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1(v_x_1131_, v_a_1132_, v_a_1133_);
lean_dec(v_a_1132_);
return v_res_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg___lam__0(lean_object* v_ps_1135_, lean_object* v_fst_1136_, lean_object* v_fst_1137_, lean_object* v_a_1138_){
_start:
{
lean_object* v___x_1139_; lean_object* v___x_1140_; lean_object* v___x_1141_; lean_object* v___x_1142_; 
v___x_1139_ = l_Std_Do_PostShape_args(v_ps_1135_);
lean_inc(v_a_1138_);
v___x_1140_ = lean_apply_1(v_fst_1136_, v_a_1138_);
v___x_1141_ = lean_apply_1(v_fst_1137_, v_a_1138_);
v___x_1142_ = l_Std_Do_SPred_and(v___x_1139_, v___x_1140_, v___x_1141_);
return v___x_1142_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg___lam__0___boxed(lean_object* v_ps_1143_, lean_object* v_fst_1144_, lean_object* v_fst_1145_, lean_object* v_a_1146_){
_start:
{
lean_object* v_res_1147_; 
v_res_1147_ = l_Std_Do_PostCond_and___redArg___lam__0(v_ps_1143_, v_fst_1144_, v_fst_1145_, v_a_1146_);
lean_dec(v_ps_1143_);
return v_res_1147_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg(lean_object* v_ps_1148_, lean_object* v_p_1149_, lean_object* v_q_1150_){
_start:
{
lean_object* v_fst_1151_; lean_object* v_snd_1152_; lean_object* v_fst_1153_; lean_object* v_snd_1154_; lean_object* v___x_1156_; uint8_t v_isShared_1157_; uint8_t v_isSharedCheck_1163_; 
v_fst_1151_ = lean_ctor_get(v_p_1149_, 0);
lean_inc(v_fst_1151_);
v_snd_1152_ = lean_ctor_get(v_p_1149_, 1);
lean_inc(v_snd_1152_);
lean_dec_ref(v_p_1149_);
v_fst_1153_ = lean_ctor_get(v_q_1150_, 0);
v_snd_1154_ = lean_ctor_get(v_q_1150_, 1);
v_isSharedCheck_1163_ = !lean_is_exclusive(v_q_1150_);
if (v_isSharedCheck_1163_ == 0)
{
v___x_1156_ = v_q_1150_;
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
else
{
lean_inc(v_snd_1154_);
lean_inc(v_fst_1153_);
lean_dec(v_q_1150_);
v___x_1156_ = lean_box(0);
v_isShared_1157_ = v_isSharedCheck_1163_;
goto v_resetjp_1155_;
}
v_resetjp_1155_:
{
lean_object* v___f_1158_; lean_object* v___x_1159_; lean_object* v___x_1161_; 
lean_inc(v_ps_1148_);
v___f_1158_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_and___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1158_, 0, v_ps_1148_);
lean_closure_set(v___f_1158_, 1, v_fst_1151_);
lean_closure_set(v___f_1158_, 2, v_fst_1153_);
v___x_1159_ = l_Std_Do_ExceptConds_and(v_ps_1148_, v_snd_1152_, v_snd_1154_);
if (v_isShared_1157_ == 0)
{
lean_ctor_set(v___x_1156_, 1, v___x_1159_);
lean_ctor_set(v___x_1156_, 0, v___f_1158_);
v___x_1161_ = v___x_1156_;
goto v_reusejp_1160_;
}
else
{
lean_object* v_reuseFailAlloc_1162_; 
v_reuseFailAlloc_1162_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1162_, 0, v___f_1158_);
lean_ctor_set(v_reuseFailAlloc_1162_, 1, v___x_1159_);
v___x_1161_ = v_reuseFailAlloc_1162_;
goto v_reusejp_1160_;
}
v_reusejp_1160_:
{
return v___x_1161_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and(lean_object* v_00_u03b1_1164_, lean_object* v_ps_1165_, lean_object* v_p_1166_, lean_object* v_q_1167_){
_start:
{
lean_object* v_fst_1168_; lean_object* v_snd_1169_; lean_object* v_fst_1170_; lean_object* v_snd_1171_; lean_object* v___x_1173_; uint8_t v_isShared_1174_; uint8_t v_isSharedCheck_1180_; 
v_fst_1168_ = lean_ctor_get(v_p_1166_, 0);
lean_inc(v_fst_1168_);
v_snd_1169_ = lean_ctor_get(v_p_1166_, 1);
lean_inc(v_snd_1169_);
lean_dec_ref(v_p_1166_);
v_fst_1170_ = lean_ctor_get(v_q_1167_, 0);
v_snd_1171_ = lean_ctor_get(v_q_1167_, 1);
v_isSharedCheck_1180_ = !lean_is_exclusive(v_q_1167_);
if (v_isSharedCheck_1180_ == 0)
{
v___x_1173_ = v_q_1167_;
v_isShared_1174_ = v_isSharedCheck_1180_;
goto v_resetjp_1172_;
}
else
{
lean_inc(v_snd_1171_);
lean_inc(v_fst_1170_);
lean_dec(v_q_1167_);
v___x_1173_ = lean_box(0);
v_isShared_1174_ = v_isSharedCheck_1180_;
goto v_resetjp_1172_;
}
v_resetjp_1172_:
{
lean_object* v___f_1175_; lean_object* v___x_1176_; lean_object* v___x_1178_; 
lean_inc(v_ps_1165_);
v___f_1175_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_and___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1175_, 0, v_ps_1165_);
lean_closure_set(v___f_1175_, 1, v_fst_1168_);
lean_closure_set(v___f_1175_, 2, v_fst_1170_);
v___x_1176_ = l_Std_Do_ExceptConds_and(v_ps_1165_, v_snd_1169_, v_snd_1171_);
if (v_isShared_1174_ == 0)
{
lean_ctor_set(v___x_1173_, 1, v___x_1176_);
lean_ctor_set(v___x_1173_, 0, v___f_1175_);
v___x_1178_ = v___x_1173_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___f_1175_);
lean_ctor_set(v_reuseFailAlloc_1179_, 1, v___x_1176_);
v___x_1178_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
return v___x_1178_;
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1(void){
_start:
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
v___x_1200_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0));
v___x_1201_ = l_String_toRawSubstring_x27(v___x_1200_);
return v___x_1201_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1(lean_object* v_x_1216_, lean_object* v_a_1217_, lean_object* v_a_1218_){
_start:
{
lean_object* v___x_1219_; uint8_t v___x_1220_; 
v___x_1219_ = ((lean_object*)(l_Std_Do_term___u2227_u209a___00__closed__1));
lean_inc(v_x_1216_);
v___x_1220_ = l_Lean_Syntax_isOfKind(v_x_1216_, v___x_1219_);
if (v___x_1220_ == 0)
{
lean_object* v___x_1221_; lean_object* v___x_1222_; 
lean_dec(v_x_1216_);
v___x_1221_ = lean_box(1);
v___x_1222_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1222_, 0, v___x_1221_);
lean_ctor_set(v___x_1222_, 1, v_a_1218_);
return v___x_1222_;
}
else
{
lean_object* v_quotContext_1223_; lean_object* v_currMacroScope_1224_; lean_object* v_ref_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; uint8_t v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; lean_object* v___x_1236_; lean_object* v___x_1237_; lean_object* v___x_1238_; lean_object* v___x_1239_; lean_object* v___x_1240_; lean_object* v___x_1241_; 
v_quotContext_1223_ = lean_ctor_get(v_a_1217_, 1);
v_currMacroScope_1224_ = lean_ctor_get(v_a_1217_, 2);
v_ref_1225_ = lean_ctor_get(v_a_1217_, 5);
v___x_1226_ = lean_unsigned_to_nat(0u);
v___x_1227_ = l_Lean_Syntax_getArg(v_x_1216_, v___x_1226_);
v___x_1228_ = lean_unsigned_to_nat(2u);
v___x_1229_ = l_Lean_Syntax_getArg(v_x_1216_, v___x_1228_);
lean_dec(v_x_1216_);
v___x_1230_ = 0;
v___x_1231_ = l_Lean_SourceInfo_fromRef(v_ref_1225_, v___x_1230_);
v___x_1232_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_1233_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1);
v___x_1234_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2));
lean_inc(v_currMacroScope_1224_);
lean_inc(v_quotContext_1223_);
v___x_1235_ = l_Lean_addMacroScope(v_quotContext_1223_, v___x_1234_, v_currMacroScope_1224_);
v___x_1236_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5));
lean_inc_n(v___x_1231_, 2);
v___x_1237_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1237_, 0, v___x_1231_);
lean_ctor_set(v___x_1237_, 1, v___x_1233_);
lean_ctor_set(v___x_1237_, 2, v___x_1235_);
lean_ctor_set(v___x_1237_, 3, v___x_1236_);
v___x_1238_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_1239_ = l_Lean_Syntax_node2(v___x_1231_, v___x_1238_, v___x_1227_, v___x_1229_);
v___x_1240_ = l_Lean_Syntax_node2(v___x_1231_, v___x_1232_, v___x_1237_, v___x_1239_);
v___x_1241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1241_, 0, v___x_1240_);
lean_ctor_set(v___x_1241_, 1, v_a_1218_);
return v___x_1241_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___boxed(lean_object* v_x_1242_, lean_object* v_a_1243_, lean_object* v_a_1244_){
_start:
{
lean_object* v_res_1245_; 
v_res_1245_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1(v_x_1242_, v_a_1243_, v_a_1244_);
lean_dec_ref(v_a_1243_);
return v_res_1245_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1(lean_object* v_x_1246_, lean_object* v_a_1247_, lean_object* v_a_1248_){
_start:
{
lean_object* v___x_1249_; uint8_t v___x_1250_; 
v___x_1249_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_1246_);
v___x_1250_ = l_Lean_Syntax_isOfKind(v_x_1246_, v___x_1249_);
if (v___x_1250_ == 0)
{
lean_object* v___x_1251_; lean_object* v___x_1252_; 
lean_dec(v_x_1246_);
v___x_1251_ = lean_box(0);
v___x_1252_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1252_, 0, v___x_1251_);
lean_ctor_set(v___x_1252_, 1, v_a_1248_);
return v___x_1252_;
}
else
{
lean_object* v___x_1253_; lean_object* v___x_1254_; lean_object* v___x_1255_; uint8_t v___x_1256_; 
v___x_1253_ = lean_unsigned_to_nat(0u);
v___x_1254_ = l_Lean_Syntax_getArg(v_x_1246_, v___x_1253_);
v___x_1255_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_1254_);
v___x_1256_ = l_Lean_Syntax_isOfKind(v___x_1254_, v___x_1255_);
if (v___x_1256_ == 0)
{
lean_object* v___x_1257_; lean_object* v___x_1258_; 
lean_dec(v___x_1254_);
lean_dec(v_x_1246_);
v___x_1257_ = lean_box(0);
v___x_1258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1258_, 0, v___x_1257_);
lean_ctor_set(v___x_1258_, 1, v_a_1248_);
return v___x_1258_;
}
else
{
lean_object* v___x_1259_; lean_object* v___x_1260_; lean_object* v___x_1261_; uint8_t v___x_1262_; 
v___x_1259_ = lean_unsigned_to_nat(1u);
v___x_1260_ = l_Lean_Syntax_getArg(v_x_1246_, v___x_1259_);
lean_dec(v_x_1246_);
v___x_1261_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1260_);
v___x_1262_ = l_Lean_Syntax_matchesNull(v___x_1260_, v___x_1261_);
if (v___x_1262_ == 0)
{
lean_object* v___x_1263_; lean_object* v___x_1264_; 
lean_dec(v___x_1260_);
lean_dec(v___x_1254_);
v___x_1263_ = lean_box(0);
v___x_1264_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1264_, 0, v___x_1263_);
lean_ctor_set(v___x_1264_, 1, v_a_1248_);
return v___x_1264_;
}
else
{
lean_object* v___x_1265_; lean_object* v___x_1266_; lean_object* v_ref_1267_; uint8_t v___x_1268_; lean_object* v___x_1269_; lean_object* v___x_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; lean_object* v___x_1274_; 
v___x_1265_ = l_Lean_Syntax_getArg(v___x_1260_, v___x_1253_);
v___x_1266_ = l_Lean_Syntax_getArg(v___x_1260_, v___x_1259_);
lean_dec(v___x_1260_);
v_ref_1267_ = l_Lean_replaceRef(v___x_1254_, v_a_1247_);
lean_dec(v___x_1254_);
v___x_1268_ = 0;
v___x_1269_ = l_Lean_SourceInfo_fromRef(v_ref_1267_, v___x_1268_);
lean_dec(v_ref_1267_);
v___x_1270_ = ((lean_object*)(l_Std_Do_term___u2227_u209a___00__closed__1));
v___x_1271_ = ((lean_object*)(l_Std_Do_term___u2227_u209a___00__closed__2));
lean_inc(v___x_1269_);
v___x_1272_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1272_, 0, v___x_1269_);
lean_ctor_set(v___x_1272_, 1, v___x_1271_);
v___x_1273_ = l_Lean_Syntax_node3(v___x_1269_, v___x_1270_, v___x_1265_, v___x_1272_, v___x_1266_);
v___x_1274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1274_, 0, v___x_1273_);
lean_ctor_set(v___x_1274_, 1, v_a_1248_);
return v___x_1274_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1___boxed(lean_object* v_x_1275_, lean_object* v_a_1276_, lean_object* v_a_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1(v_x_1275_, v_a_1276_, v_a_1277_);
lean_dec(v_a_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg___lam__0(lean_object* v_ps_1279_, lean_object* v_fst_1280_, lean_object* v_fst_1281_, lean_object* v_a_1282_){
_start:
{
lean_object* v___x_1283_; lean_object* v___x_1284_; lean_object* v___x_1285_; lean_object* v___x_1286_; 
v___x_1283_ = l_Std_Do_PostShape_args(v_ps_1279_);
lean_inc(v_a_1282_);
v___x_1284_ = lean_apply_1(v_fst_1280_, v_a_1282_);
v___x_1285_ = lean_apply_1(v_fst_1281_, v_a_1282_);
v___x_1286_ = l_Std_Do_SPred_imp(v___x_1283_, v___x_1284_, v___x_1285_);
return v___x_1286_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg___lam__0___boxed(lean_object* v_ps_1287_, lean_object* v_fst_1288_, lean_object* v_fst_1289_, lean_object* v_a_1290_){
_start:
{
lean_object* v_res_1291_; 
v_res_1291_ = l_Std_Do_PostCond_imp___redArg___lam__0(v_ps_1287_, v_fst_1288_, v_fst_1289_, v_a_1290_);
lean_dec(v_ps_1287_);
return v_res_1291_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg(lean_object* v_ps_1292_, lean_object* v_p_1293_, lean_object* v_q_1294_){
_start:
{
lean_object* v_fst_1295_; lean_object* v_snd_1296_; lean_object* v_fst_1297_; lean_object* v_snd_1298_; lean_object* v___x_1300_; uint8_t v_isShared_1301_; uint8_t v_isSharedCheck_1307_; 
v_fst_1295_ = lean_ctor_get(v_p_1293_, 0);
lean_inc(v_fst_1295_);
v_snd_1296_ = lean_ctor_get(v_p_1293_, 1);
lean_inc(v_snd_1296_);
lean_dec_ref(v_p_1293_);
v_fst_1297_ = lean_ctor_get(v_q_1294_, 0);
v_snd_1298_ = lean_ctor_get(v_q_1294_, 1);
v_isSharedCheck_1307_ = !lean_is_exclusive(v_q_1294_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1300_ = v_q_1294_;
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
else
{
lean_inc(v_snd_1298_);
lean_inc(v_fst_1297_);
lean_dec(v_q_1294_);
v___x_1300_ = lean_box(0);
v_isShared_1301_ = v_isSharedCheck_1307_;
goto v_resetjp_1299_;
}
v_resetjp_1299_:
{
lean_object* v___f_1302_; lean_object* v___x_1303_; lean_object* v___x_1305_; 
lean_inc(v_ps_1292_);
v___f_1302_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_imp___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1302_, 0, v_ps_1292_);
lean_closure_set(v___f_1302_, 1, v_fst_1295_);
lean_closure_set(v___f_1302_, 2, v_fst_1297_);
v___x_1303_ = l_Std_Do_ExceptConds_imp(v_ps_1292_, v_snd_1296_, v_snd_1298_);
if (v_isShared_1301_ == 0)
{
lean_ctor_set(v___x_1300_, 1, v___x_1303_);
lean_ctor_set(v___x_1300_, 0, v___f_1302_);
v___x_1305_ = v___x_1300_;
goto v_reusejp_1304_;
}
else
{
lean_object* v_reuseFailAlloc_1306_; 
v_reuseFailAlloc_1306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1306_, 0, v___f_1302_);
lean_ctor_set(v_reuseFailAlloc_1306_, 1, v___x_1303_);
v___x_1305_ = v_reuseFailAlloc_1306_;
goto v_reusejp_1304_;
}
v_reusejp_1304_:
{
return v___x_1305_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp(lean_object* v_00_u03b1_1308_, lean_object* v_ps_1309_, lean_object* v_p_1310_, lean_object* v_q_1311_){
_start:
{
lean_object* v_fst_1312_; lean_object* v_snd_1313_; lean_object* v_fst_1314_; lean_object* v_snd_1315_; lean_object* v___x_1317_; uint8_t v_isShared_1318_; uint8_t v_isSharedCheck_1324_; 
v_fst_1312_ = lean_ctor_get(v_p_1310_, 0);
lean_inc(v_fst_1312_);
v_snd_1313_ = lean_ctor_get(v_p_1310_, 1);
lean_inc(v_snd_1313_);
lean_dec_ref(v_p_1310_);
v_fst_1314_ = lean_ctor_get(v_q_1311_, 0);
v_snd_1315_ = lean_ctor_get(v_q_1311_, 1);
v_isSharedCheck_1324_ = !lean_is_exclusive(v_q_1311_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1317_ = v_q_1311_;
v_isShared_1318_ = v_isSharedCheck_1324_;
goto v_resetjp_1316_;
}
else
{
lean_inc(v_snd_1315_);
lean_inc(v_fst_1314_);
lean_dec(v_q_1311_);
v___x_1317_ = lean_box(0);
v_isShared_1318_ = v_isSharedCheck_1324_;
goto v_resetjp_1316_;
}
v_resetjp_1316_:
{
lean_object* v___f_1319_; lean_object* v___x_1320_; lean_object* v___x_1322_; 
lean_inc(v_ps_1309_);
v___f_1319_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_imp___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1319_, 0, v_ps_1309_);
lean_closure_set(v___f_1319_, 1, v_fst_1312_);
lean_closure_set(v___f_1319_, 2, v_fst_1314_);
v___x_1320_ = l_Std_Do_ExceptConds_imp(v_ps_1309_, v_snd_1313_, v_snd_1315_);
if (v_isShared_1318_ == 0)
{
lean_ctor_set(v___x_1317_, 1, v___x_1320_);
lean_ctor_set(v___x_1317_, 0, v___f_1319_);
v___x_1322_ = v___x_1317_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___f_1319_);
lean_ctor_set(v_reuseFailAlloc_1323_, 1, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1(void){
_start:
{
lean_object* v___x_1344_; lean_object* v___x_1345_; 
v___x_1344_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0));
v___x_1345_ = l_String_toRawSubstring_x27(v___x_1344_);
return v___x_1345_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1(lean_object* v_x_1360_, lean_object* v_a_1361_, lean_object* v_a_1362_){
_start:
{
lean_object* v___x_1363_; uint8_t v___x_1364_; 
v___x_1363_ = ((lean_object*)(l_Std_Do_term___u2192_u209a___00__closed__1));
lean_inc(v_x_1360_);
v___x_1364_ = l_Lean_Syntax_isOfKind(v_x_1360_, v___x_1363_);
if (v___x_1364_ == 0)
{
lean_object* v___x_1365_; lean_object* v___x_1366_; 
lean_dec(v_x_1360_);
v___x_1365_ = lean_box(1);
v___x_1366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1366_, 0, v___x_1365_);
lean_ctor_set(v___x_1366_, 1, v_a_1362_);
return v___x_1366_;
}
else
{
lean_object* v_quotContext_1367_; lean_object* v_currMacroScope_1368_; lean_object* v_ref_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; uint8_t v___x_1374_; lean_object* v___x_1375_; lean_object* v___x_1376_; lean_object* v___x_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; lean_object* v___x_1385_; 
v_quotContext_1367_ = lean_ctor_get(v_a_1361_, 1);
v_currMacroScope_1368_ = lean_ctor_get(v_a_1361_, 2);
v_ref_1369_ = lean_ctor_get(v_a_1361_, 5);
v___x_1370_ = lean_unsigned_to_nat(0u);
v___x_1371_ = l_Lean_Syntax_getArg(v_x_1360_, v___x_1370_);
v___x_1372_ = lean_unsigned_to_nat(2u);
v___x_1373_ = l_Lean_Syntax_getArg(v_x_1360_, v___x_1372_);
lean_dec(v_x_1360_);
v___x_1374_ = 0;
v___x_1375_ = l_Lean_SourceInfo_fromRef(v_ref_1369_, v___x_1374_);
v___x_1376_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_1377_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1);
v___x_1378_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2));
lean_inc(v_currMacroScope_1368_);
lean_inc(v_quotContext_1367_);
v___x_1379_ = l_Lean_addMacroScope(v_quotContext_1367_, v___x_1378_, v_currMacroScope_1368_);
v___x_1380_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5));
lean_inc_n(v___x_1375_, 2);
v___x_1381_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1381_, 0, v___x_1375_);
lean_ctor_set(v___x_1381_, 1, v___x_1377_);
lean_ctor_set(v___x_1381_, 2, v___x_1379_);
lean_ctor_set(v___x_1381_, 3, v___x_1380_);
v___x_1382_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_1383_ = l_Lean_Syntax_node2(v___x_1375_, v___x_1382_, v___x_1371_, v___x_1373_);
v___x_1384_ = l_Lean_Syntax_node2(v___x_1375_, v___x_1376_, v___x_1381_, v___x_1383_);
v___x_1385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1385_, 0, v___x_1384_);
lean_ctor_set(v___x_1385_, 1, v_a_1362_);
return v___x_1385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___boxed(lean_object* v_x_1386_, lean_object* v_a_1387_, lean_object* v_a_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1(v_x_1386_, v_a_1387_, v_a_1388_);
lean_dec_ref(v_a_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1(lean_object* v_x_1390_, lean_object* v_a_1391_, lean_object* v_a_1392_){
_start:
{
lean_object* v___x_1393_; uint8_t v___x_1394_; 
v___x_1393_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_1390_);
v___x_1394_ = l_Lean_Syntax_isOfKind(v_x_1390_, v___x_1393_);
if (v___x_1394_ == 0)
{
lean_object* v___x_1395_; lean_object* v___x_1396_; 
lean_dec(v_x_1390_);
v___x_1395_ = lean_box(0);
v___x_1396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1396_, 0, v___x_1395_);
lean_ctor_set(v___x_1396_, 1, v_a_1392_);
return v___x_1396_;
}
else
{
lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; uint8_t v___x_1400_; 
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = l_Lean_Syntax_getArg(v_x_1390_, v___x_1397_);
v___x_1399_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_1398_);
v___x_1400_ = l_Lean_Syntax_isOfKind(v___x_1398_, v___x_1399_);
if (v___x_1400_ == 0)
{
lean_object* v___x_1401_; lean_object* v___x_1402_; 
lean_dec(v___x_1398_);
lean_dec(v_x_1390_);
v___x_1401_ = lean_box(0);
v___x_1402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1402_, 0, v___x_1401_);
lean_ctor_set(v___x_1402_, 1, v_a_1392_);
return v___x_1402_;
}
else
{
lean_object* v___x_1403_; lean_object* v___x_1404_; lean_object* v___x_1405_; uint8_t v___x_1406_; 
v___x_1403_ = lean_unsigned_to_nat(1u);
v___x_1404_ = l_Lean_Syntax_getArg(v_x_1390_, v___x_1403_);
lean_dec(v_x_1390_);
v___x_1405_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1404_);
v___x_1406_ = l_Lean_Syntax_matchesNull(v___x_1404_, v___x_1405_);
if (v___x_1406_ == 0)
{
lean_object* v___x_1407_; lean_object* v___x_1408_; 
lean_dec(v___x_1404_);
lean_dec(v___x_1398_);
v___x_1407_ = lean_box(0);
v___x_1408_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1408_, 0, v___x_1407_);
lean_ctor_set(v___x_1408_, 1, v_a_1392_);
return v___x_1408_;
}
else
{
lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v_ref_1411_; uint8_t v___x_1412_; lean_object* v___x_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
v___x_1409_ = l_Lean_Syntax_getArg(v___x_1404_, v___x_1397_);
v___x_1410_ = l_Lean_Syntax_getArg(v___x_1404_, v___x_1403_);
lean_dec(v___x_1404_);
v_ref_1411_ = l_Lean_replaceRef(v___x_1398_, v_a_1391_);
lean_dec(v___x_1398_);
v___x_1412_ = 0;
v___x_1413_ = l_Lean_SourceInfo_fromRef(v_ref_1411_, v___x_1412_);
lean_dec(v_ref_1411_);
v___x_1414_ = ((lean_object*)(l_Std_Do_term___u2192_u209a___00__closed__1));
v___x_1415_ = ((lean_object*)(l_Std_Do_term___u2192_u209a___00__closed__2));
lean_inc(v___x_1413_);
v___x_1416_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1413_);
lean_ctor_set(v___x_1416_, 1, v___x_1415_);
v___x_1417_ = l_Lean_Syntax_node3(v___x_1413_, v___x_1414_, v___x_1409_, v___x_1416_, v___x_1410_);
v___x_1418_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
lean_ctor_set(v___x_1418_, 1, v_a_1392_);
return v___x_1418_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1___boxed(lean_object* v_x_1419_, lean_object* v_a_1420_, lean_object* v_a_1421_){
_start:
{
lean_object* v_res_1422_; 
v_res_1422_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1(v_x_1419_, v_a_1420_, v_a_1421_);
lean_dec(v_a_1420_);
return v_res_1422_;
}
}
lean_object* runtime_initialize_Std_Do_SPred(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_PostCond(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Do_SPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Do_PostCond(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Do_SPred(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Do_PostCond(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Do_SPred(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Do_PostCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Do_PostCond(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Do_PostCond(builtin);
}
#ifdef __cplusplus
}
#endif
