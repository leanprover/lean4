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
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and___lam__0(lean_object* v_a_209_, lean_object* v_fst_210_, lean_object* v_fst_211_, lean_object* v_e_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_213_ = l_Std_Do_PostShape_args(v_a_209_);
lean_inc(v_e_212_);
v___x_214_ = lean_apply_1(v_fst_210_, v_e_212_);
v___x_215_ = lean_apply_1(v_fst_211_, v_e_212_);
v___x_216_ = l_Std_Do_SPred_and(v___x_213_, v___x_214_, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and___lam__0___boxed(lean_object* v_a_217_, lean_object* v_fst_218_, lean_object* v_fst_219_, lean_object* v_e_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_Do_ExceptConds_and___lam__0(v_a_217_, v_fst_218_, v_fst_219_, v_e_220_);
lean_dec(v_a_217_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and(lean_object* v_ps_222_, lean_object* v_x_223_, lean_object* v_y_224_){
_start:
{
switch(lean_obj_tag(v_ps_222_))
{
case 0:
{
lean_object* v___x_225_; 
lean_dec(v_y_224_);
lean_dec(v_x_223_);
v___x_225_ = lean_box(0);
return v___x_225_;
}
case 1:
{
lean_object* v_a_226_; 
v_a_226_ = lean_ctor_get(v_ps_222_, 0);
lean_inc(v_a_226_);
lean_dec_ref_known(v_ps_222_, 1);
v_ps_222_ = v_a_226_;
goto _start;
}
default: 
{
lean_object* v_a_228_; lean_object* v_fst_229_; lean_object* v_snd_230_; lean_object* v_fst_231_; lean_object* v_snd_232_; lean_object* v___x_234_; uint8_t v_isShared_235_; uint8_t v_isSharedCheck_241_; 
v_a_228_ = lean_ctor_get(v_ps_222_, 0);
lean_inc(v_a_228_);
lean_dec_ref_known(v_ps_222_, 1);
v_fst_229_ = lean_ctor_get(v_x_223_, 0);
lean_inc(v_fst_229_);
v_snd_230_ = lean_ctor_get(v_x_223_, 1);
lean_inc(v_snd_230_);
lean_dec(v_x_223_);
v_fst_231_ = lean_ctor_get(v_y_224_, 0);
v_snd_232_ = lean_ctor_get(v_y_224_, 1);
v_isSharedCheck_241_ = !lean_is_exclusive(v_y_224_);
if (v_isSharedCheck_241_ == 0)
{
v___x_234_ = v_y_224_;
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
else
{
lean_inc(v_snd_232_);
lean_inc(v_fst_231_);
lean_dec(v_y_224_);
v___x_234_ = lean_box(0);
v_isShared_235_ = v_isSharedCheck_241_;
goto v_resetjp_233_;
}
v_resetjp_233_:
{
lean_object* v___f_236_; lean_object* v___x_237_; lean_object* v___x_239_; 
lean_inc(v_a_228_);
v___f_236_ = lean_alloc_closure((void*)(l_Std_Do_ExceptConds_and___lam__0___boxed), 4, 3);
lean_closure_set(v___f_236_, 0, v_a_228_);
lean_closure_set(v___f_236_, 1, v_fst_229_);
lean_closure_set(v___f_236_, 2, v_fst_231_);
v___x_237_ = l_Std_Do_ExceptConds_and(v_a_228_, v_snd_230_, v_snd_232_);
if (v_isShared_235_ == 0)
{
lean_ctor_set(v___x_234_, 1, v___x_237_);
lean_ctor_set(v___x_234_, 0, v___f_236_);
v___x_239_ = v___x_234_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_240_; 
v_reuseFailAlloc_240_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_240_, 0, v___f_236_);
lean_ctor_set(v_reuseFailAlloc_240_, 1, v___x_237_);
v___x_239_ = v_reuseFailAlloc_240_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
return v___x_239_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1(void){
_start:
{
lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_264_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0));
v___x_265_ = l_String_toRawSubstring_x27(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1(lean_object* v_x_281_, lean_object* v_a_282_, lean_object* v_a_283_){
_start:
{
lean_object* v___x_284_; uint8_t v___x_285_; 
v___x_284_ = ((lean_object*)(l_Std_Do_term___u2227_u2091___00__closed__1));
lean_inc(v_x_281_);
v___x_285_ = l_Lean_Syntax_isOfKind(v_x_281_, v___x_284_);
if (v___x_285_ == 0)
{
lean_object* v___x_286_; lean_object* v___x_287_; 
lean_dec(v_x_281_);
v___x_286_ = lean_box(1);
v___x_287_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_287_, 0, v___x_286_);
lean_ctor_set(v___x_287_, 1, v_a_283_);
return v___x_287_;
}
else
{
lean_object* v_quotContext_288_; lean_object* v_currMacroScope_289_; lean_object* v_ref_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; uint8_t v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
v_quotContext_288_ = lean_ctor_get(v_a_282_, 1);
v_currMacroScope_289_ = lean_ctor_get(v_a_282_, 2);
v_ref_290_ = lean_ctor_get(v_a_282_, 5);
v___x_291_ = lean_unsigned_to_nat(0u);
v___x_292_ = l_Lean_Syntax_getArg(v_x_281_, v___x_291_);
v___x_293_ = lean_unsigned_to_nat(2u);
v___x_294_ = l_Lean_Syntax_getArg(v_x_281_, v___x_293_);
lean_dec(v_x_281_);
v___x_295_ = 0;
v___x_296_ = l_Lean_SourceInfo_fromRef(v_ref_290_, v___x_295_);
v___x_297_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_298_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1);
v___x_299_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3));
lean_inc(v_currMacroScope_289_);
lean_inc(v_quotContext_288_);
v___x_300_ = l_Lean_addMacroScope(v_quotContext_288_, v___x_299_, v_currMacroScope_289_);
v___x_301_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6));
lean_inc_n(v___x_296_, 2);
v___x_302_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_302_, 0, v___x_296_);
lean_ctor_set(v___x_302_, 1, v___x_298_);
lean_ctor_set(v___x_302_, 2, v___x_300_);
lean_ctor_set(v___x_302_, 3, v___x_301_);
v___x_303_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_304_ = l_Lean_Syntax_node2(v___x_296_, v___x_303_, v___x_292_, v___x_294_);
v___x_305_ = l_Lean_Syntax_node2(v___x_296_, v___x_297_, v___x_302_, v___x_304_);
v___x_306_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_306_, 0, v___x_305_);
lean_ctor_set(v___x_306_, 1, v_a_283_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___boxed(lean_object* v_x_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1(v_x_307_, v_a_308_, v_a_309_);
lean_dec_ref(v_a_308_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1(lean_object* v_x_311_, lean_object* v_a_312_, lean_object* v_a_313_){
_start:
{
lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_314_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_311_);
v___x_315_ = l_Lean_Syntax_isOfKind(v_x_311_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v_x_311_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_a_313_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_318_ = lean_unsigned_to_nat(0u);
v___x_319_ = l_Lean_Syntax_getArg(v_x_311_, v___x_318_);
v___x_320_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_319_);
v___x_321_ = l_Lean_Syntax_isOfKind(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v___x_319_);
lean_dec(v_x_311_);
v___x_322_ = lean_box(0);
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_a_313_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; uint8_t v___x_327_; 
v___x_324_ = lean_unsigned_to_nat(1u);
v___x_325_ = l_Lean_Syntax_getArg(v_x_311_, v___x_324_);
lean_dec(v_x_311_);
v___x_326_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_325_);
v___x_327_ = l_Lean_Syntax_matchesNull(v___x_325_, v___x_326_);
if (v___x_327_ == 0)
{
lean_object* v___x_328_; lean_object* v___x_329_; 
lean_dec(v___x_325_);
lean_dec(v___x_319_);
v___x_328_ = lean_box(0);
v___x_329_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v_a_313_);
return v___x_329_;
}
else
{
lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v_ref_332_; uint8_t v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v___x_330_ = l_Lean_Syntax_getArg(v___x_325_, v___x_318_);
v___x_331_ = l_Lean_Syntax_getArg(v___x_325_, v___x_324_);
lean_dec(v___x_325_);
v_ref_332_ = l_Lean_replaceRef(v___x_319_, v_a_312_);
lean_dec(v___x_319_);
v___x_333_ = 0;
v___x_334_ = l_Lean_SourceInfo_fromRef(v_ref_332_, v___x_333_);
lean_dec(v_ref_332_);
v___x_335_ = ((lean_object*)(l_Std_Do_term___u2227_u2091___00__closed__1));
v___x_336_ = ((lean_object*)(l_Std_Do_term___u2227_u2091___00__closed__2));
lean_inc(v___x_334_);
v___x_337_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_334_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = l_Lean_Syntax_node3(v___x_334_, v___x_335_, v___x_330_, v___x_337_, v___x_331_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v_a_313_);
return v___x_339_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1___boxed(lean_object* v_x_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v_res_343_; 
v_res_343_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1(v_x_340_, v_a_341_, v_a_342_);
lean_dec(v_a_341_);
return v_res_343_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp___lam__0(lean_object* v_a_344_, lean_object* v_fst_345_, lean_object* v_fst_346_, lean_object* v_e_347_){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_348_ = l_Std_Do_PostShape_args(v_a_344_);
lean_inc(v_e_347_);
v___x_349_ = lean_apply_1(v_fst_345_, v_e_347_);
v___x_350_ = lean_apply_1(v_fst_346_, v_e_347_);
v___x_351_ = l_Std_Do_SPred_imp(v___x_348_, v___x_349_, v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp___lam__0___boxed(lean_object* v_a_352_, lean_object* v_fst_353_, lean_object* v_fst_354_, lean_object* v_e_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_Do_ExceptConds_imp___lam__0(v_a_352_, v_fst_353_, v_fst_354_, v_e_355_);
lean_dec(v_a_352_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp(lean_object* v_ps_357_, lean_object* v_x_358_, lean_object* v_y_359_){
_start:
{
switch(lean_obj_tag(v_ps_357_))
{
case 0:
{
lean_object* v___x_360_; 
lean_dec(v_y_359_);
lean_dec(v_x_358_);
v___x_360_ = lean_box(0);
return v___x_360_;
}
case 1:
{
lean_object* v_a_361_; 
v_a_361_ = lean_ctor_get(v_ps_357_, 0);
lean_inc(v_a_361_);
lean_dec_ref_known(v_ps_357_, 1);
v_ps_357_ = v_a_361_;
goto _start;
}
default: 
{
lean_object* v_a_363_; lean_object* v_fst_364_; lean_object* v_snd_365_; lean_object* v_fst_366_; lean_object* v_snd_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_376_; 
v_a_363_ = lean_ctor_get(v_ps_357_, 0);
lean_inc(v_a_363_);
lean_dec_ref_known(v_ps_357_, 1);
v_fst_364_ = lean_ctor_get(v_x_358_, 0);
lean_inc(v_fst_364_);
v_snd_365_ = lean_ctor_get(v_x_358_, 1);
lean_inc(v_snd_365_);
lean_dec(v_x_358_);
v_fst_366_ = lean_ctor_get(v_y_359_, 0);
v_snd_367_ = lean_ctor_get(v_y_359_, 1);
v_isSharedCheck_376_ = !lean_is_exclusive(v_y_359_);
if (v_isSharedCheck_376_ == 0)
{
v___x_369_ = v_y_359_;
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_snd_367_);
lean_inc(v_fst_366_);
lean_dec(v_y_359_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_376_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___f_371_; lean_object* v___x_372_; lean_object* v___x_374_; 
lean_inc(v_a_363_);
v___f_371_ = lean_alloc_closure((void*)(l_Std_Do_ExceptConds_imp___lam__0___boxed), 4, 3);
lean_closure_set(v___f_371_, 0, v_a_363_);
lean_closure_set(v___f_371_, 1, v_fst_364_);
lean_closure_set(v___f_371_, 2, v_fst_366_);
v___x_372_ = l_Std_Do_ExceptConds_imp(v_a_363_, v_snd_365_, v_snd_367_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v___x_372_);
lean_ctor_set(v___x_369_, 0, v___f_371_);
v___x_374_ = v___x_369_;
goto v_reusejp_373_;
}
else
{
lean_object* v_reuseFailAlloc_375_; 
v_reuseFailAlloc_375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_375_, 0, v___f_371_);
lean_ctor_set(v_reuseFailAlloc_375_, 1, v___x_372_);
v___x_374_ = v_reuseFailAlloc_375_;
goto v_reusejp_373_;
}
v_reusejp_373_:
{
return v___x_374_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1(void){
_start:
{
lean_object* v___x_396_; lean_object* v___x_397_; 
v___x_396_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0));
v___x_397_ = l_String_toRawSubstring_x27(v___x_396_);
return v___x_397_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1(lean_object* v_x_413_, lean_object* v_a_414_, lean_object* v_a_415_){
_start:
{
lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_416_ = ((lean_object*)(l_Std_Do_term___u2192_u2091___00__closed__1));
lean_inc(v_x_413_);
v___x_417_ = l_Lean_Syntax_isOfKind(v_x_413_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v_x_413_);
v___x_418_ = lean_box(1);
v___x_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v_a_415_);
return v___x_419_;
}
else
{
lean_object* v_quotContext_420_; lean_object* v_currMacroScope_421_; lean_object* v_ref_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; lean_object* v___x_433_; lean_object* v___x_434_; lean_object* v___x_435_; lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_438_; 
v_quotContext_420_ = lean_ctor_get(v_a_414_, 1);
v_currMacroScope_421_ = lean_ctor_get(v_a_414_, 2);
v_ref_422_ = lean_ctor_get(v_a_414_, 5);
v___x_423_ = lean_unsigned_to_nat(0u);
v___x_424_ = l_Lean_Syntax_getArg(v_x_413_, v___x_423_);
v___x_425_ = lean_unsigned_to_nat(2u);
v___x_426_ = l_Lean_Syntax_getArg(v_x_413_, v___x_425_);
lean_dec(v_x_413_);
v___x_427_ = 0;
v___x_428_ = l_Lean_SourceInfo_fromRef(v_ref_422_, v___x_427_);
v___x_429_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_430_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1);
v___x_431_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3));
lean_inc(v_currMacroScope_421_);
lean_inc(v_quotContext_420_);
v___x_432_ = l_Lean_addMacroScope(v_quotContext_420_, v___x_431_, v_currMacroScope_421_);
v___x_433_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6));
lean_inc_n(v___x_428_, 2);
v___x_434_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_434_, 0, v___x_428_);
lean_ctor_set(v___x_434_, 1, v___x_430_);
lean_ctor_set(v___x_434_, 2, v___x_432_);
lean_ctor_set(v___x_434_, 3, v___x_433_);
v___x_435_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_436_ = l_Lean_Syntax_node2(v___x_428_, v___x_435_, v___x_424_, v___x_426_);
v___x_437_ = l_Lean_Syntax_node2(v___x_428_, v___x_429_, v___x_434_, v___x_436_);
v___x_438_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_438_, 0, v___x_437_);
lean_ctor_set(v___x_438_, 1, v_a_415_);
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___boxed(lean_object* v_x_439_, lean_object* v_a_440_, lean_object* v_a_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1(v_x_439_, v_a_440_, v_a_441_);
lean_dec_ref(v_a_440_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1(lean_object* v_x_443_, lean_object* v_a_444_, lean_object* v_a_445_){
_start:
{
lean_object* v___x_446_; uint8_t v___x_447_; 
v___x_446_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_443_);
v___x_447_ = l_Lean_Syntax_isOfKind(v_x_443_, v___x_446_);
if (v___x_447_ == 0)
{
lean_object* v___x_448_; lean_object* v___x_449_; 
lean_dec(v_x_443_);
v___x_448_ = lean_box(0);
v___x_449_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_449_, 0, v___x_448_);
lean_ctor_set(v___x_449_, 1, v_a_445_);
return v___x_449_;
}
else
{
lean_object* v___x_450_; lean_object* v___x_451_; lean_object* v___x_452_; uint8_t v___x_453_; 
v___x_450_ = lean_unsigned_to_nat(0u);
v___x_451_ = l_Lean_Syntax_getArg(v_x_443_, v___x_450_);
v___x_452_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_451_);
v___x_453_ = l_Lean_Syntax_isOfKind(v___x_451_, v___x_452_);
if (v___x_453_ == 0)
{
lean_object* v___x_454_; lean_object* v___x_455_; 
lean_dec(v___x_451_);
lean_dec(v_x_443_);
v___x_454_ = lean_box(0);
v___x_455_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_455_, 0, v___x_454_);
lean_ctor_set(v___x_455_, 1, v_a_445_);
return v___x_455_;
}
else
{
lean_object* v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; uint8_t v___x_459_; 
v___x_456_ = lean_unsigned_to_nat(1u);
v___x_457_ = l_Lean_Syntax_getArg(v_x_443_, v___x_456_);
lean_dec(v_x_443_);
v___x_458_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_457_);
v___x_459_ = l_Lean_Syntax_matchesNull(v___x_457_, v___x_458_);
if (v___x_459_ == 0)
{
lean_object* v___x_460_; lean_object* v___x_461_; 
lean_dec(v___x_457_);
lean_dec(v___x_451_);
v___x_460_ = lean_box(0);
v___x_461_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_461_, 0, v___x_460_);
lean_ctor_set(v___x_461_, 1, v_a_445_);
return v___x_461_;
}
else
{
lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v_ref_464_; uint8_t v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; lean_object* v___x_470_; lean_object* v___x_471_; 
v___x_462_ = l_Lean_Syntax_getArg(v___x_457_, v___x_450_);
v___x_463_ = l_Lean_Syntax_getArg(v___x_457_, v___x_456_);
lean_dec(v___x_457_);
v_ref_464_ = l_Lean_replaceRef(v___x_451_, v_a_444_);
lean_dec(v___x_451_);
v___x_465_ = 0;
v___x_466_ = l_Lean_SourceInfo_fromRef(v_ref_464_, v___x_465_);
lean_dec(v_ref_464_);
v___x_467_ = ((lean_object*)(l_Std_Do_term___u2192_u2091___00__closed__1));
v___x_468_ = ((lean_object*)(l_Std_Do_term___u2192_u2091___00__closed__2));
lean_inc(v___x_466_);
v___x_469_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_469_, 0, v___x_466_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
v___x_470_ = l_Lean_Syntax_node3(v___x_466_, v___x_467_, v___x_462_, v___x_469_, v___x_463_);
v___x_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_471_, 0, v___x_470_);
lean_ctor_set(v___x_471_, 1, v_a_445_);
return v___x_471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1___boxed(lean_object* v_x_472_, lean_object* v_a_473_, lean_object* v_a_474_){
_start:
{
lean_object* v_res_475_; 
v_res_475_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1(v_x_472_, v_a_473_, v_a_474_);
lean_dec(v_a_473_);
return v_res_475_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13(void){
_start:
{
lean_object* v___x_545_; 
v___x_545_ = l_Array_mkArray0___redArg();
return v___x_545_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15(void){
_start:
{
lean_object* v___x_547_; lean_object* v___x_548_; 
v___x_547_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14));
v___x_548_ = l_String_toRawSubstring_x27(v___x_547_);
return v___x_548_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1(lean_object* v_x_565_, lean_object* v_a_566_, lean_object* v_a_567_){
_start:
{
lean_object* v___x_568_; uint8_t v___x_569_; 
v___x_568_ = ((lean_object*)(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1));
lean_inc(v_x_565_);
v___x_569_ = l_Lean_Syntax_isOfKind(v_x_565_, v___x_568_);
if (v___x_569_ == 0)
{
lean_object* v___x_570_; lean_object* v___x_571_; 
lean_dec(v_x_565_);
v___x_570_ = lean_box(1);
v___x_571_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_571_, 0, v___x_570_);
lean_ctor_set(v___x_571_, 1, v_a_567_);
return v___x_571_;
}
else
{
lean_object* v_quotContext_572_; lean_object* v_currMacroScope_573_; lean_object* v_ref_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; uint8_t v___x_579_; lean_object* v___x_580_; lean_object* v___x_581_; lean_object* v___x_582_; lean_object* v___x_583_; lean_object* v___x_584_; lean_object* v___x_585_; lean_object* v___x_586_; lean_object* v___x_587_; lean_object* v___x_588_; lean_object* v___x_589_; lean_object* v___x_590_; lean_object* v___x_591_; lean_object* v___x_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; lean_object* v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; 
v_quotContext_572_ = lean_ctor_get(v_a_566_, 1);
v_currMacroScope_573_ = lean_ctor_get(v_a_566_, 2);
v_ref_574_ = lean_ctor_get(v_a_566_, 5);
v___x_575_ = lean_unsigned_to_nat(1u);
v___x_576_ = l_Lean_Syntax_getArg(v_x_565_, v___x_575_);
lean_dec(v_x_565_);
v___x_577_ = ((lean_object*)(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5));
v___x_578_ = l_Lean_Syntax_getArgs(v___x_576_);
lean_dec(v___x_576_);
v___x_579_ = 0;
v___x_580_ = l_Lean_SourceInfo_fromRef(v_ref_574_, v___x_579_);
v___x_581_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1));
v___x_582_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2));
lean_inc_n(v___x_580_, 12);
v___x_583_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_583_, 0, v___x_580_);
lean_ctor_set(v___x_583_, 1, v___x_582_);
v___x_584_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5));
v___x_585_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7));
v___x_586_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_587_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8));
v___x_588_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9));
v___x_589_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_589_, 0, v___x_580_);
lean_ctor_set(v___x_589_, 1, v___x_587_);
v___x_590_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11));
v___x_591_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12));
v___x_592_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_592_, 0, v___x_580_);
lean_ctor_set(v___x_592_, 1, v___x_591_);
v___x_593_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
v___x_594_ = l_Array_append___redArg(v___x_593_, v___x_578_);
lean_dec_ref(v___x_578_);
v___x_595_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_595_, 0, v___x_580_);
lean_ctor_set(v___x_595_, 1, v___x_577_);
v___x_596_ = lean_array_push(v___x_594_, v___x_595_);
v___x_597_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15);
v___x_598_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18));
lean_inc(v_currMacroScope_573_);
lean_inc(v_quotContext_572_);
v___x_599_ = l_Lean_addMacroScope(v_quotContext_572_, v___x_598_, v_currMacroScope_573_);
v___x_600_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22));
v___x_601_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_601_, 0, v___x_580_);
lean_ctor_set(v___x_601_, 1, v___x_597_);
lean_ctor_set(v___x_601_, 2, v___x_599_);
lean_ctor_set(v___x_601_, 3, v___x_600_);
v___x_602_ = lean_array_push(v___x_596_, v___x_601_);
v___x_603_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_603_, 0, v___x_580_);
lean_ctor_set(v___x_603_, 1, v___x_586_);
lean_ctor_set(v___x_603_, 2, v___x_602_);
v___x_604_ = ((lean_object*)(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10));
v___x_605_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_605_, 0, v___x_580_);
lean_ctor_set(v___x_605_, 1, v___x_604_);
v___x_606_ = l_Lean_Syntax_node3(v___x_580_, v___x_590_, v___x_592_, v___x_603_, v___x_605_);
v___x_607_ = l_Lean_Syntax_node2(v___x_580_, v___x_588_, v___x_589_, v___x_606_);
v___x_608_ = l_Lean_Syntax_node1(v___x_580_, v___x_586_, v___x_607_);
v___x_609_ = l_Lean_Syntax_node1(v___x_580_, v___x_585_, v___x_608_);
v___x_610_ = l_Lean_Syntax_node1(v___x_580_, v___x_584_, v___x_609_);
v___x_611_ = l_Lean_Syntax_node2(v___x_580_, v___x_581_, v___x_583_, v___x_610_);
v___x_612_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_612_, 0, v___x_611_);
lean_ctor_set(v___x_612_, 1, v_a_567_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___boxed(lean_object* v_x_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v_res_616_; 
v_res_616_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1(v_x_613_, v_a_614_, v_a_615_);
lean_dec_ref(v_a_614_);
return v_res_616_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_noThrow___redArg(lean_object* v_ps_617_, lean_object* v_p_618_){
_start:
{
lean_object* v___x_619_; lean_object* v___x_620_; 
v___x_619_ = l_Std_Do_ExceptConds_const___redArg(v_ps_617_);
v___x_620_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_620_, 0, v_p_618_);
lean_ctor_set(v___x_620_, 1, v___x_619_);
return v___x_620_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_noThrow(lean_object* v_00_u03b1_621_, lean_object* v_ps_622_, lean_object* v_p_623_){
_start:
{
lean_object* v___x_624_; lean_object* v___x_625_; 
v___x_624_ = l_Std_Do_ExceptConds_const___redArg(v_ps_622_);
v___x_625_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_625_, 0, v_p_623_);
lean_ctor_set(v___x_625_, 1, v___x_624_);
return v___x_625_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(size_t v_sz_678_, size_t v_i_679_, lean_object* v_bs_680_){
_start:
{
uint8_t v___x_681_; 
v___x_681_ = lean_usize_dec_lt(v_i_679_, v_sz_678_);
if (v___x_681_ == 0)
{
return v_bs_680_;
}
else
{
lean_object* v_v_682_; lean_object* v___x_683_; lean_object* v_bs_x27_684_; size_t v___x_685_; size_t v___x_686_; lean_object* v___x_687_; 
v_v_682_ = lean_array_uget(v_bs_680_, v_i_679_);
v___x_683_ = lean_unsigned_to_nat(0u);
v_bs_x27_684_ = lean_array_uset(v_bs_680_, v_i_679_, v___x_683_);
v___x_685_ = ((size_t)1ULL);
v___x_686_ = lean_usize_add(v_i_679_, v___x_685_);
v___x_687_ = lean_array_uset(v_bs_x27_684_, v_i_679_, v_v_682_);
v_i_679_ = v___x_686_;
v_bs_680_ = v___x_687_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0_0interp(lean_interpreter_value* stack)
{
size_t v_sz_678_ = stack[0].m_num;
size_t v_i_679_ = stack[1].m_num;
lean_object* v_bs_680_ = stack[2].m_obj;
lean_object* v_res_689_;
v_res_689_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_678_, v_i_679_, v_bs_680_);
stack->m_obj
 = v_res_689_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0___boxed(lean_object* v_sz_690_, lean_object* v_i_691_, lean_object* v_bs_692_){
_start:
{
size_t v_sz_boxed_693_; size_t v_i_boxed_694_; lean_object* v_res_695_; 
v_sz_boxed_693_ = lean_unbox_usize(v_sz_690_);
lean_dec(v_sz_690_);
v_i_boxed_694_ = lean_unbox_usize(v_i_691_);
lean_dec(v_i_691_);
v_res_695_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_boxed_693_, v_i_boxed_694_, v_bs_692_);
return v_res_695_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_697_; lean_object* v___x_698_; 
v___x_697_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0));
v___x_698_ = l_String_toRawSubstring_x27(v___x_697_);
return v___x_698_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16(void){
_start:
{
lean_object* v___x_732_; lean_object* v___x_733_; 
v___x_732_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15));
v___x_733_ = l_String_toRawSubstring_x27(v___x_732_);
return v___x_733_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1(lean_object* v_x_762_, lean_object* v_a_763_, lean_object* v_a_764_){
_start:
{
lean_object* v___x_765_; uint8_t v___x_766_; 
v___x_765_ = ((lean_object*)(l_Std_Do_term___u21d3___x3d_x3e___00__closed__1));
lean_inc(v_x_762_);
v___x_766_ = l_Lean_Syntax_isOfKind(v_x_762_, v___x_765_);
if (v___x_766_ == 0)
{
lean_object* v___x_767_; lean_object* v___x_768_; 
lean_dec(v_x_762_);
v___x_767_ = lean_box(1);
v___x_768_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_768_, 0, v___x_767_);
lean_ctor_set(v___x_768_, 1, v_a_764_);
return v___x_768_;
}
else
{
lean_object* v_quotContext_769_; lean_object* v_currMacroScope_770_; lean_object* v_ref_771_; lean_object* v___x_772_; lean_object* v___x_773_; lean_object* v___x_774_; lean_object* v___x_775_; lean_object* v_xs_776_; uint8_t v___x_777_; lean_object* v___x_778_; lean_object* v___x_779_; lean_object* v___x_780_; lean_object* v___x_781_; lean_object* v___x_782_; lean_object* v___x_783_; lean_object* v___x_784_; lean_object* v___x_785_; lean_object* v___x_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; lean_object* v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; size_t v_sz_811_; size_t v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; lean_object* v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; 
v_quotContext_769_ = lean_ctor_get(v_a_763_, 1);
v_currMacroScope_770_ = lean_ctor_get(v_a_763_, 2);
v_ref_771_ = lean_ctor_get(v_a_763_, 5);
v___x_772_ = lean_unsigned_to_nat(2u);
v___x_773_ = l_Lean_Syntax_getArg(v_x_762_, v___x_772_);
v___x_774_ = lean_unsigned_to_nat(4u);
v___x_775_ = l_Lean_Syntax_getArg(v_x_762_, v___x_774_);
lean_dec(v_x_762_);
v_xs_776_ = l_Lean_Syntax_getArgs(v___x_773_);
lean_dec(v___x_773_);
v___x_777_ = 0;
v___x_778_ = l_Lean_SourceInfo_fromRef(v_ref_771_, v___x_777_);
v___x_779_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_780_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1);
v___x_781_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4));
lean_inc_n(v_currMacroScope_770_, 2);
lean_inc_n(v_quotContext_769_, 2);
v___x_782_ = l_Lean_addMacroScope(v_quotContext_769_, v___x_781_, v_currMacroScope_770_);
v___x_783_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7));
lean_inc_n(v___x_778_, 23);
v___x_784_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_784_, 0, v___x_778_);
lean_ctor_set(v___x_784_, 1, v___x_780_);
lean_ctor_set(v___x_784_, 2, v___x_782_);
lean_ctor_set(v___x_784_, 3, v___x_783_);
v___x_785_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_786_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9));
v___x_787_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11));
v___x_788_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12));
v___x_789_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_789_, 0, v___x_778_);
lean_ctor_set(v___x_789_, 1, v___x_788_);
v___x_790_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14));
v___x_791_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16);
v___x_792_ = lean_box(0);
v___x_793_ = l_Lean_addMacroScope(v_quotContext_769_, v___x_792_, v_currMacroScope_770_);
v___x_794_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19));
v___x_795_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_795_, 0, v___x_778_);
lean_ctor_set(v___x_795_, 1, v___x_791_);
lean_ctor_set(v___x_795_, 2, v___x_793_);
lean_ctor_set(v___x_795_, 3, v___x_794_);
v___x_796_ = l_Lean_Syntax_node1(v___x_778_, v___x_790_, v___x_795_);
v___x_797_ = l_Lean_Syntax_node2(v___x_778_, v___x_787_, v___x_789_, v___x_796_);
v___x_798_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1));
v___x_799_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2));
v___x_800_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_800_, 0, v___x_778_);
lean_ctor_set(v___x_800_, 1, v___x_799_);
v___x_801_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5));
v___x_802_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7));
v___x_803_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8));
v___x_804_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9));
v___x_805_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_805_, 0, v___x_778_);
lean_ctor_set(v___x_805_, 1, v___x_803_);
v___x_806_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20));
v___x_807_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21));
v___x_808_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_808_, 0, v___x_778_);
lean_ctor_set(v___x_808_, 1, v___x_806_);
v___x_809_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23));
v___x_810_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
v_sz_811_ = lean_array_size(v_xs_776_);
v___x_812_ = ((size_t)0ULL);
v___x_813_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_811_, v___x_812_, v_xs_776_);
v___x_814_ = l_Array_append___redArg(v___x_810_, v___x_813_);
lean_dec_ref(v___x_813_);
v___x_815_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_815_, 0, v___x_778_);
lean_ctor_set(v___x_815_, 1, v___x_785_);
lean_ctor_set(v___x_815_, 2, v___x_814_);
v___x_816_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_816_, 0, v___x_778_);
lean_ctor_set(v___x_816_, 1, v___x_785_);
lean_ctor_set(v___x_816_, 2, v___x_810_);
v___x_817_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24));
v___x_818_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_818_, 0, v___x_778_);
lean_ctor_set(v___x_818_, 1, v___x_817_);
v___x_819_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26));
v___x_820_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27));
v___x_821_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_778_);
lean_ctor_set(v___x_821_, 1, v___x_820_);
v___x_822_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28));
v___x_823_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_823_, 0, v___x_778_);
lean_ctor_set(v___x_823_, 1, v___x_822_);
lean_inc_ref(v___x_823_);
v___x_824_ = l_Lean_Syntax_node3(v___x_778_, v___x_819_, v___x_821_, v___x_775_, v___x_823_);
v___x_825_ = l_Lean_Syntax_node4(v___x_778_, v___x_809_, v___x_815_, v___x_816_, v___x_818_, v___x_824_);
v___x_826_ = l_Lean_Syntax_node2(v___x_778_, v___x_807_, v___x_808_, v___x_825_);
v___x_827_ = l_Lean_Syntax_node2(v___x_778_, v___x_804_, v___x_805_, v___x_826_);
v___x_828_ = l_Lean_Syntax_node1(v___x_778_, v___x_785_, v___x_827_);
v___x_829_ = l_Lean_Syntax_node1(v___x_778_, v___x_802_, v___x_828_);
v___x_830_ = l_Lean_Syntax_node1(v___x_778_, v___x_801_, v___x_829_);
v___x_831_ = l_Lean_Syntax_node2(v___x_778_, v___x_798_, v___x_800_, v___x_830_);
v___x_832_ = l_Lean_Syntax_node3(v___x_778_, v___x_786_, v___x_797_, v___x_831_, v___x_823_);
v___x_833_ = l_Lean_Syntax_node1(v___x_778_, v___x_785_, v___x_832_);
v___x_834_ = l_Lean_Syntax_node2(v___x_778_, v___x_779_, v___x_784_, v___x_833_);
v___x_835_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_835_, 0, v___x_834_);
lean_ctor_set(v___x_835_, 1, v_a_764_);
return v___x_835_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___boxed(lean_object* v_x_836_, lean_object* v_a_837_, lean_object* v_a_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1(v_x_836_, v_a_837_, v_a_838_);
lean_dec_ref(v_a_837_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_mayThrow___redArg(lean_object* v_ps_840_, lean_object* v_p_841_){
_start:
{
lean_object* v___x_842_; lean_object* v___x_843_; 
v___x_842_ = l_Std_Do_ExceptConds_const___redArg(v_ps_840_);
v___x_843_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_843_, 0, v_p_841_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
return v___x_843_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_mayThrow(lean_object* v_00_u03b1_844_, lean_object* v_ps_845_, lean_object* v_p_846_){
_start:
{
lean_object* v___x_847_; lean_object* v___x_848_; 
v___x_847_ = l_Std_Do_ExceptConds_const___redArg(v_ps_845_);
v___x_848_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_848_, 0, v_p_846_);
lean_ctor_set(v___x_848_, 1, v___x_847_);
return v___x_848_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_879_; lean_object* v___x_880_; 
v___x_879_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0));
v___x_880_ = l_String_toRawSubstring_x27(v___x_879_);
return v___x_880_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1(lean_object* v_x_896_, lean_object* v_a_897_, lean_object* v_a_898_){
_start:
{
lean_object* v___x_899_; uint8_t v___x_900_; 
v___x_899_ = ((lean_object*)(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1));
lean_inc(v_x_896_);
v___x_900_ = l_Lean_Syntax_isOfKind(v_x_896_, v___x_899_);
if (v___x_900_ == 0)
{
lean_object* v___x_901_; lean_object* v___x_902_; 
lean_dec(v_x_896_);
v___x_901_ = lean_box(1);
v___x_902_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_902_, 0, v___x_901_);
lean_ctor_set(v___x_902_, 1, v_a_898_);
return v___x_902_;
}
else
{
lean_object* v_quotContext_903_; lean_object* v_currMacroScope_904_; lean_object* v_ref_905_; lean_object* v___x_906_; lean_object* v___x_907_; lean_object* v___x_908_; lean_object* v___x_909_; lean_object* v_xs_910_; uint8_t v___x_911_; lean_object* v___x_912_; lean_object* v___x_913_; lean_object* v___x_914_; lean_object* v___x_915_; lean_object* v___x_916_; lean_object* v___x_917_; lean_object* v___x_918_; lean_object* v___x_919_; lean_object* v___x_920_; lean_object* v___x_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v___x_926_; lean_object* v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; size_t v_sz_945_; size_t v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; lean_object* v___x_961_; lean_object* v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; 
v_quotContext_903_ = lean_ctor_get(v_a_897_, 1);
v_currMacroScope_904_ = lean_ctor_get(v_a_897_, 2);
v_ref_905_ = lean_ctor_get(v_a_897_, 5);
v___x_906_ = lean_unsigned_to_nat(2u);
v___x_907_ = l_Lean_Syntax_getArg(v_x_896_, v___x_906_);
v___x_908_ = lean_unsigned_to_nat(4u);
v___x_909_ = l_Lean_Syntax_getArg(v_x_896_, v___x_908_);
lean_dec(v_x_896_);
v_xs_910_ = l_Lean_Syntax_getArgs(v___x_907_);
lean_dec(v___x_907_);
v___x_911_ = 0;
v___x_912_ = l_Lean_SourceInfo_fromRef(v_ref_905_, v___x_911_);
v___x_913_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_914_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1);
v___x_915_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3));
lean_inc_n(v_currMacroScope_904_, 2);
lean_inc_n(v_quotContext_903_, 2);
v___x_916_ = l_Lean_addMacroScope(v_quotContext_903_, v___x_915_, v_currMacroScope_904_);
v___x_917_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6));
lean_inc_n(v___x_912_, 23);
v___x_918_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_918_, 0, v___x_912_);
lean_ctor_set(v___x_918_, 1, v___x_914_);
lean_ctor_set(v___x_918_, 2, v___x_916_);
lean_ctor_set(v___x_918_, 3, v___x_917_);
v___x_919_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_920_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9));
v___x_921_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11));
v___x_922_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12));
v___x_923_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_923_, 0, v___x_912_);
lean_ctor_set(v___x_923_, 1, v___x_922_);
v___x_924_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14));
v___x_925_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16);
v___x_926_ = lean_box(0);
v___x_927_ = l_Lean_addMacroScope(v_quotContext_903_, v___x_926_, v_currMacroScope_904_);
v___x_928_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19));
v___x_929_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_929_, 0, v___x_912_);
lean_ctor_set(v___x_929_, 1, v___x_925_);
lean_ctor_set(v___x_929_, 2, v___x_927_);
lean_ctor_set(v___x_929_, 3, v___x_928_);
v___x_930_ = l_Lean_Syntax_node1(v___x_912_, v___x_924_, v___x_929_);
v___x_931_ = l_Lean_Syntax_node2(v___x_912_, v___x_921_, v___x_923_, v___x_930_);
v___x_932_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1));
v___x_933_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2));
v___x_934_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_934_, 0, v___x_912_);
lean_ctor_set(v___x_934_, 1, v___x_933_);
v___x_935_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5));
v___x_936_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7));
v___x_937_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8));
v___x_938_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9));
v___x_939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_912_);
lean_ctor_set(v___x_939_, 1, v___x_937_);
v___x_940_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20));
v___x_941_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21));
v___x_942_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_942_, 0, v___x_912_);
lean_ctor_set(v___x_942_, 1, v___x_940_);
v___x_943_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23));
v___x_944_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
v_sz_945_ = lean_array_size(v_xs_910_);
v___x_946_ = ((size_t)0ULL);
v___x_947_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_945_, v___x_946_, v_xs_910_);
v___x_948_ = l_Array_append___redArg(v___x_944_, v___x_947_);
lean_dec_ref(v___x_947_);
v___x_949_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_949_, 0, v___x_912_);
lean_ctor_set(v___x_949_, 1, v___x_919_);
lean_ctor_set(v___x_949_, 2, v___x_948_);
v___x_950_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_950_, 0, v___x_912_);
lean_ctor_set(v___x_950_, 1, v___x_919_);
lean_ctor_set(v___x_950_, 2, v___x_944_);
v___x_951_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24));
v___x_952_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_952_, 0, v___x_912_);
lean_ctor_set(v___x_952_, 1, v___x_951_);
v___x_953_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26));
v___x_954_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27));
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_912_);
lean_ctor_set(v___x_955_, 1, v___x_954_);
v___x_956_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28));
v___x_957_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_957_, 0, v___x_912_);
lean_ctor_set(v___x_957_, 1, v___x_956_);
lean_inc_ref(v___x_957_);
v___x_958_ = l_Lean_Syntax_node3(v___x_912_, v___x_953_, v___x_955_, v___x_909_, v___x_957_);
v___x_959_ = l_Lean_Syntax_node4(v___x_912_, v___x_943_, v___x_949_, v___x_950_, v___x_952_, v___x_958_);
v___x_960_ = l_Lean_Syntax_node2(v___x_912_, v___x_941_, v___x_942_, v___x_959_);
v___x_961_ = l_Lean_Syntax_node2(v___x_912_, v___x_938_, v___x_939_, v___x_960_);
v___x_962_ = l_Lean_Syntax_node1(v___x_912_, v___x_919_, v___x_961_);
v___x_963_ = l_Lean_Syntax_node1(v___x_912_, v___x_936_, v___x_962_);
v___x_964_ = l_Lean_Syntax_node1(v___x_912_, v___x_935_, v___x_963_);
v___x_965_ = l_Lean_Syntax_node2(v___x_912_, v___x_932_, v___x_934_, v___x_964_);
v___x_966_ = l_Lean_Syntax_node3(v___x_912_, v___x_920_, v___x_931_, v___x_965_, v___x_957_);
v___x_967_ = l_Lean_Syntax_node1(v___x_912_, v___x_919_, v___x_966_);
v___x_968_ = l_Lean_Syntax_node2(v___x_912_, v___x_913_, v___x_918_, v___x_967_);
v___x_969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_969_, 0, v___x_968_);
lean_ctor_set(v___x_969_, 1, v_a_898_);
return v___x_969_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___boxed(lean_object* v_x_970_, lean_object* v_a_971_, lean_object* v_a_972_){
_start:
{
lean_object* v_res_973_; 
v_res_973_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1(v_x_970_, v_a_971_, v_a_972_);
lean_dec_ref(v_a_971_);
return v_res_973_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__0(lean_object* v_x_974_){
_start:
{
lean_object* v___x_975_; 
v___x_975_ = lean_box(0);
return v___x_975_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__0___boxed(lean_object* v_x_976_){
_start:
{
lean_object* v_res_977_; 
v_res_977_ = l_Std_Do_instInhabitedPostCond___redArg___lam__0(v_x_976_);
lean_dec(v_x_976_);
return v_res_977_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__1(lean_object* v_ps_978_, lean_object* v___f_979_, lean_object* v_x_980_){
_start:
{
lean_object* v___x_981_; lean_object* v___x_982_; 
v___x_981_ = l_Std_Do_PostShape_args(v_ps_978_);
v___x_982_ = l_Std_Do_SVal_curry___redArg(v___x_981_, lean_box(0));
return v___x_982_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__1___boxed(lean_object* v_ps_983_, lean_object* v___f_984_, lean_object* v_x_985_){
_start:
{
lean_object* v_res_986_; 
v_res_986_ = l_Std_Do_instInhabitedPostCond___redArg___lam__1(v_ps_983_, v___f_984_, v_x_985_);
lean_dec(v_x_985_);
lean_dec(v_ps_983_);
return v_res_986_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg(lean_object* v_ps_987_){
_start:
{
lean_object* v___f_988_; lean_object* v___x_989_; lean_object* v___x_990_; 
lean_inc(v_ps_987_);
v___f_988_ = lean_alloc_closure((void*)(l_Std_Do_instInhabitedPostCond___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_988_, 0, v_ps_987_);
lean_closure_set(v___f_988_, 1, lean_box(0));
v___x_989_ = l_Std_Do_ExceptConds_const___redArg(v_ps_987_);
v___x_990_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_990_, 0, v___f_988_);
lean_ctor_set(v___x_990_, 1, v___x_989_);
return v___x_990_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond(lean_object* v_ps_991_, lean_object* v_00_u03b1_992_){
_start:
{
lean_object* v___x_993_; 
v___x_993_ = l_Std_Do_instInhabitedPostCond___redArg(v_ps_991_);
return v___x_993_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1(void){
_start:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0));
v___x_1014_ = l_String_toRawSubstring_x27(v___x_1013_);
return v___x_1014_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1(lean_object* v_x_1029_, lean_object* v_a_1030_, lean_object* v_a_1031_){
_start:
{
lean_object* v___x_1032_; uint8_t v___x_1033_; 
v___x_1032_ = ((lean_object*)(l_Std_Do_term___u22a2_u209a___00__closed__1));
lean_inc(v_x_1029_);
v___x_1033_ = l_Lean_Syntax_isOfKind(v_x_1029_, v___x_1032_);
if (v___x_1033_ == 0)
{
lean_object* v___x_1034_; lean_object* v___x_1035_; 
lean_dec(v_x_1029_);
v___x_1034_ = lean_box(1);
v___x_1035_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1035_, 0, v___x_1034_);
lean_ctor_set(v___x_1035_, 1, v_a_1031_);
return v___x_1035_;
}
else
{
lean_object* v_quotContext_1036_; lean_object* v_currMacroScope_1037_; lean_object* v_ref_1038_; lean_object* v___x_1039_; lean_object* v___x_1040_; lean_object* v___x_1041_; lean_object* v___x_1042_; uint8_t v___x_1043_; lean_object* v___x_1044_; lean_object* v___x_1045_; lean_object* v___x_1046_; lean_object* v___x_1047_; lean_object* v___x_1048_; lean_object* v___x_1049_; lean_object* v___x_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; 
v_quotContext_1036_ = lean_ctor_get(v_a_1030_, 1);
v_currMacroScope_1037_ = lean_ctor_get(v_a_1030_, 2);
v_ref_1038_ = lean_ctor_get(v_a_1030_, 5);
v___x_1039_ = lean_unsigned_to_nat(0u);
v___x_1040_ = l_Lean_Syntax_getArg(v_x_1029_, v___x_1039_);
v___x_1041_ = lean_unsigned_to_nat(2u);
v___x_1042_ = l_Lean_Syntax_getArg(v_x_1029_, v___x_1041_);
lean_dec(v_x_1029_);
v___x_1043_ = 0;
v___x_1044_ = l_Lean_SourceInfo_fromRef(v_ref_1038_, v___x_1043_);
v___x_1045_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_1046_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1);
v___x_1047_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2));
lean_inc(v_currMacroScope_1037_);
lean_inc(v_quotContext_1036_);
v___x_1048_ = l_Lean_addMacroScope(v_quotContext_1036_, v___x_1047_, v_currMacroScope_1037_);
v___x_1049_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5));
lean_inc_n(v___x_1044_, 2);
v___x_1050_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1050_, 0, v___x_1044_);
lean_ctor_set(v___x_1050_, 1, v___x_1046_);
lean_ctor_set(v___x_1050_, 2, v___x_1048_);
lean_ctor_set(v___x_1050_, 3, v___x_1049_);
v___x_1051_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_1052_ = l_Lean_Syntax_node2(v___x_1044_, v___x_1051_, v___x_1040_, v___x_1042_);
v___x_1053_ = l_Lean_Syntax_node2(v___x_1044_, v___x_1045_, v___x_1050_, v___x_1052_);
v___x_1054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1054_, 0, v___x_1053_);
lean_ctor_set(v___x_1054_, 1, v_a_1031_);
return v___x_1054_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___boxed(lean_object* v_x_1055_, lean_object* v_a_1056_, lean_object* v_a_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1(v_x_1055_, v_a_1056_, v_a_1057_);
lean_dec_ref(v_a_1056_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1(lean_object* v_x_1059_, lean_object* v_a_1060_, lean_object* v_a_1061_){
_start:
{
lean_object* v___x_1062_; uint8_t v___x_1063_; 
v___x_1062_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_1059_);
v___x_1063_ = l_Lean_Syntax_isOfKind(v_x_1059_, v___x_1062_);
if (v___x_1063_ == 0)
{
lean_object* v___x_1064_; lean_object* v___x_1065_; 
lean_dec(v_x_1059_);
v___x_1064_ = lean_box(0);
v___x_1065_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1065_, 0, v___x_1064_);
lean_ctor_set(v___x_1065_, 1, v_a_1061_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; lean_object* v___x_1068_; uint8_t v___x_1069_; 
v___x_1066_ = lean_unsigned_to_nat(0u);
v___x_1067_ = l_Lean_Syntax_getArg(v_x_1059_, v___x_1066_);
v___x_1068_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_1067_);
v___x_1069_ = l_Lean_Syntax_isOfKind(v___x_1067_, v___x_1068_);
if (v___x_1069_ == 0)
{
lean_object* v___x_1070_; lean_object* v___x_1071_; 
lean_dec(v___x_1067_);
lean_dec(v_x_1059_);
v___x_1070_ = lean_box(0);
v___x_1071_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1071_, 0, v___x_1070_);
lean_ctor_set(v___x_1071_, 1, v_a_1061_);
return v___x_1071_;
}
else
{
lean_object* v___x_1072_; lean_object* v___x_1073_; lean_object* v___x_1074_; uint8_t v___x_1075_; 
v___x_1072_ = lean_unsigned_to_nat(1u);
v___x_1073_ = l_Lean_Syntax_getArg(v_x_1059_, v___x_1072_);
lean_dec(v_x_1059_);
v___x_1074_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1073_);
v___x_1075_ = l_Lean_Syntax_matchesNull(v___x_1073_, v___x_1074_);
if (v___x_1075_ == 0)
{
lean_object* v___x_1076_; lean_object* v___x_1077_; 
lean_dec(v___x_1073_);
lean_dec(v___x_1067_);
v___x_1076_ = lean_box(0);
v___x_1077_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
lean_ctor_set(v___x_1077_, 1, v_a_1061_);
return v___x_1077_;
}
else
{
lean_object* v___x_1078_; lean_object* v___x_1079_; lean_object* v_ref_1080_; uint8_t v___x_1081_; lean_object* v___x_1082_; lean_object* v___x_1083_; lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; lean_object* v___x_1087_; 
v___x_1078_ = l_Lean_Syntax_getArg(v___x_1073_, v___x_1066_);
v___x_1079_ = l_Lean_Syntax_getArg(v___x_1073_, v___x_1072_);
lean_dec(v___x_1073_);
v_ref_1080_ = l_Lean_replaceRef(v___x_1067_, v_a_1060_);
lean_dec(v___x_1067_);
v___x_1081_ = 0;
v___x_1082_ = l_Lean_SourceInfo_fromRef(v_ref_1080_, v___x_1081_);
lean_dec(v_ref_1080_);
v___x_1083_ = ((lean_object*)(l_Std_Do_term___u22a2_u209a___00__closed__1));
v___x_1084_ = ((lean_object*)(l_Std_Do_term___u22a2_u209a___00__closed__2));
lean_inc(v___x_1082_);
v___x_1085_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1082_);
lean_ctor_set(v___x_1085_, 1, v___x_1084_);
v___x_1086_ = l_Lean_Syntax_node3(v___x_1082_, v___x_1083_, v___x_1078_, v___x_1085_, v___x_1079_);
v___x_1087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1087_, 0, v___x_1086_);
lean_ctor_set(v___x_1087_, 1, v_a_1061_);
return v___x_1087_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1___boxed(lean_object* v_x_1088_, lean_object* v_a_1089_, lean_object* v_a_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1(v_x_1088_, v_a_1089_, v_a_1090_);
lean_dec(v_a_1089_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg___lam__0(lean_object* v_ps_1092_, lean_object* v_fst_1093_, lean_object* v_fst_1094_, lean_object* v_a_1095_){
_start:
{
lean_object* v___x_1096_; lean_object* v___x_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
v___x_1096_ = l_Std_Do_PostShape_args(v_ps_1092_);
lean_inc(v_a_1095_);
v___x_1097_ = lean_apply_1(v_fst_1093_, v_a_1095_);
v___x_1098_ = lean_apply_1(v_fst_1094_, v_a_1095_);
v___x_1099_ = l_Std_Do_SPred_and(v___x_1096_, v___x_1097_, v___x_1098_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg___lam__0___boxed(lean_object* v_ps_1100_, lean_object* v_fst_1101_, lean_object* v_fst_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l_Std_Do_PostCond_and___redArg___lam__0(v_ps_1100_, v_fst_1101_, v_fst_1102_, v_a_1103_);
lean_dec(v_ps_1100_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg(lean_object* v_ps_1105_, lean_object* v_p_1106_, lean_object* v_q_1107_){
_start:
{
lean_object* v_fst_1108_; lean_object* v_snd_1109_; lean_object* v_fst_1110_; lean_object* v_snd_1111_; lean_object* v___x_1113_; uint8_t v_isShared_1114_; uint8_t v_isSharedCheck_1120_; 
v_fst_1108_ = lean_ctor_get(v_p_1106_, 0);
lean_inc(v_fst_1108_);
v_snd_1109_ = lean_ctor_get(v_p_1106_, 1);
lean_inc(v_snd_1109_);
lean_dec_ref(v_p_1106_);
v_fst_1110_ = lean_ctor_get(v_q_1107_, 0);
v_snd_1111_ = lean_ctor_get(v_q_1107_, 1);
v_isSharedCheck_1120_ = !lean_is_exclusive(v_q_1107_);
if (v_isSharedCheck_1120_ == 0)
{
v___x_1113_ = v_q_1107_;
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
else
{
lean_inc(v_snd_1111_);
lean_inc(v_fst_1110_);
lean_dec(v_q_1107_);
v___x_1113_ = lean_box(0);
v_isShared_1114_ = v_isSharedCheck_1120_;
goto v_resetjp_1112_;
}
v_resetjp_1112_:
{
lean_object* v___f_1115_; lean_object* v___x_1116_; lean_object* v___x_1118_; 
lean_inc(v_ps_1105_);
v___f_1115_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_and___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1115_, 0, v_ps_1105_);
lean_closure_set(v___f_1115_, 1, v_fst_1108_);
lean_closure_set(v___f_1115_, 2, v_fst_1110_);
v___x_1116_ = l_Std_Do_ExceptConds_and(v_ps_1105_, v_snd_1109_, v_snd_1111_);
if (v_isShared_1114_ == 0)
{
lean_ctor_set(v___x_1113_, 1, v___x_1116_);
lean_ctor_set(v___x_1113_, 0, v___f_1115_);
v___x_1118_ = v___x_1113_;
goto v_reusejp_1117_;
}
else
{
lean_object* v_reuseFailAlloc_1119_; 
v_reuseFailAlloc_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1119_, 0, v___f_1115_);
lean_ctor_set(v_reuseFailAlloc_1119_, 1, v___x_1116_);
v___x_1118_ = v_reuseFailAlloc_1119_;
goto v_reusejp_1117_;
}
v_reusejp_1117_:
{
return v___x_1118_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and(lean_object* v_00_u03b1_1121_, lean_object* v_ps_1122_, lean_object* v_p_1123_, lean_object* v_q_1124_){
_start:
{
lean_object* v_fst_1125_; lean_object* v_snd_1126_; lean_object* v_fst_1127_; lean_object* v_snd_1128_; lean_object* v___x_1130_; uint8_t v_isShared_1131_; uint8_t v_isSharedCheck_1137_; 
v_fst_1125_ = lean_ctor_get(v_p_1123_, 0);
lean_inc(v_fst_1125_);
v_snd_1126_ = lean_ctor_get(v_p_1123_, 1);
lean_inc(v_snd_1126_);
lean_dec_ref(v_p_1123_);
v_fst_1127_ = lean_ctor_get(v_q_1124_, 0);
v_snd_1128_ = lean_ctor_get(v_q_1124_, 1);
v_isSharedCheck_1137_ = !lean_is_exclusive(v_q_1124_);
if (v_isSharedCheck_1137_ == 0)
{
v___x_1130_ = v_q_1124_;
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
else
{
lean_inc(v_snd_1128_);
lean_inc(v_fst_1127_);
lean_dec(v_q_1124_);
v___x_1130_ = lean_box(0);
v_isShared_1131_ = v_isSharedCheck_1137_;
goto v_resetjp_1129_;
}
v_resetjp_1129_:
{
lean_object* v___f_1132_; lean_object* v___x_1133_; lean_object* v___x_1135_; 
lean_inc(v_ps_1122_);
v___f_1132_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_and___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1132_, 0, v_ps_1122_);
lean_closure_set(v___f_1132_, 1, v_fst_1125_);
lean_closure_set(v___f_1132_, 2, v_fst_1127_);
v___x_1133_ = l_Std_Do_ExceptConds_and(v_ps_1122_, v_snd_1126_, v_snd_1128_);
if (v_isShared_1131_ == 0)
{
lean_ctor_set(v___x_1130_, 1, v___x_1133_);
lean_ctor_set(v___x_1130_, 0, v___f_1132_);
v___x_1135_ = v___x_1130_;
goto v_reusejp_1134_;
}
else
{
lean_object* v_reuseFailAlloc_1136_; 
v_reuseFailAlloc_1136_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1136_, 0, v___f_1132_);
lean_ctor_set(v_reuseFailAlloc_1136_, 1, v___x_1133_);
v___x_1135_ = v_reuseFailAlloc_1136_;
goto v_reusejp_1134_;
}
v_reusejp_1134_:
{
return v___x_1135_;
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1(void){
_start:
{
lean_object* v___x_1157_; lean_object* v___x_1158_; 
v___x_1157_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0));
v___x_1158_ = l_String_toRawSubstring_x27(v___x_1157_);
return v___x_1158_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1(lean_object* v_x_1173_, lean_object* v_a_1174_, lean_object* v_a_1175_){
_start:
{
lean_object* v___x_1176_; uint8_t v___x_1177_; 
v___x_1176_ = ((lean_object*)(l_Std_Do_term___u2227_u209a___00__closed__1));
lean_inc(v_x_1173_);
v___x_1177_ = l_Lean_Syntax_isOfKind(v_x_1173_, v___x_1176_);
if (v___x_1177_ == 0)
{
lean_object* v___x_1178_; lean_object* v___x_1179_; 
lean_dec(v_x_1173_);
v___x_1178_ = lean_box(1);
v___x_1179_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1179_, 0, v___x_1178_);
lean_ctor_set(v___x_1179_, 1, v_a_1175_);
return v___x_1179_;
}
else
{
lean_object* v_quotContext_1180_; lean_object* v_currMacroScope_1181_; lean_object* v_ref_1182_; lean_object* v___x_1183_; lean_object* v___x_1184_; lean_object* v___x_1185_; lean_object* v___x_1186_; uint8_t v___x_1187_; lean_object* v___x_1188_; lean_object* v___x_1189_; lean_object* v___x_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v_quotContext_1180_ = lean_ctor_get(v_a_1174_, 1);
v_currMacroScope_1181_ = lean_ctor_get(v_a_1174_, 2);
v_ref_1182_ = lean_ctor_get(v_a_1174_, 5);
v___x_1183_ = lean_unsigned_to_nat(0u);
v___x_1184_ = l_Lean_Syntax_getArg(v_x_1173_, v___x_1183_);
v___x_1185_ = lean_unsigned_to_nat(2u);
v___x_1186_ = l_Lean_Syntax_getArg(v_x_1173_, v___x_1185_);
lean_dec(v_x_1173_);
v___x_1187_ = 0;
v___x_1188_ = l_Lean_SourceInfo_fromRef(v_ref_1182_, v___x_1187_);
v___x_1189_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_1190_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1);
v___x_1191_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2));
lean_inc(v_currMacroScope_1181_);
lean_inc(v_quotContext_1180_);
v___x_1192_ = l_Lean_addMacroScope(v_quotContext_1180_, v___x_1191_, v_currMacroScope_1181_);
v___x_1193_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5));
lean_inc_n(v___x_1188_, 2);
v___x_1194_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1188_);
lean_ctor_set(v___x_1194_, 1, v___x_1190_);
lean_ctor_set(v___x_1194_, 2, v___x_1192_);
lean_ctor_set(v___x_1194_, 3, v___x_1193_);
v___x_1195_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_1196_ = l_Lean_Syntax_node2(v___x_1188_, v___x_1195_, v___x_1184_, v___x_1186_);
v___x_1197_ = l_Lean_Syntax_node2(v___x_1188_, v___x_1189_, v___x_1194_, v___x_1196_);
v___x_1198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1198_, 0, v___x_1197_);
lean_ctor_set(v___x_1198_, 1, v_a_1175_);
return v___x_1198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___boxed(lean_object* v_x_1199_, lean_object* v_a_1200_, lean_object* v_a_1201_){
_start:
{
lean_object* v_res_1202_; 
v_res_1202_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1(v_x_1199_, v_a_1200_, v_a_1201_);
lean_dec_ref(v_a_1200_);
return v_res_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1(lean_object* v_x_1203_, lean_object* v_a_1204_, lean_object* v_a_1205_){
_start:
{
lean_object* v___x_1206_; uint8_t v___x_1207_; 
v___x_1206_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_1203_);
v___x_1207_ = l_Lean_Syntax_isOfKind(v_x_1203_, v___x_1206_);
if (v___x_1207_ == 0)
{
lean_object* v___x_1208_; lean_object* v___x_1209_; 
lean_dec(v_x_1203_);
v___x_1208_ = lean_box(0);
v___x_1209_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1209_, 0, v___x_1208_);
lean_ctor_set(v___x_1209_, 1, v_a_1205_);
return v___x_1209_;
}
else
{
lean_object* v___x_1210_; lean_object* v___x_1211_; lean_object* v___x_1212_; uint8_t v___x_1213_; 
v___x_1210_ = lean_unsigned_to_nat(0u);
v___x_1211_ = l_Lean_Syntax_getArg(v_x_1203_, v___x_1210_);
v___x_1212_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_1211_);
v___x_1213_ = l_Lean_Syntax_isOfKind(v___x_1211_, v___x_1212_);
if (v___x_1213_ == 0)
{
lean_object* v___x_1214_; lean_object* v___x_1215_; 
lean_dec(v___x_1211_);
lean_dec(v_x_1203_);
v___x_1214_ = lean_box(0);
v___x_1215_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1215_, 0, v___x_1214_);
lean_ctor_set(v___x_1215_, 1, v_a_1205_);
return v___x_1215_;
}
else
{
lean_object* v___x_1216_; lean_object* v___x_1217_; lean_object* v___x_1218_; uint8_t v___x_1219_; 
v___x_1216_ = lean_unsigned_to_nat(1u);
v___x_1217_ = l_Lean_Syntax_getArg(v_x_1203_, v___x_1216_);
lean_dec(v_x_1203_);
v___x_1218_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1217_);
v___x_1219_ = l_Lean_Syntax_matchesNull(v___x_1217_, v___x_1218_);
if (v___x_1219_ == 0)
{
lean_object* v___x_1220_; lean_object* v___x_1221_; 
lean_dec(v___x_1217_);
lean_dec(v___x_1211_);
v___x_1220_ = lean_box(0);
v___x_1221_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1220_);
lean_ctor_set(v___x_1221_, 1, v_a_1205_);
return v___x_1221_;
}
else
{
lean_object* v___x_1222_; lean_object* v___x_1223_; lean_object* v_ref_1224_; uint8_t v___x_1225_; lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v___x_1228_; lean_object* v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; 
v___x_1222_ = l_Lean_Syntax_getArg(v___x_1217_, v___x_1210_);
v___x_1223_ = l_Lean_Syntax_getArg(v___x_1217_, v___x_1216_);
lean_dec(v___x_1217_);
v_ref_1224_ = l_Lean_replaceRef(v___x_1211_, v_a_1204_);
lean_dec(v___x_1211_);
v___x_1225_ = 0;
v___x_1226_ = l_Lean_SourceInfo_fromRef(v_ref_1224_, v___x_1225_);
lean_dec(v_ref_1224_);
v___x_1227_ = ((lean_object*)(l_Std_Do_term___u2227_u209a___00__closed__1));
v___x_1228_ = ((lean_object*)(l_Std_Do_term___u2227_u209a___00__closed__2));
lean_inc(v___x_1226_);
v___x_1229_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1229_, 0, v___x_1226_);
lean_ctor_set(v___x_1229_, 1, v___x_1228_);
v___x_1230_ = l_Lean_Syntax_node3(v___x_1226_, v___x_1227_, v___x_1222_, v___x_1229_, v___x_1223_);
v___x_1231_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1231_, 0, v___x_1230_);
lean_ctor_set(v___x_1231_, 1, v_a_1205_);
return v___x_1231_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1___boxed(lean_object* v_x_1232_, lean_object* v_a_1233_, lean_object* v_a_1234_){
_start:
{
lean_object* v_res_1235_; 
v_res_1235_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1(v_x_1232_, v_a_1233_, v_a_1234_);
lean_dec(v_a_1233_);
return v_res_1235_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg___lam__0(lean_object* v_ps_1236_, lean_object* v_fst_1237_, lean_object* v_fst_1238_, lean_object* v_a_1239_){
_start:
{
lean_object* v___x_1240_; lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1240_ = l_Std_Do_PostShape_args(v_ps_1236_);
lean_inc(v_a_1239_);
v___x_1241_ = lean_apply_1(v_fst_1237_, v_a_1239_);
v___x_1242_ = lean_apply_1(v_fst_1238_, v_a_1239_);
v___x_1243_ = l_Std_Do_SPred_imp(v___x_1240_, v___x_1241_, v___x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg___lam__0___boxed(lean_object* v_ps_1244_, lean_object* v_fst_1245_, lean_object* v_fst_1246_, lean_object* v_a_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_Std_Do_PostCond_imp___redArg___lam__0(v_ps_1244_, v_fst_1245_, v_fst_1246_, v_a_1247_);
lean_dec(v_ps_1244_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg(lean_object* v_ps_1249_, lean_object* v_p_1250_, lean_object* v_q_1251_){
_start:
{
lean_object* v_fst_1252_; lean_object* v_snd_1253_; lean_object* v_fst_1254_; lean_object* v_snd_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1264_; 
v_fst_1252_ = lean_ctor_get(v_p_1250_, 0);
lean_inc(v_fst_1252_);
v_snd_1253_ = lean_ctor_get(v_p_1250_, 1);
lean_inc(v_snd_1253_);
lean_dec_ref(v_p_1250_);
v_fst_1254_ = lean_ctor_get(v_q_1251_, 0);
v_snd_1255_ = lean_ctor_get(v_q_1251_, 1);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_q_1251_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1257_ = v_q_1251_;
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_snd_1255_);
lean_inc(v_fst_1254_);
lean_dec(v_q_1251_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1264_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v___f_1259_; lean_object* v___x_1260_; lean_object* v___x_1262_; 
lean_inc(v_ps_1249_);
v___f_1259_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_imp___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1259_, 0, v_ps_1249_);
lean_closure_set(v___f_1259_, 1, v_fst_1252_);
lean_closure_set(v___f_1259_, 2, v_fst_1254_);
v___x_1260_ = l_Std_Do_ExceptConds_imp(v_ps_1249_, v_snd_1253_, v_snd_1255_);
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 1, v___x_1260_);
lean_ctor_set(v___x_1257_, 0, v___f_1259_);
v___x_1262_ = v___x_1257_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v___f_1259_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1260_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp(lean_object* v_00_u03b1_1265_, lean_object* v_ps_1266_, lean_object* v_p_1267_, lean_object* v_q_1268_){
_start:
{
lean_object* v_fst_1269_; lean_object* v_snd_1270_; lean_object* v_fst_1271_; lean_object* v_snd_1272_; lean_object* v___x_1274_; uint8_t v_isShared_1275_; uint8_t v_isSharedCheck_1281_; 
v_fst_1269_ = lean_ctor_get(v_p_1267_, 0);
lean_inc(v_fst_1269_);
v_snd_1270_ = lean_ctor_get(v_p_1267_, 1);
lean_inc(v_snd_1270_);
lean_dec_ref(v_p_1267_);
v_fst_1271_ = lean_ctor_get(v_q_1268_, 0);
v_snd_1272_ = lean_ctor_get(v_q_1268_, 1);
v_isSharedCheck_1281_ = !lean_is_exclusive(v_q_1268_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1274_ = v_q_1268_;
v_isShared_1275_ = v_isSharedCheck_1281_;
goto v_resetjp_1273_;
}
else
{
lean_inc(v_snd_1272_);
lean_inc(v_fst_1271_);
lean_dec(v_q_1268_);
v___x_1274_ = lean_box(0);
v_isShared_1275_ = v_isSharedCheck_1281_;
goto v_resetjp_1273_;
}
v_resetjp_1273_:
{
lean_object* v___f_1276_; lean_object* v___x_1277_; lean_object* v___x_1279_; 
lean_inc(v_ps_1266_);
v___f_1276_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_imp___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1276_, 0, v_ps_1266_);
lean_closure_set(v___f_1276_, 1, v_fst_1269_);
lean_closure_set(v___f_1276_, 2, v_fst_1271_);
v___x_1277_ = l_Std_Do_ExceptConds_imp(v_ps_1266_, v_snd_1270_, v_snd_1272_);
if (v_isShared_1275_ == 0)
{
lean_ctor_set(v___x_1274_, 1, v___x_1277_);
lean_ctor_set(v___x_1274_, 0, v___f_1276_);
v___x_1279_ = v___x_1274_;
goto v_reusejp_1278_;
}
else
{
lean_object* v_reuseFailAlloc_1280_; 
v_reuseFailAlloc_1280_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1280_, 0, v___f_1276_);
lean_ctor_set(v_reuseFailAlloc_1280_, 1, v___x_1277_);
v___x_1279_ = v_reuseFailAlloc_1280_;
goto v_reusejp_1278_;
}
v_reusejp_1278_:
{
return v___x_1279_;
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1(void){
_start:
{
lean_object* v___x_1301_; lean_object* v___x_1302_; 
v___x_1301_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0));
v___x_1302_ = l_String_toRawSubstring_x27(v___x_1301_);
return v___x_1302_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1(lean_object* v_x_1317_, lean_object* v_a_1318_, lean_object* v_a_1319_){
_start:
{
lean_object* v___x_1320_; uint8_t v___x_1321_; 
v___x_1320_ = ((lean_object*)(l_Std_Do_term___u2192_u209a___00__closed__1));
lean_inc(v_x_1317_);
v___x_1321_ = l_Lean_Syntax_isOfKind(v_x_1317_, v___x_1320_);
if (v___x_1321_ == 0)
{
lean_object* v___x_1322_; lean_object* v___x_1323_; 
lean_dec(v_x_1317_);
v___x_1322_ = lean_box(1);
v___x_1323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1323_, 0, v___x_1322_);
lean_ctor_set(v___x_1323_, 1, v_a_1319_);
return v___x_1323_;
}
else
{
lean_object* v_quotContext_1324_; lean_object* v_currMacroScope_1325_; lean_object* v_ref_1326_; lean_object* v___x_1327_; lean_object* v___x_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; uint8_t v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; lean_object* v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; 
v_quotContext_1324_ = lean_ctor_get(v_a_1318_, 1);
v_currMacroScope_1325_ = lean_ctor_get(v_a_1318_, 2);
v_ref_1326_ = lean_ctor_get(v_a_1318_, 5);
v___x_1327_ = lean_unsigned_to_nat(0u);
v___x_1328_ = l_Lean_Syntax_getArg(v_x_1317_, v___x_1327_);
v___x_1329_ = lean_unsigned_to_nat(2u);
v___x_1330_ = l_Lean_Syntax_getArg(v_x_1317_, v___x_1329_);
lean_dec(v_x_1317_);
v___x_1331_ = 0;
v___x_1332_ = l_Lean_SourceInfo_fromRef(v_ref_1326_, v___x_1331_);
v___x_1333_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_1334_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1);
v___x_1335_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2));
lean_inc(v_currMacroScope_1325_);
lean_inc(v_quotContext_1324_);
v___x_1336_ = l_Lean_addMacroScope(v_quotContext_1324_, v___x_1335_, v_currMacroScope_1325_);
v___x_1337_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5));
lean_inc_n(v___x_1332_, 2);
v___x_1338_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1338_, 0, v___x_1332_);
lean_ctor_set(v___x_1338_, 1, v___x_1334_);
lean_ctor_set(v___x_1338_, 2, v___x_1336_);
lean_ctor_set(v___x_1338_, 3, v___x_1337_);
v___x_1339_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_1340_ = l_Lean_Syntax_node2(v___x_1332_, v___x_1339_, v___x_1328_, v___x_1330_);
v___x_1341_ = l_Lean_Syntax_node2(v___x_1332_, v___x_1333_, v___x_1338_, v___x_1340_);
v___x_1342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1341_);
lean_ctor_set(v___x_1342_, 1, v_a_1319_);
return v___x_1342_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___boxed(lean_object* v_x_1343_, lean_object* v_a_1344_, lean_object* v_a_1345_){
_start:
{
lean_object* v_res_1346_; 
v_res_1346_ = l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1(v_x_1343_, v_a_1344_, v_a_1345_);
lean_dec_ref(v_a_1344_);
return v_res_1346_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1(lean_object* v_x_1347_, lean_object* v_a_1348_, lean_object* v_a_1349_){
_start:
{
lean_object* v___x_1350_; uint8_t v___x_1351_; 
v___x_1350_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_1347_);
v___x_1351_ = l_Lean_Syntax_isOfKind(v_x_1347_, v___x_1350_);
if (v___x_1351_ == 0)
{
lean_object* v___x_1352_; lean_object* v___x_1353_; 
lean_dec(v_x_1347_);
v___x_1352_ = lean_box(0);
v___x_1353_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1353_, 0, v___x_1352_);
lean_ctor_set(v___x_1353_, 1, v_a_1349_);
return v___x_1353_;
}
else
{
lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v___x_1354_ = lean_unsigned_to_nat(0u);
v___x_1355_ = l_Lean_Syntax_getArg(v_x_1347_, v___x_1354_);
v___x_1356_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_1355_);
v___x_1357_ = l_Lean_Syntax_isOfKind(v___x_1355_, v___x_1356_);
if (v___x_1357_ == 0)
{
lean_object* v___x_1358_; lean_object* v___x_1359_; 
lean_dec(v___x_1355_);
lean_dec(v_x_1347_);
v___x_1358_ = lean_box(0);
v___x_1359_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1359_, 0, v___x_1358_);
lean_ctor_set(v___x_1359_, 1, v_a_1349_);
return v___x_1359_;
}
else
{
lean_object* v___x_1360_; lean_object* v___x_1361_; lean_object* v___x_1362_; uint8_t v___x_1363_; 
v___x_1360_ = lean_unsigned_to_nat(1u);
v___x_1361_ = l_Lean_Syntax_getArg(v_x_1347_, v___x_1360_);
lean_dec(v_x_1347_);
v___x_1362_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1361_);
v___x_1363_ = l_Lean_Syntax_matchesNull(v___x_1361_, v___x_1362_);
if (v___x_1363_ == 0)
{
lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec(v___x_1361_);
lean_dec(v___x_1355_);
v___x_1364_ = lean_box(0);
v___x_1365_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
lean_ctor_set(v___x_1365_, 1, v_a_1349_);
return v___x_1365_;
}
else
{
lean_object* v___x_1366_; lean_object* v___x_1367_; lean_object* v_ref_1368_; uint8_t v___x_1369_; lean_object* v___x_1370_; lean_object* v___x_1371_; lean_object* v___x_1372_; lean_object* v___x_1373_; lean_object* v___x_1374_; lean_object* v___x_1375_; 
v___x_1366_ = l_Lean_Syntax_getArg(v___x_1361_, v___x_1354_);
v___x_1367_ = l_Lean_Syntax_getArg(v___x_1361_, v___x_1360_);
lean_dec(v___x_1361_);
v_ref_1368_ = l_Lean_replaceRef(v___x_1355_, v_a_1348_);
lean_dec(v___x_1355_);
v___x_1369_ = 0;
v___x_1370_ = l_Lean_SourceInfo_fromRef(v_ref_1368_, v___x_1369_);
lean_dec(v_ref_1368_);
v___x_1371_ = ((lean_object*)(l_Std_Do_term___u2192_u209a___00__closed__1));
v___x_1372_ = ((lean_object*)(l_Std_Do_term___u2192_u209a___00__closed__2));
lean_inc(v___x_1370_);
v___x_1373_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1373_, 0, v___x_1370_);
lean_ctor_set(v___x_1373_, 1, v___x_1372_);
v___x_1374_ = l_Lean_Syntax_node3(v___x_1370_, v___x_1371_, v___x_1366_, v___x_1373_, v___x_1367_);
v___x_1375_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1375_, 0, v___x_1374_);
lean_ctor_set(v___x_1375_, 1, v_a_1349_);
return v___x_1375_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1___boxed(lean_object* v_x_1376_, lean_object* v_a_1377_, lean_object* v_a_1378_){
_start:
{
lean_object* v_res_1379_; 
v_res_1379_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1(v_x_1376_, v_a_1377_, v_a_1378_);
lean_dec(v_a_1377_);
return v_res_1379_;
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
