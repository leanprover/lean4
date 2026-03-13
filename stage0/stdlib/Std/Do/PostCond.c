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
lean_object* l_Array_mkArray0(lean_object*);
lean_object* l_Array_append___redArg(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node1(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_Syntax_node4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorIdx(lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorIdx___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__imp__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorIdx(lean_object* v_x_1_){
_start:
{
switch(lean_obj_tag(v_x_1_))
{
case 0:
{
lean_object* v___x_2_; 
v___x_2_ = lean_unsigned_to_nat(0u);
return v___x_2_;
}
case 1:
{
lean_object* v___x_3_; 
v___x_3_ = lean_unsigned_to_nat(1u);
return v___x_3_;
}
default: 
{
lean_object* v___x_4_; 
v___x_4_ = lean_unsigned_to_nat(2u);
return v___x_4_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorIdx___boxed(lean_object* v_x_5_){
_start:
{
lean_object* v_res_6_; 
v_res_6_ = l_Std_Do_PostShape_ctorIdx(v_x_5_);
lean_dec(v_x_5_);
return v_res_6_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorElim___redArg(lean_object* v_t_7_, lean_object* v_k_8_){
_start:
{
if (lean_obj_tag(v_t_7_) == 0)
{
return v_k_8_;
}
else
{
lean_object* v_a_9_; lean_object* v___x_10_; 
v_a_9_ = lean_ctor_get(v_t_7_, 0);
lean_inc(v_a_9_);
lean_dec(v_t_7_);
v___x_10_ = lean_apply_2(v_k_8_, lean_box(0), v_a_9_);
return v___x_10_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorElim(lean_object* v_motive_11_, lean_object* v_ctorIdx_12_, lean_object* v_t_13_, lean_object* v_h_14_, lean_object* v_k_15_){
_start:
{
lean_object* v___x_16_; 
v___x_16_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_13_, v_k_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_ctorElim___boxed(lean_object* v_motive_17_, lean_object* v_ctorIdx_18_, lean_object* v_t_19_, lean_object* v_h_20_, lean_object* v_k_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Std_Do_PostShape_ctorElim(v_motive_17_, v_ctorIdx_18_, v_t_19_, v_h_20_, v_k_21_);
lean_dec(v_ctorIdx_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_pure_elim___redArg(lean_object* v_t_23_, lean_object* v_pure_24_){
_start:
{
lean_object* v___x_25_; 
v___x_25_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_23_, v_pure_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_pure_elim(lean_object* v_motive_26_, lean_object* v_t_27_, lean_object* v_h_28_, lean_object* v_pure_29_){
_start:
{
lean_object* v___x_30_; 
v___x_30_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_27_, v_pure_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_arg_elim___redArg(lean_object* v_t_31_, lean_object* v_arg_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_31_, v_arg_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_arg_elim(lean_object* v_motive_34_, lean_object* v_t_35_, lean_object* v_h_36_, lean_object* v_arg_37_){
_start:
{
lean_object* v___x_38_; 
v___x_38_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_35_, v_arg_37_);
return v___x_38_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_except_elim___redArg(lean_object* v_t_39_, lean_object* v_except_40_){
_start:
{
lean_object* v___x_41_; 
v___x_41_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_39_, v_except_40_);
return v___x_41_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_except_elim(lean_object* v_motive_42_, lean_object* v_t_43_, lean_object* v_h_44_, lean_object* v_except_45_){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = l_Std_Do_PostShape_ctorElim___redArg(v_t_43_, v_except_45_);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_args(lean_object* v_x_47_){
_start:
{
switch(lean_obj_tag(v_x_47_))
{
case 0:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
case 1:
{
lean_object* v_a_49_; lean_object* v___x_50_; lean_object* v___x_51_; 
v_a_49_ = lean_ctor_get(v_x_47_, 0);
v___x_50_ = l_Std_Do_PostShape_args(v_a_49_);
v___x_51_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_51_, 0, lean_box(0));
lean_ctor_set(v___x_51_, 1, v___x_50_);
return v___x_51_;
}
default: 
{
lean_object* v_a_52_; 
v_a_52_ = lean_ctor_get(v_x_47_, 0);
v_x_47_ = v_a_52_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostShape_args___boxed(lean_object* v_x_54_){
_start:
{
lean_object* v_res_55_; 
v_res_55_ = l_Std_Do_PostShape_args(v_x_54_);
lean_dec(v_x_54_);
return v_res_55_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const___redArg___lam__0(lean_object* v_a_56_, lean_object* v_00___u03b5_57_){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_58_ = l_Std_Do_PostShape_args(v_a_56_);
v___x_59_ = l_Std_Do_SPred_pure___redArg(v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const___redArg___lam__0___boxed(lean_object* v_a_60_, lean_object* v_00___u03b5_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Std_Do_ExceptConds_const___redArg___lam__0(v_a_60_, v_00___u03b5_61_);
lean_dec(v_00___u03b5_61_);
lean_dec(v_a_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const___redArg(lean_object* v_ps_63_){
_start:
{
switch(lean_obj_tag(v_ps_63_))
{
case 0:
{
lean_object* v___x_64_; 
v___x_64_ = lean_box(0);
return v___x_64_;
}
case 1:
{
lean_object* v_a_65_; 
v_a_65_ = lean_ctor_get(v_ps_63_, 0);
lean_inc(v_a_65_);
lean_dec_ref(v_ps_63_);
v_ps_63_ = v_a_65_;
goto _start;
}
default: 
{
lean_object* v_a_67_; lean_object* v___f_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v_a_67_ = lean_ctor_get(v_ps_63_, 0);
lean_inc(v_a_67_);
lean_dec_ref(v_ps_63_);
lean_inc(v_a_67_);
v___f_68_ = lean_alloc_closure((void*)(l_Std_Do_ExceptConds_const___redArg___lam__0___boxed), 2, 1);
lean_closure_set(v___f_68_, 0, v_a_67_);
v___x_69_ = l_Std_Do_ExceptConds_const___redArg(v_a_67_);
v___x_70_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_70_, 0, v___f_68_);
lean_ctor_set(v___x_70_, 1, v___x_69_);
return v___x_70_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_const(lean_object* v_ps_71_, lean_object* v_p_72_){
_start:
{
lean_object* v___x_73_; 
v___x_73_ = l_Std_Do_ExceptConds_const___redArg(v_ps_71_);
return v___x_73_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_true(lean_object* v_ps_74_){
_start:
{
lean_object* v___x_75_; 
v___x_75_ = l_Std_Do_ExceptConds_const___redArg(v_ps_74_);
return v___x_75_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_false(lean_object* v_ps_76_){
_start:
{
lean_object* v___x_77_; 
v___x_77_ = l_Std_Do_ExceptConds_const___redArg(v_ps_76_);
return v___x_77_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedExceptConds(lean_object* v_ps_78_){
_start:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_Do_ExceptConds_const___redArg(v_ps_78_);
return v___x_79_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6(void){
_start:
{
lean_object* v___x_119_; lean_object* v___x_120_; 
v___x_119_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__5));
v___x_120_ = l_String_toRawSubstring_x27(v___x_119_);
return v___x_120_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1(lean_object* v_x_145_, lean_object* v_a_146_, lean_object* v_a_147_){
_start:
{
lean_object* v___x_148_; uint8_t v___x_149_; 
v___x_148_ = ((lean_object*)(l_Std_Do_term___u22a2_u2091___00__closed__3));
lean_inc(v_x_145_);
v___x_149_ = l_Lean_Syntax_isOfKind(v_x_145_, v___x_148_);
if (v___x_149_ == 0)
{
lean_object* v___x_150_; lean_object* v___x_151_; 
lean_dec_ref(v_a_146_);
lean_dec(v_x_145_);
v___x_150_ = lean_box(1);
v___x_151_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_a_147_);
return v___x_151_;
}
else
{
lean_object* v_quotContext_152_; lean_object* v_currMacroScope_153_; lean_object* v_ref_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v_quotContext_152_ = lean_ctor_get(v_a_146_, 1);
lean_inc(v_quotContext_152_);
v_currMacroScope_153_ = lean_ctor_get(v_a_146_, 2);
lean_inc(v_currMacroScope_153_);
v_ref_154_ = lean_ctor_get(v_a_146_, 5);
lean_inc(v_ref_154_);
lean_dec_ref(v_a_146_);
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = l_Lean_Syntax_getArg(v_x_145_, v___x_155_);
v___x_157_ = lean_unsigned_to_nat(2u);
v___x_158_ = l_Lean_Syntax_getArg(v_x_145_, v___x_157_);
lean_dec(v_x_145_);
v___x_159_ = 0;
v___x_160_ = l_Lean_SourceInfo_fromRef(v_ref_154_, v___x_159_);
lean_dec(v_ref_154_);
v___x_161_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_162_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__6);
v___x_163_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__9));
v___x_164_ = l_Lean_addMacroScope(v_quotContext_152_, v___x_163_, v_currMacroScope_153_);
v___x_165_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__14));
lean_inc(v___x_160_);
v___x_166_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_166_, 0, v___x_160_);
lean_ctor_set(v___x_166_, 1, v___x_162_);
lean_ctor_set(v___x_166_, 2, v___x_164_);
lean_ctor_set(v___x_166_, 3, v___x_165_);
v___x_167_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
lean_inc(v___x_160_);
v___x_168_ = l_Lean_Syntax_node2(v___x_160_, v___x_167_, v___x_156_, v___x_158_);
v___x_169_ = l_Lean_Syntax_node2(v___x_160_, v___x_161_, v___x_166_, v___x_168_);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v_a_147_);
return v___x_170_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1(lean_object* v_x_174_, lean_object* v_a_175_, lean_object* v_a_176_){
_start:
{
lean_object* v___x_177_; uint8_t v___x_178_; 
v___x_177_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_174_);
v___x_178_ = l_Lean_Syntax_isOfKind(v_x_174_, v___x_177_);
if (v___x_178_ == 0)
{
lean_object* v___x_179_; lean_object* v___x_180_; 
lean_dec(v_x_174_);
v___x_179_ = lean_box(0);
v___x_180_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_180_, 0, v___x_179_);
lean_ctor_set(v___x_180_, 1, v_a_176_);
return v___x_180_;
}
else
{
lean_object* v___x_181_; lean_object* v___x_182_; lean_object* v___x_183_; uint8_t v___x_184_; 
v___x_181_ = lean_unsigned_to_nat(0u);
v___x_182_ = l_Lean_Syntax_getArg(v_x_174_, v___x_181_);
v___x_183_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_182_);
v___x_184_ = l_Lean_Syntax_isOfKind(v___x_182_, v___x_183_);
if (v___x_184_ == 0)
{
lean_object* v___x_185_; lean_object* v___x_186_; 
lean_dec(v___x_182_);
lean_dec(v_x_174_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_186_, 0, v___x_185_);
lean_ctor_set(v___x_186_, 1, v_a_176_);
return v___x_186_;
}
else
{
lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; uint8_t v___x_190_; 
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = l_Lean_Syntax_getArg(v_x_174_, v___x_187_);
lean_dec(v_x_174_);
v___x_189_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_188_);
v___x_190_ = l_Lean_Syntax_matchesNull(v___x_188_, v___x_189_);
if (v___x_190_ == 0)
{
lean_object* v___x_191_; lean_object* v___x_192_; 
lean_dec(v___x_188_);
lean_dec(v___x_182_);
v___x_191_ = lean_box(0);
v___x_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v_a_176_);
return v___x_192_;
}
else
{
lean_object* v___x_193_; lean_object* v___x_194_; lean_object* v_ref_195_; uint8_t v___x_196_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_193_ = l_Lean_Syntax_getArg(v___x_188_, v___x_181_);
v___x_194_ = l_Lean_Syntax_getArg(v___x_188_, v___x_187_);
lean_dec(v___x_188_);
v_ref_195_ = l_Lean_replaceRef(v___x_182_, v_a_175_);
lean_dec(v___x_182_);
v___x_196_ = 0;
v___x_197_ = l_Lean_SourceInfo_fromRef(v_ref_195_, v___x_196_);
lean_dec(v_ref_195_);
v___x_198_ = ((lean_object*)(l_Std_Do_term___u22a2_u2091___00__closed__3));
v___x_199_ = ((lean_object*)(l_Std_Do_term___u22a2_u2091___00__closed__6));
lean_inc(v___x_197_);
v___x_200_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_200_, 0, v___x_197_);
lean_ctor_set(v___x_200_, 1, v___x_199_);
v___x_201_ = l_Lean_Syntax_node3(v___x_197_, v___x_198_, v___x_193_, v___x_200_, v___x_194_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v___x_201_);
lean_ctor_set(v___x_202_, 1, v_a_176_);
return v___x_202_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___boxed(lean_object* v_x_203_, lean_object* v_a_204_, lean_object* v_a_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1(v_x_203_, v_a_204_, v_a_205_);
lean_dec(v_a_204_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_ExceptConds_entails_match__1_splitter___redArg(lean_object* v_ps_207_, lean_object* v_x_208_, lean_object* v_y_209_, lean_object* v_h__1_210_, lean_object* v_h__2_211_, lean_object* v_h__3_212_){
_start:
{
switch(lean_obj_tag(v_ps_207_))
{
case 0:
{
lean_object* v___x_213_; 
lean_dec(v_h__3_212_);
lean_dec(v_h__2_211_);
v___x_213_ = lean_apply_2(v_h__1_210_, v_x_208_, v_y_209_);
return v___x_213_;
}
case 1:
{
lean_object* v_a_214_; lean_object* v___x_215_; 
lean_dec(v_h__3_212_);
lean_dec(v_h__1_210_);
v_a_214_ = lean_ctor_get(v_ps_207_, 0);
lean_inc(v_a_214_);
lean_dec_ref(v_ps_207_);
v___x_215_ = lean_apply_4(v_h__2_211_, lean_box(0), v_a_214_, v_x_208_, v_y_209_);
return v___x_215_;
}
default: 
{
lean_object* v_a_216_; lean_object* v___x_217_; 
lean_dec(v_h__2_211_);
lean_dec(v_h__1_210_);
v_a_216_ = lean_ctor_get(v_ps_207_, 0);
lean_inc(v_a_216_);
lean_dec_ref(v_ps_207_);
v___x_217_ = lean_apply_4(v_h__3_212_, lean_box(0), v_a_216_, v_x_208_, v_y_209_);
return v___x_217_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_ExceptConds_entails_match__1_splitter(lean_object* v_motive_218_, lean_object* v_ps_219_, lean_object* v_x_220_, lean_object* v_y_221_, lean_object* v_h__1_222_, lean_object* v_h__2_223_, lean_object* v_h__3_224_){
_start:
{
lean_object* v___x_225_; 
v___x_225_ = l___private_Std_Do_PostCond_0__Std_Do_ExceptConds_entails_match__1_splitter___redArg(v_ps_219_, v_x_220_, v_y_221_, v_h__1_222_, v_h__2_223_, v_h__3_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_PostShape_args_match__1_splitter___redArg(lean_object* v_x_226_, lean_object* v_h__1_227_, lean_object* v_h__2_228_, lean_object* v_h__3_229_){
_start:
{
switch(lean_obj_tag(v_x_226_))
{
case 0:
{
lean_object* v___x_230_; lean_object* v___x_231_; 
lean_dec(v_h__3_229_);
lean_dec(v_h__2_228_);
v___x_230_ = lean_box(0);
v___x_231_ = lean_apply_1(v_h__1_227_, v___x_230_);
return v___x_231_;
}
case 1:
{
lean_object* v_a_232_; lean_object* v___x_233_; 
lean_dec(v_h__3_229_);
lean_dec(v_h__1_227_);
v_a_232_ = lean_ctor_get(v_x_226_, 0);
lean_inc(v_a_232_);
lean_dec_ref(v_x_226_);
v___x_233_ = lean_apply_2(v_h__2_228_, lean_box(0), v_a_232_);
return v___x_233_;
}
default: 
{
lean_object* v_a_234_; lean_object* v___x_235_; 
lean_dec(v_h__2_228_);
lean_dec(v_h__1_227_);
v_a_234_ = lean_ctor_get(v_x_226_, 0);
lean_inc(v_a_234_);
lean_dec_ref(v_x_226_);
v___x_235_ = lean_apply_2(v_h__3_229_, lean_box(0), v_a_234_);
return v___x_235_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Do_PostCond_0__Std_Do_PostShape_args_match__1_splitter(lean_object* v_motive_236_, lean_object* v_x_237_, lean_object* v_h__1_238_, lean_object* v_h__2_239_, lean_object* v_h__3_240_){
_start:
{
lean_object* v___x_241_; 
v___x_241_ = l___private_Std_Do_PostCond_0__Std_Do_PostShape_args_match__1_splitter___redArg(v_x_237_, v_h__1_238_, v_h__2_239_, v_h__3_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and___lam__0(lean_object* v_a_242_, lean_object* v_fst_243_, lean_object* v_fst_244_, lean_object* v_e_245_){
_start:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_246_ = l_Std_Do_PostShape_args(v_a_242_);
lean_inc(v_e_245_);
v___x_247_ = lean_apply_1(v_fst_243_, v_e_245_);
v___x_248_ = lean_apply_1(v_fst_244_, v_e_245_);
v___x_249_ = l_Std_Do_SPred_and(v___x_246_, v___x_247_, v___x_248_);
return v___x_249_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and___lam__0___boxed(lean_object* v_a_250_, lean_object* v_fst_251_, lean_object* v_fst_252_, lean_object* v_e_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_Do_ExceptConds_and___lam__0(v_a_250_, v_fst_251_, v_fst_252_, v_e_253_);
lean_dec(v_a_250_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_and(lean_object* v_ps_255_, lean_object* v_x_256_, lean_object* v_y_257_){
_start:
{
switch(lean_obj_tag(v_ps_255_))
{
case 0:
{
lean_object* v___x_258_; 
lean_dec(v_y_257_);
lean_dec(v_x_256_);
v___x_258_ = lean_box(0);
return v___x_258_;
}
case 1:
{
lean_object* v_a_259_; 
v_a_259_ = lean_ctor_get(v_ps_255_, 0);
lean_inc(v_a_259_);
lean_dec_ref(v_ps_255_);
v_ps_255_ = v_a_259_;
goto _start;
}
default: 
{
lean_object* v_a_261_; lean_object* v_fst_262_; lean_object* v_snd_263_; lean_object* v_fst_264_; lean_object* v_snd_265_; lean_object* v___x_267_; uint8_t v_isShared_268_; uint8_t v_isSharedCheck_274_; 
v_a_261_ = lean_ctor_get(v_ps_255_, 0);
lean_inc(v_a_261_);
lean_dec_ref(v_ps_255_);
v_fst_262_ = lean_ctor_get(v_x_256_, 0);
lean_inc(v_fst_262_);
v_snd_263_ = lean_ctor_get(v_x_256_, 1);
lean_inc(v_snd_263_);
lean_dec(v_x_256_);
v_fst_264_ = lean_ctor_get(v_y_257_, 0);
v_snd_265_ = lean_ctor_get(v_y_257_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_y_257_);
if (v_isSharedCheck_274_ == 0)
{
v___x_267_ = v_y_257_;
v_isShared_268_ = v_isSharedCheck_274_;
goto v_resetjp_266_;
}
else
{
lean_inc(v_snd_265_);
lean_inc(v_fst_264_);
lean_dec(v_y_257_);
v___x_267_ = lean_box(0);
v_isShared_268_ = v_isSharedCheck_274_;
goto v_resetjp_266_;
}
v_resetjp_266_:
{
lean_object* v___f_269_; lean_object* v___x_270_; lean_object* v___x_272_; 
lean_inc(v_a_261_);
v___f_269_ = lean_alloc_closure((void*)(l_Std_Do_ExceptConds_and___lam__0___boxed), 4, 3);
lean_closure_set(v___f_269_, 0, v_a_261_);
lean_closure_set(v___f_269_, 1, v_fst_262_);
lean_closure_set(v___f_269_, 2, v_fst_264_);
v___x_270_ = l_Std_Do_ExceptConds_and(v_a_261_, v_snd_263_, v_snd_265_);
if (v_isShared_268_ == 0)
{
lean_ctor_set(v___x_267_, 1, v___x_270_);
lean_ctor_set(v___x_267_, 0, v___f_269_);
v___x_272_ = v___x_267_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___f_269_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v___x_270_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1(void){
_start:
{
lean_object* v___x_297_; lean_object* v___x_298_; 
v___x_297_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__0));
v___x_298_ = l_String_toRawSubstring_x27(v___x_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1(lean_object* v_x_314_, lean_object* v_a_315_, lean_object* v_a_316_){
_start:
{
lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_317_ = ((lean_object*)(l_Std_Do_term___u2227_u2091___00__closed__1));
lean_inc(v_x_314_);
v___x_318_ = l_Lean_Syntax_isOfKind(v_x_314_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec_ref(v_a_315_);
lean_dec(v_x_314_);
v___x_319_ = lean_box(1);
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_a_316_);
return v___x_320_;
}
else
{
lean_object* v_quotContext_321_; lean_object* v_currMacroScope_322_; lean_object* v_ref_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; uint8_t v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; 
v_quotContext_321_ = lean_ctor_get(v_a_315_, 1);
lean_inc(v_quotContext_321_);
v_currMacroScope_322_ = lean_ctor_get(v_a_315_, 2);
lean_inc(v_currMacroScope_322_);
v_ref_323_ = lean_ctor_get(v_a_315_, 5);
lean_inc(v_ref_323_);
lean_dec_ref(v_a_315_);
v___x_324_ = lean_unsigned_to_nat(0u);
v___x_325_ = l_Lean_Syntax_getArg(v_x_314_, v___x_324_);
v___x_326_ = lean_unsigned_to_nat(2u);
v___x_327_ = l_Lean_Syntax_getArg(v_x_314_, v___x_326_);
lean_dec(v_x_314_);
v___x_328_ = 0;
v___x_329_ = l_Lean_SourceInfo_fromRef(v_ref_323_, v___x_328_);
lean_dec(v_ref_323_);
v___x_330_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_331_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__1);
v___x_332_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__3));
v___x_333_ = l_Lean_addMacroScope(v_quotContext_321_, v___x_332_, v_currMacroScope_322_);
v___x_334_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u2091____1___closed__6));
lean_inc(v___x_329_);
v___x_335_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_335_, 0, v___x_329_);
lean_ctor_set(v___x_335_, 1, v___x_331_);
lean_ctor_set(v___x_335_, 2, v___x_333_);
lean_ctor_set(v___x_335_, 3, v___x_334_);
v___x_336_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
lean_inc(v___x_329_);
v___x_337_ = l_Lean_Syntax_node2(v___x_329_, v___x_336_, v___x_325_, v___x_327_);
v___x_338_ = l_Lean_Syntax_node2(v___x_329_, v___x_330_, v___x_335_, v___x_337_);
v___x_339_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
lean_ctor_set(v___x_339_, 1, v_a_316_);
return v___x_339_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1(lean_object* v_x_340_, lean_object* v_a_341_, lean_object* v_a_342_){
_start:
{
lean_object* v___x_343_; uint8_t v___x_344_; 
v___x_343_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_340_);
v___x_344_ = l_Lean_Syntax_isOfKind(v_x_340_, v___x_343_);
if (v___x_344_ == 0)
{
lean_object* v___x_345_; lean_object* v___x_346_; 
lean_dec(v_x_340_);
v___x_345_ = lean_box(0);
v___x_346_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set(v___x_346_, 1, v_a_342_);
return v___x_346_;
}
else
{
lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; uint8_t v___x_350_; 
v___x_347_ = lean_unsigned_to_nat(0u);
v___x_348_ = l_Lean_Syntax_getArg(v_x_340_, v___x_347_);
v___x_349_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_348_);
v___x_350_ = l_Lean_Syntax_isOfKind(v___x_348_, v___x_349_);
if (v___x_350_ == 0)
{
lean_object* v___x_351_; lean_object* v___x_352_; 
lean_dec(v___x_348_);
lean_dec(v_x_340_);
v___x_351_ = lean_box(0);
v___x_352_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_352_, 0, v___x_351_);
lean_ctor_set(v___x_352_, 1, v_a_342_);
return v___x_352_;
}
else
{
lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; 
v___x_353_ = lean_unsigned_to_nat(1u);
v___x_354_ = l_Lean_Syntax_getArg(v_x_340_, v___x_353_);
lean_dec(v_x_340_);
v___x_355_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_354_);
v___x_356_ = l_Lean_Syntax_matchesNull(v___x_354_, v___x_355_);
if (v___x_356_ == 0)
{
lean_object* v___x_357_; lean_object* v___x_358_; 
lean_dec(v___x_354_);
lean_dec(v___x_348_);
v___x_357_ = lean_box(0);
v___x_358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v_a_342_);
return v___x_358_;
}
else
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v_ref_361_; uint8_t v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; 
v___x_359_ = l_Lean_Syntax_getArg(v___x_354_, v___x_347_);
v___x_360_ = l_Lean_Syntax_getArg(v___x_354_, v___x_353_);
lean_dec(v___x_354_);
v_ref_361_ = l_Lean_replaceRef(v___x_348_, v_a_341_);
lean_dec(v___x_348_);
v___x_362_ = 0;
v___x_363_ = l_Lean_SourceInfo_fromRef(v_ref_361_, v___x_362_);
lean_dec(v_ref_361_);
v___x_364_ = ((lean_object*)(l_Std_Do_term___u2227_u2091___00__closed__1));
v___x_365_ = ((lean_object*)(l_Std_Do_term___u2227_u2091___00__closed__2));
lean_inc(v___x_363_);
v___x_366_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_363_);
lean_ctor_set(v___x_366_, 1, v___x_365_);
v___x_367_ = l_Lean_Syntax_node3(v___x_363_, v___x_364_, v___x_359_, v___x_366_, v___x_360_);
v___x_368_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_367_);
lean_ctor_set(v___x_368_, 1, v_a_342_);
return v___x_368_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1___boxed(lean_object* v_x_369_, lean_object* v_a_370_, lean_object* v_a_371_){
_start:
{
lean_object* v_res_372_; 
v_res_372_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__and__1(v_x_369_, v_a_370_, v_a_371_);
lean_dec(v_a_370_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp___lam__0(lean_object* v_a_373_, lean_object* v_fst_374_, lean_object* v_fst_375_, lean_object* v_e_376_){
_start:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; 
v___x_377_ = l_Std_Do_PostShape_args(v_a_373_);
lean_inc(v_e_376_);
v___x_378_ = lean_apply_1(v_fst_374_, v_e_376_);
v___x_379_ = lean_apply_1(v_fst_375_, v_e_376_);
v___x_380_ = l_Std_Do_SPred_imp(v___x_377_, v___x_378_, v___x_379_);
return v___x_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp___lam__0___boxed(lean_object* v_a_381_, lean_object* v_fst_382_, lean_object* v_fst_383_, lean_object* v_e_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_Do_ExceptConds_imp___lam__0(v_a_381_, v_fst_382_, v_fst_383_, v_e_384_);
lean_dec(v_a_381_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_ExceptConds_imp(lean_object* v_ps_386_, lean_object* v_x_387_, lean_object* v_y_388_){
_start:
{
switch(lean_obj_tag(v_ps_386_))
{
case 0:
{
lean_object* v___x_389_; 
lean_dec(v_y_388_);
lean_dec(v_x_387_);
v___x_389_ = lean_box(0);
return v___x_389_;
}
case 1:
{
lean_object* v_a_390_; 
v_a_390_ = lean_ctor_get(v_ps_386_, 0);
lean_inc(v_a_390_);
lean_dec_ref(v_ps_386_);
v_ps_386_ = v_a_390_;
goto _start;
}
default: 
{
lean_object* v_a_392_; lean_object* v_fst_393_; lean_object* v_snd_394_; lean_object* v_fst_395_; lean_object* v_snd_396_; lean_object* v___x_398_; uint8_t v_isShared_399_; uint8_t v_isSharedCheck_405_; 
v_a_392_ = lean_ctor_get(v_ps_386_, 0);
lean_inc(v_a_392_);
lean_dec_ref(v_ps_386_);
v_fst_393_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_fst_393_);
v_snd_394_ = lean_ctor_get(v_x_387_, 1);
lean_inc(v_snd_394_);
lean_dec(v_x_387_);
v_fst_395_ = lean_ctor_get(v_y_388_, 0);
v_snd_396_ = lean_ctor_get(v_y_388_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_y_388_);
if (v_isSharedCheck_405_ == 0)
{
v___x_398_ = v_y_388_;
v_isShared_399_ = v_isSharedCheck_405_;
goto v_resetjp_397_;
}
else
{
lean_inc(v_snd_396_);
lean_inc(v_fst_395_);
lean_dec(v_y_388_);
v___x_398_ = lean_box(0);
v_isShared_399_ = v_isSharedCheck_405_;
goto v_resetjp_397_;
}
v_resetjp_397_:
{
lean_object* v___f_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
lean_inc(v_a_392_);
v___f_400_ = lean_alloc_closure((void*)(l_Std_Do_ExceptConds_imp___lam__0___boxed), 4, 3);
lean_closure_set(v___f_400_, 0, v_a_392_);
lean_closure_set(v___f_400_, 1, v_fst_393_);
lean_closure_set(v___f_400_, 2, v_fst_395_);
v___x_401_ = l_Std_Do_ExceptConds_imp(v_a_392_, v_snd_394_, v_snd_396_);
if (v_isShared_399_ == 0)
{
lean_ctor_set(v___x_398_, 1, v___x_401_);
lean_ctor_set(v___x_398_, 0, v___f_400_);
v___x_403_ = v___x_398_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___f_400_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1(void){
_start:
{
lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_425_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__0));
v___x_426_ = l_String_toRawSubstring_x27(v___x_425_);
return v___x_426_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1(lean_object* v_x_442_, lean_object* v_a_443_, lean_object* v_a_444_){
_start:
{
lean_object* v___x_445_; uint8_t v___x_446_; 
v___x_445_ = ((lean_object*)(l_Std_Do_term___u2192_u2091___00__closed__1));
lean_inc(v_x_442_);
v___x_446_ = l_Lean_Syntax_isOfKind(v_x_442_, v___x_445_);
if (v___x_446_ == 0)
{
lean_object* v___x_447_; lean_object* v___x_448_; 
lean_dec_ref(v_a_443_);
lean_dec(v_x_442_);
v___x_447_ = lean_box(1);
v___x_448_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_448_, 0, v___x_447_);
lean_ctor_set(v___x_448_, 1, v_a_444_);
return v___x_448_;
}
else
{
lean_object* v_quotContext_449_; lean_object* v_currMacroScope_450_; lean_object* v_ref_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; uint8_t v___x_456_; lean_object* v___x_457_; lean_object* v___x_458_; lean_object* v___x_459_; lean_object* v___x_460_; lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_467_; 
v_quotContext_449_ = lean_ctor_get(v_a_443_, 1);
lean_inc(v_quotContext_449_);
v_currMacroScope_450_ = lean_ctor_get(v_a_443_, 2);
lean_inc(v_currMacroScope_450_);
v_ref_451_ = lean_ctor_get(v_a_443_, 5);
lean_inc(v_ref_451_);
lean_dec_ref(v_a_443_);
v___x_452_ = lean_unsigned_to_nat(0u);
v___x_453_ = l_Lean_Syntax_getArg(v_x_442_, v___x_452_);
v___x_454_ = lean_unsigned_to_nat(2u);
v___x_455_ = l_Lean_Syntax_getArg(v_x_442_, v___x_454_);
lean_dec(v_x_442_);
v___x_456_ = 0;
v___x_457_ = l_Lean_SourceInfo_fromRef(v_ref_451_, v___x_456_);
lean_dec(v_ref_451_);
v___x_458_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_459_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__1);
v___x_460_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__3));
v___x_461_ = l_Lean_addMacroScope(v_quotContext_449_, v___x_460_, v_currMacroScope_450_);
v___x_462_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u2091____1___closed__6));
lean_inc(v___x_457_);
v___x_463_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_463_, 0, v___x_457_);
lean_ctor_set(v___x_463_, 1, v___x_459_);
lean_ctor_set(v___x_463_, 2, v___x_461_);
lean_ctor_set(v___x_463_, 3, v___x_462_);
v___x_464_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
lean_inc(v___x_457_);
v___x_465_ = l_Lean_Syntax_node2(v___x_457_, v___x_464_, v___x_453_, v___x_455_);
v___x_466_ = l_Lean_Syntax_node2(v___x_457_, v___x_458_, v___x_463_, v___x_465_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___x_466_);
lean_ctor_set(v___x_467_, 1, v_a_444_);
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1(lean_object* v_x_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
lean_object* v___x_471_; uint8_t v___x_472_; 
v___x_471_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_468_);
v___x_472_ = l_Lean_Syntax_isOfKind(v_x_468_, v___x_471_);
if (v___x_472_ == 0)
{
lean_object* v___x_473_; lean_object* v___x_474_; 
lean_dec(v_x_468_);
v___x_473_ = lean_box(0);
v___x_474_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_474_, 0, v___x_473_);
lean_ctor_set(v___x_474_, 1, v_a_470_);
return v___x_474_;
}
else
{
lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_475_ = lean_unsigned_to_nat(0u);
v___x_476_ = l_Lean_Syntax_getArg(v_x_468_, v___x_475_);
v___x_477_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_476_);
v___x_478_ = l_Lean_Syntax_isOfKind(v___x_476_, v___x_477_);
if (v___x_478_ == 0)
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v___x_476_);
lean_dec(v_x_468_);
v___x_479_ = lean_box(0);
v___x_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_480_, 0, v___x_479_);
lean_ctor_set(v___x_480_, 1, v_a_470_);
return v___x_480_;
}
else
{
lean_object* v___x_481_; lean_object* v___x_482_; lean_object* v___x_483_; uint8_t v___x_484_; 
v___x_481_ = lean_unsigned_to_nat(1u);
v___x_482_ = l_Lean_Syntax_getArg(v_x_468_, v___x_481_);
lean_dec(v_x_468_);
v___x_483_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_482_);
v___x_484_ = l_Lean_Syntax_matchesNull(v___x_482_, v___x_483_);
if (v___x_484_ == 0)
{
lean_object* v___x_485_; lean_object* v___x_486_; 
lean_dec(v___x_482_);
lean_dec(v___x_476_);
v___x_485_ = lean_box(0);
v___x_486_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
lean_ctor_set(v___x_486_, 1, v_a_470_);
return v___x_486_;
}
else
{
lean_object* v___x_487_; lean_object* v___x_488_; lean_object* v_ref_489_; uint8_t v___x_490_; lean_object* v___x_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; lean_object* v___x_495_; lean_object* v___x_496_; 
v___x_487_ = l_Lean_Syntax_getArg(v___x_482_, v___x_475_);
v___x_488_ = l_Lean_Syntax_getArg(v___x_482_, v___x_481_);
lean_dec(v___x_482_);
v_ref_489_ = l_Lean_replaceRef(v___x_476_, v_a_469_);
lean_dec(v___x_476_);
v___x_490_ = 0;
v___x_491_ = l_Lean_SourceInfo_fromRef(v_ref_489_, v___x_490_);
lean_dec(v_ref_489_);
v___x_492_ = ((lean_object*)(l_Std_Do_term___u2192_u2091___00__closed__1));
v___x_493_ = ((lean_object*)(l_Std_Do_term___u2192_u2091___00__closed__2));
lean_inc(v___x_491_);
v___x_494_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_494_, 0, v___x_491_);
lean_ctor_set(v___x_494_, 1, v___x_493_);
v___x_495_ = l_Lean_Syntax_node3(v___x_491_, v___x_492_, v___x_487_, v___x_494_, v___x_488_);
v___x_496_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_496_, 0, v___x_495_);
lean_ctor_set(v___x_496_, 1, v_a_470_);
return v___x_496_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1___boxed(lean_object* v_x_497_, lean_object* v_a_498_, lean_object* v_a_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__imp__1(v_x_497_, v_a_498_, v_a_499_);
lean_dec(v_a_498_);
return v_res_500_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13(void){
_start:
{
lean_object* v___x_570_; 
v___x_570_ = l_Array_mkArray0(lean_box(0));
return v___x_570_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15(void){
_start:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__14));
v___x_573_ = l_String_toRawSubstring_x27(v___x_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1(lean_object* v_x_590_, lean_object* v_a_591_, lean_object* v_a_592_){
_start:
{
lean_object* v___x_593_; uint8_t v___x_594_; 
v___x_593_ = ((lean_object*)(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__1));
lean_inc(v_x_590_);
v___x_594_ = l_Lean_Syntax_isOfKind(v_x_590_, v___x_593_);
if (v___x_594_ == 0)
{
lean_object* v___x_595_; lean_object* v___x_596_; 
lean_dec_ref(v_a_591_);
lean_dec(v_x_590_);
v___x_595_ = lean_box(1);
v___x_596_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_596_, 0, v___x_595_);
lean_ctor_set(v___x_596_, 1, v_a_592_);
return v___x_596_;
}
else
{
lean_object* v_quotContext_597_; lean_object* v_currMacroScope_598_; lean_object* v_ref_599_; lean_object* v___x_600_; lean_object* v___x_601_; lean_object* v___x_602_; lean_object* v___x_603_; uint8_t v___x_604_; lean_object* v___x_605_; lean_object* v___x_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; lean_object* v___x_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; 
v_quotContext_597_ = lean_ctor_get(v_a_591_, 1);
lean_inc(v_quotContext_597_);
v_currMacroScope_598_ = lean_ctor_get(v_a_591_, 2);
lean_inc(v_currMacroScope_598_);
v_ref_599_ = lean_ctor_get(v_a_591_, 5);
lean_inc(v_ref_599_);
lean_dec_ref(v_a_591_);
v___x_600_ = lean_unsigned_to_nat(1u);
v___x_601_ = l_Lean_Syntax_getArg(v_x_590_, v___x_600_);
lean_dec(v_x_590_);
v___x_602_ = ((lean_object*)(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__5));
v___x_603_ = l_Lean_Syntax_getArgs(v___x_601_);
lean_dec(v___x_601_);
v___x_604_ = 0;
v___x_605_ = l_Lean_SourceInfo_fromRef(v_ref_599_, v___x_604_);
lean_dec(v_ref_599_);
v___x_606_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1));
v___x_607_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2));
lean_inc(v___x_605_);
v___x_608_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_605_);
lean_ctor_set(v___x_608_, 1, v___x_607_);
v___x_609_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5));
v___x_610_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7));
v___x_611_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_612_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8));
v___x_613_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9));
lean_inc(v___x_605_);
v___x_614_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_614_, 0, v___x_605_);
lean_ctor_set(v___x_614_, 1, v___x_612_);
v___x_615_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__11));
v___x_616_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__12));
lean_inc(v___x_605_);
v___x_617_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_617_, 0, v___x_605_);
lean_ctor_set(v___x_617_, 1, v___x_616_);
v___x_618_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
v___x_619_ = l_Array_append___redArg(v___x_618_, v___x_603_);
lean_dec_ref(v___x_603_);
lean_inc(v___x_605_);
v___x_620_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_620_, 0, v___x_605_);
lean_ctor_set(v___x_620_, 1, v___x_602_);
v___x_621_ = lean_array_push(v___x_619_, v___x_620_);
v___x_622_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__15);
v___x_623_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__18));
v___x_624_ = l_Lean_addMacroScope(v_quotContext_597_, v___x_623_, v_currMacroScope_598_);
v___x_625_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__22));
lean_inc(v___x_605_);
v___x_626_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_626_, 0, v___x_605_);
lean_ctor_set(v___x_626_, 1, v___x_622_);
lean_ctor_set(v___x_626_, 2, v___x_624_);
lean_ctor_set(v___x_626_, 3, v___x_625_);
v___x_627_ = lean_array_push(v___x_621_, v___x_626_);
lean_inc(v___x_605_);
v___x_628_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_628_, 0, v___x_605_);
lean_ctor_set(v___x_628_, 1, v___x_611_);
lean_ctor_set(v___x_628_, 2, v___x_627_);
v___x_629_ = ((lean_object*)(l_Std_Do_termPost_u27e8___x2c_x2c_u27e9___closed__10));
lean_inc(v___x_605_);
v___x_630_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_630_, 0, v___x_605_);
lean_ctor_set(v___x_630_, 1, v___x_629_);
lean_inc(v___x_605_);
v___x_631_ = l_Lean_Syntax_node3(v___x_605_, v___x_615_, v___x_617_, v___x_628_, v___x_630_);
lean_inc(v___x_605_);
v___x_632_ = l_Lean_Syntax_node2(v___x_605_, v___x_613_, v___x_614_, v___x_631_);
lean_inc(v___x_605_);
v___x_633_ = l_Lean_Syntax_node1(v___x_605_, v___x_611_, v___x_632_);
lean_inc(v___x_605_);
v___x_634_ = l_Lean_Syntax_node1(v___x_605_, v___x_610_, v___x_633_);
lean_inc(v___x_605_);
v___x_635_ = l_Lean_Syntax_node1(v___x_605_, v___x_609_, v___x_634_);
v___x_636_ = l_Lean_Syntax_node2(v___x_605_, v___x_606_, v___x_608_, v___x_635_);
v___x_637_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_637_, 0, v___x_636_);
lean_ctor_set(v___x_637_, 1, v_a_592_);
return v___x_637_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_noThrow___redArg(lean_object* v_ps_638_, lean_object* v_p_639_){
_start:
{
lean_object* v___x_640_; lean_object* v___x_641_; 
v___x_640_ = l_Std_Do_ExceptConds_const___redArg(v_ps_638_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v_p_639_);
lean_ctor_set(v___x_641_, 1, v___x_640_);
return v___x_641_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_noThrow(lean_object* v_00_u03b1_642_, lean_object* v_ps_643_, lean_object* v_p_644_){
_start:
{
lean_object* v___x_645_; lean_object* v___x_646_; 
v___x_645_ = l_Std_Do_ExceptConds_const___redArg(v_ps_643_);
v___x_646_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_646_, 0, v_p_644_);
lean_ctor_set(v___x_646_, 1, v___x_645_);
return v___x_646_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(size_t v_sz_699_, size_t v_i_700_, lean_object* v_bs_701_){
_start:
{
uint8_t v___x_702_; 
v___x_702_ = lean_usize_dec_lt(v_i_700_, v_sz_699_);
if (v___x_702_ == 0)
{
return v_bs_701_;
}
else
{
lean_object* v_v_703_; lean_object* v___x_704_; lean_object* v_bs_x27_705_; size_t v___x_706_; size_t v___x_707_; lean_object* v___x_708_; 
v_v_703_ = lean_array_uget(v_bs_701_, v_i_700_);
v___x_704_ = lean_unsigned_to_nat(0u);
v_bs_x27_705_ = lean_array_uset(v_bs_701_, v_i_700_, v___x_704_);
v___x_706_ = ((size_t)1ULL);
v___x_707_ = lean_usize_add(v_i_700_, v___x_706_);
v___x_708_ = lean_array_uset(v_bs_x27_705_, v_i_700_, v_v_703_);
v_i_700_ = v___x_707_;
v_bs_701_ = v___x_708_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0___boxed(lean_object* v_sz_710_, lean_object* v_i_711_, lean_object* v_bs_712_){
_start:
{
size_t v_sz_boxed_713_; size_t v_i_boxed_714_; lean_object* v_res_715_; 
v_sz_boxed_713_ = lean_unbox_usize(v_sz_710_);
lean_dec(v_sz_710_);
v_i_boxed_714_ = lean_unbox_usize(v_i_711_);
lean_dec(v_i_711_);
v_res_715_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_boxed_713_, v_i_boxed_714_, v_bs_712_);
return v_res_715_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_717_; lean_object* v___x_718_; 
v___x_717_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__0));
v___x_718_ = l_String_toRawSubstring_x27(v___x_717_);
return v___x_718_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16(void){
_start:
{
lean_object* v___x_752_; lean_object* v___x_753_; 
v___x_752_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__15));
v___x_753_ = l_String_toRawSubstring_x27(v___x_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1(lean_object* v_x_782_, lean_object* v_a_783_, lean_object* v_a_784_){
_start:
{
lean_object* v___x_785_; uint8_t v___x_786_; 
v___x_785_ = ((lean_object*)(l_Std_Do_term___u21d3___x3d_x3e___00__closed__1));
lean_inc(v_x_782_);
v___x_786_ = l_Lean_Syntax_isOfKind(v_x_782_, v___x_785_);
if (v___x_786_ == 0)
{
lean_object* v___x_787_; lean_object* v___x_788_; 
lean_dec_ref(v_a_783_);
lean_dec(v_x_782_);
v___x_787_ = lean_box(1);
v___x_788_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_788_, 0, v___x_787_);
lean_ctor_set(v___x_788_, 1, v_a_784_);
return v___x_788_;
}
else
{
lean_object* v_quotContext_789_; lean_object* v_currMacroScope_790_; lean_object* v_ref_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v_xs_796_; uint8_t v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; lean_object* v___x_803_; lean_object* v___x_804_; lean_object* v___x_805_; lean_object* v___x_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; size_t v_sz_831_; size_t v___x_832_; lean_object* v___x_833_; lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v___x_848_; lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v_quotContext_789_ = lean_ctor_get(v_a_783_, 1);
lean_inc(v_quotContext_789_);
v_currMacroScope_790_ = lean_ctor_get(v_a_783_, 2);
lean_inc(v_currMacroScope_790_);
v_ref_791_ = lean_ctor_get(v_a_783_, 5);
lean_inc(v_ref_791_);
lean_dec_ref(v_a_783_);
v___x_792_ = lean_unsigned_to_nat(2u);
v___x_793_ = l_Lean_Syntax_getArg(v_x_782_, v___x_792_);
v___x_794_ = lean_unsigned_to_nat(4u);
v___x_795_ = l_Lean_Syntax_getArg(v_x_782_, v___x_794_);
lean_dec(v_x_782_);
v_xs_796_ = l_Lean_Syntax_getArgs(v___x_793_);
lean_dec(v___x_793_);
v___x_797_ = 0;
v___x_798_ = l_Lean_SourceInfo_fromRef(v_ref_791_, v___x_797_);
lean_dec(v_ref_791_);
v___x_799_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_800_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__1);
v___x_801_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__4));
lean_inc(v_currMacroScope_790_);
lean_inc(v_quotContext_789_);
v___x_802_ = l_Lean_addMacroScope(v_quotContext_789_, v___x_801_, v_currMacroScope_790_);
v___x_803_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__7));
lean_inc(v___x_798_);
v___x_804_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_804_, 0, v___x_798_);
lean_ctor_set(v___x_804_, 1, v___x_800_);
lean_ctor_set(v___x_804_, 2, v___x_802_);
lean_ctor_set(v___x_804_, 3, v___x_803_);
v___x_805_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_806_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9));
v___x_807_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11));
v___x_808_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12));
lean_inc(v___x_798_);
v___x_809_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_798_);
lean_ctor_set(v___x_809_, 1, v___x_808_);
v___x_810_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14));
v___x_811_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16);
v___x_812_ = lean_box(0);
v___x_813_ = l_Lean_addMacroScope(v_quotContext_789_, v___x_812_, v_currMacroScope_790_);
v___x_814_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19));
lean_inc(v___x_798_);
v___x_815_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_815_, 0, v___x_798_);
lean_ctor_set(v___x_815_, 1, v___x_811_);
lean_ctor_set(v___x_815_, 2, v___x_813_);
lean_ctor_set(v___x_815_, 3, v___x_814_);
lean_inc(v___x_798_);
v___x_816_ = l_Lean_Syntax_node1(v___x_798_, v___x_810_, v___x_815_);
lean_inc(v___x_798_);
v___x_817_ = l_Lean_Syntax_node2(v___x_798_, v___x_807_, v___x_809_, v___x_816_);
v___x_818_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1));
v___x_819_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2));
lean_inc(v___x_798_);
v___x_820_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_820_, 0, v___x_798_);
lean_ctor_set(v___x_820_, 1, v___x_819_);
v___x_821_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5));
v___x_822_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7));
v___x_823_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8));
v___x_824_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9));
lean_inc(v___x_798_);
v___x_825_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_798_);
lean_ctor_set(v___x_825_, 1, v___x_823_);
v___x_826_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20));
v___x_827_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21));
lean_inc(v___x_798_);
v___x_828_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_828_, 0, v___x_798_);
lean_ctor_set(v___x_828_, 1, v___x_826_);
v___x_829_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23));
v___x_830_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
v_sz_831_ = lean_array_size(v_xs_796_);
v___x_832_ = ((size_t)0ULL);
v___x_833_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_831_, v___x_832_, v_xs_796_);
v___x_834_ = l_Array_append___redArg(v___x_830_, v___x_833_);
lean_dec_ref(v___x_833_);
lean_inc(v___x_798_);
v___x_835_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_835_, 0, v___x_798_);
lean_ctor_set(v___x_835_, 1, v___x_805_);
lean_ctor_set(v___x_835_, 2, v___x_834_);
lean_inc(v___x_798_);
v___x_836_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_836_, 0, v___x_798_);
lean_ctor_set(v___x_836_, 1, v___x_805_);
lean_ctor_set(v___x_836_, 2, v___x_830_);
v___x_837_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24));
lean_inc(v___x_798_);
v___x_838_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_838_, 0, v___x_798_);
lean_ctor_set(v___x_838_, 1, v___x_837_);
v___x_839_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26));
v___x_840_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27));
lean_inc(v___x_798_);
v___x_841_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_841_, 0, v___x_798_);
lean_ctor_set(v___x_841_, 1, v___x_840_);
v___x_842_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28));
lean_inc(v___x_798_);
v___x_843_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_843_, 0, v___x_798_);
lean_ctor_set(v___x_843_, 1, v___x_842_);
lean_inc_ref(v___x_843_);
lean_inc(v___x_798_);
v___x_844_ = l_Lean_Syntax_node3(v___x_798_, v___x_839_, v___x_841_, v___x_795_, v___x_843_);
lean_inc(v___x_798_);
v___x_845_ = l_Lean_Syntax_node4(v___x_798_, v___x_829_, v___x_835_, v___x_836_, v___x_838_, v___x_844_);
lean_inc(v___x_798_);
v___x_846_ = l_Lean_Syntax_node2(v___x_798_, v___x_827_, v___x_828_, v___x_845_);
lean_inc(v___x_798_);
v___x_847_ = l_Lean_Syntax_node2(v___x_798_, v___x_824_, v___x_825_, v___x_846_);
lean_inc(v___x_798_);
v___x_848_ = l_Lean_Syntax_node1(v___x_798_, v___x_805_, v___x_847_);
lean_inc(v___x_798_);
v___x_849_ = l_Lean_Syntax_node1(v___x_798_, v___x_822_, v___x_848_);
lean_inc(v___x_798_);
v___x_850_ = l_Lean_Syntax_node1(v___x_798_, v___x_821_, v___x_849_);
lean_inc(v___x_798_);
v___x_851_ = l_Lean_Syntax_node2(v___x_798_, v___x_818_, v___x_820_, v___x_850_);
lean_inc(v___x_798_);
v___x_852_ = l_Lean_Syntax_node3(v___x_798_, v___x_806_, v___x_817_, v___x_851_, v___x_843_);
lean_inc(v___x_798_);
v___x_853_ = l_Lean_Syntax_node1(v___x_798_, v___x_805_, v___x_852_);
v___x_854_ = l_Lean_Syntax_node2(v___x_798_, v___x_799_, v___x_804_, v___x_853_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v_a_784_);
return v___x_855_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_mayThrow___redArg(lean_object* v_ps_856_, lean_object* v_p_857_){
_start:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = l_Std_Do_ExceptConds_const___redArg(v_ps_856_);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v_p_857_);
lean_ctor_set(v___x_859_, 1, v___x_858_);
return v___x_859_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_mayThrow(lean_object* v_00_u03b1_860_, lean_object* v_ps_861_, lean_object* v_p_862_){
_start:
{
lean_object* v___x_863_; lean_object* v___x_864_; 
v___x_863_ = l_Std_Do_ExceptConds_const___redArg(v_ps_861_);
v___x_864_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_864_, 0, v_p_862_);
lean_ctor_set(v___x_864_, 1, v___x_863_);
return v___x_864_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_895_; lean_object* v___x_896_; 
v___x_895_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__0));
v___x_896_ = l_String_toRawSubstring_x27(v___x_895_);
return v___x_896_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1(lean_object* v_x_912_, lean_object* v_a_913_, lean_object* v_a_914_){
_start:
{
lean_object* v___x_915_; uint8_t v___x_916_; 
v___x_915_ = ((lean_object*)(l_Std_Do_term___u21d3_x3f___x3d_x3e___00__closed__1));
lean_inc(v_x_912_);
v___x_916_ = l_Lean_Syntax_isOfKind(v_x_912_, v___x_915_);
if (v___x_916_ == 0)
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec_ref(v_a_913_);
lean_dec(v_x_912_);
v___x_917_ = lean_box(1);
v___x_918_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_918_, 0, v___x_917_);
lean_ctor_set(v___x_918_, 1, v_a_914_);
return v___x_918_;
}
else
{
lean_object* v_quotContext_919_; lean_object* v_currMacroScope_920_; lean_object* v_ref_921_; lean_object* v___x_922_; lean_object* v___x_923_; lean_object* v___x_924_; lean_object* v___x_925_; lean_object* v_xs_926_; uint8_t v___x_927_; lean_object* v___x_928_; lean_object* v___x_929_; lean_object* v___x_930_; lean_object* v___x_931_; lean_object* v___x_932_; lean_object* v___x_933_; lean_object* v___x_934_; lean_object* v___x_935_; lean_object* v___x_936_; lean_object* v___x_937_; lean_object* v___x_938_; lean_object* v___x_939_; lean_object* v___x_940_; lean_object* v___x_941_; lean_object* v___x_942_; lean_object* v___x_943_; lean_object* v___x_944_; lean_object* v___x_945_; lean_object* v___x_946_; lean_object* v___x_947_; lean_object* v___x_948_; lean_object* v___x_949_; lean_object* v___x_950_; lean_object* v___x_951_; lean_object* v___x_952_; lean_object* v___x_953_; lean_object* v___x_954_; lean_object* v___x_955_; lean_object* v___x_956_; lean_object* v___x_957_; lean_object* v___x_958_; lean_object* v___x_959_; lean_object* v___x_960_; size_t v_sz_961_; size_t v___x_962_; lean_object* v___x_963_; lean_object* v___x_964_; lean_object* v___x_965_; lean_object* v___x_966_; lean_object* v___x_967_; lean_object* v___x_968_; lean_object* v___x_969_; lean_object* v___x_970_; lean_object* v___x_971_; lean_object* v___x_972_; lean_object* v___x_973_; lean_object* v___x_974_; lean_object* v___x_975_; lean_object* v___x_976_; lean_object* v___x_977_; lean_object* v___x_978_; lean_object* v___x_979_; lean_object* v___x_980_; lean_object* v___x_981_; lean_object* v___x_982_; lean_object* v___x_983_; lean_object* v___x_984_; lean_object* v___x_985_; 
v_quotContext_919_ = lean_ctor_get(v_a_913_, 1);
lean_inc(v_quotContext_919_);
v_currMacroScope_920_ = lean_ctor_get(v_a_913_, 2);
lean_inc(v_currMacroScope_920_);
v_ref_921_ = lean_ctor_get(v_a_913_, 5);
lean_inc(v_ref_921_);
lean_dec_ref(v_a_913_);
v___x_922_ = lean_unsigned_to_nat(2u);
v___x_923_ = l_Lean_Syntax_getArg(v_x_912_, v___x_922_);
v___x_924_ = lean_unsigned_to_nat(4u);
v___x_925_ = l_Lean_Syntax_getArg(v_x_912_, v___x_924_);
lean_dec(v_x_912_);
v_xs_926_ = l_Lean_Syntax_getArgs(v___x_923_);
lean_dec(v___x_923_);
v___x_927_ = 0;
v___x_928_ = l_Lean_SourceInfo_fromRef(v_ref_921_, v___x_927_);
lean_dec(v_ref_921_);
v___x_929_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_930_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__1);
v___x_931_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__3));
lean_inc(v_currMacroScope_920_);
lean_inc(v_quotContext_919_);
v___x_932_ = l_Lean_addMacroScope(v_quotContext_919_, v___x_931_, v_currMacroScope_920_);
v___x_933_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3_x3f___x3d_x3e____1___closed__6));
lean_inc(v___x_928_);
v___x_934_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_934_, 0, v___x_928_);
lean_ctor_set(v___x_934_, 1, v___x_930_);
lean_ctor_set(v___x_934_, 2, v___x_932_);
lean_ctor_set(v___x_934_, 3, v___x_933_);
v___x_935_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
v___x_936_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__9));
v___x_937_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__11));
v___x_938_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__12));
lean_inc(v___x_928_);
v___x_939_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_939_, 0, v___x_928_);
lean_ctor_set(v___x_939_, 1, v___x_938_);
v___x_940_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__14));
v___x_941_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__16);
v___x_942_ = lean_box(0);
v___x_943_ = l_Lean_addMacroScope(v_quotContext_919_, v___x_942_, v_currMacroScope_920_);
v___x_944_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__19));
lean_inc(v___x_928_);
v___x_945_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_945_, 0, v___x_928_);
lean_ctor_set(v___x_945_, 1, v___x_941_);
lean_ctor_set(v___x_945_, 2, v___x_943_);
lean_ctor_set(v___x_945_, 3, v___x_944_);
lean_inc(v___x_928_);
v___x_946_ = l_Lean_Syntax_node1(v___x_928_, v___x_940_, v___x_945_);
lean_inc(v___x_928_);
v___x_947_ = l_Lean_Syntax_node2(v___x_928_, v___x_937_, v___x_939_, v___x_946_);
v___x_948_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__1));
v___x_949_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__2));
lean_inc(v___x_928_);
v___x_950_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_950_, 0, v___x_928_);
lean_ctor_set(v___x_950_, 1, v___x_949_);
v___x_951_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__5));
v___x_952_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__7));
v___x_953_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__8));
v___x_954_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__9));
lean_inc(v___x_928_);
v___x_955_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_955_, 0, v___x_928_);
lean_ctor_set(v___x_955_, 1, v___x_953_);
v___x_956_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__20));
v___x_957_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__21));
lean_inc(v___x_928_);
v___x_958_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_958_, 0, v___x_928_);
lean_ctor_set(v___x_958_, 1, v___x_956_);
v___x_959_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__23));
v___x_960_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__termPost_u27e8___x2c_x2c_u27e9__1___closed__13);
v_sz_961_ = lean_array_size(v_xs_926_);
v___x_962_ = ((size_t)0ULL);
v___x_963_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1_spec__0(v_sz_961_, v___x_962_, v_xs_926_);
v___x_964_ = l_Array_append___redArg(v___x_960_, v___x_963_);
lean_dec_ref(v___x_963_);
lean_inc(v___x_928_);
v___x_965_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_965_, 0, v___x_928_);
lean_ctor_set(v___x_965_, 1, v___x_935_);
lean_ctor_set(v___x_965_, 2, v___x_964_);
lean_inc(v___x_928_);
v___x_966_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_966_, 0, v___x_928_);
lean_ctor_set(v___x_966_, 1, v___x_935_);
lean_ctor_set(v___x_966_, 2, v___x_960_);
v___x_967_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__24));
lean_inc(v___x_928_);
v___x_968_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_968_, 0, v___x_928_);
lean_ctor_set(v___x_968_, 1, v___x_967_);
v___x_969_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__26));
v___x_970_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__27));
lean_inc(v___x_928_);
v___x_971_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_971_, 0, v___x_928_);
lean_ctor_set(v___x_971_, 1, v___x_970_);
v___x_972_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u21d3___x3d_x3e____1___closed__28));
lean_inc(v___x_928_);
v___x_973_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_973_, 0, v___x_928_);
lean_ctor_set(v___x_973_, 1, v___x_972_);
lean_inc_ref(v___x_973_);
lean_inc(v___x_928_);
v___x_974_ = l_Lean_Syntax_node3(v___x_928_, v___x_969_, v___x_971_, v___x_925_, v___x_973_);
lean_inc(v___x_928_);
v___x_975_ = l_Lean_Syntax_node4(v___x_928_, v___x_959_, v___x_965_, v___x_966_, v___x_968_, v___x_974_);
lean_inc(v___x_928_);
v___x_976_ = l_Lean_Syntax_node2(v___x_928_, v___x_957_, v___x_958_, v___x_975_);
lean_inc(v___x_928_);
v___x_977_ = l_Lean_Syntax_node2(v___x_928_, v___x_954_, v___x_955_, v___x_976_);
lean_inc(v___x_928_);
v___x_978_ = l_Lean_Syntax_node1(v___x_928_, v___x_935_, v___x_977_);
lean_inc(v___x_928_);
v___x_979_ = l_Lean_Syntax_node1(v___x_928_, v___x_952_, v___x_978_);
lean_inc(v___x_928_);
v___x_980_ = l_Lean_Syntax_node1(v___x_928_, v___x_951_, v___x_979_);
lean_inc(v___x_928_);
v___x_981_ = l_Lean_Syntax_node2(v___x_928_, v___x_948_, v___x_950_, v___x_980_);
lean_inc(v___x_928_);
v___x_982_ = l_Lean_Syntax_node3(v___x_928_, v___x_936_, v___x_947_, v___x_981_, v___x_973_);
lean_inc(v___x_928_);
v___x_983_ = l_Lean_Syntax_node1(v___x_928_, v___x_935_, v___x_982_);
v___x_984_ = l_Lean_Syntax_node2(v___x_928_, v___x_929_, v___x_934_, v___x_983_);
v___x_985_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_985_, 0, v___x_984_);
lean_ctor_set(v___x_985_, 1, v_a_914_);
return v___x_985_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__0(lean_object* v_x_986_){
_start:
{
lean_object* v___x_987_; 
v___x_987_ = lean_box(0);
return v___x_987_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__0___boxed(lean_object* v_x_988_){
_start:
{
lean_object* v_res_989_; 
v_res_989_ = l_Std_Do_instInhabitedPostCond___redArg___lam__0(v_x_988_);
lean_dec(v_x_988_);
return v_res_989_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__1(lean_object* v_ps_990_, lean_object* v___f_991_, lean_object* v_x_992_){
_start:
{
lean_object* v___x_993_; lean_object* v___x_994_; 
v___x_993_ = l_Std_Do_PostShape_args(v_ps_990_);
v___x_994_ = l_Std_Do_SVal_curry___redArg(v___x_993_, lean_box(0));
return v___x_994_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg___lam__1___boxed(lean_object* v_ps_995_, lean_object* v___f_996_, lean_object* v_x_997_){
_start:
{
lean_object* v_res_998_; 
v_res_998_ = l_Std_Do_instInhabitedPostCond___redArg___lam__1(v_ps_995_, v___f_996_, v_x_997_);
lean_dec(v_x_997_);
lean_dec(v_ps_995_);
return v_res_998_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond___redArg(lean_object* v_ps_999_){
_start:
{
lean_object* v___f_1000_; lean_object* v___x_1001_; lean_object* v___x_1002_; 
lean_inc(v_ps_999_);
v___f_1000_ = lean_alloc_closure((void*)(l_Std_Do_instInhabitedPostCond___redArg___lam__1___boxed), 3, 2);
lean_closure_set(v___f_1000_, 0, v_ps_999_);
lean_closure_set(v___f_1000_, 1, lean_box(0));
v___x_1001_ = l_Std_Do_ExceptConds_const___redArg(v_ps_999_);
v___x_1002_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1002_, 0, v___f_1000_);
lean_ctor_set(v___x_1002_, 1, v___x_1001_);
return v___x_1002_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_instInhabitedPostCond(lean_object* v_ps_1003_, lean_object* v_00_u03b1_1004_){
_start:
{
lean_object* v___x_1005_; 
v___x_1005_ = l_Std_Do_instInhabitedPostCond___redArg(v_ps_1003_);
return v___x_1005_;
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1(void){
_start:
{
lean_object* v___x_1025_; lean_object* v___x_1026_; 
v___x_1025_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__0));
v___x_1026_ = l_String_toRawSubstring_x27(v___x_1025_);
return v___x_1026_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1(lean_object* v_x_1041_, lean_object* v_a_1042_, lean_object* v_a_1043_){
_start:
{
lean_object* v___x_1044_; uint8_t v___x_1045_; 
v___x_1044_ = ((lean_object*)(l_Std_Do_term___u22a2_u209a___00__closed__1));
lean_inc(v_x_1041_);
v___x_1045_ = l_Lean_Syntax_isOfKind(v_x_1041_, v___x_1044_);
if (v___x_1045_ == 0)
{
lean_object* v___x_1046_; lean_object* v___x_1047_; 
lean_dec_ref(v_a_1042_);
lean_dec(v_x_1041_);
v___x_1046_ = lean_box(1);
v___x_1047_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1047_, 0, v___x_1046_);
lean_ctor_set(v___x_1047_, 1, v_a_1043_);
return v___x_1047_;
}
else
{
lean_object* v_quotContext_1048_; lean_object* v_currMacroScope_1049_; lean_object* v_ref_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; lean_object* v___x_1053_; lean_object* v___x_1054_; uint8_t v___x_1055_; lean_object* v___x_1056_; lean_object* v___x_1057_; lean_object* v___x_1058_; lean_object* v___x_1059_; lean_object* v___x_1060_; lean_object* v___x_1061_; lean_object* v___x_1062_; lean_object* v___x_1063_; lean_object* v___x_1064_; lean_object* v___x_1065_; lean_object* v___x_1066_; 
v_quotContext_1048_ = lean_ctor_get(v_a_1042_, 1);
lean_inc(v_quotContext_1048_);
v_currMacroScope_1049_ = lean_ctor_get(v_a_1042_, 2);
lean_inc(v_currMacroScope_1049_);
v_ref_1050_ = lean_ctor_get(v_a_1042_, 5);
lean_inc(v_ref_1050_);
lean_dec_ref(v_a_1042_);
v___x_1051_ = lean_unsigned_to_nat(0u);
v___x_1052_ = l_Lean_Syntax_getArg(v_x_1041_, v___x_1051_);
v___x_1053_ = lean_unsigned_to_nat(2u);
v___x_1054_ = l_Lean_Syntax_getArg(v_x_1041_, v___x_1053_);
lean_dec(v_x_1041_);
v___x_1055_ = 0;
v___x_1056_ = l_Lean_SourceInfo_fromRef(v_ref_1050_, v___x_1055_);
lean_dec(v_ref_1050_);
v___x_1057_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_1058_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__1);
v___x_1059_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__2));
v___x_1060_ = l_Lean_addMacroScope(v_quotContext_1048_, v___x_1059_, v_currMacroScope_1049_);
v___x_1061_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u209a____1___closed__5));
lean_inc(v___x_1056_);
v___x_1062_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1062_, 0, v___x_1056_);
lean_ctor_set(v___x_1062_, 1, v___x_1058_);
lean_ctor_set(v___x_1062_, 2, v___x_1060_);
lean_ctor_set(v___x_1062_, 3, v___x_1061_);
v___x_1063_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
lean_inc(v___x_1056_);
v___x_1064_ = l_Lean_Syntax_node2(v___x_1056_, v___x_1063_, v___x_1052_, v___x_1054_);
v___x_1065_ = l_Lean_Syntax_node2(v___x_1056_, v___x_1057_, v___x_1062_, v___x_1064_);
v___x_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1066_, 0, v___x_1065_);
lean_ctor_set(v___x_1066_, 1, v_a_1043_);
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1(lean_object* v_x_1067_, lean_object* v_a_1068_, lean_object* v_a_1069_){
_start:
{
lean_object* v___x_1070_; uint8_t v___x_1071_; 
v___x_1070_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_1067_);
v___x_1071_ = l_Lean_Syntax_isOfKind(v_x_1067_, v___x_1070_);
if (v___x_1071_ == 0)
{
lean_object* v___x_1072_; lean_object* v___x_1073_; 
lean_dec(v_x_1067_);
v___x_1072_ = lean_box(0);
v___x_1073_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1073_, 0, v___x_1072_);
lean_ctor_set(v___x_1073_, 1, v_a_1069_);
return v___x_1073_;
}
else
{
lean_object* v___x_1074_; lean_object* v___x_1075_; lean_object* v___x_1076_; uint8_t v___x_1077_; 
v___x_1074_ = lean_unsigned_to_nat(0u);
v___x_1075_ = l_Lean_Syntax_getArg(v_x_1067_, v___x_1074_);
v___x_1076_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_1075_);
v___x_1077_ = l_Lean_Syntax_isOfKind(v___x_1075_, v___x_1076_);
if (v___x_1077_ == 0)
{
lean_object* v___x_1078_; lean_object* v___x_1079_; 
lean_dec(v___x_1075_);
lean_dec(v_x_1067_);
v___x_1078_ = lean_box(0);
v___x_1079_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1079_, 0, v___x_1078_);
lean_ctor_set(v___x_1079_, 1, v_a_1069_);
return v___x_1079_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; lean_object* v___x_1082_; uint8_t v___x_1083_; 
v___x_1080_ = lean_unsigned_to_nat(1u);
v___x_1081_ = l_Lean_Syntax_getArg(v_x_1067_, v___x_1080_);
lean_dec(v_x_1067_);
v___x_1082_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1081_);
v___x_1083_ = l_Lean_Syntax_matchesNull(v___x_1081_, v___x_1082_);
if (v___x_1083_ == 0)
{
lean_object* v___x_1084_; lean_object* v___x_1085_; 
lean_dec(v___x_1081_);
lean_dec(v___x_1075_);
v___x_1084_ = lean_box(0);
v___x_1085_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v_a_1069_);
return v___x_1085_;
}
else
{
lean_object* v___x_1086_; lean_object* v___x_1087_; lean_object* v_ref_1088_; uint8_t v___x_1089_; lean_object* v___x_1090_; lean_object* v___x_1091_; lean_object* v___x_1092_; lean_object* v___x_1093_; lean_object* v___x_1094_; lean_object* v___x_1095_; 
v___x_1086_ = l_Lean_Syntax_getArg(v___x_1081_, v___x_1074_);
v___x_1087_ = l_Lean_Syntax_getArg(v___x_1081_, v___x_1080_);
lean_dec(v___x_1081_);
v_ref_1088_ = l_Lean_replaceRef(v___x_1075_, v_a_1068_);
lean_dec(v___x_1075_);
v___x_1089_ = 0;
v___x_1090_ = l_Lean_SourceInfo_fromRef(v_ref_1088_, v___x_1089_);
lean_dec(v_ref_1088_);
v___x_1091_ = ((lean_object*)(l_Std_Do_term___u22a2_u209a___00__closed__1));
v___x_1092_ = ((lean_object*)(l_Std_Do_term___u22a2_u209a___00__closed__2));
lean_inc(v___x_1090_);
v___x_1093_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1093_, 0, v___x_1090_);
lean_ctor_set(v___x_1093_, 1, v___x_1092_);
v___x_1094_ = l_Lean_Syntax_node3(v___x_1090_, v___x_1091_, v___x_1086_, v___x_1093_, v___x_1087_);
v___x_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1095_, 0, v___x_1094_);
lean_ctor_set(v___x_1095_, 1, v_a_1069_);
return v___x_1095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1___boxed(lean_object* v_x_1096_, lean_object* v_a_1097_, lean_object* v_a_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__entails__1(v_x_1096_, v_a_1097_, v_a_1098_);
lean_dec(v_a_1097_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg___lam__0(lean_object* v_ps_1100_, lean_object* v_fst_1101_, lean_object* v_fst_1102_, lean_object* v_a_1103_){
_start:
{
lean_object* v___x_1104_; lean_object* v___x_1105_; lean_object* v___x_1106_; lean_object* v___x_1107_; 
v___x_1104_ = l_Std_Do_PostShape_args(v_ps_1100_);
lean_inc(v_a_1103_);
v___x_1105_ = lean_apply_1(v_fst_1101_, v_a_1103_);
v___x_1106_ = lean_apply_1(v_fst_1102_, v_a_1103_);
v___x_1107_ = l_Std_Do_SPred_and(v___x_1104_, v___x_1105_, v___x_1106_);
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg___lam__0___boxed(lean_object* v_ps_1108_, lean_object* v_fst_1109_, lean_object* v_fst_1110_, lean_object* v_a_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l_Std_Do_PostCond_and___redArg___lam__0(v_ps_1108_, v_fst_1109_, v_fst_1110_, v_a_1111_);
lean_dec(v_ps_1108_);
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and___redArg(lean_object* v_ps_1113_, lean_object* v_p_1114_, lean_object* v_q_1115_){
_start:
{
lean_object* v_fst_1116_; lean_object* v_snd_1117_; lean_object* v_fst_1118_; lean_object* v_snd_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1128_; 
v_fst_1116_ = lean_ctor_get(v_p_1114_, 0);
lean_inc(v_fst_1116_);
v_snd_1117_ = lean_ctor_get(v_p_1114_, 1);
lean_inc(v_snd_1117_);
lean_dec_ref(v_p_1114_);
v_fst_1118_ = lean_ctor_get(v_q_1115_, 0);
v_snd_1119_ = lean_ctor_get(v_q_1115_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_q_1115_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1121_ = v_q_1115_;
v_isShared_1122_ = v_isSharedCheck_1128_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_snd_1119_);
lean_inc(v_fst_1118_);
lean_dec(v_q_1115_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1128_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___f_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
lean_inc(v_ps_1113_);
v___f_1123_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_and___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1123_, 0, v_ps_1113_);
lean_closure_set(v___f_1123_, 1, v_fst_1116_);
lean_closure_set(v___f_1123_, 2, v_fst_1118_);
v___x_1124_ = l_Std_Do_ExceptConds_and(v_ps_1113_, v_snd_1117_, v_snd_1119_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v___x_1124_);
lean_ctor_set(v___x_1121_, 0, v___f_1123_);
v___x_1126_ = v___x_1121_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___f_1123_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v___x_1124_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_and(lean_object* v_00_u03b1_1129_, lean_object* v_ps_1130_, lean_object* v_p_1131_, lean_object* v_q_1132_){
_start:
{
lean_object* v_fst_1133_; lean_object* v_snd_1134_; lean_object* v_fst_1135_; lean_object* v_snd_1136_; lean_object* v___x_1138_; uint8_t v_isShared_1139_; uint8_t v_isSharedCheck_1145_; 
v_fst_1133_ = lean_ctor_get(v_p_1131_, 0);
lean_inc(v_fst_1133_);
v_snd_1134_ = lean_ctor_get(v_p_1131_, 1);
lean_inc(v_snd_1134_);
lean_dec_ref(v_p_1131_);
v_fst_1135_ = lean_ctor_get(v_q_1132_, 0);
v_snd_1136_ = lean_ctor_get(v_q_1132_, 1);
v_isSharedCheck_1145_ = !lean_is_exclusive(v_q_1132_);
if (v_isSharedCheck_1145_ == 0)
{
v___x_1138_ = v_q_1132_;
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
else
{
lean_inc(v_snd_1136_);
lean_inc(v_fst_1135_);
lean_dec(v_q_1132_);
v___x_1138_ = lean_box(0);
v_isShared_1139_ = v_isSharedCheck_1145_;
goto v_resetjp_1137_;
}
v_resetjp_1137_:
{
lean_object* v___f_1140_; lean_object* v___x_1141_; lean_object* v___x_1143_; 
lean_inc(v_ps_1130_);
v___f_1140_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_and___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1140_, 0, v_ps_1130_);
lean_closure_set(v___f_1140_, 1, v_fst_1133_);
lean_closure_set(v___f_1140_, 2, v_fst_1135_);
v___x_1141_ = l_Std_Do_ExceptConds_and(v_ps_1130_, v_snd_1134_, v_snd_1136_);
if (v_isShared_1139_ == 0)
{
lean_ctor_set(v___x_1138_, 1, v___x_1141_);
lean_ctor_set(v___x_1138_, 0, v___f_1140_);
v___x_1143_ = v___x_1138_;
goto v_reusejp_1142_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v___f_1140_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v___x_1141_);
v___x_1143_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1142_;
}
v_reusejp_1142_:
{
return v___x_1143_;
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1(void){
_start:
{
lean_object* v___x_1165_; lean_object* v___x_1166_; 
v___x_1165_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__0));
v___x_1166_ = l_String_toRawSubstring_x27(v___x_1165_);
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1(lean_object* v_x_1181_, lean_object* v_a_1182_, lean_object* v_a_1183_){
_start:
{
lean_object* v___x_1184_; uint8_t v___x_1185_; 
v___x_1184_ = ((lean_object*)(l_Std_Do_term___u2227_u209a___00__closed__1));
lean_inc(v_x_1181_);
v___x_1185_ = l_Lean_Syntax_isOfKind(v_x_1181_, v___x_1184_);
if (v___x_1185_ == 0)
{
lean_object* v___x_1186_; lean_object* v___x_1187_; 
lean_dec_ref(v_a_1182_);
lean_dec(v_x_1181_);
v___x_1186_ = lean_box(1);
v___x_1187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1187_, 0, v___x_1186_);
lean_ctor_set(v___x_1187_, 1, v_a_1183_);
return v___x_1187_;
}
else
{
lean_object* v_quotContext_1188_; lean_object* v_currMacroScope_1189_; lean_object* v_ref_1190_; lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; lean_object* v___x_1194_; uint8_t v___x_1195_; lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; lean_object* v___x_1199_; lean_object* v___x_1200_; lean_object* v___x_1201_; lean_object* v___x_1202_; lean_object* v___x_1203_; lean_object* v___x_1204_; lean_object* v___x_1205_; lean_object* v___x_1206_; 
v_quotContext_1188_ = lean_ctor_get(v_a_1182_, 1);
lean_inc(v_quotContext_1188_);
v_currMacroScope_1189_ = lean_ctor_get(v_a_1182_, 2);
lean_inc(v_currMacroScope_1189_);
v_ref_1190_ = lean_ctor_get(v_a_1182_, 5);
lean_inc(v_ref_1190_);
lean_dec_ref(v_a_1182_);
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = l_Lean_Syntax_getArg(v_x_1181_, v___x_1191_);
v___x_1193_ = lean_unsigned_to_nat(2u);
v___x_1194_ = l_Lean_Syntax_getArg(v_x_1181_, v___x_1193_);
lean_dec(v_x_1181_);
v___x_1195_ = 0;
v___x_1196_ = l_Lean_SourceInfo_fromRef(v_ref_1190_, v___x_1195_);
lean_dec(v_ref_1190_);
v___x_1197_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_1198_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__1);
v___x_1199_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__2));
v___x_1200_ = l_Lean_addMacroScope(v_quotContext_1188_, v___x_1199_, v_currMacroScope_1189_);
v___x_1201_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2227_u209a____1___closed__5));
lean_inc(v___x_1196_);
v___x_1202_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1202_, 0, v___x_1196_);
lean_ctor_set(v___x_1202_, 1, v___x_1198_);
lean_ctor_set(v___x_1202_, 2, v___x_1200_);
lean_ctor_set(v___x_1202_, 3, v___x_1201_);
v___x_1203_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
lean_inc(v___x_1196_);
v___x_1204_ = l_Lean_Syntax_node2(v___x_1196_, v___x_1203_, v___x_1192_, v___x_1194_);
v___x_1205_ = l_Lean_Syntax_node2(v___x_1196_, v___x_1197_, v___x_1202_, v___x_1204_);
v___x_1206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1206_, 0, v___x_1205_);
lean_ctor_set(v___x_1206_, 1, v_a_1183_);
return v___x_1206_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1(lean_object* v_x_1207_, lean_object* v_a_1208_, lean_object* v_a_1209_){
_start:
{
lean_object* v___x_1210_; uint8_t v___x_1211_; 
v___x_1210_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
lean_inc(v_x_1207_);
v___x_1211_ = l_Lean_Syntax_isOfKind(v_x_1207_, v___x_1210_);
if (v___x_1211_ == 0)
{
lean_object* v___x_1212_; lean_object* v___x_1213_; 
lean_dec(v_x_1207_);
v___x_1212_ = lean_box(0);
v___x_1213_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1213_, 0, v___x_1212_);
lean_ctor_set(v___x_1213_, 1, v_a_1209_);
return v___x_1213_;
}
else
{
lean_object* v___x_1214_; lean_object* v___x_1215_; lean_object* v___x_1216_; uint8_t v___x_1217_; 
v___x_1214_ = lean_unsigned_to_nat(0u);
v___x_1215_ = l_Lean_Syntax_getArg(v_x_1207_, v___x_1214_);
v___x_1216_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__ExceptConds__entails__1___closed__1));
lean_inc(v___x_1215_);
v___x_1217_ = l_Lean_Syntax_isOfKind(v___x_1215_, v___x_1216_);
if (v___x_1217_ == 0)
{
lean_object* v___x_1218_; lean_object* v___x_1219_; 
lean_dec(v___x_1215_);
lean_dec(v_x_1207_);
v___x_1218_ = lean_box(0);
v___x_1219_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1218_);
lean_ctor_set(v___x_1219_, 1, v_a_1209_);
return v___x_1219_;
}
else
{
lean_object* v___x_1220_; lean_object* v___x_1221_; lean_object* v___x_1222_; uint8_t v___x_1223_; 
v___x_1220_ = lean_unsigned_to_nat(1u);
v___x_1221_ = l_Lean_Syntax_getArg(v_x_1207_, v___x_1220_);
lean_dec(v_x_1207_);
v___x_1222_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_1221_);
v___x_1223_ = l_Lean_Syntax_matchesNull(v___x_1221_, v___x_1222_);
if (v___x_1223_ == 0)
{
lean_object* v___x_1224_; lean_object* v___x_1225_; 
lean_dec(v___x_1221_);
lean_dec(v___x_1215_);
v___x_1224_ = lean_box(0);
v___x_1225_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1225_, 0, v___x_1224_);
lean_ctor_set(v___x_1225_, 1, v_a_1209_);
return v___x_1225_;
}
else
{
lean_object* v___x_1226_; lean_object* v___x_1227_; lean_object* v_ref_1228_; uint8_t v___x_1229_; lean_object* v___x_1230_; lean_object* v___x_1231_; lean_object* v___x_1232_; lean_object* v___x_1233_; lean_object* v___x_1234_; lean_object* v___x_1235_; 
v___x_1226_ = l_Lean_Syntax_getArg(v___x_1221_, v___x_1214_);
v___x_1227_ = l_Lean_Syntax_getArg(v___x_1221_, v___x_1220_);
lean_dec(v___x_1221_);
v_ref_1228_ = l_Lean_replaceRef(v___x_1215_, v_a_1208_);
lean_dec(v___x_1215_);
v___x_1229_ = 0;
v___x_1230_ = l_Lean_SourceInfo_fromRef(v_ref_1228_, v___x_1229_);
lean_dec(v_ref_1228_);
v___x_1231_ = ((lean_object*)(l_Std_Do_term___u2227_u209a___00__closed__1));
v___x_1232_ = ((lean_object*)(l_Std_Do_term___u2227_u209a___00__closed__2));
lean_inc(v___x_1230_);
v___x_1233_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_1233_, 0, v___x_1230_);
lean_ctor_set(v___x_1233_, 1, v___x_1232_);
v___x_1234_ = l_Lean_Syntax_node3(v___x_1230_, v___x_1231_, v___x_1226_, v___x_1233_, v___x_1227_);
v___x_1235_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1235_, 0, v___x_1234_);
lean_ctor_set(v___x_1235_, 1, v_a_1209_);
return v___x_1235_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1___boxed(lean_object* v_x_1236_, lean_object* v_a_1237_, lean_object* v_a_1238_){
_start:
{
lean_object* v_res_1239_; 
v_res_1239_ = l_Std_Do___aux__Std__Do__PostCond______unexpand__Std__Do__PostCond__and__1(v_x_1236_, v_a_1237_, v_a_1238_);
lean_dec(v_a_1237_);
return v_res_1239_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg___lam__0(lean_object* v_ps_1240_, lean_object* v_fst_1241_, lean_object* v_fst_1242_, lean_object* v_a_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
v___x_1244_ = l_Std_Do_PostShape_args(v_ps_1240_);
lean_inc(v_a_1243_);
v___x_1245_ = lean_apply_1(v_fst_1241_, v_a_1243_);
v___x_1246_ = lean_apply_1(v_fst_1242_, v_a_1243_);
v___x_1247_ = l_Std_Do_SPred_imp(v___x_1244_, v___x_1245_, v___x_1246_);
return v___x_1247_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg___lam__0___boxed(lean_object* v_ps_1248_, lean_object* v_fst_1249_, lean_object* v_fst_1250_, lean_object* v_a_1251_){
_start:
{
lean_object* v_res_1252_; 
v_res_1252_ = l_Std_Do_PostCond_imp___redArg___lam__0(v_ps_1248_, v_fst_1249_, v_fst_1250_, v_a_1251_);
lean_dec(v_ps_1248_);
return v_res_1252_;
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp___redArg(lean_object* v_ps_1253_, lean_object* v_p_1254_, lean_object* v_q_1255_){
_start:
{
lean_object* v_fst_1256_; lean_object* v_snd_1257_; lean_object* v_fst_1258_; lean_object* v_snd_1259_; lean_object* v___x_1261_; uint8_t v_isShared_1262_; uint8_t v_isSharedCheck_1268_; 
v_fst_1256_ = lean_ctor_get(v_p_1254_, 0);
lean_inc(v_fst_1256_);
v_snd_1257_ = lean_ctor_get(v_p_1254_, 1);
lean_inc(v_snd_1257_);
lean_dec_ref(v_p_1254_);
v_fst_1258_ = lean_ctor_get(v_q_1255_, 0);
v_snd_1259_ = lean_ctor_get(v_q_1255_, 1);
v_isSharedCheck_1268_ = !lean_is_exclusive(v_q_1255_);
if (v_isSharedCheck_1268_ == 0)
{
v___x_1261_ = v_q_1255_;
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
else
{
lean_inc(v_snd_1259_);
lean_inc(v_fst_1258_);
lean_dec(v_q_1255_);
v___x_1261_ = lean_box(0);
v_isShared_1262_ = v_isSharedCheck_1268_;
goto v_resetjp_1260_;
}
v_resetjp_1260_:
{
lean_object* v___f_1263_; lean_object* v___x_1264_; lean_object* v___x_1266_; 
lean_inc(v_ps_1253_);
v___f_1263_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_imp___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1263_, 0, v_ps_1253_);
lean_closure_set(v___f_1263_, 1, v_fst_1256_);
lean_closure_set(v___f_1263_, 2, v_fst_1258_);
v___x_1264_ = l_Std_Do_ExceptConds_imp(v_ps_1253_, v_snd_1257_, v_snd_1259_);
if (v_isShared_1262_ == 0)
{
lean_ctor_set(v___x_1261_, 1, v___x_1264_);
lean_ctor_set(v___x_1261_, 0, v___f_1263_);
v___x_1266_ = v___x_1261_;
goto v_reusejp_1265_;
}
else
{
lean_object* v_reuseFailAlloc_1267_; 
v_reuseFailAlloc_1267_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1267_, 0, v___f_1263_);
lean_ctor_set(v_reuseFailAlloc_1267_, 1, v___x_1264_);
v___x_1266_ = v_reuseFailAlloc_1267_;
goto v_reusejp_1265_;
}
v_reusejp_1265_:
{
return v___x_1266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Do_PostCond_imp(lean_object* v_00_u03b1_1269_, lean_object* v_ps_1270_, lean_object* v_p_1271_, lean_object* v_q_1272_){
_start:
{
lean_object* v_fst_1273_; lean_object* v_snd_1274_; lean_object* v_fst_1275_; lean_object* v_snd_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1285_; 
v_fst_1273_ = lean_ctor_get(v_p_1271_, 0);
lean_inc(v_fst_1273_);
v_snd_1274_ = lean_ctor_get(v_p_1271_, 1);
lean_inc(v_snd_1274_);
lean_dec_ref(v_p_1271_);
v_fst_1275_ = lean_ctor_get(v_q_1272_, 0);
v_snd_1276_ = lean_ctor_get(v_q_1272_, 1);
v_isSharedCheck_1285_ = !lean_is_exclusive(v_q_1272_);
if (v_isSharedCheck_1285_ == 0)
{
v___x_1278_ = v_q_1272_;
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_snd_1276_);
lean_inc(v_fst_1275_);
lean_dec(v_q_1272_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1285_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v___f_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
lean_inc(v_ps_1270_);
v___f_1280_ = lean_alloc_closure((void*)(l_Std_Do_PostCond_imp___redArg___lam__0___boxed), 4, 3);
lean_closure_set(v___f_1280_, 0, v_ps_1270_);
lean_closure_set(v___f_1280_, 1, v_fst_1273_);
lean_closure_set(v___f_1280_, 2, v_fst_1275_);
v___x_1281_ = l_Std_Do_ExceptConds_imp(v_ps_1270_, v_snd_1274_, v_snd_1276_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v___x_1281_);
lean_ctor_set(v___x_1278_, 0, v___f_1280_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1284_; 
v_reuseFailAlloc_1284_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1284_, 0, v___f_1280_);
lean_ctor_set(v_reuseFailAlloc_1284_, 1, v___x_1281_);
v___x_1283_ = v_reuseFailAlloc_1284_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
return v___x_1283_;
}
}
}
}
static lean_object* _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1(void){
_start:
{
lean_object* v___x_1305_; lean_object* v___x_1306_; 
v___x_1305_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__0));
v___x_1306_ = l_String_toRawSubstring_x27(v___x_1305_);
return v___x_1306_;
}
}
LEAN_EXPORT lean_object* l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1(lean_object* v_x_1321_, lean_object* v_a_1322_, lean_object* v_a_1323_){
_start:
{
lean_object* v___x_1324_; uint8_t v___x_1325_; 
v___x_1324_ = ((lean_object*)(l_Std_Do_term___u2192_u209a___00__closed__1));
lean_inc(v_x_1321_);
v___x_1325_ = l_Lean_Syntax_isOfKind(v_x_1321_, v___x_1324_);
if (v___x_1325_ == 0)
{
lean_object* v___x_1326_; lean_object* v___x_1327_; 
lean_dec_ref(v_a_1322_);
lean_dec(v_x_1321_);
v___x_1326_ = lean_box(1);
v___x_1327_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_1327_, 0, v___x_1326_);
lean_ctor_set(v___x_1327_, 1, v_a_1323_);
return v___x_1327_;
}
else
{
lean_object* v_quotContext_1328_; lean_object* v_currMacroScope_1329_; lean_object* v_ref_1330_; lean_object* v___x_1331_; lean_object* v___x_1332_; lean_object* v___x_1333_; lean_object* v___x_1334_; uint8_t v___x_1335_; lean_object* v___x_1336_; lean_object* v___x_1337_; lean_object* v___x_1338_; lean_object* v___x_1339_; lean_object* v___x_1340_; lean_object* v___x_1341_; lean_object* v___x_1342_; lean_object* v___x_1343_; lean_object* v___x_1344_; lean_object* v___x_1345_; lean_object* v___x_1346_; 
v_quotContext_1328_ = lean_ctor_get(v_a_1322_, 1);
lean_inc(v_quotContext_1328_);
v_currMacroScope_1329_ = lean_ctor_get(v_a_1322_, 2);
lean_inc(v_currMacroScope_1329_);
v_ref_1330_ = lean_ctor_get(v_a_1322_, 5);
lean_inc(v_ref_1330_);
lean_dec_ref(v_a_1322_);
v___x_1331_ = lean_unsigned_to_nat(0u);
v___x_1332_ = l_Lean_Syntax_getArg(v_x_1321_, v___x_1331_);
v___x_1333_ = lean_unsigned_to_nat(2u);
v___x_1334_ = l_Lean_Syntax_getArg(v_x_1321_, v___x_1333_);
lean_dec(v_x_1321_);
v___x_1335_ = 0;
v___x_1336_ = l_Lean_SourceInfo_fromRef(v_ref_1330_, v___x_1335_);
lean_dec(v_ref_1330_);
v___x_1337_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__4));
v___x_1338_ = lean_obj_once(&l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1, &l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1_once, _init_l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__1);
v___x_1339_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__2));
v___x_1340_ = l_Lean_addMacroScope(v_quotContext_1328_, v___x_1339_, v_currMacroScope_1329_);
v___x_1341_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u2192_u209a____1___closed__5));
lean_inc(v___x_1336_);
v___x_1342_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_1342_, 0, v___x_1336_);
lean_ctor_set(v___x_1342_, 1, v___x_1338_);
lean_ctor_set(v___x_1342_, 2, v___x_1340_);
lean_ctor_set(v___x_1342_, 3, v___x_1341_);
v___x_1343_ = ((lean_object*)(l_Std_Do___aux__Std__Do__PostCond______macroRules__Std__Do__term___u22a2_u2091____1___closed__16));
lean_inc(v___x_1336_);
v___x_1344_ = l_Lean_Syntax_node2(v___x_1336_, v___x_1343_, v___x_1332_, v___x_1334_);
v___x_1345_ = l_Lean_Syntax_node2(v___x_1336_, v___x_1337_, v___x_1342_, v___x_1344_);
v___x_1346_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1346_, 0, v___x_1345_);
lean_ctor_set(v___x_1346_, 1, v_a_1323_);
return v___x_1346_;
}
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Do_PostCond(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
