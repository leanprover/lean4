// Lean compiler output
// Module: Init.Control.Basic
// Imports: public import Init.Core public import Init.BinderNameHint
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
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_matchesNull(lean_object*, lean_object*);
lean_object* l_Lean_replaceRef(lean_object*, lean_object*);
lean_object* l_Lean_SourceInfo_fromRef(lean_object*, uint8_t);
lean_object* l_Lean_Syntax_node3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_addMacroScope(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_node2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInOfForIn_x27___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInOfForIn_x27___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instForInOfForIn_x27(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_value___redArg(lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_value___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_value(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_ForInStep_value___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_mapRev(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___x3c_x26_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_<&>_"};
static const lean_object* l_term___x3c_x26_x3e___00__closed__0 = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__0_value;
static const lean_ctor_object l_term___x3c_x26_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x3c_x26_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(229, 64, 46, 51, 179, 128, 115, 248)}};
static const lean_object* l_term___x3c_x26_x3e___00__closed__1 = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__1_value;
static const lean_string_object l_term___x3c_x26_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "andthen"};
static const lean_object* l_term___x3c_x26_x3e___00__closed__2 = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__2_value;
static const lean_ctor_object l_term___x3c_x26_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x3c_x26_x3e___00__closed__2_value),LEAN_SCALAR_PTR_LITERAL(40, 255, 78, 30, 143, 119, 117, 174)}};
static const lean_object* l_term___x3c_x26_x3e___00__closed__3 = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__3_value;
static const lean_string_object l_term___x3c_x26_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " <&> "};
static const lean_object* l_term___x3c_x26_x3e___00__closed__4 = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__4_value;
static const lean_ctor_object l_term___x3c_x26_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__4_value)}};
static const lean_object* l_term___x3c_x26_x3e___00__closed__5 = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__5_value;
static const lean_string_object l_term___x3c_x26_x3e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "term"};
static const lean_object* l_term___x3c_x26_x3e___00__closed__6 = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__6_value;
static const lean_ctor_object l_term___x3c_x26_x3e___00__closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x3c_x26_x3e___00__closed__6_value),LEAN_SCALAR_PTR_LITERAL(187, 230, 181, 162, 253, 146, 122, 119)}};
static const lean_object* l_term___x3c_x26_x3e___00__closed__7 = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__7_value;
static const lean_ctor_object l_term___x3c_x26_x3e___00__closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__7_value),((lean_object*)(((size_t)(100) << 1) | 1))}};
static const lean_object* l_term___x3c_x26_x3e___00__closed__8 = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__8_value;
static const lean_ctor_object l_term___x3c_x26_x3e___00__closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__3_value),((lean_object*)&l_term___x3c_x26_x3e___00__closed__5_value),((lean_object*)&l_term___x3c_x26_x3e___00__closed__8_value)}};
static const lean_object* l_term___x3c_x26_x3e___00__closed__9 = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__9_value;
static const lean_ctor_object l_term___x3c_x26_x3e___00__closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__1_value),((lean_object*)(((size_t)(100) << 1) | 1)),((lean_object*)(((size_t)(101) << 1) | 1)),((lean_object*)&l_term___x3c_x26_x3e___00__closed__9_value)}};
static const lean_object* l_term___x3c_x26_x3e___00__closed__10 = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__10_value;
LEAN_EXPORT const lean_object* l_term___x3c_x26_x3e__ = (const lean_object*)&l_term___x3c_x26_x3e___00__closed__10_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Parser"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Term"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "app"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__1_value),LEAN_SCALAR_PTR_LITERAL(103, 136, 125, 166, 167, 98, 71, 111)}};
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_1),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(75, 170, 162, 138, 136, 204, 251, 229)}};
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value_aux_2),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(69, 118, 10, 41, 220, 156, 243, 179)}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "Functor.mapRev"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5_value;
static lean_once_cell_t l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "Functor"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "mapRev"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__7_value),LEAN_SCALAR_PTR_LITERAL(39, 234, 35, 88, 204, 30, 230, 30)}};
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value_aux_0),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__8_value),LEAN_SCALAR_PTR_LITERAL(92, 240, 223, 153, 202, 59, 2, 247)}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__10_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "null"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__12_value),LEAN_SCALAR_PTR_LITERAL(24, 58, 49, 223, 146, 207, 197, 136)}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13_value;
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = "ident"};
static const lean_object* l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0 = (const lean_object*)&l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value;
static const lean_ctor_object l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(52, 159, 208, 51, 14, 60, 6, 71)}};
static const lean_object* l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1 = (const lean_object*)&l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1_value;
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Functor_discard(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instOrElseOfAlternative___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instOrElseOfAlternative(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_guard___redArg(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_guard___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_guard(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_guard___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_optional___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_optional___redArg___lam__1(lean_object*, lean_object*);
static const lean_closure_object l_optional___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_optional___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_optional___redArg___closed__0 = (const lean_object*)&l_optional___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_optional___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_optional(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_instToBoolBool___lam__0(uint8_t);
LEAN_EXPORT lean_object* l_instToBoolBool___lam__0___boxed(lean_object*);
static const lean_closure_object l_instToBoolBool___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instToBoolBool___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instToBoolBool___closed__0 = (const lean_object*)&l_instToBoolBool___closed__0_value;
LEAN_EXPORT const lean_object* l_instToBoolBool = (const lean_object*)&l_instToBoolBool___closed__0_value;
static const lean_string_object l_term___x3c_x7c_x7c_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_<||>_"};
static const lean_object* l_term___x3c_x7c_x7c_x3e___00__closed__0 = (const lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__0_value;
static const lean_ctor_object l_term___x3c_x7c_x7c_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 4, 151, 30, 219, 83, 67, 252)}};
static const lean_object* l_term___x3c_x7c_x7c_x3e___00__closed__1 = (const lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__1_value;
static const lean_string_object l_term___x3c_x7c_x7c_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " <||> "};
static const lean_object* l_term___x3c_x7c_x7c_x3e___00__closed__2 = (const lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__2_value;
static const lean_ctor_object l_term___x3c_x7c_x7c_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__2_value)}};
static const lean_object* l_term___x3c_x7c_x7c_x3e___00__closed__3 = (const lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__3_value;
static const lean_ctor_object l_term___x3c_x7c_x7c_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__7_value),((lean_object*)(((size_t)(30) << 1) | 1))}};
static const lean_object* l_term___x3c_x7c_x7c_x3e___00__closed__4 = (const lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__4_value;
static const lean_ctor_object l_term___x3c_x7c_x7c_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__3_value),((lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__3_value),((lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__4_value)}};
static const lean_object* l_term___x3c_x7c_x7c_x3e___00__closed__5 = (const lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__5_value;
static const lean_ctor_object l_term___x3c_x7c_x7c_x3e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__1_value),((lean_object*)(((size_t)(30) << 1) | 1)),((lean_object*)(((size_t)(31) << 1) | 1)),((lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__5_value)}};
static const lean_object* l_term___x3c_x7c_x7c_x3e___00__closed__6 = (const lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__6_value;
LEAN_EXPORT const lean_object* l_term___x3c_x7c_x7c_x3e__ = (const lean_object*)&l_term___x3c_x7c_x7c_x3e___00__closed__6_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "orM"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(162, 21, 89, 2, 36, 160, 27, 247)}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4_value;
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__orM__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__orM__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___x3c_x26_x26_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "term_<&&>_"};
static const lean_object* l_term___x3c_x26_x26_x3e___00__closed__0 = (const lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__0_value;
static const lean_ctor_object l_term___x3c_x26_x26_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(246, 63, 64, 32, 246, 94, 158, 54)}};
static const lean_object* l_term___x3c_x26_x26_x3e___00__closed__1 = (const lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__1_value;
static const lean_string_object l_term___x3c_x26_x26_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = " <&&> "};
static const lean_object* l_term___x3c_x26_x26_x3e___00__closed__2 = (const lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__2_value;
static const lean_ctor_object l_term___x3c_x26_x26_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__2_value)}};
static const lean_object* l_term___x3c_x26_x26_x3e___00__closed__3 = (const lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__3_value;
static const lean_ctor_object l_term___x3c_x26_x26_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__7_value),((lean_object*)(((size_t)(35) << 1) | 1))}};
static const lean_object* l_term___x3c_x26_x26_x3e___00__closed__4 = (const lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__4_value;
static const lean_ctor_object l_term___x3c_x26_x26_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__3_value),((lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__3_value),((lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__4_value)}};
static const lean_object* l_term___x3c_x26_x26_x3e___00__closed__5 = (const lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__5_value;
static const lean_ctor_object l_term___x3c_x26_x26_x3e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__1_value),((lean_object*)(((size_t)(35) << 1) | 1)),((lean_object*)(((size_t)(36) << 1) | 1)),((lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__5_value)}};
static const lean_object* l_term___x3c_x26_x26_x3e___00__closed__6 = (const lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__6_value;
LEAN_EXPORT const lean_object* l_term___x3c_x26_x26_x3e__ = (const lean_object*)&l_term___x3c_x26_x26_x3e___00__closed__6_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "andM"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(151, 195, 207, 154, 232, 230, 36, 123)}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4_value;
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__andM__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__andM__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__2(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_instMonadControlTOfPure___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlTOfPure___redArg___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_instMonadControlTOfPure___redArg___closed__0 = (const lean_object*)&l_instMonadControlTOfPure___redArg___closed__0_value;
static const lean_closure_object l_instMonadControlTOfPure___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_instMonadControlTOfPure___redArg___lam__1, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_instMonadControlTOfPure___redArg___closed__0_value)} };
static const lean_object* l_instMonadControlTOfPure___redArg___closed__1 = (const lean_object*)&l_instMonadControlTOfPure___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg(lean_object*);
LEAN_EXPORT lean_object* l_instMonadControlTOfPure(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_controlAt___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_controlAt(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_control___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_control(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bind_kleisliRight___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bind_kleisliRight(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bind_kleisliLeft___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bind_kleisliLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bind_bindLeft___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Bind_bindLeft(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___x3e_x3d_x3e___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_>=>_"};
static const lean_object* l_term___x3e_x3d_x3e___00__closed__0 = (const lean_object*)&l_term___x3e_x3d_x3e___00__closed__0_value;
static const lean_ctor_object l_term___x3e_x3d_x3e___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x3e_x3d_x3e___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(44, 3, 24, 186, 53, 243, 56, 5)}};
static const lean_object* l_term___x3e_x3d_x3e___00__closed__1 = (const lean_object*)&l_term___x3e_x3d_x3e___00__closed__1_value;
static const lean_string_object l_term___x3e_x3d_x3e___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " >=> "};
static const lean_object* l_term___x3e_x3d_x3e___00__closed__2 = (const lean_object*)&l_term___x3e_x3d_x3e___00__closed__2_value;
static const lean_ctor_object l_term___x3e_x3d_x3e___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___x3e_x3d_x3e___00__closed__2_value)}};
static const lean_object* l_term___x3e_x3d_x3e___00__closed__3 = (const lean_object*)&l_term___x3e_x3d_x3e___00__closed__3_value;
static const lean_ctor_object l_term___x3e_x3d_x3e___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 7}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__7_value),((lean_object*)(((size_t)(55) << 1) | 1))}};
static const lean_object* l_term___x3e_x3d_x3e___00__closed__4 = (const lean_object*)&l_term___x3e_x3d_x3e___00__closed__4_value;
static const lean_ctor_object l_term___x3e_x3d_x3e___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__3_value),((lean_object*)&l_term___x3e_x3d_x3e___00__closed__3_value),((lean_object*)&l_term___x3e_x3d_x3e___00__closed__4_value)}};
static const lean_object* l_term___x3e_x3d_x3e___00__closed__5 = (const lean_object*)&l_term___x3e_x3d_x3e___00__closed__5_value;
static const lean_ctor_object l_term___x3e_x3d_x3e___00__closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___x3e_x3d_x3e___00__closed__1_value),((lean_object*)(((size_t)(55) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1)),((lean_object*)&l_term___x3e_x3d_x3e___00__closed__5_value)}};
static const lean_object* l_term___x3e_x3d_x3e___00__closed__6 = (const lean_object*)&l_term___x3e_x3d_x3e___00__closed__6_value;
LEAN_EXPORT const lean_object* l_term___x3e_x3d_x3e__ = (const lean_object*)&l_term___x3e_x3d_x3e___00__closed__6_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "Bind.kleisliRight"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Bind"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "kleisliRight"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(222, 192, 22, 179, 212, 181, 141, 219)}};
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value_aux_0),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__3_value),LEAN_SCALAR_PTR_LITERAL(240, 87, 86, 191, 63, 130, 155, 187)}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__5_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6_value;
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___x3c_x3d_x3c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_<=<_"};
static const lean_object* l_term___x3c_x3d_x3c___00__closed__0 = (const lean_object*)&l_term___x3c_x3d_x3c___00__closed__0_value;
static const lean_ctor_object l_term___x3c_x3d_x3c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x3c_x3d_x3c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(116, 132, 184, 107, 38, 119, 74, 91)}};
static const lean_object* l_term___x3c_x3d_x3c___00__closed__1 = (const lean_object*)&l_term___x3c_x3d_x3c___00__closed__1_value;
static const lean_string_object l_term___x3c_x3d_x3c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " <=< "};
static const lean_object* l_term___x3c_x3d_x3c___00__closed__2 = (const lean_object*)&l_term___x3c_x3d_x3c___00__closed__2_value;
static const lean_ctor_object l_term___x3c_x3d_x3c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___x3c_x3d_x3c___00__closed__2_value)}};
static const lean_object* l_term___x3c_x3d_x3c___00__closed__3 = (const lean_object*)&l_term___x3c_x3d_x3c___00__closed__3_value;
static const lean_ctor_object l_term___x3c_x3d_x3c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__3_value),((lean_object*)&l_term___x3c_x3d_x3c___00__closed__3_value),((lean_object*)&l_term___x3e_x3d_x3e___00__closed__4_value)}};
static const lean_object* l_term___x3c_x3d_x3c___00__closed__4 = (const lean_object*)&l_term___x3c_x3d_x3c___00__closed__4_value;
static const lean_ctor_object l_term___x3c_x3d_x3c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___x3c_x3d_x3c___00__closed__1_value),((lean_object*)(((size_t)(55) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1)),((lean_object*)&l_term___x3c_x3d_x3c___00__closed__4_value)}};
static const lean_object* l_term___x3c_x3d_x3c___00__closed__5 = (const lean_object*)&l_term___x3c_x3d_x3c___00__closed__5_value;
LEAN_EXPORT const lean_object* l_term___x3c_x3d_x3c__ = (const lean_object*)&l_term___x3c_x3d_x3c___00__closed__5_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 17, .m_capacity = 17, .m_length = 16, .m_data = "Bind.kleisliLeft"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 12, .m_capacity = 12, .m_length = 11, .m_data = "kleisliLeft"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(222, 192, 22, 179, 212, 181, 141, 219)}};
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value_aux_0),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(124, 60, 93, 1, 97, 30, 47, 33)}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5_value;
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_term___x3d_x3c_x3c___00__closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "term_=<<_"};
static const lean_object* l_term___x3d_x3c_x3c___00__closed__0 = (const lean_object*)&l_term___x3d_x3c_x3c___00__closed__0_value;
static const lean_ctor_object l_term___x3d_x3c_x3c___00__closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_term___x3d_x3c_x3c___00__closed__0_value),LEAN_SCALAR_PTR_LITERAL(40, 145, 230, 65, 4, 58, 20, 86)}};
static const lean_object* l_term___x3d_x3c_x3c___00__closed__1 = (const lean_object*)&l_term___x3d_x3c_x3c___00__closed__1_value;
static const lean_string_object l_term___x3d_x3c_x3c___00__closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 6, .m_capacity = 6, .m_length = 5, .m_data = " =<< "};
static const lean_object* l_term___x3d_x3c_x3c___00__closed__2 = (const lean_object*)&l_term___x3d_x3c_x3c___00__closed__2_value;
static const lean_ctor_object l_term___x3d_x3c_x3c___00__closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 5}, .m_objs = {((lean_object*)&l_term___x3d_x3c_x3c___00__closed__2_value)}};
static const lean_object* l_term___x3d_x3c_x3c___00__closed__3 = (const lean_object*)&l_term___x3d_x3c_x3c___00__closed__3_value;
static const lean_ctor_object l_term___x3d_x3c_x3c___00__closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 2}, .m_objs = {((lean_object*)&l_term___x3c_x26_x3e___00__closed__3_value),((lean_object*)&l_term___x3d_x3c_x3c___00__closed__3_value),((lean_object*)&l_term___x3e_x3d_x3e___00__closed__4_value)}};
static const lean_object* l_term___x3d_x3c_x3c___00__closed__4 = (const lean_object*)&l_term___x3d_x3c_x3c___00__closed__4_value;
static const lean_ctor_object l_term___x3d_x3c_x3c___00__closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 0, .m_other = 4, .m_tag = 4}, .m_objs = {((lean_object*)&l_term___x3d_x3c_x3c___00__closed__1_value),((lean_object*)(((size_t)(55) << 1) | 1)),((lean_object*)(((size_t)(56) << 1) | 1)),((lean_object*)&l_term___x3d_x3c_x3c___00__closed__4_value)}};
static const lean_object* l_term___x3d_x3c_x3c___00__closed__5 = (const lean_object*)&l_term___x3d_x3c_x3c___00__closed__5_value;
LEAN_EXPORT const lean_object* l_term___x3d_x3c_x3c__ = (const lean_object*)&l_term___x3d_x3c_x3c___00__closed__5_value;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "Bind.bindLeft"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0_value;
static lean_once_cell_t l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1;
static const lean_string_object l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "bindLeft"};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(222, 192, 22, 179, 212, 181, 141, 219)}};
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value_aux_0),((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__2_value),LEAN_SCALAR_PTR_LITERAL(108, 94, 90, 101, 157, 107, 234, 141)}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value;
static const lean_ctor_object l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__4_value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5 = (const lean_object*)&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5_value;
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_instForInOfForIn_x27___redArg___lam__0(lean_object* v_f_1_, lean_object* v_a_2_, lean_object* v_x_3_, lean_object* v___y_4_){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = lean_apply_2(v_f_1_, v_a_2_, v___y_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_instForInOfForIn_x27___redArg___lam__1(lean_object* v_inst_6_, lean_object* v_00_u03b2_7_, lean_object* v_x_8_, lean_object* v_b_9_, lean_object* v_f_10_){
_start:
{
lean_object* v___f_11_; lean_object* v___x_12_; 
v___f_11_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__0), 4, 1);
lean_closure_set(v___f_11_, 0, v_f_10_);
v___x_12_ = lean_apply_4(v_inst_6_, lean_box(0), v_x_8_, v_b_9_, v___f_11_);
return v___x_12_;
}
}
LEAN_EXPORT lean_object* l_instForInOfForIn_x27___redArg(lean_object* v_inst_13_){
_start:
{
lean_object* v___f_14_; 
v___f_14_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_14_, 0, v_inst_13_);
return v___f_14_;
}
}
LEAN_EXPORT lean_object* l_instForInOfForIn_x27(lean_object* v_m_15_, lean_object* v_00_u03c1_16_, lean_object* v_00_u03b1_17_, lean_object* v_d_18_, lean_object* v_inst_19_){
_start:
{
lean_object* v___f_20_; 
v___f_20_ = lean_alloc_closure((void*)(l_instForInOfForIn_x27___redArg___lam__1), 5, 1);
lean_closure_set(v___f_20_, 0, v_inst_19_);
return v___f_20_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_value___redArg(lean_object* v_x_21_){
_start:
{
lean_object* v_a_22_; 
v_a_22_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_a_22_);
return v_a_22_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_value___redArg___boxed(lean_object* v_x_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_ForInStep_value___redArg(v_x_23_);
lean_dec_ref(v_x_23_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_value(lean_object* v_00_u03b1_25_, lean_object* v_x_26_){
_start:
{
lean_object* v_a_27_; 
v_a_27_ = lean_ctor_get(v_x_26_, 0);
lean_inc(v_a_27_);
return v_a_27_;
}
}
LEAN_EXPORT lean_object* l_ForInStep_value___boxed(lean_object* v_00_u03b1_28_, lean_object* v_x_29_){
_start:
{
lean_object* v_res_30_; 
v_res_30_ = l_ForInStep_value(v_00_u03b1_28_, v_x_29_);
lean_dec_ref(v_x_29_);
return v_res_30_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev___redArg(lean_object* v_inst_31_, lean_object* v_a_32_, lean_object* v_f_33_){
_start:
{
lean_object* v_map_34_; lean_object* v___x_35_; 
v_map_34_ = lean_ctor_get(v_inst_31_, 0);
lean_inc(v_map_34_);
lean_dec_ref(v_inst_31_);
v___x_35_ = lean_apply_4(v_map_34_, lean_box(0), lean_box(0), v_f_33_, v_a_32_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_Functor_mapRev(lean_object* v_f_36_, lean_object* v_inst_37_, lean_object* v_00_u03b1_38_, lean_object* v_00_u03b2_39_, lean_object* v_a_40_, lean_object* v_f_41_){
_start:
{
lean_object* v___x_42_; 
v___x_42_ = l_Functor_mapRev___redArg(v_inst_37_, v_a_40_, v_f_41_);
return v___x_42_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6(void){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; 
v___x_78_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__5));
v___x_79_ = l_String_toRawSubstring_x27(v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1(lean_object* v_x_94_, lean_object* v_a_95_, lean_object* v_a_96_){
_start:
{
lean_object* v___x_97_; uint8_t v___x_98_; 
v___x_97_ = ((lean_object*)(l_term___x3c_x26_x3e___00__closed__1));
lean_inc(v_x_94_);
v___x_98_ = l_Lean_Syntax_isOfKind(v_x_94_, v___x_97_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; 
lean_dec(v_x_94_);
v___x_99_ = lean_box(1);
v___x_100_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
lean_ctor_set(v___x_100_, 1, v_a_96_);
return v___x_100_;
}
else
{
lean_object* v_quotContext_101_; lean_object* v_currMacroScope_102_; lean_object* v_ref_103_; lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; uint8_t v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_quotContext_101_ = lean_ctor_get(v_a_95_, 1);
v_currMacroScope_102_ = lean_ctor_get(v_a_95_, 2);
v_ref_103_ = lean_ctor_get(v_a_95_, 5);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = l_Lean_Syntax_getArg(v_x_94_, v___x_104_);
v___x_106_ = lean_unsigned_to_nat(2u);
v___x_107_ = l_Lean_Syntax_getArg(v_x_94_, v___x_106_);
lean_dec(v_x_94_);
v___x_108_ = 0;
v___x_109_ = l_Lean_SourceInfo_fromRef(v_ref_103_, v___x_108_);
v___x_110_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_111_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6, &l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6);
v___x_112_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9));
lean_inc(v_currMacroScope_102_);
lean_inc(v_quotContext_101_);
v___x_113_ = l_Lean_addMacroScope(v_quotContext_101_, v___x_112_, v_currMacroScope_102_);
v___x_114_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11));
lean_inc_n(v___x_109_, 2);
v___x_115_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_115_, 0, v___x_109_);
lean_ctor_set(v___x_115_, 1, v___x_111_);
lean_ctor_set(v___x_115_, 2, v___x_113_);
lean_ctor_set(v___x_115_, 3, v___x_114_);
v___x_116_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
v___x_117_ = l_Lean_Syntax_node2(v___x_109_, v___x_116_, v___x_105_, v___x_107_);
v___x_118_ = l_Lean_Syntax_node2(v___x_109_, v___x_110_, v___x_115_, v___x_117_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_a_96_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___boxed(lean_object* v_x_120_, lean_object* v_a_121_, lean_object* v_a_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1(v_x_120_, v_a_121_, v_a_122_);
lean_dec_ref(v_a_121_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1(lean_object* v_x_127_, lean_object* v_a_128_, lean_object* v_a_129_){
_start:
{
lean_object* v___x_130_; uint8_t v___x_131_; 
v___x_130_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_127_);
v___x_131_ = l_Lean_Syntax_isOfKind(v_x_127_, v___x_130_);
if (v___x_131_ == 0)
{
lean_object* v___x_132_; lean_object* v___x_133_; 
lean_dec(v_x_127_);
v___x_132_ = lean_box(0);
v___x_133_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_133_, 0, v___x_132_);
lean_ctor_set(v___x_133_, 1, v_a_129_);
return v___x_133_;
}
else
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_134_ = lean_unsigned_to_nat(0u);
v___x_135_ = l_Lean_Syntax_getArg(v_x_127_, v___x_134_);
v___x_136_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_135_);
v___x_137_ = l_Lean_Syntax_isOfKind(v___x_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; lean_object* v___x_139_; 
lean_dec(v___x_135_);
lean_dec(v_x_127_);
v___x_138_ = lean_box(0);
v___x_139_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_139_, 0, v___x_138_);
lean_ctor_set(v___x_139_, 1, v_a_129_);
return v___x_139_;
}
else
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; uint8_t v___x_143_; 
v___x_140_ = lean_unsigned_to_nat(1u);
v___x_141_ = l_Lean_Syntax_getArg(v_x_127_, v___x_140_);
lean_dec(v_x_127_);
v___x_142_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_141_);
v___x_143_ = l_Lean_Syntax_matchesNull(v___x_141_, v___x_142_);
if (v___x_143_ == 0)
{
lean_object* v___x_144_; lean_object* v___x_145_; 
lean_dec(v___x_141_);
lean_dec(v___x_135_);
v___x_144_ = lean_box(0);
v___x_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_145_, 0, v___x_144_);
lean_ctor_set(v___x_145_, 1, v_a_129_);
return v___x_145_;
}
else
{
lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v_ref_148_; uint8_t v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_146_ = l_Lean_Syntax_getArg(v___x_141_, v___x_134_);
v___x_147_ = l_Lean_Syntax_getArg(v___x_141_, v___x_140_);
lean_dec(v___x_141_);
v_ref_148_ = l_Lean_replaceRef(v___x_135_, v_a_128_);
lean_dec(v___x_135_);
v___x_149_ = 0;
v___x_150_ = l_Lean_SourceInfo_fromRef(v_ref_148_, v___x_149_);
lean_dec(v_ref_148_);
v___x_151_ = ((lean_object*)(l_term___x3c_x26_x3e___00__closed__1));
v___x_152_ = ((lean_object*)(l_term___x3c_x26_x3e___00__closed__4));
lean_inc(v___x_150_);
v___x_153_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_153_, 0, v___x_150_);
lean_ctor_set(v___x_153_, 1, v___x_152_);
v___x_154_ = l_Lean_Syntax_node3(v___x_150_, v___x_151_, v___x_146_, v___x_153_, v___x_147_);
v___x_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_155_, 0, v___x_154_);
lean_ctor_set(v___x_155_, 1, v_a_129_);
return v___x_155_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___boxed(lean_object* v_x_156_, lean_object* v_a_157_, lean_object* v_a_158_){
_start:
{
lean_object* v_res_159_; 
v_res_159_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1(v_x_156_, v_a_157_, v_a_158_);
lean_dec(v_a_157_);
return v_res_159_;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___redArg(lean_object* v_inst_160_, lean_object* v_x_161_){
_start:
{
lean_object* v_mapConst_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v_mapConst_162_ = lean_ctor_get(v_inst_160_, 1);
lean_inc(v_mapConst_162_);
lean_dec_ref(v_inst_160_);
v___x_163_ = lean_box(0);
v___x_164_ = lean_apply_4(v_mapConst_162_, lean_box(0), lean_box(0), v___x_163_, v_x_161_);
return v___x_164_;
}
}
LEAN_EXPORT lean_object* l_Functor_discard(lean_object* v_f_165_, lean_object* v_00_u03b1_166_, lean_object* v_inst_167_, lean_object* v_x_168_){
_start:
{
lean_object* v_mapConst_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v_mapConst_169_ = lean_ctor_get(v_inst_167_, 1);
lean_inc(v_mapConst_169_);
lean_dec_ref(v_inst_167_);
v___x_170_ = lean_box(0);
v___x_171_ = lean_apply_4(v_mapConst_169_, lean_box(0), lean_box(0), v___x_170_, v_x_168_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_instOrElseOfAlternative___redArg(lean_object* v_inst_172_){
_start:
{
lean_object* v_orElse_173_; lean_object* v___x_174_; 
v_orElse_173_ = lean_ctor_get(v_inst_172_, 2);
lean_inc(v_orElse_173_);
lean_dec_ref(v_inst_172_);
v___x_174_ = lean_apply_1(v_orElse_173_, lean_box(0));
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_instOrElseOfAlternative(lean_object* v_f_175_, lean_object* v_00_u03b1_176_, lean_object* v_inst_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_instOrElseOfAlternative___redArg(v_inst_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_guard___redArg(lean_object* v_inst_179_, uint8_t v_inst_180_){
_start:
{
if (v_inst_180_ == 0)
{
lean_object* v_failure_181_; lean_object* v___x_182_; 
v_failure_181_ = lean_ctor_get(v_inst_179_, 1);
lean_inc(v_failure_181_);
lean_dec_ref(v_inst_179_);
v___x_182_ = lean_apply_1(v_failure_181_, lean_box(0));
return v___x_182_;
}
else
{
lean_object* v_toApplicative_183_; lean_object* v_toPure_184_; lean_object* v___x_185_; lean_object* v___x_186_; 
v_toApplicative_183_ = lean_ctor_get(v_inst_179_, 0);
lean_inc_ref(v_toApplicative_183_);
lean_dec_ref(v_inst_179_);
v_toPure_184_ = lean_ctor_get(v_toApplicative_183_, 1);
lean_inc(v_toPure_184_);
lean_dec_ref(v_toApplicative_183_);
v___x_185_ = lean_box(0);
v___x_186_ = lean_apply_2(v_toPure_184_, lean_box(0), v___x_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l_guard___redArg___boxed(lean_object* v_inst_187_, lean_object* v_inst_188_){
_start:
{
uint8_t v_inst_22__boxed_189_; lean_object* v_res_190_; 
v_inst_22__boxed_189_ = lean_unbox(v_inst_188_);
v_res_190_ = l_guard___redArg(v_inst_187_, v_inst_22__boxed_189_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_guard(lean_object* v_f_191_, lean_object* v_inst_192_, lean_object* v_p_193_, uint8_t v_inst_194_){
_start:
{
if (v_inst_194_ == 0)
{
lean_object* v_failure_195_; lean_object* v___x_196_; 
v_failure_195_ = lean_ctor_get(v_inst_192_, 1);
lean_inc(v_failure_195_);
lean_dec_ref(v_inst_192_);
v___x_196_ = lean_apply_1(v_failure_195_, lean_box(0));
return v___x_196_;
}
else
{
lean_object* v_toApplicative_197_; lean_object* v_toPure_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v_toApplicative_197_ = lean_ctor_get(v_inst_192_, 0);
lean_inc_ref(v_toApplicative_197_);
lean_dec_ref(v_inst_192_);
v_toPure_198_ = lean_ctor_get(v_toApplicative_197_, 1);
lean_inc(v_toPure_198_);
lean_dec_ref(v_toApplicative_197_);
v___x_199_ = lean_box(0);
v___x_200_ = lean_apply_2(v_toPure_198_, lean_box(0), v___x_199_);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_guard___boxed(lean_object* v_f_201_, lean_object* v_inst_202_, lean_object* v_p_203_, lean_object* v_inst_204_){
_start:
{
uint8_t v_inst_34__boxed_205_; lean_object* v_res_206_; 
v_inst_34__boxed_205_ = lean_unbox(v_inst_204_);
v_res_206_ = l_guard(v_f_201_, v_inst_202_, v_p_203_, v_inst_34__boxed_205_);
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l_optional___redArg___lam__0(lean_object* v_val_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v_val_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_optional___redArg___lam__1(lean_object* v_toPure_209_, lean_object* v_x_210_){
_start:
{
lean_object* v___x_211_; lean_object* v___x_212_; 
v___x_211_ = lean_box(0);
v___x_212_ = lean_apply_2(v_toPure_209_, lean_box(0), v___x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_optional___redArg(lean_object* v_inst_214_, lean_object* v_x_215_){
_start:
{
lean_object* v_toApplicative_216_; lean_object* v_toFunctor_217_; lean_object* v_orElse_218_; lean_object* v_toPure_219_; lean_object* v_map_220_; lean_object* v___f_221_; lean_object* v___f_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_toApplicative_216_ = lean_ctor_get(v_inst_214_, 0);
lean_inc_ref(v_toApplicative_216_);
v_toFunctor_217_ = lean_ctor_get(v_toApplicative_216_, 0);
lean_inc_ref(v_toFunctor_217_);
v_orElse_218_ = lean_ctor_get(v_inst_214_, 2);
lean_inc(v_orElse_218_);
lean_dec_ref(v_inst_214_);
v_toPure_219_ = lean_ctor_get(v_toApplicative_216_, 1);
lean_inc(v_toPure_219_);
lean_dec_ref(v_toApplicative_216_);
v_map_220_ = lean_ctor_get(v_toFunctor_217_, 0);
lean_inc(v_map_220_);
lean_dec_ref(v_toFunctor_217_);
v___f_221_ = ((lean_object*)(l_optional___redArg___closed__0));
v___f_222_ = lean_alloc_closure((void*)(l_optional___redArg___lam__1), 2, 1);
lean_closure_set(v___f_222_, 0, v_toPure_219_);
v___x_223_ = lean_apply_4(v_map_220_, lean_box(0), lean_box(0), v___f_221_, v_x_215_);
v___x_224_ = lean_apply_3(v_orElse_218_, lean_box(0), v___x_223_, v___f_222_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_optional(lean_object* v_f_225_, lean_object* v_inst_226_, lean_object* v_00_u03b1_227_, lean_object* v_x_228_){
_start:
{
lean_object* v_toApplicative_229_; lean_object* v_toFunctor_230_; lean_object* v_orElse_231_; lean_object* v_toPure_232_; lean_object* v_map_233_; lean_object* v___f_234_; lean_object* v___f_235_; lean_object* v___x_236_; lean_object* v___x_237_; 
v_toApplicative_229_ = lean_ctor_get(v_inst_226_, 0);
lean_inc_ref(v_toApplicative_229_);
v_toFunctor_230_ = lean_ctor_get(v_toApplicative_229_, 0);
lean_inc_ref(v_toFunctor_230_);
v_orElse_231_ = lean_ctor_get(v_inst_226_, 2);
lean_inc(v_orElse_231_);
lean_dec_ref(v_inst_226_);
v_toPure_232_ = lean_ctor_get(v_toApplicative_229_, 1);
lean_inc(v_toPure_232_);
lean_dec_ref(v_toApplicative_229_);
v_map_233_ = lean_ctor_get(v_toFunctor_230_, 0);
lean_inc(v_map_233_);
lean_dec_ref(v_toFunctor_230_);
v___f_234_ = ((lean_object*)(l_optional___redArg___closed__0));
v___f_235_ = lean_alloc_closure((void*)(l_optional___redArg___lam__1), 2, 1);
lean_closure_set(v___f_235_, 0, v_toPure_232_);
v___x_236_ = lean_apply_4(v_map_233_, lean_box(0), lean_box(0), v___f_234_, v_x_228_);
v___x_237_ = lean_apply_3(v_orElse_231_, lean_box(0), v___x_236_, v___f_235_);
return v___x_237_;
}
}
LEAN_EXPORT uint8_t l_instToBoolBool___lam__0(uint8_t v_b_238_){
_start:
{
return v_b_238_;
}
}
LEAN_EXPORT lean_object* l_instToBoolBool___lam__0___boxed(lean_object* v_b_239_){
_start:
{
uint8_t v_b_boxed_240_; uint8_t v_res_241_; lean_object* v_r_242_; 
v_b_boxed_240_ = lean_unbox(v_b_239_);
v_res_241_ = l_instToBoolBool___lam__0(v_b_boxed_240_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_265_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0));
v___x_266_ = l_String_toRawSubstring_x27(v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(lean_object* v_x_275_, lean_object* v_a_276_, lean_object* v_a_277_){
_start:
{
lean_object* v___x_278_; uint8_t v___x_279_; 
v___x_278_ = ((lean_object*)(l_term___x3c_x7c_x7c_x3e___00__closed__1));
lean_inc(v_x_275_);
v___x_279_ = l_Lean_Syntax_isOfKind(v_x_275_, v___x_278_);
if (v___x_279_ == 0)
{
lean_object* v___x_280_; lean_object* v___x_281_; 
lean_dec(v_x_275_);
v___x_280_ = lean_box(1);
v___x_281_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_280_);
lean_ctor_set(v___x_281_, 1, v_a_277_);
return v___x_281_;
}
else
{
lean_object* v_quotContext_282_; lean_object* v_currMacroScope_283_; lean_object* v_ref_284_; lean_object* v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; uint8_t v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; 
v_quotContext_282_ = lean_ctor_get(v_a_276_, 1);
v_currMacroScope_283_ = lean_ctor_get(v_a_276_, 2);
v_ref_284_ = lean_ctor_get(v_a_276_, 5);
v___x_285_ = lean_unsigned_to_nat(0u);
v___x_286_ = l_Lean_Syntax_getArg(v_x_275_, v___x_285_);
v___x_287_ = lean_unsigned_to_nat(2u);
v___x_288_ = l_Lean_Syntax_getArg(v_x_275_, v___x_287_);
lean_dec(v_x_275_);
v___x_289_ = 0;
v___x_290_ = l_Lean_SourceInfo_fromRef(v_ref_284_, v___x_289_);
v___x_291_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_292_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1);
v___x_293_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2));
lean_inc(v_currMacroScope_283_);
lean_inc(v_quotContext_282_);
v___x_294_ = l_Lean_addMacroScope(v_quotContext_282_, v___x_293_, v_currMacroScope_283_);
v___x_295_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4));
lean_inc_n(v___x_290_, 2);
v___x_296_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_296_, 0, v___x_290_);
lean_ctor_set(v___x_296_, 1, v___x_292_);
lean_ctor_set(v___x_296_, 2, v___x_294_);
lean_ctor_set(v___x_296_, 3, v___x_295_);
v___x_297_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
v___x_298_ = l_Lean_Syntax_node2(v___x_290_, v___x_297_, v___x_286_, v___x_288_);
v___x_299_ = l_Lean_Syntax_node2(v___x_290_, v___x_291_, v___x_296_, v___x_298_);
v___x_300_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_300_, 0, v___x_299_);
lean_ctor_set(v___x_300_, 1, v_a_277_);
return v___x_300_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___boxed(lean_object* v_x_301_, lean_object* v_a_302_, lean_object* v_a_303_){
_start:
{
lean_object* v_res_304_; 
v_res_304_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(v_x_301_, v_a_302_, v_a_303_);
lean_dec_ref(v_a_302_);
return v_res_304_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__orM__1(lean_object* v_x_305_, lean_object* v_a_306_, lean_object* v_a_307_){
_start:
{
lean_object* v___x_308_; uint8_t v___x_309_; 
v___x_308_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_305_);
v___x_309_ = l_Lean_Syntax_isOfKind(v_x_305_, v___x_308_);
if (v___x_309_ == 0)
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_x_305_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_310_);
lean_ctor_set(v___x_311_, 1, v_a_307_);
return v___x_311_;
}
else
{
lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; uint8_t v___x_315_; 
v___x_312_ = lean_unsigned_to_nat(0u);
v___x_313_ = l_Lean_Syntax_getArg(v_x_305_, v___x_312_);
v___x_314_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_313_);
v___x_315_ = l_Lean_Syntax_isOfKind(v___x_313_, v___x_314_);
if (v___x_315_ == 0)
{
lean_object* v___x_316_; lean_object* v___x_317_; 
lean_dec(v___x_313_);
lean_dec(v_x_305_);
v___x_316_ = lean_box(0);
v___x_317_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_316_);
lean_ctor_set(v___x_317_, 1, v_a_307_);
return v___x_317_;
}
else
{
lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; uint8_t v___x_321_; 
v___x_318_ = lean_unsigned_to_nat(1u);
v___x_319_ = l_Lean_Syntax_getArg(v_x_305_, v___x_318_);
lean_dec(v_x_305_);
v___x_320_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_319_);
v___x_321_ = l_Lean_Syntax_matchesNull(v___x_319_, v___x_320_);
if (v___x_321_ == 0)
{
lean_object* v___x_322_; lean_object* v___x_323_; 
lean_dec(v___x_319_);
lean_dec(v___x_313_);
v___x_322_ = lean_box(0);
v___x_323_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
lean_ctor_set(v___x_323_, 1, v_a_307_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v_ref_326_; uint8_t v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___x_324_ = l_Lean_Syntax_getArg(v___x_319_, v___x_312_);
v___x_325_ = l_Lean_Syntax_getArg(v___x_319_, v___x_318_);
lean_dec(v___x_319_);
v_ref_326_ = l_Lean_replaceRef(v___x_313_, v_a_306_);
lean_dec(v___x_313_);
v___x_327_ = 0;
v___x_328_ = l_Lean_SourceInfo_fromRef(v_ref_326_, v___x_327_);
lean_dec(v_ref_326_);
v___x_329_ = ((lean_object*)(l_term___x3c_x7c_x7c_x3e___00__closed__1));
v___x_330_ = ((lean_object*)(l_term___x3c_x7c_x7c_x3e___00__closed__2));
lean_inc(v___x_328_);
v___x_331_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_328_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = l_Lean_Syntax_node3(v___x_328_, v___x_329_, v___x_324_, v___x_331_, v___x_325_);
v___x_333_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set(v___x_333_, 1, v_a_307_);
return v___x_333_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__orM__1___boxed(lean_object* v_x_334_, lean_object* v_a_335_, lean_object* v_a_336_){
_start:
{
lean_object* v_res_337_; 
v_res_337_ = l___aux__Init__Control__Basic______unexpand__orM__1(v_x_334_, v_a_335_, v_a_336_);
lean_dec(v_a_335_);
return v_res_337_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_358_; lean_object* v___x_359_; 
v___x_358_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0));
v___x_359_ = l_String_toRawSubstring_x27(v___x_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(lean_object* v_x_368_, lean_object* v_a_369_, lean_object* v_a_370_){
_start:
{
lean_object* v___x_371_; uint8_t v___x_372_; 
v___x_371_ = ((lean_object*)(l_term___x3c_x26_x26_x3e___00__closed__1));
lean_inc(v_x_368_);
v___x_372_ = l_Lean_Syntax_isOfKind(v_x_368_, v___x_371_);
if (v___x_372_ == 0)
{
lean_object* v___x_373_; lean_object* v___x_374_; 
lean_dec(v_x_368_);
v___x_373_ = lean_box(1);
v___x_374_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_374_, 0, v___x_373_);
lean_ctor_set(v___x_374_, 1, v_a_370_);
return v___x_374_;
}
else
{
lean_object* v_quotContext_375_; lean_object* v_currMacroScope_376_; lean_object* v_ref_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; uint8_t v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; 
v_quotContext_375_ = lean_ctor_get(v_a_369_, 1);
v_currMacroScope_376_ = lean_ctor_get(v_a_369_, 2);
v_ref_377_ = lean_ctor_get(v_a_369_, 5);
v___x_378_ = lean_unsigned_to_nat(0u);
v___x_379_ = l_Lean_Syntax_getArg(v_x_368_, v___x_378_);
v___x_380_ = lean_unsigned_to_nat(2u);
v___x_381_ = l_Lean_Syntax_getArg(v_x_368_, v___x_380_);
lean_dec(v_x_368_);
v___x_382_ = 0;
v___x_383_ = l_Lean_SourceInfo_fromRef(v_ref_377_, v___x_382_);
v___x_384_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_385_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1);
v___x_386_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2));
lean_inc(v_currMacroScope_376_);
lean_inc(v_quotContext_375_);
v___x_387_ = l_Lean_addMacroScope(v_quotContext_375_, v___x_386_, v_currMacroScope_376_);
v___x_388_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4));
lean_inc_n(v___x_383_, 2);
v___x_389_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_389_, 0, v___x_383_);
lean_ctor_set(v___x_389_, 1, v___x_385_);
lean_ctor_set(v___x_389_, 2, v___x_387_);
lean_ctor_set(v___x_389_, 3, v___x_388_);
v___x_390_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
v___x_391_ = l_Lean_Syntax_node2(v___x_383_, v___x_390_, v___x_379_, v___x_381_);
v___x_392_ = l_Lean_Syntax_node2(v___x_383_, v___x_384_, v___x_389_, v___x_391_);
v___x_393_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_393_, 0, v___x_392_);
lean_ctor_set(v___x_393_, 1, v_a_370_);
return v___x_393_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___boxed(lean_object* v_x_394_, lean_object* v_a_395_, lean_object* v_a_396_){
_start:
{
lean_object* v_res_397_; 
v_res_397_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(v_x_394_, v_a_395_, v_a_396_);
lean_dec_ref(v_a_395_);
return v_res_397_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__andM__1(lean_object* v_x_398_, lean_object* v_a_399_, lean_object* v_a_400_){
_start:
{
lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_401_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_398_);
v___x_402_ = l_Lean_Syntax_isOfKind(v_x_398_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v_x_398_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_a_400_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_405_ = lean_unsigned_to_nat(0u);
v___x_406_ = l_Lean_Syntax_getArg(v_x_398_, v___x_405_);
v___x_407_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_406_);
v___x_408_ = l_Lean_Syntax_isOfKind(v___x_406_, v___x_407_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v___x_406_);
lean_dec(v_x_398_);
v___x_409_ = lean_box(0);
v___x_410_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_410_, 0, v___x_409_);
lean_ctor_set(v___x_410_, 1, v_a_400_);
return v___x_410_;
}
else
{
lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; uint8_t v___x_414_; 
v___x_411_ = lean_unsigned_to_nat(1u);
v___x_412_ = l_Lean_Syntax_getArg(v_x_398_, v___x_411_);
lean_dec(v_x_398_);
v___x_413_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_412_);
v___x_414_ = l_Lean_Syntax_matchesNull(v___x_412_, v___x_413_);
if (v___x_414_ == 0)
{
lean_object* v___x_415_; lean_object* v___x_416_; 
lean_dec(v___x_412_);
lean_dec(v___x_406_);
v___x_415_ = lean_box(0);
v___x_416_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_416_, 0, v___x_415_);
lean_ctor_set(v___x_416_, 1, v_a_400_);
return v___x_416_;
}
else
{
lean_object* v___x_417_; lean_object* v___x_418_; lean_object* v_ref_419_; uint8_t v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; 
v___x_417_ = l_Lean_Syntax_getArg(v___x_412_, v___x_405_);
v___x_418_ = l_Lean_Syntax_getArg(v___x_412_, v___x_411_);
lean_dec(v___x_412_);
v_ref_419_ = l_Lean_replaceRef(v___x_406_, v_a_399_);
lean_dec(v___x_406_);
v___x_420_ = 0;
v___x_421_ = l_Lean_SourceInfo_fromRef(v_ref_419_, v___x_420_);
lean_dec(v_ref_419_);
v___x_422_ = ((lean_object*)(l_term___x3c_x26_x26_x3e___00__closed__1));
v___x_423_ = ((lean_object*)(l_term___x3c_x26_x26_x3e___00__closed__2));
lean_inc(v___x_421_);
v___x_424_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_424_, 0, v___x_421_);
lean_ctor_set(v___x_424_, 1, v___x_423_);
v___x_425_ = l_Lean_Syntax_node3(v___x_421_, v___x_422_, v___x_417_, v___x_424_, v___x_418_);
v___x_426_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_426_, 0, v___x_425_);
lean_ctor_set(v___x_426_, 1, v_a_400_);
return v___x_426_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__andM__1___boxed(lean_object* v_x_427_, lean_object* v_a_428_, lean_object* v_a_429_){
_start:
{
lean_object* v_res_430_; 
v_res_430_ = l___aux__Init__Control__Basic______unexpand__andM__1(v_x_427_, v_a_428_, v_a_429_);
lean_dec(v_a_428_);
return v_res_430_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__0(lean_object* v_x_u2082_431_, lean_object* v_x_u2081_432_, lean_object* v_00_u03b2_433_, lean_object* v___y_434_){
_start:
{
lean_object* v___x_435_; lean_object* v___x_436_; 
v___x_435_ = lean_apply_2(v_x_u2082_431_, lean_box(0), v___y_434_);
v___x_436_ = lean_apply_2(v_x_u2081_432_, lean_box(0), v___x_435_);
return v___x_436_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__1(lean_object* v_x_u2082_437_, lean_object* v_f_438_, lean_object* v_x_u2081_439_){
_start:
{
lean_object* v___f_440_; lean_object* v___x_441_; 
v___f_440_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__0), 4, 2);
lean_closure_set(v___f_440_, 0, v_x_u2082_437_);
lean_closure_set(v___f_440_, 1, v_x_u2081_439_);
v___x_441_ = lean_apply_1(v_f_438_, v___f_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__2(lean_object* v_inst_442_, lean_object* v_f_443_, lean_object* v_x_u2082_444_){
_start:
{
lean_object* v_liftWith_445_; lean_object* v___f_446_; lean_object* v___x_447_; 
v_liftWith_445_ = lean_ctor_get(v_inst_442_, 0);
lean_inc(v_liftWith_445_);
lean_dec_ref(v_inst_442_);
v___f_446_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_446_, 0, v_x_u2082_444_);
lean_closure_set(v___f_446_, 1, v_f_443_);
v___x_447_ = lean_apply_2(v_liftWith_445_, lean_box(0), v___f_446_);
return v___x_447_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_00_u03b1_450_, lean_object* v_f_451_){
_start:
{
lean_object* v_liftWith_452_; lean_object* v___f_453_; lean_object* v___x_454_; 
v_liftWith_452_ = lean_ctor_get(v_inst_448_, 0);
lean_inc(v_liftWith_452_);
lean_dec_ref(v_inst_448_);
v___f_453_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__2), 3, 2);
lean_closure_set(v___f_453_, 0, v_inst_449_);
lean_closure_set(v___f_453_, 1, v_f_451_);
v___x_454_ = lean_apply_2(v_liftWith_452_, lean_box(0), v___f_453_);
return v___x_454_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_00_u03b1_457_, lean_object* v___y_458_){
_start:
{
lean_object* v_restoreM_459_; lean_object* v_restoreM_460_; lean_object* v___x_461_; lean_object* v___x_462_; 
v_restoreM_459_ = lean_ctor_get(v_inst_455_, 1);
lean_inc(v_restoreM_459_);
lean_dec_ref(v_inst_455_);
v_restoreM_460_ = lean_ctor_get(v_inst_456_, 1);
lean_inc(v_restoreM_460_);
lean_dec_ref(v_inst_456_);
v___x_461_ = lean_apply_2(v_restoreM_460_, lean_box(0), v___y_458_);
v___x_462_ = lean_apply_2(v_restoreM_459_, lean_box(0), v___x_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg(lean_object* v_inst_463_, lean_object* v_inst_464_){
_start:
{
lean_object* v___f_465_; lean_object* v___f_466_; lean_object* v___x_467_; 
lean_inc_ref(v_inst_464_);
lean_inc_ref(v_inst_463_);
v___f_465_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_465_, 0, v_inst_463_);
lean_closure_set(v___f_465_, 1, v_inst_464_);
v___f_466_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_466_, 0, v_inst_463_);
lean_closure_set(v___f_466_, 1, v_inst_464_);
v___x_467_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_467_, 0, v___f_465_);
lean_ctor_set(v___x_467_, 1, v___f_466_);
return v___x_467_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl(lean_object* v_m_468_, lean_object* v_n_469_, lean_object* v_o_470_, lean_object* v_inst_471_, lean_object* v_inst_472_){
_start:
{
lean_object* v___f_473_; lean_object* v___f_474_; lean_object* v___x_475_; 
lean_inc_ref(v_inst_472_);
lean_inc_ref(v_inst_471_);
v___f_473_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_473_, 0, v_inst_471_);
lean_closure_set(v___f_473_, 1, v_inst_472_);
v___f_474_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_474_, 0, v_inst_471_);
lean_closure_set(v___f_474_, 1, v_inst_472_);
v___x_475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_475_, 0, v___f_473_);
lean_ctor_set(v___x_475_, 1, v___f_474_);
return v___x_475_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__0(lean_object* v_00_u03b2_476_, lean_object* v_x_477_){
_start:
{
lean_inc(v_x_477_);
return v_x_477_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__0___boxed(lean_object* v_00_u03b2_478_, lean_object* v_x_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_instMonadControlTOfPure___redArg___lam__0(v_00_u03b2_478_, v_x_479_);
lean_dec(v_x_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__1(lean_object* v___f_481_, lean_object* v_00_u03b1_482_, lean_object* v_f_483_){
_start:
{
lean_object* v___x_484_; 
v___x_484_ = lean_apply_1(v_f_483_, v___f_481_);
return v___x_484_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__2(lean_object* v_inst_485_, lean_object* v_00_u03b1_486_, lean_object* v_x_487_){
_start:
{
lean_object* v___x_488_; 
v___x_488_ = lean_apply_2(v_inst_485_, lean_box(0), v_x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg(lean_object* v_inst_492_){
_start:
{
lean_object* v___f_493_; lean_object* v___f_494_; lean_object* v___x_495_; 
v___f_493_ = ((lean_object*)(l_instMonadControlTOfPure___redArg___closed__1));
v___f_494_ = lean_alloc_closure((void*)(l_instMonadControlTOfPure___redArg___lam__2), 3, 1);
lean_closure_set(v___f_494_, 0, v_inst_492_);
v___x_495_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_495_, 0, v___f_493_);
lean_ctor_set(v___x_495_, 1, v___f_494_);
return v___x_495_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure(lean_object* v_m_496_, lean_object* v_inst_497_){
_start:
{
lean_object* v___x_498_; 
v___x_498_ = l_instMonadControlTOfPure___redArg(v_inst_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_controlAt___redArg(lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_f_501_){
_start:
{
lean_object* v_liftWith_502_; lean_object* v_restoreM_503_; lean_object* v___x_504_; lean_object* v___x_505_; lean_object* v___x_506_; 
v_liftWith_502_ = lean_ctor_get(v_inst_499_, 0);
lean_inc(v_liftWith_502_);
v_restoreM_503_ = lean_ctor_get(v_inst_499_, 1);
lean_inc(v_restoreM_503_);
lean_dec_ref(v_inst_499_);
v___x_504_ = lean_apply_2(v_liftWith_502_, lean_box(0), v_f_501_);
v___x_505_ = lean_apply_1(v_restoreM_503_, lean_box(0));
v___x_506_ = lean_apply_4(v_inst_500_, lean_box(0), lean_box(0), v___x_504_, v___x_505_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_controlAt(lean_object* v_m_507_, lean_object* v_n_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_00_u03b1_511_, lean_object* v_f_512_){
_start:
{
lean_object* v_liftWith_513_; lean_object* v_restoreM_514_; lean_object* v___x_515_; lean_object* v___x_516_; lean_object* v___x_517_; 
v_liftWith_513_ = lean_ctor_get(v_inst_509_, 0);
lean_inc(v_liftWith_513_);
v_restoreM_514_ = lean_ctor_get(v_inst_509_, 1);
lean_inc(v_restoreM_514_);
lean_dec_ref(v_inst_509_);
v___x_515_ = lean_apply_2(v_liftWith_513_, lean_box(0), v_f_512_);
v___x_516_ = lean_apply_1(v_restoreM_514_, lean_box(0));
v___x_517_ = lean_apply_4(v_inst_510_, lean_box(0), lean_box(0), v___x_515_, v___x_516_);
return v___x_517_;
}
}
LEAN_EXPORT lean_object* l_control___redArg(lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_f_520_){
_start:
{
lean_object* v_liftWith_521_; lean_object* v_restoreM_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; 
v_liftWith_521_ = lean_ctor_get(v_inst_518_, 0);
lean_inc(v_liftWith_521_);
v_restoreM_522_ = lean_ctor_get(v_inst_518_, 1);
lean_inc(v_restoreM_522_);
lean_dec_ref(v_inst_518_);
v___x_523_ = lean_apply_2(v_liftWith_521_, lean_box(0), v_f_520_);
v___x_524_ = lean_apply_1(v_restoreM_522_, lean_box(0));
v___x_525_ = lean_apply_4(v_inst_519_, lean_box(0), lean_box(0), v___x_523_, v___x_524_);
return v___x_525_;
}
}
LEAN_EXPORT lean_object* l_control(lean_object* v_m_526_, lean_object* v_n_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_00_u03b1_530_, lean_object* v_f_531_){
_start:
{
lean_object* v_liftWith_532_; lean_object* v_restoreM_533_; lean_object* v___x_534_; lean_object* v___x_535_; lean_object* v___x_536_; 
v_liftWith_532_ = lean_ctor_get(v_inst_528_, 0);
lean_inc(v_liftWith_532_);
v_restoreM_533_ = lean_ctor_get(v_inst_528_, 1);
lean_inc(v_restoreM_533_);
lean_dec_ref(v_inst_528_);
v___x_534_ = lean_apply_2(v_liftWith_532_, lean_box(0), v_f_531_);
v___x_535_ = lean_apply_1(v_restoreM_533_, lean_box(0));
v___x_536_ = lean_apply_4(v_inst_529_, lean_box(0), lean_box(0), v___x_534_, v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliRight___redArg(lean_object* v_inst_537_, lean_object* v_f_u2081_538_, lean_object* v_f_u2082_539_, lean_object* v_a_540_){
_start:
{
lean_object* v___x_541_; lean_object* v___x_542_; 
v___x_541_ = lean_apply_1(v_f_u2081_538_, v_a_540_);
v___x_542_ = lean_apply_4(v_inst_537_, lean_box(0), lean_box(0), v___x_541_, v_f_u2082_539_);
return v___x_542_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliRight(lean_object* v_00_u03b1_543_, lean_object* v_m_544_, lean_object* v_00_u03b2_545_, lean_object* v_00_u03b3_546_, lean_object* v_inst_547_, lean_object* v_f_u2081_548_, lean_object* v_f_u2082_549_, lean_object* v_a_550_){
_start:
{
lean_object* v___x_551_; lean_object* v___x_552_; 
v___x_551_ = lean_apply_1(v_f_u2081_548_, v_a_550_);
v___x_552_ = lean_apply_4(v_inst_547_, lean_box(0), lean_box(0), v___x_551_, v_f_u2082_549_);
return v___x_552_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliLeft___redArg(lean_object* v_inst_553_, lean_object* v_f_u2082_554_, lean_object* v_f_u2081_555_, lean_object* v_a_556_){
_start:
{
lean_object* v___x_557_; lean_object* v___x_558_; 
v___x_557_ = lean_apply_1(v_f_u2081_555_, v_a_556_);
v___x_558_ = lean_apply_4(v_inst_553_, lean_box(0), lean_box(0), v___x_557_, v_f_u2082_554_);
return v___x_558_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliLeft(lean_object* v_00_u03b1_559_, lean_object* v_m_560_, lean_object* v_00_u03b2_561_, lean_object* v_00_u03b3_562_, lean_object* v_inst_563_, lean_object* v_f_u2082_564_, lean_object* v_f_u2081_565_, lean_object* v_a_566_){
_start:
{
lean_object* v___x_567_; lean_object* v___x_568_; 
v___x_567_ = lean_apply_1(v_f_u2081_565_, v_a_566_);
v___x_568_ = lean_apply_4(v_inst_563_, lean_box(0), lean_box(0), v___x_567_, v_f_u2082_564_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l_Bind_bindLeft___redArg(lean_object* v_inst_569_, lean_object* v_f_570_, lean_object* v_ma_571_){
_start:
{
lean_object* v___x_572_; 
v___x_572_ = lean_apply_4(v_inst_569_, lean_box(0), lean_box(0), v_ma_571_, v_f_570_);
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_Bind_bindLeft(lean_object* v_00_u03b1_573_, lean_object* v_m_574_, lean_object* v_00_u03b2_575_, lean_object* v_inst_576_, lean_object* v_f_577_, lean_object* v_ma_578_){
_start:
{
lean_object* v___x_579_; 
v___x_579_ = lean_apply_4(v_inst_576_, lean_box(0), lean_box(0), v_ma_578_, v_f_577_);
return v___x_579_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_600_; lean_object* v___x_601_; 
v___x_600_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0));
v___x_601_ = l_String_toRawSubstring_x27(v___x_600_);
return v___x_601_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(lean_object* v_x_613_, lean_object* v_a_614_, lean_object* v_a_615_){
_start:
{
lean_object* v___x_616_; uint8_t v___x_617_; 
v___x_616_ = ((lean_object*)(l_term___x3e_x3d_x3e___00__closed__1));
lean_inc(v_x_613_);
v___x_617_ = l_Lean_Syntax_isOfKind(v_x_613_, v___x_616_);
if (v___x_617_ == 0)
{
lean_object* v___x_618_; lean_object* v___x_619_; 
lean_dec(v_x_613_);
v___x_618_ = lean_box(1);
v___x_619_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_619_, 0, v___x_618_);
lean_ctor_set(v___x_619_, 1, v_a_615_);
return v___x_619_;
}
else
{
lean_object* v_quotContext_620_; lean_object* v_currMacroScope_621_; lean_object* v_ref_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; uint8_t v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; 
v_quotContext_620_ = lean_ctor_get(v_a_614_, 1);
v_currMacroScope_621_ = lean_ctor_get(v_a_614_, 2);
v_ref_622_ = lean_ctor_get(v_a_614_, 5);
v___x_623_ = lean_unsigned_to_nat(0u);
v___x_624_ = l_Lean_Syntax_getArg(v_x_613_, v___x_623_);
v___x_625_ = lean_unsigned_to_nat(2u);
v___x_626_ = l_Lean_Syntax_getArg(v_x_613_, v___x_625_);
lean_dec(v_x_613_);
v___x_627_ = 0;
v___x_628_ = l_Lean_SourceInfo_fromRef(v_ref_622_, v___x_627_);
v___x_629_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_630_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1);
v___x_631_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4));
lean_inc(v_currMacroScope_621_);
lean_inc(v_quotContext_620_);
v___x_632_ = l_Lean_addMacroScope(v_quotContext_620_, v___x_631_, v_currMacroScope_621_);
v___x_633_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6));
lean_inc_n(v___x_628_, 2);
v___x_634_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_634_, 0, v___x_628_);
lean_ctor_set(v___x_634_, 1, v___x_630_);
lean_ctor_set(v___x_634_, 2, v___x_632_);
lean_ctor_set(v___x_634_, 3, v___x_633_);
v___x_635_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
v___x_636_ = l_Lean_Syntax_node2(v___x_628_, v___x_635_, v___x_624_, v___x_626_);
v___x_637_ = l_Lean_Syntax_node2(v___x_628_, v___x_629_, v___x_634_, v___x_636_);
v___x_638_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_638_, 0, v___x_637_);
lean_ctor_set(v___x_638_, 1, v_a_615_);
return v___x_638_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___boxed(lean_object* v_x_639_, lean_object* v_a_640_, lean_object* v_a_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(v_x_639_, v_a_640_, v_a_641_);
lean_dec_ref(v_a_640_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(lean_object* v_x_643_, lean_object* v_a_644_, lean_object* v_a_645_){
_start:
{
lean_object* v___x_646_; uint8_t v___x_647_; 
v___x_646_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_643_);
v___x_647_ = l_Lean_Syntax_isOfKind(v_x_643_, v___x_646_);
if (v___x_647_ == 0)
{
lean_object* v___x_648_; lean_object* v___x_649_; 
lean_dec(v_x_643_);
v___x_648_ = lean_box(0);
v___x_649_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_649_, 0, v___x_648_);
lean_ctor_set(v___x_649_, 1, v_a_645_);
return v___x_649_;
}
else
{
lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; uint8_t v___x_653_; 
v___x_650_ = lean_unsigned_to_nat(0u);
v___x_651_ = l_Lean_Syntax_getArg(v_x_643_, v___x_650_);
v___x_652_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_651_);
v___x_653_ = l_Lean_Syntax_isOfKind(v___x_651_, v___x_652_);
if (v___x_653_ == 0)
{
lean_object* v___x_654_; lean_object* v___x_655_; 
lean_dec(v___x_651_);
lean_dec(v_x_643_);
v___x_654_ = lean_box(0);
v___x_655_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_a_645_);
return v___x_655_;
}
else
{
lean_object* v___x_656_; lean_object* v___x_657_; lean_object* v___x_658_; uint8_t v___x_659_; 
v___x_656_ = lean_unsigned_to_nat(1u);
v___x_657_ = l_Lean_Syntax_getArg(v_x_643_, v___x_656_);
lean_dec(v_x_643_);
v___x_658_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_657_);
v___x_659_ = l_Lean_Syntax_matchesNull(v___x_657_, v___x_658_);
if (v___x_659_ == 0)
{
lean_object* v___x_660_; lean_object* v___x_661_; 
lean_dec(v___x_657_);
lean_dec(v___x_651_);
v___x_660_ = lean_box(0);
v___x_661_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_660_);
lean_ctor_set(v___x_661_, 1, v_a_645_);
return v___x_661_;
}
else
{
lean_object* v___x_662_; lean_object* v___x_663_; lean_object* v_ref_664_; uint8_t v___x_665_; lean_object* v___x_666_; lean_object* v___x_667_; lean_object* v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; 
v___x_662_ = l_Lean_Syntax_getArg(v___x_657_, v___x_650_);
v___x_663_ = l_Lean_Syntax_getArg(v___x_657_, v___x_656_);
lean_dec(v___x_657_);
v_ref_664_ = l_Lean_replaceRef(v___x_651_, v_a_644_);
lean_dec(v___x_651_);
v___x_665_ = 0;
v___x_666_ = l_Lean_SourceInfo_fromRef(v_ref_664_, v___x_665_);
lean_dec(v_ref_664_);
v___x_667_ = ((lean_object*)(l_term___x3e_x3d_x3e___00__closed__1));
v___x_668_ = ((lean_object*)(l_term___x3e_x3d_x3e___00__closed__2));
lean_inc(v___x_666_);
v___x_669_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_669_, 0, v___x_666_);
lean_ctor_set(v___x_669_, 1, v___x_668_);
v___x_670_ = l_Lean_Syntax_node3(v___x_666_, v___x_667_, v___x_662_, v___x_669_, v___x_663_);
v___x_671_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_671_, 0, v___x_670_);
lean_ctor_set(v___x_671_, 1, v_a_645_);
return v___x_671_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1___boxed(lean_object* v_x_672_, lean_object* v_a_673_, lean_object* v_a_674_){
_start:
{
lean_object* v_res_675_; 
v_res_675_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(v_x_672_, v_a_673_, v_a_674_);
lean_dec(v_a_673_);
return v_res_675_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_693_; lean_object* v___x_694_; 
v___x_693_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0));
v___x_694_ = l_String_toRawSubstring_x27(v___x_693_);
return v___x_694_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(lean_object* v_x_705_, lean_object* v_a_706_, lean_object* v_a_707_){
_start:
{
lean_object* v___x_708_; uint8_t v___x_709_; 
v___x_708_ = ((lean_object*)(l_term___x3c_x3d_x3c___00__closed__1));
lean_inc(v_x_705_);
v___x_709_ = l_Lean_Syntax_isOfKind(v_x_705_, v___x_708_);
if (v___x_709_ == 0)
{
lean_object* v___x_710_; lean_object* v___x_711_; 
lean_dec(v_x_705_);
v___x_710_ = lean_box(1);
v___x_711_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_711_, 0, v___x_710_);
lean_ctor_set(v___x_711_, 1, v_a_707_);
return v___x_711_;
}
else
{
lean_object* v_quotContext_712_; lean_object* v_currMacroScope_713_; lean_object* v_ref_714_; lean_object* v___x_715_; lean_object* v___x_716_; lean_object* v___x_717_; lean_object* v___x_718_; uint8_t v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; 
v_quotContext_712_ = lean_ctor_get(v_a_706_, 1);
v_currMacroScope_713_ = lean_ctor_get(v_a_706_, 2);
v_ref_714_ = lean_ctor_get(v_a_706_, 5);
v___x_715_ = lean_unsigned_to_nat(0u);
v___x_716_ = l_Lean_Syntax_getArg(v_x_705_, v___x_715_);
v___x_717_ = lean_unsigned_to_nat(2u);
v___x_718_ = l_Lean_Syntax_getArg(v_x_705_, v___x_717_);
lean_dec(v_x_705_);
v___x_719_ = 0;
v___x_720_ = l_Lean_SourceInfo_fromRef(v_ref_714_, v___x_719_);
v___x_721_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_722_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1);
v___x_723_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3));
lean_inc(v_currMacroScope_713_);
lean_inc(v_quotContext_712_);
v___x_724_ = l_Lean_addMacroScope(v_quotContext_712_, v___x_723_, v_currMacroScope_713_);
v___x_725_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5));
lean_inc_n(v___x_720_, 2);
v___x_726_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_726_, 0, v___x_720_);
lean_ctor_set(v___x_726_, 1, v___x_722_);
lean_ctor_set(v___x_726_, 2, v___x_724_);
lean_ctor_set(v___x_726_, 3, v___x_725_);
v___x_727_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
v___x_728_ = l_Lean_Syntax_node2(v___x_720_, v___x_727_, v___x_716_, v___x_718_);
v___x_729_ = l_Lean_Syntax_node2(v___x_720_, v___x_721_, v___x_726_, v___x_728_);
v___x_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_730_, 0, v___x_729_);
lean_ctor_set(v___x_730_, 1, v_a_707_);
return v___x_730_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___boxed(lean_object* v_x_731_, lean_object* v_a_732_, lean_object* v_a_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(v_x_731_, v_a_732_, v_a_733_);
lean_dec_ref(v_a_732_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(lean_object* v_x_735_, lean_object* v_a_736_, lean_object* v_a_737_){
_start:
{
lean_object* v___x_738_; uint8_t v___x_739_; 
v___x_738_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_735_);
v___x_739_ = l_Lean_Syntax_isOfKind(v_x_735_, v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; lean_object* v___x_741_; 
lean_dec(v_x_735_);
v___x_740_ = lean_box(0);
v___x_741_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_740_);
lean_ctor_set(v___x_741_, 1, v_a_737_);
return v___x_741_;
}
else
{
lean_object* v___x_742_; lean_object* v___x_743_; lean_object* v___x_744_; uint8_t v___x_745_; 
v___x_742_ = lean_unsigned_to_nat(0u);
v___x_743_ = l_Lean_Syntax_getArg(v_x_735_, v___x_742_);
v___x_744_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_743_);
v___x_745_ = l_Lean_Syntax_isOfKind(v___x_743_, v___x_744_);
if (v___x_745_ == 0)
{
lean_object* v___x_746_; lean_object* v___x_747_; 
lean_dec(v___x_743_);
lean_dec(v_x_735_);
v___x_746_ = lean_box(0);
v___x_747_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_747_, 0, v___x_746_);
lean_ctor_set(v___x_747_, 1, v_a_737_);
return v___x_747_;
}
else
{
lean_object* v___x_748_; lean_object* v___x_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v___x_748_ = lean_unsigned_to_nat(1u);
v___x_749_ = l_Lean_Syntax_getArg(v_x_735_, v___x_748_);
lean_dec(v_x_735_);
v___x_750_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_749_);
v___x_751_ = l_Lean_Syntax_matchesNull(v___x_749_, v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; lean_object* v___x_753_; 
lean_dec(v___x_749_);
lean_dec(v___x_743_);
v___x_752_ = lean_box(0);
v___x_753_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_753_, 0, v___x_752_);
lean_ctor_set(v___x_753_, 1, v_a_737_);
return v___x_753_;
}
else
{
lean_object* v___x_754_; lean_object* v___x_755_; lean_object* v_ref_756_; uint8_t v___x_757_; lean_object* v___x_758_; lean_object* v___x_759_; lean_object* v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; 
v___x_754_ = l_Lean_Syntax_getArg(v___x_749_, v___x_742_);
v___x_755_ = l_Lean_Syntax_getArg(v___x_749_, v___x_748_);
lean_dec(v___x_749_);
v_ref_756_ = l_Lean_replaceRef(v___x_743_, v_a_736_);
lean_dec(v___x_743_);
v___x_757_ = 0;
v___x_758_ = l_Lean_SourceInfo_fromRef(v_ref_756_, v___x_757_);
lean_dec(v_ref_756_);
v___x_759_ = ((lean_object*)(l_term___x3c_x3d_x3c___00__closed__1));
v___x_760_ = ((lean_object*)(l_term___x3c_x3d_x3c___00__closed__2));
lean_inc(v___x_758_);
v___x_761_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_761_, 0, v___x_758_);
lean_ctor_set(v___x_761_, 1, v___x_760_);
v___x_762_ = l_Lean_Syntax_node3(v___x_758_, v___x_759_, v___x_754_, v___x_761_, v___x_755_);
v___x_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_763_, 0, v___x_762_);
lean_ctor_set(v___x_763_, 1, v_a_737_);
return v___x_763_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1___boxed(lean_object* v_x_764_, lean_object* v_a_765_, lean_object* v_a_766_){
_start:
{
lean_object* v_res_767_; 
v_res_767_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(v_x_764_, v_a_765_, v_a_766_);
lean_dec(v_a_765_);
return v_res_767_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_785_; lean_object* v___x_786_; 
v___x_785_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0));
v___x_786_ = l_String_toRawSubstring_x27(v___x_785_);
return v___x_786_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(lean_object* v_x_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_800_; uint8_t v___x_801_; 
v___x_800_ = ((lean_object*)(l_term___x3d_x3c_x3c___00__closed__1));
lean_inc(v_x_797_);
v___x_801_ = l_Lean_Syntax_isOfKind(v_x_797_, v___x_800_);
if (v___x_801_ == 0)
{
lean_object* v___x_802_; lean_object* v___x_803_; 
lean_dec(v_x_797_);
v___x_802_ = lean_box(1);
v___x_803_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_803_, 0, v___x_802_);
lean_ctor_set(v___x_803_, 1, v_a_799_);
return v___x_803_;
}
else
{
lean_object* v_quotContext_804_; lean_object* v_currMacroScope_805_; lean_object* v_ref_806_; lean_object* v___x_807_; lean_object* v___x_808_; lean_object* v___x_809_; lean_object* v___x_810_; uint8_t v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; lean_object* v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; 
v_quotContext_804_ = lean_ctor_get(v_a_798_, 1);
v_currMacroScope_805_ = lean_ctor_get(v_a_798_, 2);
v_ref_806_ = lean_ctor_get(v_a_798_, 5);
v___x_807_ = lean_unsigned_to_nat(0u);
v___x_808_ = l_Lean_Syntax_getArg(v_x_797_, v___x_807_);
v___x_809_ = lean_unsigned_to_nat(2u);
v___x_810_ = l_Lean_Syntax_getArg(v_x_797_, v___x_809_);
lean_dec(v_x_797_);
v___x_811_ = 0;
v___x_812_ = l_Lean_SourceInfo_fromRef(v_ref_806_, v___x_811_);
v___x_813_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_814_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1);
v___x_815_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3));
lean_inc(v_currMacroScope_805_);
lean_inc(v_quotContext_804_);
v___x_816_ = l_Lean_addMacroScope(v_quotContext_804_, v___x_815_, v_currMacroScope_805_);
v___x_817_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5));
lean_inc_n(v___x_812_, 2);
v___x_818_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_818_, 0, v___x_812_);
lean_ctor_set(v___x_818_, 1, v___x_814_);
lean_ctor_set(v___x_818_, 2, v___x_816_);
lean_ctor_set(v___x_818_, 3, v___x_817_);
v___x_819_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
v___x_820_ = l_Lean_Syntax_node2(v___x_812_, v___x_819_, v___x_808_, v___x_810_);
v___x_821_ = l_Lean_Syntax_node2(v___x_812_, v___x_813_, v___x_818_, v___x_820_);
v___x_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_822_, 0, v___x_821_);
lean_ctor_set(v___x_822_, 1, v_a_799_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___boxed(lean_object* v_x_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(v_x_823_, v_a_824_, v_a_825_);
lean_dec_ref(v_a_824_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(lean_object* v_x_827_, lean_object* v_a_828_, lean_object* v_a_829_){
_start:
{
lean_object* v___x_830_; uint8_t v___x_831_; 
v___x_830_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_827_);
v___x_831_ = l_Lean_Syntax_isOfKind(v_x_827_, v___x_830_);
if (v___x_831_ == 0)
{
lean_object* v___x_832_; lean_object* v___x_833_; 
lean_dec(v_x_827_);
v___x_832_ = lean_box(0);
v___x_833_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_833_, 0, v___x_832_);
lean_ctor_set(v___x_833_, 1, v_a_829_);
return v___x_833_;
}
else
{
lean_object* v___x_834_; lean_object* v___x_835_; lean_object* v___x_836_; uint8_t v___x_837_; 
v___x_834_ = lean_unsigned_to_nat(0u);
v___x_835_ = l_Lean_Syntax_getArg(v_x_827_, v___x_834_);
v___x_836_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_835_);
v___x_837_ = l_Lean_Syntax_isOfKind(v___x_835_, v___x_836_);
if (v___x_837_ == 0)
{
lean_object* v___x_838_; lean_object* v___x_839_; 
lean_dec(v___x_835_);
lean_dec(v_x_827_);
v___x_838_ = lean_box(0);
v___x_839_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_839_, 0, v___x_838_);
lean_ctor_set(v___x_839_, 1, v_a_829_);
return v___x_839_;
}
else
{
lean_object* v___x_840_; lean_object* v___x_841_; lean_object* v___x_842_; uint8_t v___x_843_; 
v___x_840_ = lean_unsigned_to_nat(1u);
v___x_841_ = l_Lean_Syntax_getArg(v_x_827_, v___x_840_);
lean_dec(v_x_827_);
v___x_842_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_841_);
v___x_843_ = l_Lean_Syntax_matchesNull(v___x_841_, v___x_842_);
if (v___x_843_ == 0)
{
lean_object* v___x_844_; lean_object* v___x_845_; 
lean_dec(v___x_841_);
lean_dec(v___x_835_);
v___x_844_ = lean_box(0);
v___x_845_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_845_, 0, v___x_844_);
lean_ctor_set(v___x_845_, 1, v_a_829_);
return v___x_845_;
}
else
{
lean_object* v___x_846_; lean_object* v___x_847_; lean_object* v_ref_848_; uint8_t v___x_849_; lean_object* v___x_850_; lean_object* v___x_851_; lean_object* v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; 
v___x_846_ = l_Lean_Syntax_getArg(v___x_841_, v___x_834_);
v___x_847_ = l_Lean_Syntax_getArg(v___x_841_, v___x_840_);
lean_dec(v___x_841_);
v_ref_848_ = l_Lean_replaceRef(v___x_835_, v_a_828_);
lean_dec(v___x_835_);
v___x_849_ = 0;
v___x_850_ = l_Lean_SourceInfo_fromRef(v_ref_848_, v___x_849_);
lean_dec(v_ref_848_);
v___x_851_ = ((lean_object*)(l_term___x3d_x3c_x3c___00__closed__1));
v___x_852_ = ((lean_object*)(l_term___x3d_x3c_x3c___00__closed__2));
lean_inc(v___x_850_);
v___x_853_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_853_, 0, v___x_850_);
lean_ctor_set(v___x_853_, 1, v___x_852_);
v___x_854_ = l_Lean_Syntax_node3(v___x_850_, v___x_851_, v___x_846_, v___x_853_, v___x_847_);
v___x_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_855_, 0, v___x_854_);
lean_ctor_set(v___x_855_, 1, v_a_829_);
return v___x_855_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1___boxed(lean_object* v_x_856_, lean_object* v_a_857_, lean_object* v_a_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(v_x_856_, v_a_857_, v_a_858_);
lean_dec(v_a_857_);
return v_res_859_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
lean_object* runtime_initialize_Init_BinderNameHint(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Control_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Core(uint8_t builtin);
lean_object* initialize_Init_BinderNameHint(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Control_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Core(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_BinderNameHint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Control_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Control_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Control_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
