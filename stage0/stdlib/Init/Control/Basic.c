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
lean_object* l_guard___redArg(lean_object* v_inst_179_, uint8_t v_inst_180_){
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
LEAN_EXPORT void l_guard___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_179_ = stack[0].m_obj;
uint8_t v_inst_180_ = stack[1].m_num;
lean_object* v_res_187_;
v_res_187_ = l_guard___redArg(v_inst_179_, v_inst_180_);
stack->m_obj
 = v_res_187_;
}
LEAN_EXPORT lean_object* l_guard___redArg___boxed(lean_object* v_inst_188_, lean_object* v_inst_189_){
_start:
{
uint8_t v_inst_21__boxed_190_; lean_object* v_res_191_; 
v_inst_21__boxed_190_ = lean_unbox(v_inst_189_);
v_res_191_ = l_guard___redArg(v_inst_188_, v_inst_21__boxed_190_);
return v_res_191_;
}
}
lean_object* l_guard(lean_object* v_f_192_, lean_object* v_inst_193_, lean_object* v_p_194_, uint8_t v_inst_195_){
_start:
{
if (v_inst_195_ == 0)
{
lean_object* v_failure_196_; lean_object* v___x_197_; 
v_failure_196_ = lean_ctor_get(v_inst_193_, 1);
lean_inc(v_failure_196_);
lean_dec_ref(v_inst_193_);
v___x_197_ = lean_apply_1(v_failure_196_, lean_box(0));
return v___x_197_;
}
else
{
lean_object* v_toApplicative_198_; lean_object* v_toPure_199_; lean_object* v___x_200_; lean_object* v___x_201_; 
v_toApplicative_198_ = lean_ctor_get(v_inst_193_, 0);
lean_inc_ref(v_toApplicative_198_);
lean_dec_ref(v_inst_193_);
v_toPure_199_ = lean_ctor_get(v_toApplicative_198_, 1);
lean_inc(v_toPure_199_);
lean_dec_ref(v_toApplicative_198_);
v___x_200_ = lean_box(0);
v___x_201_ = lean_apply_2(v_toPure_199_, lean_box(0), v___x_200_);
return v___x_201_;
}
}
}
LEAN_EXPORT void l_guard_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_193_ = stack[1].m_obj;
uint8_t v_inst_195_ = stack[3].m_num;
lean_object* v_res_202_;
v_res_202_ = l_guard(lean_box(0), v_inst_193_, lean_box(0), v_inst_195_);
stack->m_obj
 = v_res_202_;
}
LEAN_EXPORT lean_object* l_guard___boxed(lean_object* v_f_203_, lean_object* v_inst_204_, lean_object* v_p_205_, lean_object* v_inst_206_){
_start:
{
uint8_t v_inst_40__boxed_207_; lean_object* v_res_208_; 
v_inst_40__boxed_207_ = lean_unbox(v_inst_206_);
v_res_208_ = l_guard(v_f_203_, v_inst_204_, v_p_205_, v_inst_40__boxed_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_optional___redArg___lam__0(lean_object* v_val_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_210_, 0, v_val_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_optional___redArg___lam__1(lean_object* v_toPure_211_, lean_object* v_x_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_box(0);
v___x_214_ = lean_apply_2(v_toPure_211_, lean_box(0), v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_optional___redArg(lean_object* v_inst_216_, lean_object* v_x_217_){
_start:
{
lean_object* v_toApplicative_218_; lean_object* v_toFunctor_219_; lean_object* v_orElse_220_; lean_object* v_toPure_221_; lean_object* v_map_222_; lean_object* v___f_223_; lean_object* v___f_224_; lean_object* v___x_225_; lean_object* v___x_226_; 
v_toApplicative_218_ = lean_ctor_get(v_inst_216_, 0);
lean_inc_ref(v_toApplicative_218_);
v_toFunctor_219_ = lean_ctor_get(v_toApplicative_218_, 0);
lean_inc_ref(v_toFunctor_219_);
v_orElse_220_ = lean_ctor_get(v_inst_216_, 2);
lean_inc(v_orElse_220_);
lean_dec_ref(v_inst_216_);
v_toPure_221_ = lean_ctor_get(v_toApplicative_218_, 1);
lean_inc(v_toPure_221_);
lean_dec_ref(v_toApplicative_218_);
v_map_222_ = lean_ctor_get(v_toFunctor_219_, 0);
lean_inc(v_map_222_);
lean_dec_ref(v_toFunctor_219_);
v___f_223_ = ((lean_object*)(l_optional___redArg___closed__0));
v___f_224_ = lean_alloc_closure((void*)(l_optional___redArg___lam__1), 2, 1);
lean_closure_set(v___f_224_, 0, v_toPure_221_);
v___x_225_ = lean_apply_4(v_map_222_, lean_box(0), lean_box(0), v___f_223_, v_x_217_);
v___x_226_ = lean_apply_3(v_orElse_220_, lean_box(0), v___x_225_, v___f_224_);
return v___x_226_;
}
}
LEAN_EXPORT lean_object* l_optional(lean_object* v_f_227_, lean_object* v_inst_228_, lean_object* v_00_u03b1_229_, lean_object* v_x_230_){
_start:
{
lean_object* v_toApplicative_231_; lean_object* v_toFunctor_232_; lean_object* v_orElse_233_; lean_object* v_toPure_234_; lean_object* v_map_235_; lean_object* v___f_236_; lean_object* v___f_237_; lean_object* v___x_238_; lean_object* v___x_239_; 
v_toApplicative_231_ = lean_ctor_get(v_inst_228_, 0);
lean_inc_ref(v_toApplicative_231_);
v_toFunctor_232_ = lean_ctor_get(v_toApplicative_231_, 0);
lean_inc_ref(v_toFunctor_232_);
v_orElse_233_ = lean_ctor_get(v_inst_228_, 2);
lean_inc(v_orElse_233_);
lean_dec_ref(v_inst_228_);
v_toPure_234_ = lean_ctor_get(v_toApplicative_231_, 1);
lean_inc(v_toPure_234_);
lean_dec_ref(v_toApplicative_231_);
v_map_235_ = lean_ctor_get(v_toFunctor_232_, 0);
lean_inc(v_map_235_);
lean_dec_ref(v_toFunctor_232_);
v___f_236_ = ((lean_object*)(l_optional___redArg___closed__0));
v___f_237_ = lean_alloc_closure((void*)(l_optional___redArg___lam__1), 2, 1);
lean_closure_set(v___f_237_, 0, v_toPure_234_);
v___x_238_ = lean_apply_4(v_map_235_, lean_box(0), lean_box(0), v___f_236_, v_x_230_);
v___x_239_ = lean_apply_3(v_orElse_233_, lean_box(0), v___x_238_, v___f_237_);
return v___x_239_;
}
}
uint8_t l_instToBoolBool___lam__0(uint8_t v_b_240_){
_start:
{
return v_b_240_;
}
}
LEAN_EXPORT void l_instToBoolBool___lam__0_0interp(lean_interpreter_value* stack)
{
uint8_t v_b_240_ = stack[0].m_num;
uint8_t v_res_241_;
v_res_241_ = l_instToBoolBool___lam__0(v_b_240_);
stack->m_num = v_res_241_;
}
LEAN_EXPORT lean_object* l_instToBoolBool___lam__0___boxed(lean_object* v_b_242_){
_start:
{
uint8_t v_b_boxed_243_; uint8_t v_res_244_; lean_object* v_r_245_; 
v_b_boxed_243_ = lean_unbox(v_b_242_);
v_res_244_ = l_instToBoolBool___lam__0(v_b_boxed_243_);
v_r_245_ = lean_box(v_res_244_);
return v_r_245_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_268_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0));
v___x_269_ = l_String_toRawSubstring_x27(v___x_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(lean_object* v_x_278_, lean_object* v_a_279_, lean_object* v_a_280_){
_start:
{
lean_object* v___x_281_; uint8_t v___x_282_; 
v___x_281_ = ((lean_object*)(l_term___x3c_x7c_x7c_x3e___00__closed__1));
lean_inc(v_x_278_);
v___x_282_ = l_Lean_Syntax_isOfKind(v_x_278_, v___x_281_);
if (v___x_282_ == 0)
{
lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v_x_278_);
v___x_283_ = lean_box(1);
v___x_284_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_284_, 0, v___x_283_);
lean_ctor_set(v___x_284_, 1, v_a_280_);
return v___x_284_;
}
else
{
lean_object* v_quotContext_285_; lean_object* v_currMacroScope_286_; lean_object* v_ref_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; uint8_t v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_303_; 
v_quotContext_285_ = lean_ctor_get(v_a_279_, 1);
v_currMacroScope_286_ = lean_ctor_get(v_a_279_, 2);
v_ref_287_ = lean_ctor_get(v_a_279_, 5);
v___x_288_ = lean_unsigned_to_nat(0u);
v___x_289_ = l_Lean_Syntax_getArg(v_x_278_, v___x_288_);
v___x_290_ = lean_unsigned_to_nat(2u);
v___x_291_ = l_Lean_Syntax_getArg(v_x_278_, v___x_290_);
lean_dec(v_x_278_);
v___x_292_ = 0;
v___x_293_ = l_Lean_SourceInfo_fromRef(v_ref_287_, v___x_292_);
v___x_294_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_295_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1);
v___x_296_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2));
lean_inc(v_currMacroScope_286_);
lean_inc(v_quotContext_285_);
v___x_297_ = l_Lean_addMacroScope(v_quotContext_285_, v___x_296_, v_currMacroScope_286_);
v___x_298_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4));
lean_inc_n(v___x_293_, 2);
v___x_299_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_299_, 0, v___x_293_);
lean_ctor_set(v___x_299_, 1, v___x_295_);
lean_ctor_set(v___x_299_, 2, v___x_297_);
lean_ctor_set(v___x_299_, 3, v___x_298_);
v___x_300_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
v___x_301_ = l_Lean_Syntax_node2(v___x_293_, v___x_300_, v___x_289_, v___x_291_);
v___x_302_ = l_Lean_Syntax_node2(v___x_293_, v___x_294_, v___x_299_, v___x_301_);
v___x_303_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_a_280_);
return v___x_303_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___boxed(lean_object* v_x_304_, lean_object* v_a_305_, lean_object* v_a_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(v_x_304_, v_a_305_, v_a_306_);
lean_dec_ref(v_a_305_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__orM__1(lean_object* v_x_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v___x_311_; uint8_t v___x_312_; 
v___x_311_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_308_);
v___x_312_ = l_Lean_Syntax_isOfKind(v_x_308_, v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; lean_object* v___x_314_; 
lean_dec(v_x_308_);
v___x_313_ = lean_box(0);
v___x_314_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_314_, 0, v___x_313_);
lean_ctor_set(v___x_314_, 1, v_a_310_);
return v___x_314_;
}
else
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; uint8_t v___x_318_; 
v___x_315_ = lean_unsigned_to_nat(0u);
v___x_316_ = l_Lean_Syntax_getArg(v_x_308_, v___x_315_);
v___x_317_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_316_);
v___x_318_ = l_Lean_Syntax_isOfKind(v___x_316_, v___x_317_);
if (v___x_318_ == 0)
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v___x_316_);
lean_dec(v_x_308_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_320_, 0, v___x_319_);
lean_ctor_set(v___x_320_, 1, v_a_310_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; uint8_t v___x_324_; 
v___x_321_ = lean_unsigned_to_nat(1u);
v___x_322_ = l_Lean_Syntax_getArg(v_x_308_, v___x_321_);
lean_dec(v_x_308_);
v___x_323_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_322_);
v___x_324_ = l_Lean_Syntax_matchesNull(v___x_322_, v___x_323_);
if (v___x_324_ == 0)
{
lean_object* v___x_325_; lean_object* v___x_326_; 
lean_dec(v___x_322_);
lean_dec(v___x_316_);
v___x_325_ = lean_box(0);
v___x_326_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_325_);
lean_ctor_set(v___x_326_, 1, v_a_310_);
return v___x_326_;
}
else
{
lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v_ref_329_; uint8_t v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_327_ = l_Lean_Syntax_getArg(v___x_322_, v___x_315_);
v___x_328_ = l_Lean_Syntax_getArg(v___x_322_, v___x_321_);
lean_dec(v___x_322_);
v_ref_329_ = l_Lean_replaceRef(v___x_316_, v_a_309_);
lean_dec(v___x_316_);
v___x_330_ = 0;
v___x_331_ = l_Lean_SourceInfo_fromRef(v_ref_329_, v___x_330_);
lean_dec(v_ref_329_);
v___x_332_ = ((lean_object*)(l_term___x3c_x7c_x7c_x3e___00__closed__1));
v___x_333_ = ((lean_object*)(l_term___x3c_x7c_x7c_x3e___00__closed__2));
lean_inc(v___x_331_);
v___x_334_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_331_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = l_Lean_Syntax_node3(v___x_331_, v___x_332_, v___x_327_, v___x_334_, v___x_328_);
v___x_336_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_336_, 0, v___x_335_);
lean_ctor_set(v___x_336_, 1, v_a_310_);
return v___x_336_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__orM__1___boxed(lean_object* v_x_337_, lean_object* v_a_338_, lean_object* v_a_339_){
_start:
{
lean_object* v_res_340_; 
v_res_340_ = l___aux__Init__Control__Basic______unexpand__orM__1(v_x_337_, v_a_338_, v_a_339_);
lean_dec(v_a_338_);
return v_res_340_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_361_; lean_object* v___x_362_; 
v___x_361_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0));
v___x_362_ = l_String_toRawSubstring_x27(v___x_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(lean_object* v_x_371_, lean_object* v_a_372_, lean_object* v_a_373_){
_start:
{
lean_object* v___x_374_; uint8_t v___x_375_; 
v___x_374_ = ((lean_object*)(l_term___x3c_x26_x26_x3e___00__closed__1));
lean_inc(v_x_371_);
v___x_375_ = l_Lean_Syntax_isOfKind(v_x_371_, v___x_374_);
if (v___x_375_ == 0)
{
lean_object* v___x_376_; lean_object* v___x_377_; 
lean_dec(v_x_371_);
v___x_376_ = lean_box(1);
v___x_377_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set(v___x_377_, 1, v_a_373_);
return v___x_377_;
}
else
{
lean_object* v_quotContext_378_; lean_object* v_currMacroScope_379_; lean_object* v_ref_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; uint8_t v___x_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
v_quotContext_378_ = lean_ctor_get(v_a_372_, 1);
v_currMacroScope_379_ = lean_ctor_get(v_a_372_, 2);
v_ref_380_ = lean_ctor_get(v_a_372_, 5);
v___x_381_ = lean_unsigned_to_nat(0u);
v___x_382_ = l_Lean_Syntax_getArg(v_x_371_, v___x_381_);
v___x_383_ = lean_unsigned_to_nat(2u);
v___x_384_ = l_Lean_Syntax_getArg(v_x_371_, v___x_383_);
lean_dec(v_x_371_);
v___x_385_ = 0;
v___x_386_ = l_Lean_SourceInfo_fromRef(v_ref_380_, v___x_385_);
v___x_387_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_388_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1);
v___x_389_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2));
lean_inc(v_currMacroScope_379_);
lean_inc(v_quotContext_378_);
v___x_390_ = l_Lean_addMacroScope(v_quotContext_378_, v___x_389_, v_currMacroScope_379_);
v___x_391_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4));
lean_inc_n(v___x_386_, 2);
v___x_392_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_392_, 0, v___x_386_);
lean_ctor_set(v___x_392_, 1, v___x_388_);
lean_ctor_set(v___x_392_, 2, v___x_390_);
lean_ctor_set(v___x_392_, 3, v___x_391_);
v___x_393_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
v___x_394_ = l_Lean_Syntax_node2(v___x_386_, v___x_393_, v___x_382_, v___x_384_);
v___x_395_ = l_Lean_Syntax_node2(v___x_386_, v___x_387_, v___x_392_, v___x_394_);
v___x_396_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_396_, 0, v___x_395_);
lean_ctor_set(v___x_396_, 1, v_a_373_);
return v___x_396_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___boxed(lean_object* v_x_397_, lean_object* v_a_398_, lean_object* v_a_399_){
_start:
{
lean_object* v_res_400_; 
v_res_400_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(v_x_397_, v_a_398_, v_a_399_);
lean_dec_ref(v_a_398_);
return v_res_400_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__andM__1(lean_object* v_x_401_, lean_object* v_a_402_, lean_object* v_a_403_){
_start:
{
lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_404_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_401_);
v___x_405_ = l_Lean_Syntax_isOfKind(v_x_401_, v___x_404_);
if (v___x_405_ == 0)
{
lean_object* v___x_406_; lean_object* v___x_407_; 
lean_dec(v_x_401_);
v___x_406_ = lean_box(0);
v___x_407_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_407_, 0, v___x_406_);
lean_ctor_set(v___x_407_, 1, v_a_403_);
return v___x_407_;
}
else
{
lean_object* v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_408_ = lean_unsigned_to_nat(0u);
v___x_409_ = l_Lean_Syntax_getArg(v_x_401_, v___x_408_);
v___x_410_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_409_);
v___x_411_ = l_Lean_Syntax_isOfKind(v___x_409_, v___x_410_);
if (v___x_411_ == 0)
{
lean_object* v___x_412_; lean_object* v___x_413_; 
lean_dec(v___x_409_);
lean_dec(v_x_401_);
v___x_412_ = lean_box(0);
v___x_413_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_413_, 0, v___x_412_);
lean_ctor_set(v___x_413_, 1, v_a_403_);
return v___x_413_;
}
else
{
lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; uint8_t v___x_417_; 
v___x_414_ = lean_unsigned_to_nat(1u);
v___x_415_ = l_Lean_Syntax_getArg(v_x_401_, v___x_414_);
lean_dec(v_x_401_);
v___x_416_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_415_);
v___x_417_ = l_Lean_Syntax_matchesNull(v___x_415_, v___x_416_);
if (v___x_417_ == 0)
{
lean_object* v___x_418_; lean_object* v___x_419_; 
lean_dec(v___x_415_);
lean_dec(v___x_409_);
v___x_418_ = lean_box(0);
v___x_419_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_419_, 0, v___x_418_);
lean_ctor_set(v___x_419_, 1, v_a_403_);
return v___x_419_;
}
else
{
lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v_ref_422_; uint8_t v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v___x_420_ = l_Lean_Syntax_getArg(v___x_415_, v___x_408_);
v___x_421_ = l_Lean_Syntax_getArg(v___x_415_, v___x_414_);
lean_dec(v___x_415_);
v_ref_422_ = l_Lean_replaceRef(v___x_409_, v_a_402_);
lean_dec(v___x_409_);
v___x_423_ = 0;
v___x_424_ = l_Lean_SourceInfo_fromRef(v_ref_422_, v___x_423_);
lean_dec(v_ref_422_);
v___x_425_ = ((lean_object*)(l_term___x3c_x26_x26_x3e___00__closed__1));
v___x_426_ = ((lean_object*)(l_term___x3c_x26_x26_x3e___00__closed__2));
lean_inc(v___x_424_);
v___x_427_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_427_, 0, v___x_424_);
lean_ctor_set(v___x_427_, 1, v___x_426_);
v___x_428_ = l_Lean_Syntax_node3(v___x_424_, v___x_425_, v___x_420_, v___x_427_, v___x_421_);
v___x_429_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_429_, 0, v___x_428_);
lean_ctor_set(v___x_429_, 1, v_a_403_);
return v___x_429_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__andM__1___boxed(lean_object* v_x_430_, lean_object* v_a_431_, lean_object* v_a_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l___aux__Init__Control__Basic______unexpand__andM__1(v_x_430_, v_a_431_, v_a_432_);
lean_dec(v_a_431_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__0(lean_object* v_x_u2082_434_, lean_object* v_x_u2081_435_, lean_object* v_00_u03b2_436_, lean_object* v___y_437_){
_start:
{
lean_object* v___x_438_; lean_object* v___x_439_; 
v___x_438_ = lean_apply_2(v_x_u2082_434_, lean_box(0), v___y_437_);
v___x_439_ = lean_apply_2(v_x_u2081_435_, lean_box(0), v___x_438_);
return v___x_439_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__1(lean_object* v_x_u2082_440_, lean_object* v_f_441_, lean_object* v_x_u2081_442_){
_start:
{
lean_object* v___f_443_; lean_object* v___x_444_; 
v___f_443_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__0), 4, 2);
lean_closure_set(v___f_443_, 0, v_x_u2082_440_);
lean_closure_set(v___f_443_, 1, v_x_u2081_442_);
v___x_444_ = lean_apply_1(v_f_441_, v___f_443_);
return v___x_444_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__2(lean_object* v_inst_445_, lean_object* v_f_446_, lean_object* v_x_u2082_447_){
_start:
{
lean_object* v_liftWith_448_; lean_object* v___f_449_; lean_object* v___x_450_; 
v_liftWith_448_ = lean_ctor_get(v_inst_445_, 0);
lean_inc(v_liftWith_448_);
lean_dec_ref(v_inst_445_);
v___f_449_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_449_, 0, v_x_u2082_447_);
lean_closure_set(v___f_449_, 1, v_f_446_);
v___x_450_ = lean_apply_2(v_liftWith_448_, lean_box(0), v___f_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_00_u03b1_453_, lean_object* v_f_454_){
_start:
{
lean_object* v_liftWith_455_; lean_object* v___f_456_; lean_object* v___x_457_; 
v_liftWith_455_ = lean_ctor_get(v_inst_451_, 0);
lean_inc(v_liftWith_455_);
lean_dec_ref(v_inst_451_);
v___f_456_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__2), 3, 2);
lean_closure_set(v___f_456_, 0, v_inst_452_);
lean_closure_set(v___f_456_, 1, v_f_454_);
v___x_457_ = lean_apply_2(v_liftWith_455_, lean_box(0), v___f_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_00_u03b1_460_, lean_object* v___y_461_){
_start:
{
lean_object* v_restoreM_462_; lean_object* v_restoreM_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_restoreM_462_ = lean_ctor_get(v_inst_458_, 1);
lean_inc(v_restoreM_462_);
lean_dec_ref(v_inst_458_);
v_restoreM_463_ = lean_ctor_get(v_inst_459_, 1);
lean_inc(v_restoreM_463_);
lean_dec_ref(v_inst_459_);
v___x_464_ = lean_apply_2(v_restoreM_463_, lean_box(0), v___y_461_);
v___x_465_ = lean_apply_2(v_restoreM_462_, lean_box(0), v___x_464_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg(lean_object* v_inst_466_, lean_object* v_inst_467_){
_start:
{
lean_object* v___f_468_; lean_object* v___f_469_; lean_object* v___x_470_; 
lean_inc_ref(v_inst_467_);
lean_inc_ref(v_inst_466_);
v___f_468_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_468_, 0, v_inst_466_);
lean_closure_set(v___f_468_, 1, v_inst_467_);
v___f_469_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_469_, 0, v_inst_466_);
lean_closure_set(v___f_469_, 1, v_inst_467_);
v___x_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_470_, 0, v___f_468_);
lean_ctor_set(v___x_470_, 1, v___f_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl(lean_object* v_m_471_, lean_object* v_n_472_, lean_object* v_o_473_, lean_object* v_inst_474_, lean_object* v_inst_475_){
_start:
{
lean_object* v___f_476_; lean_object* v___f_477_; lean_object* v___x_478_; 
lean_inc_ref(v_inst_475_);
lean_inc_ref(v_inst_474_);
v___f_476_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_476_, 0, v_inst_474_);
lean_closure_set(v___f_476_, 1, v_inst_475_);
v___f_477_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_477_, 0, v_inst_474_);
lean_closure_set(v___f_477_, 1, v_inst_475_);
v___x_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_478_, 0, v___f_476_);
lean_ctor_set(v___x_478_, 1, v___f_477_);
return v___x_478_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__0(lean_object* v_00_u03b2_479_, lean_object* v_x_480_){
_start:
{
lean_inc(v_x_480_);
return v_x_480_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__0___boxed(lean_object* v_00_u03b2_481_, lean_object* v_x_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_instMonadControlTOfPure___redArg___lam__0(v_00_u03b2_481_, v_x_482_);
lean_dec(v_x_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__1(lean_object* v___f_484_, lean_object* v_00_u03b1_485_, lean_object* v_f_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = lean_apply_1(v_f_486_, v___f_484_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__2(lean_object* v_inst_488_, lean_object* v_00_u03b1_489_, lean_object* v_x_490_){
_start:
{
lean_object* v___x_491_; 
v___x_491_ = lean_apply_2(v_inst_488_, lean_box(0), v_x_490_);
return v___x_491_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg(lean_object* v_inst_495_){
_start:
{
lean_object* v___f_496_; lean_object* v___f_497_; lean_object* v___x_498_; 
v___f_496_ = ((lean_object*)(l_instMonadControlTOfPure___redArg___closed__1));
v___f_497_ = lean_alloc_closure((void*)(l_instMonadControlTOfPure___redArg___lam__2), 3, 1);
lean_closure_set(v___f_497_, 0, v_inst_495_);
v___x_498_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_498_, 0, v___f_496_);
lean_ctor_set(v___x_498_, 1, v___f_497_);
return v___x_498_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure(lean_object* v_m_499_, lean_object* v_inst_500_){
_start:
{
lean_object* v___x_501_; 
v___x_501_ = l_instMonadControlTOfPure___redArg(v_inst_500_);
return v___x_501_;
}
}
LEAN_EXPORT lean_object* l_controlAt___redArg(lean_object* v_inst_502_, lean_object* v_inst_503_, lean_object* v_f_504_){
_start:
{
lean_object* v_liftWith_505_; lean_object* v_restoreM_506_; lean_object* v___x_507_; lean_object* v___x_508_; lean_object* v___x_509_; 
v_liftWith_505_ = lean_ctor_get(v_inst_502_, 0);
lean_inc(v_liftWith_505_);
v_restoreM_506_ = lean_ctor_get(v_inst_502_, 1);
lean_inc(v_restoreM_506_);
lean_dec_ref(v_inst_502_);
v___x_507_ = lean_apply_2(v_liftWith_505_, lean_box(0), v_f_504_);
v___x_508_ = lean_apply_1(v_restoreM_506_, lean_box(0));
v___x_509_ = lean_apply_4(v_inst_503_, lean_box(0), lean_box(0), v___x_507_, v___x_508_);
return v___x_509_;
}
}
LEAN_EXPORT lean_object* l_controlAt(lean_object* v_m_510_, lean_object* v_n_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_00_u03b1_514_, lean_object* v_f_515_){
_start:
{
lean_object* v_liftWith_516_; lean_object* v_restoreM_517_; lean_object* v___x_518_; lean_object* v___x_519_; lean_object* v___x_520_; 
v_liftWith_516_ = lean_ctor_get(v_inst_512_, 0);
lean_inc(v_liftWith_516_);
v_restoreM_517_ = lean_ctor_get(v_inst_512_, 1);
lean_inc(v_restoreM_517_);
lean_dec_ref(v_inst_512_);
v___x_518_ = lean_apply_2(v_liftWith_516_, lean_box(0), v_f_515_);
v___x_519_ = lean_apply_1(v_restoreM_517_, lean_box(0));
v___x_520_ = lean_apply_4(v_inst_513_, lean_box(0), lean_box(0), v___x_518_, v___x_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l_control___redArg(lean_object* v_inst_521_, lean_object* v_inst_522_, lean_object* v_f_523_){
_start:
{
lean_object* v_liftWith_524_; lean_object* v_restoreM_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
v_liftWith_524_ = lean_ctor_get(v_inst_521_, 0);
lean_inc(v_liftWith_524_);
v_restoreM_525_ = lean_ctor_get(v_inst_521_, 1);
lean_inc(v_restoreM_525_);
lean_dec_ref(v_inst_521_);
v___x_526_ = lean_apply_2(v_liftWith_524_, lean_box(0), v_f_523_);
v___x_527_ = lean_apply_1(v_restoreM_525_, lean_box(0));
v___x_528_ = lean_apply_4(v_inst_522_, lean_box(0), lean_box(0), v___x_526_, v___x_527_);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l_control(lean_object* v_m_529_, lean_object* v_n_530_, lean_object* v_inst_531_, lean_object* v_inst_532_, lean_object* v_00_u03b1_533_, lean_object* v_f_534_){
_start:
{
lean_object* v_liftWith_535_; lean_object* v_restoreM_536_; lean_object* v___x_537_; lean_object* v___x_538_; lean_object* v___x_539_; 
v_liftWith_535_ = lean_ctor_get(v_inst_531_, 0);
lean_inc(v_liftWith_535_);
v_restoreM_536_ = lean_ctor_get(v_inst_531_, 1);
lean_inc(v_restoreM_536_);
lean_dec_ref(v_inst_531_);
v___x_537_ = lean_apply_2(v_liftWith_535_, lean_box(0), v_f_534_);
v___x_538_ = lean_apply_1(v_restoreM_536_, lean_box(0));
v___x_539_ = lean_apply_4(v_inst_532_, lean_box(0), lean_box(0), v___x_537_, v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliRight___redArg(lean_object* v_inst_540_, lean_object* v_f_u2081_541_, lean_object* v_f_u2082_542_, lean_object* v_a_543_){
_start:
{
lean_object* v___x_544_; lean_object* v___x_545_; 
v___x_544_ = lean_apply_1(v_f_u2081_541_, v_a_543_);
v___x_545_ = lean_apply_4(v_inst_540_, lean_box(0), lean_box(0), v___x_544_, v_f_u2082_542_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliRight(lean_object* v_00_u03b1_546_, lean_object* v_m_547_, lean_object* v_00_u03b2_548_, lean_object* v_00_u03b3_549_, lean_object* v_inst_550_, lean_object* v_f_u2081_551_, lean_object* v_f_u2082_552_, lean_object* v_a_553_){
_start:
{
lean_object* v___x_554_; lean_object* v___x_555_; 
v___x_554_ = lean_apply_1(v_f_u2081_551_, v_a_553_);
v___x_555_ = lean_apply_4(v_inst_550_, lean_box(0), lean_box(0), v___x_554_, v_f_u2082_552_);
return v___x_555_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliLeft___redArg(lean_object* v_inst_556_, lean_object* v_f_u2082_557_, lean_object* v_f_u2081_558_, lean_object* v_a_559_){
_start:
{
lean_object* v___x_560_; lean_object* v___x_561_; 
v___x_560_ = lean_apply_1(v_f_u2081_558_, v_a_559_);
v___x_561_ = lean_apply_4(v_inst_556_, lean_box(0), lean_box(0), v___x_560_, v_f_u2082_557_);
return v___x_561_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliLeft(lean_object* v_00_u03b1_562_, lean_object* v_m_563_, lean_object* v_00_u03b2_564_, lean_object* v_00_u03b3_565_, lean_object* v_inst_566_, lean_object* v_f_u2082_567_, lean_object* v_f_u2081_568_, lean_object* v_a_569_){
_start:
{
lean_object* v___x_570_; lean_object* v___x_571_; 
v___x_570_ = lean_apply_1(v_f_u2081_568_, v_a_569_);
v___x_571_ = lean_apply_4(v_inst_566_, lean_box(0), lean_box(0), v___x_570_, v_f_u2082_567_);
return v___x_571_;
}
}
LEAN_EXPORT lean_object* l_Bind_bindLeft___redArg(lean_object* v_inst_572_, lean_object* v_f_573_, lean_object* v_ma_574_){
_start:
{
lean_object* v___x_575_; 
v___x_575_ = lean_apply_4(v_inst_572_, lean_box(0), lean_box(0), v_ma_574_, v_f_573_);
return v___x_575_;
}
}
LEAN_EXPORT lean_object* l_Bind_bindLeft(lean_object* v_00_u03b1_576_, lean_object* v_m_577_, lean_object* v_00_u03b2_578_, lean_object* v_inst_579_, lean_object* v_f_580_, lean_object* v_ma_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = lean_apply_4(v_inst_579_, lean_box(0), lean_box(0), v_ma_581_, v_f_580_);
return v___x_582_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_603_; lean_object* v___x_604_; 
v___x_603_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0));
v___x_604_ = l_String_toRawSubstring_x27(v___x_603_);
return v___x_604_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(lean_object* v_x_616_, lean_object* v_a_617_, lean_object* v_a_618_){
_start:
{
lean_object* v___x_619_; uint8_t v___x_620_; 
v___x_619_ = ((lean_object*)(l_term___x3e_x3d_x3e___00__closed__1));
lean_inc(v_x_616_);
v___x_620_ = l_Lean_Syntax_isOfKind(v_x_616_, v___x_619_);
if (v___x_620_ == 0)
{
lean_object* v___x_621_; lean_object* v___x_622_; 
lean_dec(v_x_616_);
v___x_621_ = lean_box(1);
v___x_622_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_622_, 0, v___x_621_);
lean_ctor_set(v___x_622_, 1, v_a_618_);
return v___x_622_;
}
else
{
lean_object* v_quotContext_623_; lean_object* v_currMacroScope_624_; lean_object* v_ref_625_; lean_object* v___x_626_; lean_object* v___x_627_; lean_object* v___x_628_; lean_object* v___x_629_; uint8_t v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; lean_object* v___x_633_; lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; lean_object* v___x_637_; lean_object* v___x_638_; lean_object* v___x_639_; lean_object* v___x_640_; lean_object* v___x_641_; 
v_quotContext_623_ = lean_ctor_get(v_a_617_, 1);
v_currMacroScope_624_ = lean_ctor_get(v_a_617_, 2);
v_ref_625_ = lean_ctor_get(v_a_617_, 5);
v___x_626_ = lean_unsigned_to_nat(0u);
v___x_627_ = l_Lean_Syntax_getArg(v_x_616_, v___x_626_);
v___x_628_ = lean_unsigned_to_nat(2u);
v___x_629_ = l_Lean_Syntax_getArg(v_x_616_, v___x_628_);
lean_dec(v_x_616_);
v___x_630_ = 0;
v___x_631_ = l_Lean_SourceInfo_fromRef(v_ref_625_, v___x_630_);
v___x_632_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_633_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1);
v___x_634_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4));
lean_inc(v_currMacroScope_624_);
lean_inc(v_quotContext_623_);
v___x_635_ = l_Lean_addMacroScope(v_quotContext_623_, v___x_634_, v_currMacroScope_624_);
v___x_636_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6));
lean_inc_n(v___x_631_, 2);
v___x_637_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_637_, 0, v___x_631_);
lean_ctor_set(v___x_637_, 1, v___x_633_);
lean_ctor_set(v___x_637_, 2, v___x_635_);
lean_ctor_set(v___x_637_, 3, v___x_636_);
v___x_638_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
v___x_639_ = l_Lean_Syntax_node2(v___x_631_, v___x_638_, v___x_627_, v___x_629_);
v___x_640_ = l_Lean_Syntax_node2(v___x_631_, v___x_632_, v___x_637_, v___x_639_);
v___x_641_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_641_, 0, v___x_640_);
lean_ctor_set(v___x_641_, 1, v_a_618_);
return v___x_641_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___boxed(lean_object* v_x_642_, lean_object* v_a_643_, lean_object* v_a_644_){
_start:
{
lean_object* v_res_645_; 
v_res_645_ = l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(v_x_642_, v_a_643_, v_a_644_);
lean_dec_ref(v_a_643_);
return v_res_645_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(lean_object* v_x_646_, lean_object* v_a_647_, lean_object* v_a_648_){
_start:
{
lean_object* v___x_649_; uint8_t v___x_650_; 
v___x_649_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_646_);
v___x_650_ = l_Lean_Syntax_isOfKind(v_x_646_, v___x_649_);
if (v___x_650_ == 0)
{
lean_object* v___x_651_; lean_object* v___x_652_; 
lean_dec(v_x_646_);
v___x_651_ = lean_box(0);
v___x_652_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_652_, 0, v___x_651_);
lean_ctor_set(v___x_652_, 1, v_a_648_);
return v___x_652_;
}
else
{
lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; uint8_t v___x_656_; 
v___x_653_ = lean_unsigned_to_nat(0u);
v___x_654_ = l_Lean_Syntax_getArg(v_x_646_, v___x_653_);
v___x_655_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_654_);
v___x_656_ = l_Lean_Syntax_isOfKind(v___x_654_, v___x_655_);
if (v___x_656_ == 0)
{
lean_object* v___x_657_; lean_object* v___x_658_; 
lean_dec(v___x_654_);
lean_dec(v_x_646_);
v___x_657_ = lean_box(0);
v___x_658_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_658_, 0, v___x_657_);
lean_ctor_set(v___x_658_, 1, v_a_648_);
return v___x_658_;
}
else
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; uint8_t v___x_662_; 
v___x_659_ = lean_unsigned_to_nat(1u);
v___x_660_ = l_Lean_Syntax_getArg(v_x_646_, v___x_659_);
lean_dec(v_x_646_);
v___x_661_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_660_);
v___x_662_ = l_Lean_Syntax_matchesNull(v___x_660_, v___x_661_);
if (v___x_662_ == 0)
{
lean_object* v___x_663_; lean_object* v___x_664_; 
lean_dec(v___x_660_);
lean_dec(v___x_654_);
v___x_663_ = lean_box(0);
v___x_664_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_664_, 0, v___x_663_);
lean_ctor_set(v___x_664_, 1, v_a_648_);
return v___x_664_;
}
else
{
lean_object* v___x_665_; lean_object* v___x_666_; lean_object* v_ref_667_; uint8_t v___x_668_; lean_object* v___x_669_; lean_object* v___x_670_; lean_object* v___x_671_; lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_665_ = l_Lean_Syntax_getArg(v___x_660_, v___x_653_);
v___x_666_ = l_Lean_Syntax_getArg(v___x_660_, v___x_659_);
lean_dec(v___x_660_);
v_ref_667_ = l_Lean_replaceRef(v___x_654_, v_a_647_);
lean_dec(v___x_654_);
v___x_668_ = 0;
v___x_669_ = l_Lean_SourceInfo_fromRef(v_ref_667_, v___x_668_);
lean_dec(v_ref_667_);
v___x_670_ = ((lean_object*)(l_term___x3e_x3d_x3e___00__closed__1));
v___x_671_ = ((lean_object*)(l_term___x3e_x3d_x3e___00__closed__2));
lean_inc(v___x_669_);
v___x_672_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_672_, 0, v___x_669_);
lean_ctor_set(v___x_672_, 1, v___x_671_);
v___x_673_ = l_Lean_Syntax_node3(v___x_669_, v___x_670_, v___x_665_, v___x_672_, v___x_666_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_673_);
lean_ctor_set(v___x_674_, 1, v_a_648_);
return v___x_674_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1___boxed(lean_object* v_x_675_, lean_object* v_a_676_, lean_object* v_a_677_){
_start:
{
lean_object* v_res_678_; 
v_res_678_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(v_x_675_, v_a_676_, v_a_677_);
lean_dec(v_a_676_);
return v_res_678_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_696_; lean_object* v___x_697_; 
v___x_696_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0));
v___x_697_ = l_String_toRawSubstring_x27(v___x_696_);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(lean_object* v_x_708_, lean_object* v_a_709_, lean_object* v_a_710_){
_start:
{
lean_object* v___x_711_; uint8_t v___x_712_; 
v___x_711_ = ((lean_object*)(l_term___x3c_x3d_x3c___00__closed__1));
lean_inc(v_x_708_);
v___x_712_ = l_Lean_Syntax_isOfKind(v_x_708_, v___x_711_);
if (v___x_712_ == 0)
{
lean_object* v___x_713_; lean_object* v___x_714_; 
lean_dec(v_x_708_);
v___x_713_ = lean_box(1);
v___x_714_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v_a_710_);
return v___x_714_;
}
else
{
lean_object* v_quotContext_715_; lean_object* v_currMacroScope_716_; lean_object* v_ref_717_; lean_object* v___x_718_; lean_object* v___x_719_; lean_object* v___x_720_; lean_object* v___x_721_; uint8_t v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; lean_object* v___x_725_; lean_object* v___x_726_; lean_object* v___x_727_; lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; lean_object* v___x_731_; lean_object* v___x_732_; lean_object* v___x_733_; 
v_quotContext_715_ = lean_ctor_get(v_a_709_, 1);
v_currMacroScope_716_ = lean_ctor_get(v_a_709_, 2);
v_ref_717_ = lean_ctor_get(v_a_709_, 5);
v___x_718_ = lean_unsigned_to_nat(0u);
v___x_719_ = l_Lean_Syntax_getArg(v_x_708_, v___x_718_);
v___x_720_ = lean_unsigned_to_nat(2u);
v___x_721_ = l_Lean_Syntax_getArg(v_x_708_, v___x_720_);
lean_dec(v_x_708_);
v___x_722_ = 0;
v___x_723_ = l_Lean_SourceInfo_fromRef(v_ref_717_, v___x_722_);
v___x_724_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_725_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1);
v___x_726_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3));
lean_inc(v_currMacroScope_716_);
lean_inc(v_quotContext_715_);
v___x_727_ = l_Lean_addMacroScope(v_quotContext_715_, v___x_726_, v_currMacroScope_716_);
v___x_728_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5));
lean_inc_n(v___x_723_, 2);
v___x_729_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_729_, 0, v___x_723_);
lean_ctor_set(v___x_729_, 1, v___x_725_);
lean_ctor_set(v___x_729_, 2, v___x_727_);
lean_ctor_set(v___x_729_, 3, v___x_728_);
v___x_730_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
v___x_731_ = l_Lean_Syntax_node2(v___x_723_, v___x_730_, v___x_719_, v___x_721_);
v___x_732_ = l_Lean_Syntax_node2(v___x_723_, v___x_724_, v___x_729_, v___x_731_);
v___x_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v_a_710_);
return v___x_733_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___boxed(lean_object* v_x_734_, lean_object* v_a_735_, lean_object* v_a_736_){
_start:
{
lean_object* v_res_737_; 
v_res_737_ = l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(v_x_734_, v_a_735_, v_a_736_);
lean_dec_ref(v_a_735_);
return v_res_737_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(lean_object* v_x_738_, lean_object* v_a_739_, lean_object* v_a_740_){
_start:
{
lean_object* v___x_741_; uint8_t v___x_742_; 
v___x_741_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_738_);
v___x_742_ = l_Lean_Syntax_isOfKind(v_x_738_, v___x_741_);
if (v___x_742_ == 0)
{
lean_object* v___x_743_; lean_object* v___x_744_; 
lean_dec(v_x_738_);
v___x_743_ = lean_box(0);
v___x_744_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_744_, 0, v___x_743_);
lean_ctor_set(v___x_744_, 1, v_a_740_);
return v___x_744_;
}
else
{
lean_object* v___x_745_; lean_object* v___x_746_; lean_object* v___x_747_; uint8_t v___x_748_; 
v___x_745_ = lean_unsigned_to_nat(0u);
v___x_746_ = l_Lean_Syntax_getArg(v_x_738_, v___x_745_);
v___x_747_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_746_);
v___x_748_ = l_Lean_Syntax_isOfKind(v___x_746_, v___x_747_);
if (v___x_748_ == 0)
{
lean_object* v___x_749_; lean_object* v___x_750_; 
lean_dec(v___x_746_);
lean_dec(v_x_738_);
v___x_749_ = lean_box(0);
v___x_750_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_750_, 0, v___x_749_);
lean_ctor_set(v___x_750_, 1, v_a_740_);
return v___x_750_;
}
else
{
lean_object* v___x_751_; lean_object* v___x_752_; lean_object* v___x_753_; uint8_t v___x_754_; 
v___x_751_ = lean_unsigned_to_nat(1u);
v___x_752_ = l_Lean_Syntax_getArg(v_x_738_, v___x_751_);
lean_dec(v_x_738_);
v___x_753_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_752_);
v___x_754_ = l_Lean_Syntax_matchesNull(v___x_752_, v___x_753_);
if (v___x_754_ == 0)
{
lean_object* v___x_755_; lean_object* v___x_756_; 
lean_dec(v___x_752_);
lean_dec(v___x_746_);
v___x_755_ = lean_box(0);
v___x_756_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_756_, 0, v___x_755_);
lean_ctor_set(v___x_756_, 1, v_a_740_);
return v___x_756_;
}
else
{
lean_object* v___x_757_; lean_object* v___x_758_; lean_object* v_ref_759_; uint8_t v___x_760_; lean_object* v___x_761_; lean_object* v___x_762_; lean_object* v___x_763_; lean_object* v___x_764_; lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_757_ = l_Lean_Syntax_getArg(v___x_752_, v___x_745_);
v___x_758_ = l_Lean_Syntax_getArg(v___x_752_, v___x_751_);
lean_dec(v___x_752_);
v_ref_759_ = l_Lean_replaceRef(v___x_746_, v_a_739_);
lean_dec(v___x_746_);
v___x_760_ = 0;
v___x_761_ = l_Lean_SourceInfo_fromRef(v_ref_759_, v___x_760_);
lean_dec(v_ref_759_);
v___x_762_ = ((lean_object*)(l_term___x3c_x3d_x3c___00__closed__1));
v___x_763_ = ((lean_object*)(l_term___x3c_x3d_x3c___00__closed__2));
lean_inc(v___x_761_);
v___x_764_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_764_, 0, v___x_761_);
lean_ctor_set(v___x_764_, 1, v___x_763_);
v___x_765_ = l_Lean_Syntax_node3(v___x_761_, v___x_762_, v___x_757_, v___x_764_, v___x_758_);
v___x_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_766_, 0, v___x_765_);
lean_ctor_set(v___x_766_, 1, v_a_740_);
return v___x_766_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1___boxed(lean_object* v_x_767_, lean_object* v_a_768_, lean_object* v_a_769_){
_start:
{
lean_object* v_res_770_; 
v_res_770_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(v_x_767_, v_a_768_, v_a_769_);
lean_dec(v_a_768_);
return v_res_770_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_788_; lean_object* v___x_789_; 
v___x_788_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0));
v___x_789_ = l_String_toRawSubstring_x27(v___x_788_);
return v___x_789_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(lean_object* v_x_800_, lean_object* v_a_801_, lean_object* v_a_802_){
_start:
{
lean_object* v___x_803_; uint8_t v___x_804_; 
v___x_803_ = ((lean_object*)(l_term___x3d_x3c_x3c___00__closed__1));
lean_inc(v_x_800_);
v___x_804_ = l_Lean_Syntax_isOfKind(v_x_800_, v___x_803_);
if (v___x_804_ == 0)
{
lean_object* v___x_805_; lean_object* v___x_806_; 
lean_dec(v_x_800_);
v___x_805_ = lean_box(1);
v___x_806_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_806_, 0, v___x_805_);
lean_ctor_set(v___x_806_, 1, v_a_802_);
return v___x_806_;
}
else
{
lean_object* v_quotContext_807_; lean_object* v_currMacroScope_808_; lean_object* v_ref_809_; lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; lean_object* v___x_813_; uint8_t v___x_814_; lean_object* v___x_815_; lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; lean_object* v___x_819_; lean_object* v___x_820_; lean_object* v___x_821_; lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v___x_824_; lean_object* v___x_825_; 
v_quotContext_807_ = lean_ctor_get(v_a_801_, 1);
v_currMacroScope_808_ = lean_ctor_get(v_a_801_, 2);
v_ref_809_ = lean_ctor_get(v_a_801_, 5);
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = l_Lean_Syntax_getArg(v_x_800_, v___x_810_);
v___x_812_ = lean_unsigned_to_nat(2u);
v___x_813_ = l_Lean_Syntax_getArg(v_x_800_, v___x_812_);
lean_dec(v_x_800_);
v___x_814_ = 0;
v___x_815_ = l_Lean_SourceInfo_fromRef(v_ref_809_, v___x_814_);
v___x_816_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_817_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1);
v___x_818_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3));
lean_inc(v_currMacroScope_808_);
lean_inc(v_quotContext_807_);
v___x_819_ = l_Lean_addMacroScope(v_quotContext_807_, v___x_818_, v_currMacroScope_808_);
v___x_820_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5));
lean_inc_n(v___x_815_, 2);
v___x_821_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_821_, 0, v___x_815_);
lean_ctor_set(v___x_821_, 1, v___x_817_);
lean_ctor_set(v___x_821_, 2, v___x_819_);
lean_ctor_set(v___x_821_, 3, v___x_820_);
v___x_822_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
v___x_823_ = l_Lean_Syntax_node2(v___x_815_, v___x_822_, v___x_811_, v___x_813_);
v___x_824_ = l_Lean_Syntax_node2(v___x_815_, v___x_816_, v___x_821_, v___x_823_);
v___x_825_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_825_, 0, v___x_824_);
lean_ctor_set(v___x_825_, 1, v_a_802_);
return v___x_825_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___boxed(lean_object* v_x_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(v_x_826_, v_a_827_, v_a_828_);
lean_dec_ref(v_a_827_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(lean_object* v_x_830_, lean_object* v_a_831_, lean_object* v_a_832_){
_start:
{
lean_object* v___x_833_; uint8_t v___x_834_; 
v___x_833_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_830_);
v___x_834_ = l_Lean_Syntax_isOfKind(v_x_830_, v___x_833_);
if (v___x_834_ == 0)
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v_x_830_);
v___x_835_ = lean_box(0);
v___x_836_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_836_, 0, v___x_835_);
lean_ctor_set(v___x_836_, 1, v_a_832_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; lean_object* v___x_838_; lean_object* v___x_839_; uint8_t v___x_840_; 
v___x_837_ = lean_unsigned_to_nat(0u);
v___x_838_ = l_Lean_Syntax_getArg(v_x_830_, v___x_837_);
v___x_839_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_838_);
v___x_840_ = l_Lean_Syntax_isOfKind(v___x_838_, v___x_839_);
if (v___x_840_ == 0)
{
lean_object* v___x_841_; lean_object* v___x_842_; 
lean_dec(v___x_838_);
lean_dec(v_x_830_);
v___x_841_ = lean_box(0);
v___x_842_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_842_, 0, v___x_841_);
lean_ctor_set(v___x_842_, 1, v_a_832_);
return v___x_842_;
}
else
{
lean_object* v___x_843_; lean_object* v___x_844_; lean_object* v___x_845_; uint8_t v___x_846_; 
v___x_843_ = lean_unsigned_to_nat(1u);
v___x_844_ = l_Lean_Syntax_getArg(v_x_830_, v___x_843_);
lean_dec(v_x_830_);
v___x_845_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_844_);
v___x_846_ = l_Lean_Syntax_matchesNull(v___x_844_, v___x_845_);
if (v___x_846_ == 0)
{
lean_object* v___x_847_; lean_object* v___x_848_; 
lean_dec(v___x_844_);
lean_dec(v___x_838_);
v___x_847_ = lean_box(0);
v___x_848_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_848_, 0, v___x_847_);
lean_ctor_set(v___x_848_, 1, v_a_832_);
return v___x_848_;
}
else
{
lean_object* v___x_849_; lean_object* v___x_850_; lean_object* v_ref_851_; uint8_t v___x_852_; lean_object* v___x_853_; lean_object* v___x_854_; lean_object* v___x_855_; lean_object* v___x_856_; lean_object* v___x_857_; lean_object* v___x_858_; 
v___x_849_ = l_Lean_Syntax_getArg(v___x_844_, v___x_837_);
v___x_850_ = l_Lean_Syntax_getArg(v___x_844_, v___x_843_);
lean_dec(v___x_844_);
v_ref_851_ = l_Lean_replaceRef(v___x_838_, v_a_831_);
lean_dec(v___x_838_);
v___x_852_ = 0;
v___x_853_ = l_Lean_SourceInfo_fromRef(v_ref_851_, v___x_852_);
lean_dec(v_ref_851_);
v___x_854_ = ((lean_object*)(l_term___x3d_x3c_x3c___00__closed__1));
v___x_855_ = ((lean_object*)(l_term___x3d_x3c_x3c___00__closed__2));
lean_inc(v___x_853_);
v___x_856_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_856_, 0, v___x_853_);
lean_ctor_set(v___x_856_, 1, v___x_855_);
v___x_857_ = l_Lean_Syntax_node3(v___x_853_, v___x_854_, v___x_849_, v___x_856_, v___x_850_);
v___x_858_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_858_, 0, v___x_857_);
lean_ctor_set(v___x_858_, 1, v_a_832_);
return v___x_858_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1___boxed(lean_object* v_x_859_, lean_object* v_a_860_, lean_object* v_a_861_){
_start:
{
lean_object* v_res_862_; 
v_res_862_ = l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(v_x_859_, v_a_860_, v_a_861_);
lean_dec(v_a_860_);
return v_res_862_;
}
}
lean_object* runtime_initialize_Init_Core(uint8_t builtin);
lean_object* runtime_initialize_Init_BinderNameHint(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Control_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
