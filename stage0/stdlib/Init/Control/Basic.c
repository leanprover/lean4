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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_String_toRawSubstring_x27(lean_object*);
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
lean_dec_ref(v_a_95_);
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
lean_inc(v_quotContext_101_);
v_currMacroScope_102_ = lean_ctor_get(v_a_95_, 2);
lean_inc(v_currMacroScope_102_);
v_ref_103_ = lean_ctor_get(v_a_95_, 5);
lean_inc(v_ref_103_);
lean_dec_ref(v_a_95_);
v___x_104_ = lean_unsigned_to_nat(0u);
v___x_105_ = l_Lean_Syntax_getArg(v_x_94_, v___x_104_);
v___x_106_ = lean_unsigned_to_nat(2u);
v___x_107_ = l_Lean_Syntax_getArg(v_x_94_, v___x_106_);
lean_dec(v_x_94_);
v___x_108_ = 0;
v___x_109_ = l_Lean_SourceInfo_fromRef(v_ref_103_, v___x_108_);
lean_dec(v_ref_103_);
v___x_110_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_111_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6, &l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__6);
v___x_112_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__9));
v___x_113_ = l_Lean_addMacroScope(v_quotContext_101_, v___x_112_, v_currMacroScope_102_);
v___x_114_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__11));
lean_inc(v___x_109_);
v___x_115_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_115_, 0, v___x_109_);
lean_ctor_set(v___x_115_, 1, v___x_111_);
lean_ctor_set(v___x_115_, 2, v___x_113_);
lean_ctor_set(v___x_115_, 3, v___x_114_);
v___x_116_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
lean_inc(v___x_109_);
v___x_117_ = l_Lean_Syntax_node2(v___x_109_, v___x_116_, v___x_105_, v___x_107_);
v___x_118_ = l_Lean_Syntax_node2(v___x_109_, v___x_110_, v___x_115_, v___x_117_);
v___x_119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_119_, 0, v___x_118_);
lean_ctor_set(v___x_119_, 1, v_a_96_);
return v___x_119_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1(lean_object* v_x_123_, lean_object* v_a_124_, lean_object* v_a_125_){
_start:
{
lean_object* v___x_126_; uint8_t v___x_127_; 
v___x_126_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_123_);
v___x_127_ = l_Lean_Syntax_isOfKind(v_x_123_, v___x_126_);
if (v___x_127_ == 0)
{
lean_object* v___x_128_; lean_object* v___x_129_; 
lean_dec(v_x_123_);
v___x_128_ = lean_box(0);
v___x_129_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_129_, 0, v___x_128_);
lean_ctor_set(v___x_129_, 1, v_a_125_);
return v___x_129_;
}
else
{
lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_130_ = lean_unsigned_to_nat(0u);
v___x_131_ = l_Lean_Syntax_getArg(v_x_123_, v___x_130_);
v___x_132_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_131_);
v___x_133_ = l_Lean_Syntax_isOfKind(v___x_131_, v___x_132_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v___x_135_; 
lean_dec(v___x_131_);
lean_dec(v_x_123_);
v___x_134_ = lean_box(0);
v___x_135_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_135_, 0, v___x_134_);
lean_ctor_set(v___x_135_, 1, v_a_125_);
return v___x_135_;
}
else
{
lean_object* v___x_136_; lean_object* v___x_137_; lean_object* v___x_138_; uint8_t v___x_139_; 
v___x_136_ = lean_unsigned_to_nat(1u);
v___x_137_ = l_Lean_Syntax_getArg(v_x_123_, v___x_136_);
lean_dec(v_x_123_);
v___x_138_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_137_);
v___x_139_ = l_Lean_Syntax_matchesNull(v___x_137_, v___x_138_);
if (v___x_139_ == 0)
{
lean_object* v___x_140_; lean_object* v___x_141_; 
lean_dec(v___x_137_);
lean_dec(v___x_131_);
v___x_140_ = lean_box(0);
v___x_141_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_141_, 0, v___x_140_);
lean_ctor_set(v___x_141_, 1, v_a_125_);
return v___x_141_;
}
else
{
lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v_ref_144_; uint8_t v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_148_; lean_object* v___x_149_; lean_object* v___x_150_; lean_object* v___x_151_; 
v___x_142_ = l_Lean_Syntax_getArg(v___x_137_, v___x_130_);
v___x_143_ = l_Lean_Syntax_getArg(v___x_137_, v___x_136_);
lean_dec(v___x_137_);
v_ref_144_ = l_Lean_replaceRef(v___x_131_, v_a_124_);
lean_dec(v___x_131_);
v___x_145_ = 0;
v___x_146_ = l_Lean_SourceInfo_fromRef(v_ref_144_, v___x_145_);
lean_dec(v_ref_144_);
v___x_147_ = ((lean_object*)(l_term___x3c_x26_x3e___00__closed__1));
v___x_148_ = ((lean_object*)(l_term___x3c_x26_x3e___00__closed__4));
lean_inc(v___x_146_);
v___x_149_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_149_, 0, v___x_146_);
lean_ctor_set(v___x_149_, 1, v___x_148_);
v___x_150_ = l_Lean_Syntax_node3(v___x_146_, v___x_147_, v___x_142_, v___x_149_, v___x_143_);
v___x_151_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_151_, 0, v___x_150_);
lean_ctor_set(v___x_151_, 1, v_a_125_);
return v___x_151_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___boxed(lean_object* v_x_152_, lean_object* v_a_153_, lean_object* v_a_154_){
_start:
{
lean_object* v_res_155_; 
v_res_155_ = l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1(v_x_152_, v_a_153_, v_a_154_);
lean_dec(v_a_153_);
return v_res_155_;
}
}
LEAN_EXPORT lean_object* l_Functor_discard___redArg(lean_object* v_inst_156_, lean_object* v_x_157_){
_start:
{
lean_object* v_mapConst_158_; lean_object* v___x_159_; lean_object* v___x_160_; 
v_mapConst_158_ = lean_ctor_get(v_inst_156_, 1);
lean_inc(v_mapConst_158_);
lean_dec_ref(v_inst_156_);
v___x_159_ = lean_box(0);
v___x_160_ = lean_apply_4(v_mapConst_158_, lean_box(0), lean_box(0), v___x_159_, v_x_157_);
return v___x_160_;
}
}
LEAN_EXPORT lean_object* l_Functor_discard(lean_object* v_f_161_, lean_object* v_00_u03b1_162_, lean_object* v_inst_163_, lean_object* v_x_164_){
_start:
{
lean_object* v_mapConst_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v_mapConst_165_ = lean_ctor_get(v_inst_163_, 1);
lean_inc(v_mapConst_165_);
lean_dec_ref(v_inst_163_);
v___x_166_ = lean_box(0);
v___x_167_ = lean_apply_4(v_mapConst_165_, lean_box(0), lean_box(0), v___x_166_, v_x_164_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_instOrElseOfAlternative___redArg(lean_object* v_inst_168_){
_start:
{
lean_object* v_orElse_169_; lean_object* v___x_170_; 
v_orElse_169_ = lean_ctor_get(v_inst_168_, 2);
lean_inc(v_orElse_169_);
lean_dec_ref(v_inst_168_);
v___x_170_ = lean_apply_1(v_orElse_169_, lean_box(0));
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_instOrElseOfAlternative(lean_object* v_f_171_, lean_object* v_00_u03b1_172_, lean_object* v_inst_173_){
_start:
{
lean_object* v___x_174_; 
v___x_174_ = l_instOrElseOfAlternative___redArg(v_inst_173_);
return v___x_174_;
}
}
LEAN_EXPORT lean_object* l_guard___redArg(lean_object* v_inst_175_, uint8_t v_inst_176_){
_start:
{
if (v_inst_176_ == 0)
{
lean_object* v_failure_177_; lean_object* v___x_178_; 
v_failure_177_ = lean_ctor_get(v_inst_175_, 1);
lean_inc(v_failure_177_);
lean_dec_ref(v_inst_175_);
v___x_178_ = lean_apply_1(v_failure_177_, lean_box(0));
return v___x_178_;
}
else
{
lean_object* v_toApplicative_179_; lean_object* v_toPure_180_; lean_object* v___x_181_; lean_object* v___x_182_; 
v_toApplicative_179_ = lean_ctor_get(v_inst_175_, 0);
lean_inc_ref(v_toApplicative_179_);
lean_dec_ref(v_inst_175_);
v_toPure_180_ = lean_ctor_get(v_toApplicative_179_, 1);
lean_inc(v_toPure_180_);
lean_dec_ref(v_toApplicative_179_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_apply_2(v_toPure_180_, lean_box(0), v___x_181_);
return v___x_182_;
}
}
}
LEAN_EXPORT lean_object* l_guard___redArg___boxed(lean_object* v_inst_183_, lean_object* v_inst_184_){
_start:
{
uint8_t v_inst_22__boxed_185_; lean_object* v_res_186_; 
v_inst_22__boxed_185_ = lean_unbox(v_inst_184_);
v_res_186_ = l_guard___redArg(v_inst_183_, v_inst_22__boxed_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_guard(lean_object* v_f_187_, lean_object* v_inst_188_, lean_object* v_p_189_, uint8_t v_inst_190_){
_start:
{
if (v_inst_190_ == 0)
{
lean_object* v_failure_191_; lean_object* v___x_192_; 
v_failure_191_ = lean_ctor_get(v_inst_188_, 1);
lean_inc(v_failure_191_);
lean_dec_ref(v_inst_188_);
v___x_192_ = lean_apply_1(v_failure_191_, lean_box(0));
return v___x_192_;
}
else
{
lean_object* v_toApplicative_193_; lean_object* v_toPure_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v_toApplicative_193_ = lean_ctor_get(v_inst_188_, 0);
lean_inc_ref(v_toApplicative_193_);
lean_dec_ref(v_inst_188_);
v_toPure_194_ = lean_ctor_get(v_toApplicative_193_, 1);
lean_inc(v_toPure_194_);
lean_dec_ref(v_toApplicative_193_);
v___x_195_ = lean_box(0);
v___x_196_ = lean_apply_2(v_toPure_194_, lean_box(0), v___x_195_);
return v___x_196_;
}
}
}
LEAN_EXPORT lean_object* l_guard___boxed(lean_object* v_f_197_, lean_object* v_inst_198_, lean_object* v_p_199_, lean_object* v_inst_200_){
_start:
{
uint8_t v_inst_34__boxed_201_; lean_object* v_res_202_; 
v_inst_34__boxed_201_ = lean_unbox(v_inst_200_);
v_res_202_ = l_guard(v_f_197_, v_inst_198_, v_p_199_, v_inst_34__boxed_201_);
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_optional___redArg___lam__0(lean_object* v_val_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_204_, 0, v_val_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_optional___redArg___lam__1(lean_object* v_toPure_205_, lean_object* v_x_206_){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = lean_box(0);
v___x_208_ = lean_apply_2(v_toPure_205_, lean_box(0), v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_optional___redArg(lean_object* v_inst_210_, lean_object* v_x_211_){
_start:
{
lean_object* v_toApplicative_212_; lean_object* v_toFunctor_213_; lean_object* v_orElse_214_; lean_object* v_toPure_215_; lean_object* v_map_216_; lean_object* v___f_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; 
v_toApplicative_212_ = lean_ctor_get(v_inst_210_, 0);
lean_inc_ref(v_toApplicative_212_);
v_toFunctor_213_ = lean_ctor_get(v_toApplicative_212_, 0);
lean_inc_ref(v_toFunctor_213_);
v_orElse_214_ = lean_ctor_get(v_inst_210_, 2);
lean_inc(v_orElse_214_);
lean_dec_ref(v_inst_210_);
v_toPure_215_ = lean_ctor_get(v_toApplicative_212_, 1);
lean_inc(v_toPure_215_);
lean_dec_ref(v_toApplicative_212_);
v_map_216_ = lean_ctor_get(v_toFunctor_213_, 0);
lean_inc(v_map_216_);
lean_dec_ref(v_toFunctor_213_);
v___f_217_ = ((lean_object*)(l_optional___redArg___closed__0));
v___f_218_ = lean_alloc_closure((void*)(l_optional___redArg___lam__1), 2, 1);
lean_closure_set(v___f_218_, 0, v_toPure_215_);
v___x_219_ = lean_apply_4(v_map_216_, lean_box(0), lean_box(0), v___f_217_, v_x_211_);
v___x_220_ = lean_apply_3(v_orElse_214_, lean_box(0), v___x_219_, v___f_218_);
return v___x_220_;
}
}
LEAN_EXPORT lean_object* l_optional(lean_object* v_f_221_, lean_object* v_inst_222_, lean_object* v_00_u03b1_223_, lean_object* v_x_224_){
_start:
{
lean_object* v_toApplicative_225_; lean_object* v_toFunctor_226_; lean_object* v_orElse_227_; lean_object* v_toPure_228_; lean_object* v_map_229_; lean_object* v___f_230_; lean_object* v___f_231_; lean_object* v___x_232_; lean_object* v___x_233_; 
v_toApplicative_225_ = lean_ctor_get(v_inst_222_, 0);
lean_inc_ref(v_toApplicative_225_);
v_toFunctor_226_ = lean_ctor_get(v_toApplicative_225_, 0);
lean_inc_ref(v_toFunctor_226_);
v_orElse_227_ = lean_ctor_get(v_inst_222_, 2);
lean_inc(v_orElse_227_);
lean_dec_ref(v_inst_222_);
v_toPure_228_ = lean_ctor_get(v_toApplicative_225_, 1);
lean_inc(v_toPure_228_);
lean_dec_ref(v_toApplicative_225_);
v_map_229_ = lean_ctor_get(v_toFunctor_226_, 0);
lean_inc(v_map_229_);
lean_dec_ref(v_toFunctor_226_);
v___f_230_ = ((lean_object*)(l_optional___redArg___closed__0));
v___f_231_ = lean_alloc_closure((void*)(l_optional___redArg___lam__1), 2, 1);
lean_closure_set(v___f_231_, 0, v_toPure_228_);
v___x_232_ = lean_apply_4(v_map_229_, lean_box(0), lean_box(0), v___f_230_, v_x_224_);
v___x_233_ = lean_apply_3(v_orElse_227_, lean_box(0), v___x_232_, v___f_231_);
return v___x_233_;
}
}
LEAN_EXPORT uint8_t l_instToBoolBool___lam__0(uint8_t v_b_234_){
_start:
{
return v_b_234_;
}
}
LEAN_EXPORT lean_object* l_instToBoolBool___lam__0___boxed(lean_object* v_b_235_){
_start:
{
uint8_t v_b_boxed_236_; uint8_t v_res_237_; lean_object* v_r_238_; 
v_b_boxed_236_ = lean_unbox(v_b_235_);
v_res_237_ = l_instToBoolBool___lam__0(v_b_boxed_236_);
v_r_238_ = lean_box(v_res_237_);
return v_r_238_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_261_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__0));
v___x_262_ = l_String_toRawSubstring_x27(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1(lean_object* v_x_271_, lean_object* v_a_272_, lean_object* v_a_273_){
_start:
{
lean_object* v___x_274_; uint8_t v___x_275_; 
v___x_274_ = ((lean_object*)(l_term___x3c_x7c_x7c_x3e___00__closed__1));
lean_inc(v_x_271_);
v___x_275_ = l_Lean_Syntax_isOfKind(v_x_271_, v___x_274_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec_ref(v_a_272_);
lean_dec(v_x_271_);
v___x_276_ = lean_box(1);
v___x_277_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_277_, 0, v___x_276_);
lean_ctor_set(v___x_277_, 1, v_a_273_);
return v___x_277_;
}
else
{
lean_object* v_quotContext_278_; lean_object* v_currMacroScope_279_; lean_object* v_ref_280_; lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; uint8_t v___x_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; 
v_quotContext_278_ = lean_ctor_get(v_a_272_, 1);
lean_inc(v_quotContext_278_);
v_currMacroScope_279_ = lean_ctor_get(v_a_272_, 2);
lean_inc(v_currMacroScope_279_);
v_ref_280_ = lean_ctor_get(v_a_272_, 5);
lean_inc(v_ref_280_);
lean_dec_ref(v_a_272_);
v___x_281_ = lean_unsigned_to_nat(0u);
v___x_282_ = l_Lean_Syntax_getArg(v_x_271_, v___x_281_);
v___x_283_ = lean_unsigned_to_nat(2u);
v___x_284_ = l_Lean_Syntax_getArg(v_x_271_, v___x_283_);
lean_dec(v_x_271_);
v___x_285_ = 0;
v___x_286_ = l_Lean_SourceInfo_fromRef(v_ref_280_, v___x_285_);
lean_dec(v_ref_280_);
v___x_287_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_288_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__1);
v___x_289_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__2));
v___x_290_ = l_Lean_addMacroScope(v_quotContext_278_, v___x_289_, v_currMacroScope_279_);
v___x_291_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x7c_x7c_x3e____1___closed__4));
lean_inc(v___x_286_);
v___x_292_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_292_, 0, v___x_286_);
lean_ctor_set(v___x_292_, 1, v___x_288_);
lean_ctor_set(v___x_292_, 2, v___x_290_);
lean_ctor_set(v___x_292_, 3, v___x_291_);
v___x_293_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
lean_inc(v___x_286_);
v___x_294_ = l_Lean_Syntax_node2(v___x_286_, v___x_293_, v___x_282_, v___x_284_);
v___x_295_ = l_Lean_Syntax_node2(v___x_286_, v___x_287_, v___x_292_, v___x_294_);
v___x_296_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_296_, 0, v___x_295_);
lean_ctor_set(v___x_296_, 1, v_a_273_);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__orM__1(lean_object* v_x_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v___x_300_; uint8_t v___x_301_; 
v___x_300_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_297_);
v___x_301_ = l_Lean_Syntax_isOfKind(v_x_297_, v___x_300_);
if (v___x_301_ == 0)
{
lean_object* v___x_302_; lean_object* v___x_303_; 
lean_dec(v_x_297_);
v___x_302_ = lean_box(0);
v___x_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_303_, 0, v___x_302_);
lean_ctor_set(v___x_303_, 1, v_a_299_);
return v___x_303_;
}
else
{
lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v___x_306_; uint8_t v___x_307_; 
v___x_304_ = lean_unsigned_to_nat(0u);
v___x_305_ = l_Lean_Syntax_getArg(v_x_297_, v___x_304_);
v___x_306_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_305_);
v___x_307_ = l_Lean_Syntax_isOfKind(v___x_305_, v___x_306_);
if (v___x_307_ == 0)
{
lean_object* v___x_308_; lean_object* v___x_309_; 
lean_dec(v___x_305_);
lean_dec(v_x_297_);
v___x_308_ = lean_box(0);
v___x_309_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_309_, 0, v___x_308_);
lean_ctor_set(v___x_309_, 1, v_a_299_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___x_312_; uint8_t v___x_313_; 
v___x_310_ = lean_unsigned_to_nat(1u);
v___x_311_ = l_Lean_Syntax_getArg(v_x_297_, v___x_310_);
lean_dec(v_x_297_);
v___x_312_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_311_);
v___x_313_ = l_Lean_Syntax_matchesNull(v___x_311_, v___x_312_);
if (v___x_313_ == 0)
{
lean_object* v___x_314_; lean_object* v___x_315_; 
lean_dec(v___x_311_);
lean_dec(v___x_305_);
v___x_314_ = lean_box(0);
v___x_315_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_314_);
lean_ctor_set(v___x_315_, 1, v_a_299_);
return v___x_315_;
}
else
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v_ref_318_; uint8_t v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; 
v___x_316_ = l_Lean_Syntax_getArg(v___x_311_, v___x_304_);
v___x_317_ = l_Lean_Syntax_getArg(v___x_311_, v___x_310_);
lean_dec(v___x_311_);
v_ref_318_ = l_Lean_replaceRef(v___x_305_, v_a_298_);
lean_dec(v___x_305_);
v___x_319_ = 0;
v___x_320_ = l_Lean_SourceInfo_fromRef(v_ref_318_, v___x_319_);
lean_dec(v_ref_318_);
v___x_321_ = ((lean_object*)(l_term___x3c_x7c_x7c_x3e___00__closed__1));
v___x_322_ = ((lean_object*)(l_term___x3c_x7c_x7c_x3e___00__closed__2));
lean_inc(v___x_320_);
v___x_323_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_323_, 0, v___x_320_);
lean_ctor_set(v___x_323_, 1, v___x_322_);
v___x_324_ = l_Lean_Syntax_node3(v___x_320_, v___x_321_, v___x_316_, v___x_323_, v___x_317_);
v___x_325_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set(v___x_325_, 1, v_a_299_);
return v___x_325_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__orM__1___boxed(lean_object* v_x_326_, lean_object* v_a_327_, lean_object* v_a_328_){
_start:
{
lean_object* v_res_329_; 
v_res_329_ = l___aux__Init__Control__Basic______unexpand__orM__1(v_x_326_, v_a_327_, v_a_328_);
lean_dec(v_a_327_);
return v_res_329_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_350_; lean_object* v___x_351_; 
v___x_350_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__0));
v___x_351_ = l_String_toRawSubstring_x27(v___x_350_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1(lean_object* v_x_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v___x_363_; uint8_t v___x_364_; 
v___x_363_ = ((lean_object*)(l_term___x3c_x26_x26_x3e___00__closed__1));
lean_inc(v_x_360_);
v___x_364_ = l_Lean_Syntax_isOfKind(v_x_360_, v___x_363_);
if (v___x_364_ == 0)
{
lean_object* v___x_365_; lean_object* v___x_366_; 
lean_dec_ref(v_a_361_);
lean_dec(v_x_360_);
v___x_365_ = lean_box(1);
v___x_366_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v_a_362_);
return v___x_366_;
}
else
{
lean_object* v_quotContext_367_; lean_object* v_currMacroScope_368_; lean_object* v_ref_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; uint8_t v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
v_quotContext_367_ = lean_ctor_get(v_a_361_, 1);
lean_inc(v_quotContext_367_);
v_currMacroScope_368_ = lean_ctor_get(v_a_361_, 2);
lean_inc(v_currMacroScope_368_);
v_ref_369_ = lean_ctor_get(v_a_361_, 5);
lean_inc(v_ref_369_);
lean_dec_ref(v_a_361_);
v___x_370_ = lean_unsigned_to_nat(0u);
v___x_371_ = l_Lean_Syntax_getArg(v_x_360_, v___x_370_);
v___x_372_ = lean_unsigned_to_nat(2u);
v___x_373_ = l_Lean_Syntax_getArg(v_x_360_, v___x_372_);
lean_dec(v_x_360_);
v___x_374_ = 0;
v___x_375_ = l_Lean_SourceInfo_fromRef(v_ref_369_, v___x_374_);
lean_dec(v_ref_369_);
v___x_376_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_377_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__1);
v___x_378_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__2));
v___x_379_ = l_Lean_addMacroScope(v_quotContext_367_, v___x_378_, v_currMacroScope_368_);
v___x_380_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x26_x3e____1___closed__4));
lean_inc(v___x_375_);
v___x_381_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_381_, 0, v___x_375_);
lean_ctor_set(v___x_381_, 1, v___x_377_);
lean_ctor_set(v___x_381_, 2, v___x_379_);
lean_ctor_set(v___x_381_, 3, v___x_380_);
v___x_382_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
lean_inc(v___x_375_);
v___x_383_ = l_Lean_Syntax_node2(v___x_375_, v___x_382_, v___x_371_, v___x_373_);
v___x_384_ = l_Lean_Syntax_node2(v___x_375_, v___x_376_, v___x_381_, v___x_383_);
v___x_385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_385_, 0, v___x_384_);
lean_ctor_set(v___x_385_, 1, v_a_362_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__andM__1(lean_object* v_x_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
lean_object* v___x_389_; uint8_t v___x_390_; 
v___x_389_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_386_);
v___x_390_ = l_Lean_Syntax_isOfKind(v_x_386_, v___x_389_);
if (v___x_390_ == 0)
{
lean_object* v___x_391_; lean_object* v___x_392_; 
lean_dec(v_x_386_);
v___x_391_ = lean_box(0);
v___x_392_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_392_, 0, v___x_391_);
lean_ctor_set(v___x_392_, 1, v_a_388_);
return v___x_392_;
}
else
{
lean_object* v___x_393_; lean_object* v___x_394_; lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_393_ = lean_unsigned_to_nat(0u);
v___x_394_ = l_Lean_Syntax_getArg(v_x_386_, v___x_393_);
v___x_395_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_394_);
v___x_396_ = l_Lean_Syntax_isOfKind(v___x_394_, v___x_395_);
if (v___x_396_ == 0)
{
lean_object* v___x_397_; lean_object* v___x_398_; 
lean_dec(v___x_394_);
lean_dec(v_x_386_);
v___x_397_ = lean_box(0);
v___x_398_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_398_, 0, v___x_397_);
lean_ctor_set(v___x_398_, 1, v_a_388_);
return v___x_398_;
}
else
{
lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; uint8_t v___x_402_; 
v___x_399_ = lean_unsigned_to_nat(1u);
v___x_400_ = l_Lean_Syntax_getArg(v_x_386_, v___x_399_);
lean_dec(v_x_386_);
v___x_401_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_400_);
v___x_402_ = l_Lean_Syntax_matchesNull(v___x_400_, v___x_401_);
if (v___x_402_ == 0)
{
lean_object* v___x_403_; lean_object* v___x_404_; 
lean_dec(v___x_400_);
lean_dec(v___x_394_);
v___x_403_ = lean_box(0);
v___x_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v_a_388_);
return v___x_404_;
}
else
{
lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v_ref_407_; uint8_t v___x_408_; lean_object* v___x_409_; lean_object* v___x_410_; lean_object* v___x_411_; lean_object* v___x_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
v___x_405_ = l_Lean_Syntax_getArg(v___x_400_, v___x_393_);
v___x_406_ = l_Lean_Syntax_getArg(v___x_400_, v___x_399_);
lean_dec(v___x_400_);
v_ref_407_ = l_Lean_replaceRef(v___x_394_, v_a_387_);
lean_dec(v___x_394_);
v___x_408_ = 0;
v___x_409_ = l_Lean_SourceInfo_fromRef(v_ref_407_, v___x_408_);
lean_dec(v_ref_407_);
v___x_410_ = ((lean_object*)(l_term___x3c_x26_x26_x3e___00__closed__1));
v___x_411_ = ((lean_object*)(l_term___x3c_x26_x26_x3e___00__closed__2));
lean_inc(v___x_409_);
v___x_412_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_412_, 0, v___x_409_);
lean_ctor_set(v___x_412_, 1, v___x_411_);
v___x_413_ = l_Lean_Syntax_node3(v___x_409_, v___x_410_, v___x_405_, v___x_412_, v___x_406_);
v___x_414_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_414_, 0, v___x_413_);
lean_ctor_set(v___x_414_, 1, v_a_388_);
return v___x_414_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__andM__1___boxed(lean_object* v_x_415_, lean_object* v_a_416_, lean_object* v_a_417_){
_start:
{
lean_object* v_res_418_; 
v_res_418_ = l___aux__Init__Control__Basic______unexpand__andM__1(v_x_415_, v_a_416_, v_a_417_);
lean_dec(v_a_416_);
return v_res_418_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__0(lean_object* v_x_u2082_419_, lean_object* v_x_u2081_420_, lean_object* v_00_u03b2_421_, lean_object* v___y_422_){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = lean_apply_2(v_x_u2082_419_, lean_box(0), v___y_422_);
v___x_424_ = lean_apply_2(v_x_u2081_420_, lean_box(0), v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__1(lean_object* v_x_u2082_425_, lean_object* v_f_426_, lean_object* v_x_u2081_427_){
_start:
{
lean_object* v___f_428_; lean_object* v___x_429_; 
v___f_428_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__0), 4, 2);
lean_closure_set(v___f_428_, 0, v_x_u2082_425_);
lean_closure_set(v___f_428_, 1, v_x_u2081_427_);
v___x_429_ = lean_apply_1(v_f_426_, v___f_428_);
return v___x_429_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__2(lean_object* v_inst_430_, lean_object* v_f_431_, lean_object* v_x_u2082_432_){
_start:
{
lean_object* v_liftWith_433_; lean_object* v___f_434_; lean_object* v___x_435_; 
v_liftWith_433_ = lean_ctor_get(v_inst_430_, 0);
lean_inc(v_liftWith_433_);
lean_dec_ref(v_inst_430_);
v___f_434_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__1), 3, 2);
lean_closure_set(v___f_434_, 0, v_x_u2082_432_);
lean_closure_set(v___f_434_, 1, v_f_431_);
v___x_435_ = lean_apply_2(v_liftWith_433_, lean_box(0), v___f_434_);
return v___x_435_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__3(lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_00_u03b1_438_, lean_object* v_f_439_){
_start:
{
lean_object* v_liftWith_440_; lean_object* v___f_441_; lean_object* v___x_442_; 
v_liftWith_440_ = lean_ctor_get(v_inst_436_, 0);
lean_inc(v_liftWith_440_);
lean_dec_ref(v_inst_436_);
v___f_441_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__2), 3, 2);
lean_closure_set(v___f_441_, 0, v_inst_437_);
lean_closure_set(v___f_441_, 1, v_f_439_);
v___x_442_ = lean_apply_2(v_liftWith_440_, lean_box(0), v___f_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg___lam__4(lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_00_u03b1_445_, lean_object* v___y_446_){
_start:
{
lean_object* v_restoreM_447_; lean_object* v_restoreM_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_restoreM_447_ = lean_ctor_get(v_inst_443_, 1);
lean_inc(v_restoreM_447_);
lean_dec_ref(v_inst_443_);
v_restoreM_448_ = lean_ctor_get(v_inst_444_, 1);
lean_inc(v_restoreM_448_);
lean_dec_ref(v_inst_444_);
v___x_449_ = lean_apply_2(v_restoreM_448_, lean_box(0), v___y_446_);
v___x_450_ = lean_apply_2(v_restoreM_447_, lean_box(0), v___x_449_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl___redArg(lean_object* v_inst_451_, lean_object* v_inst_452_){
_start:
{
lean_object* v___f_453_; lean_object* v___f_454_; lean_object* v___x_455_; 
lean_inc_ref(v_inst_452_);
lean_inc_ref(v_inst_451_);
v___f_453_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_453_, 0, v_inst_451_);
lean_closure_set(v___f_453_, 1, v_inst_452_);
v___f_454_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_454_, 0, v_inst_451_);
lean_closure_set(v___f_454_, 1, v_inst_452_);
v___x_455_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_455_, 0, v___f_453_);
lean_ctor_set(v___x_455_, 1, v___f_454_);
return v___x_455_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfMonadControl(lean_object* v_m_456_, lean_object* v_n_457_, lean_object* v_o_458_, lean_object* v_inst_459_, lean_object* v_inst_460_){
_start:
{
lean_object* v___f_461_; lean_object* v___f_462_; lean_object* v___x_463_; 
lean_inc_ref(v_inst_460_);
lean_inc_ref(v_inst_459_);
v___f_461_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__3), 4, 2);
lean_closure_set(v___f_461_, 0, v_inst_459_);
lean_closure_set(v___f_461_, 1, v_inst_460_);
v___f_462_ = lean_alloc_closure((void*)(l_instMonadControlTOfMonadControl___redArg___lam__4), 4, 2);
lean_closure_set(v___f_462_, 0, v_inst_459_);
lean_closure_set(v___f_462_, 1, v_inst_460_);
v___x_463_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_463_, 0, v___f_461_);
lean_ctor_set(v___x_463_, 1, v___f_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__0(lean_object* v_00_u03b2_464_, lean_object* v_x_465_){
_start:
{
lean_inc(v_x_465_);
return v_x_465_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__0___boxed(lean_object* v_00_u03b2_466_, lean_object* v_x_467_){
_start:
{
lean_object* v_res_468_; 
v_res_468_ = l_instMonadControlTOfPure___redArg___lam__0(v_00_u03b2_466_, v_x_467_);
lean_dec(v_x_467_);
return v_res_468_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__1(lean_object* v___f_469_, lean_object* v_00_u03b1_470_, lean_object* v_f_471_){
_start:
{
lean_object* v___x_472_; 
v___x_472_ = lean_apply_1(v_f_471_, v___f_469_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg___lam__2(lean_object* v_inst_473_, lean_object* v_00_u03b1_474_, lean_object* v_x_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = lean_apply_2(v_inst_473_, lean_box(0), v_x_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure___redArg(lean_object* v_inst_480_){
_start:
{
lean_object* v___f_481_; lean_object* v___f_482_; lean_object* v___x_483_; 
v___f_481_ = ((lean_object*)(l_instMonadControlTOfPure___redArg___closed__1));
v___f_482_ = lean_alloc_closure((void*)(l_instMonadControlTOfPure___redArg___lam__2), 3, 1);
lean_closure_set(v___f_482_, 0, v_inst_480_);
v___x_483_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_483_, 0, v___f_481_);
lean_ctor_set(v___x_483_, 1, v___f_482_);
return v___x_483_;
}
}
LEAN_EXPORT lean_object* l_instMonadControlTOfPure(lean_object* v_m_484_, lean_object* v_inst_485_){
_start:
{
lean_object* v___x_486_; 
v___x_486_ = l_instMonadControlTOfPure___redArg(v_inst_485_);
return v___x_486_;
}
}
LEAN_EXPORT lean_object* l_controlAt___redArg(lean_object* v_inst_487_, lean_object* v_inst_488_, lean_object* v_f_489_){
_start:
{
lean_object* v_liftWith_490_; lean_object* v_restoreM_491_; lean_object* v___x_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_liftWith_490_ = lean_ctor_get(v_inst_487_, 0);
lean_inc(v_liftWith_490_);
v_restoreM_491_ = lean_ctor_get(v_inst_487_, 1);
lean_inc(v_restoreM_491_);
lean_dec_ref(v_inst_487_);
v___x_492_ = lean_apply_2(v_liftWith_490_, lean_box(0), v_f_489_);
v___x_493_ = lean_apply_1(v_restoreM_491_, lean_box(0));
v___x_494_ = lean_apply_4(v_inst_488_, lean_box(0), lean_box(0), v___x_492_, v___x_493_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_controlAt(lean_object* v_m_495_, lean_object* v_n_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_00_u03b1_499_, lean_object* v_f_500_){
_start:
{
lean_object* v_liftWith_501_; lean_object* v_restoreM_502_; lean_object* v___x_503_; lean_object* v___x_504_; lean_object* v___x_505_; 
v_liftWith_501_ = lean_ctor_get(v_inst_497_, 0);
lean_inc(v_liftWith_501_);
v_restoreM_502_ = lean_ctor_get(v_inst_497_, 1);
lean_inc(v_restoreM_502_);
lean_dec_ref(v_inst_497_);
v___x_503_ = lean_apply_2(v_liftWith_501_, lean_box(0), v_f_500_);
v___x_504_ = lean_apply_1(v_restoreM_502_, lean_box(0));
v___x_505_ = lean_apply_4(v_inst_498_, lean_box(0), lean_box(0), v___x_503_, v___x_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_control___redArg(lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_f_508_){
_start:
{
lean_object* v_liftWith_509_; lean_object* v_restoreM_510_; lean_object* v___x_511_; lean_object* v___x_512_; lean_object* v___x_513_; 
v_liftWith_509_ = lean_ctor_get(v_inst_506_, 0);
lean_inc(v_liftWith_509_);
v_restoreM_510_ = lean_ctor_get(v_inst_506_, 1);
lean_inc(v_restoreM_510_);
lean_dec_ref(v_inst_506_);
v___x_511_ = lean_apply_2(v_liftWith_509_, lean_box(0), v_f_508_);
v___x_512_ = lean_apply_1(v_restoreM_510_, lean_box(0));
v___x_513_ = lean_apply_4(v_inst_507_, lean_box(0), lean_box(0), v___x_511_, v___x_512_);
return v___x_513_;
}
}
LEAN_EXPORT lean_object* l_control(lean_object* v_m_514_, lean_object* v_n_515_, lean_object* v_inst_516_, lean_object* v_inst_517_, lean_object* v_00_u03b1_518_, lean_object* v_f_519_){
_start:
{
lean_object* v_liftWith_520_; lean_object* v_restoreM_521_; lean_object* v___x_522_; lean_object* v___x_523_; lean_object* v___x_524_; 
v_liftWith_520_ = lean_ctor_get(v_inst_516_, 0);
lean_inc(v_liftWith_520_);
v_restoreM_521_ = lean_ctor_get(v_inst_516_, 1);
lean_inc(v_restoreM_521_);
lean_dec_ref(v_inst_516_);
v___x_522_ = lean_apply_2(v_liftWith_520_, lean_box(0), v_f_519_);
v___x_523_ = lean_apply_1(v_restoreM_521_, lean_box(0));
v___x_524_ = lean_apply_4(v_inst_517_, lean_box(0), lean_box(0), v___x_522_, v___x_523_);
return v___x_524_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliRight___redArg(lean_object* v_inst_525_, lean_object* v_f_u2081_526_, lean_object* v_f_u2082_527_, lean_object* v_a_528_){
_start:
{
lean_object* v___x_529_; lean_object* v___x_530_; 
v___x_529_ = lean_apply_1(v_f_u2081_526_, v_a_528_);
v___x_530_ = lean_apply_4(v_inst_525_, lean_box(0), lean_box(0), v___x_529_, v_f_u2082_527_);
return v___x_530_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliRight(lean_object* v_00_u03b1_531_, lean_object* v_m_532_, lean_object* v_00_u03b2_533_, lean_object* v_00_u03b3_534_, lean_object* v_inst_535_, lean_object* v_f_u2081_536_, lean_object* v_f_u2082_537_, lean_object* v_a_538_){
_start:
{
lean_object* v___x_539_; lean_object* v___x_540_; 
v___x_539_ = lean_apply_1(v_f_u2081_536_, v_a_538_);
v___x_540_ = lean_apply_4(v_inst_535_, lean_box(0), lean_box(0), v___x_539_, v_f_u2082_537_);
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliLeft___redArg(lean_object* v_inst_541_, lean_object* v_f_u2082_542_, lean_object* v_f_u2081_543_, lean_object* v_a_544_){
_start:
{
lean_object* v___x_545_; lean_object* v___x_546_; 
v___x_545_ = lean_apply_1(v_f_u2081_543_, v_a_544_);
v___x_546_ = lean_apply_4(v_inst_541_, lean_box(0), lean_box(0), v___x_545_, v_f_u2082_542_);
return v___x_546_;
}
}
LEAN_EXPORT lean_object* l_Bind_kleisliLeft(lean_object* v_00_u03b1_547_, lean_object* v_m_548_, lean_object* v_00_u03b2_549_, lean_object* v_00_u03b3_550_, lean_object* v_inst_551_, lean_object* v_f_u2082_552_, lean_object* v_f_u2081_553_, lean_object* v_a_554_){
_start:
{
lean_object* v___x_555_; lean_object* v___x_556_; 
v___x_555_ = lean_apply_1(v_f_u2081_553_, v_a_554_);
v___x_556_ = lean_apply_4(v_inst_551_, lean_box(0), lean_box(0), v___x_555_, v_f_u2082_552_);
return v___x_556_;
}
}
LEAN_EXPORT lean_object* l_Bind_bindLeft___redArg(lean_object* v_inst_557_, lean_object* v_f_558_, lean_object* v_ma_559_){
_start:
{
lean_object* v___x_560_; 
v___x_560_ = lean_apply_4(v_inst_557_, lean_box(0), lean_box(0), v_ma_559_, v_f_558_);
return v___x_560_;
}
}
LEAN_EXPORT lean_object* l_Bind_bindLeft(lean_object* v_00_u03b1_561_, lean_object* v_m_562_, lean_object* v_00_u03b2_563_, lean_object* v_inst_564_, lean_object* v_f_565_, lean_object* v_ma_566_){
_start:
{
lean_object* v___x_567_; 
v___x_567_ = lean_apply_4(v_inst_564_, lean_box(0), lean_box(0), v_ma_566_, v_f_565_);
return v___x_567_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1(void){
_start:
{
lean_object* v___x_588_; lean_object* v___x_589_; 
v___x_588_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__0));
v___x_589_ = l_String_toRawSubstring_x27(v___x_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1(lean_object* v_x_601_, lean_object* v_a_602_, lean_object* v_a_603_){
_start:
{
lean_object* v___x_604_; uint8_t v___x_605_; 
v___x_604_ = ((lean_object*)(l_term___x3e_x3d_x3e___00__closed__1));
lean_inc(v_x_601_);
v___x_605_ = l_Lean_Syntax_isOfKind(v_x_601_, v___x_604_);
if (v___x_605_ == 0)
{
lean_object* v___x_606_; lean_object* v___x_607_; 
lean_dec_ref(v_a_602_);
lean_dec(v_x_601_);
v___x_606_ = lean_box(1);
v___x_607_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_607_, 0, v___x_606_);
lean_ctor_set(v___x_607_, 1, v_a_603_);
return v___x_607_;
}
else
{
lean_object* v_quotContext_608_; lean_object* v_currMacroScope_609_; lean_object* v_ref_610_; lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; lean_object* v___x_614_; uint8_t v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; lean_object* v___x_618_; lean_object* v___x_619_; lean_object* v___x_620_; lean_object* v___x_621_; lean_object* v___x_622_; lean_object* v___x_623_; lean_object* v___x_624_; lean_object* v___x_625_; lean_object* v___x_626_; 
v_quotContext_608_ = lean_ctor_get(v_a_602_, 1);
lean_inc(v_quotContext_608_);
v_currMacroScope_609_ = lean_ctor_get(v_a_602_, 2);
lean_inc(v_currMacroScope_609_);
v_ref_610_ = lean_ctor_get(v_a_602_, 5);
lean_inc(v_ref_610_);
lean_dec_ref(v_a_602_);
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = l_Lean_Syntax_getArg(v_x_601_, v___x_611_);
v___x_613_ = lean_unsigned_to_nat(2u);
v___x_614_ = l_Lean_Syntax_getArg(v_x_601_, v___x_613_);
lean_dec(v_x_601_);
v___x_615_ = 0;
v___x_616_ = l_Lean_SourceInfo_fromRef(v_ref_610_, v___x_615_);
lean_dec(v_ref_610_);
v___x_617_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_618_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__1);
v___x_619_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__4));
v___x_620_ = l_Lean_addMacroScope(v_quotContext_608_, v___x_619_, v_currMacroScope_609_);
v___x_621_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3e_x3d_x3e____1___closed__6));
lean_inc(v___x_616_);
v___x_622_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_622_, 0, v___x_616_);
lean_ctor_set(v___x_622_, 1, v___x_618_);
lean_ctor_set(v___x_622_, 2, v___x_620_);
lean_ctor_set(v___x_622_, 3, v___x_621_);
v___x_623_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
lean_inc(v___x_616_);
v___x_624_ = l_Lean_Syntax_node2(v___x_616_, v___x_623_, v___x_612_, v___x_614_);
v___x_625_ = l_Lean_Syntax_node2(v___x_616_, v___x_617_, v___x_622_, v___x_624_);
v___x_626_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_626_, 0, v___x_625_);
lean_ctor_set(v___x_626_, 1, v_a_603_);
return v___x_626_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(lean_object* v_x_627_, lean_object* v_a_628_, lean_object* v_a_629_){
_start:
{
lean_object* v___x_630_; uint8_t v___x_631_; 
v___x_630_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_627_);
v___x_631_ = l_Lean_Syntax_isOfKind(v_x_627_, v___x_630_);
if (v___x_631_ == 0)
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec(v_x_627_);
v___x_632_ = lean_box(0);
v___x_633_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_633_, 0, v___x_632_);
lean_ctor_set(v___x_633_, 1, v_a_629_);
return v___x_633_;
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; lean_object* v___x_636_; uint8_t v___x_637_; 
v___x_634_ = lean_unsigned_to_nat(0u);
v___x_635_ = l_Lean_Syntax_getArg(v_x_627_, v___x_634_);
v___x_636_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_635_);
v___x_637_ = l_Lean_Syntax_isOfKind(v___x_635_, v___x_636_);
if (v___x_637_ == 0)
{
lean_object* v___x_638_; lean_object* v___x_639_; 
lean_dec(v___x_635_);
lean_dec(v_x_627_);
v___x_638_ = lean_box(0);
v___x_639_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_639_, 0, v___x_638_);
lean_ctor_set(v___x_639_, 1, v_a_629_);
return v___x_639_;
}
else
{
lean_object* v___x_640_; lean_object* v___x_641_; lean_object* v___x_642_; uint8_t v___x_643_; 
v___x_640_ = lean_unsigned_to_nat(1u);
v___x_641_ = l_Lean_Syntax_getArg(v_x_627_, v___x_640_);
lean_dec(v_x_627_);
v___x_642_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_641_);
v___x_643_ = l_Lean_Syntax_matchesNull(v___x_641_, v___x_642_);
if (v___x_643_ == 0)
{
lean_object* v___x_644_; lean_object* v___x_645_; 
lean_dec(v___x_641_);
lean_dec(v___x_635_);
v___x_644_ = lean_box(0);
v___x_645_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_645_, 0, v___x_644_);
lean_ctor_set(v___x_645_, 1, v_a_629_);
return v___x_645_;
}
else
{
lean_object* v___x_646_; lean_object* v___x_647_; lean_object* v_ref_648_; uint8_t v___x_649_; lean_object* v___x_650_; lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; lean_object* v___x_654_; lean_object* v___x_655_; 
v___x_646_ = l_Lean_Syntax_getArg(v___x_641_, v___x_634_);
v___x_647_ = l_Lean_Syntax_getArg(v___x_641_, v___x_640_);
lean_dec(v___x_641_);
v_ref_648_ = l_Lean_replaceRef(v___x_635_, v_a_628_);
lean_dec(v___x_635_);
v___x_649_ = 0;
v___x_650_ = l_Lean_SourceInfo_fromRef(v_ref_648_, v___x_649_);
lean_dec(v_ref_648_);
v___x_651_ = ((lean_object*)(l_term___x3e_x3d_x3e___00__closed__1));
v___x_652_ = ((lean_object*)(l_term___x3e_x3d_x3e___00__closed__2));
lean_inc(v___x_650_);
v___x_653_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_650_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
v___x_654_ = l_Lean_Syntax_node3(v___x_650_, v___x_651_, v___x_646_, v___x_653_, v___x_647_);
v___x_655_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_655_, 0, v___x_654_);
lean_ctor_set(v___x_655_, 1, v_a_629_);
return v___x_655_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1___boxed(lean_object* v_x_656_, lean_object* v_a_657_, lean_object* v_a_658_){
_start:
{
lean_object* v_res_659_; 
v_res_659_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliRight__1(v_x_656_, v_a_657_, v_a_658_);
lean_dec(v_a_657_);
return v_res_659_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_677_; lean_object* v___x_678_; 
v___x_677_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__0));
v___x_678_ = l_String_toRawSubstring_x27(v___x_677_);
return v___x_678_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1(lean_object* v_x_689_, lean_object* v_a_690_, lean_object* v_a_691_){
_start:
{
lean_object* v___x_692_; uint8_t v___x_693_; 
v___x_692_ = ((lean_object*)(l_term___x3c_x3d_x3c___00__closed__1));
lean_inc(v_x_689_);
v___x_693_ = l_Lean_Syntax_isOfKind(v_x_689_, v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; lean_object* v___x_695_; 
lean_dec_ref(v_a_690_);
lean_dec(v_x_689_);
v___x_694_ = lean_box(1);
v___x_695_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_695_, 0, v___x_694_);
lean_ctor_set(v___x_695_, 1, v_a_691_);
return v___x_695_;
}
else
{
lean_object* v_quotContext_696_; lean_object* v_currMacroScope_697_; lean_object* v_ref_698_; lean_object* v___x_699_; lean_object* v___x_700_; lean_object* v___x_701_; lean_object* v___x_702_; uint8_t v___x_703_; lean_object* v___x_704_; lean_object* v___x_705_; lean_object* v___x_706_; lean_object* v___x_707_; lean_object* v___x_708_; lean_object* v___x_709_; lean_object* v___x_710_; lean_object* v___x_711_; lean_object* v___x_712_; lean_object* v___x_713_; lean_object* v___x_714_; 
v_quotContext_696_ = lean_ctor_get(v_a_690_, 1);
lean_inc(v_quotContext_696_);
v_currMacroScope_697_ = lean_ctor_get(v_a_690_, 2);
lean_inc(v_currMacroScope_697_);
v_ref_698_ = lean_ctor_get(v_a_690_, 5);
lean_inc(v_ref_698_);
lean_dec_ref(v_a_690_);
v___x_699_ = lean_unsigned_to_nat(0u);
v___x_700_ = l_Lean_Syntax_getArg(v_x_689_, v___x_699_);
v___x_701_ = lean_unsigned_to_nat(2u);
v___x_702_ = l_Lean_Syntax_getArg(v_x_689_, v___x_701_);
lean_dec(v_x_689_);
v___x_703_ = 0;
v___x_704_ = l_Lean_SourceInfo_fromRef(v_ref_698_, v___x_703_);
lean_dec(v_ref_698_);
v___x_705_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_706_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__1);
v___x_707_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__3));
v___x_708_ = l_Lean_addMacroScope(v_quotContext_696_, v___x_707_, v_currMacroScope_697_);
v___x_709_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x3d_x3c____1___closed__5));
lean_inc(v___x_704_);
v___x_710_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_710_, 0, v___x_704_);
lean_ctor_set(v___x_710_, 1, v___x_706_);
lean_ctor_set(v___x_710_, 2, v___x_708_);
lean_ctor_set(v___x_710_, 3, v___x_709_);
v___x_711_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
lean_inc(v___x_704_);
v___x_712_ = l_Lean_Syntax_node2(v___x_704_, v___x_711_, v___x_700_, v___x_702_);
v___x_713_ = l_Lean_Syntax_node2(v___x_704_, v___x_705_, v___x_710_, v___x_712_);
v___x_714_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_714_, 0, v___x_713_);
lean_ctor_set(v___x_714_, 1, v_a_691_);
return v___x_714_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(lean_object* v_x_715_, lean_object* v_a_716_, lean_object* v_a_717_){
_start:
{
lean_object* v___x_718_; uint8_t v___x_719_; 
v___x_718_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_715_);
v___x_719_ = l_Lean_Syntax_isOfKind(v_x_715_, v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; lean_object* v___x_721_; 
lean_dec(v_x_715_);
v___x_720_ = lean_box(0);
v___x_721_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_721_, 0, v___x_720_);
lean_ctor_set(v___x_721_, 1, v_a_717_);
return v___x_721_;
}
else
{
lean_object* v___x_722_; lean_object* v___x_723_; lean_object* v___x_724_; uint8_t v___x_725_; 
v___x_722_ = lean_unsigned_to_nat(0u);
v___x_723_ = l_Lean_Syntax_getArg(v_x_715_, v___x_722_);
v___x_724_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_723_);
v___x_725_ = l_Lean_Syntax_isOfKind(v___x_723_, v___x_724_);
if (v___x_725_ == 0)
{
lean_object* v___x_726_; lean_object* v___x_727_; 
lean_dec(v___x_723_);
lean_dec(v_x_715_);
v___x_726_ = lean_box(0);
v___x_727_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_727_, 0, v___x_726_);
lean_ctor_set(v___x_727_, 1, v_a_717_);
return v___x_727_;
}
else
{
lean_object* v___x_728_; lean_object* v___x_729_; lean_object* v___x_730_; uint8_t v___x_731_; 
v___x_728_ = lean_unsigned_to_nat(1u);
v___x_729_ = l_Lean_Syntax_getArg(v_x_715_, v___x_728_);
lean_dec(v_x_715_);
v___x_730_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_729_);
v___x_731_ = l_Lean_Syntax_matchesNull(v___x_729_, v___x_730_);
if (v___x_731_ == 0)
{
lean_object* v___x_732_; lean_object* v___x_733_; 
lean_dec(v___x_729_);
lean_dec(v___x_723_);
v___x_732_ = lean_box(0);
v___x_733_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
lean_ctor_set(v___x_733_, 1, v_a_717_);
return v___x_733_;
}
else
{
lean_object* v___x_734_; lean_object* v___x_735_; lean_object* v_ref_736_; uint8_t v___x_737_; lean_object* v___x_738_; lean_object* v___x_739_; lean_object* v___x_740_; lean_object* v___x_741_; lean_object* v___x_742_; lean_object* v___x_743_; 
v___x_734_ = l_Lean_Syntax_getArg(v___x_729_, v___x_722_);
v___x_735_ = l_Lean_Syntax_getArg(v___x_729_, v___x_728_);
lean_dec(v___x_729_);
v_ref_736_ = l_Lean_replaceRef(v___x_723_, v_a_716_);
lean_dec(v___x_723_);
v___x_737_ = 0;
v___x_738_ = l_Lean_SourceInfo_fromRef(v_ref_736_, v___x_737_);
lean_dec(v_ref_736_);
v___x_739_ = ((lean_object*)(l_term___x3c_x3d_x3c___00__closed__1));
v___x_740_ = ((lean_object*)(l_term___x3c_x3d_x3c___00__closed__2));
lean_inc(v___x_738_);
v___x_741_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_741_, 0, v___x_738_);
lean_ctor_set(v___x_741_, 1, v___x_740_);
v___x_742_ = l_Lean_Syntax_node3(v___x_738_, v___x_739_, v___x_734_, v___x_741_, v___x_735_);
v___x_743_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_743_, 0, v___x_742_);
lean_ctor_set(v___x_743_, 1, v_a_717_);
return v___x_743_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1___boxed(lean_object* v_x_744_, lean_object* v_a_745_, lean_object* v_a_746_){
_start:
{
lean_object* v_res_747_; 
v_res_747_ = l___aux__Init__Control__Basic______unexpand__Bind__kleisliLeft__1(v_x_744_, v_a_745_, v_a_746_);
lean_dec(v_a_745_);
return v_res_747_;
}
}
static lean_object* _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1(void){
_start:
{
lean_object* v___x_765_; lean_object* v___x_766_; 
v___x_765_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__0));
v___x_766_ = l_String_toRawSubstring_x27(v___x_765_);
return v___x_766_;
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1(lean_object* v_x_777_, lean_object* v_a_778_, lean_object* v_a_779_){
_start:
{
lean_object* v___x_780_; uint8_t v___x_781_; 
v___x_780_ = ((lean_object*)(l_term___x3d_x3c_x3c___00__closed__1));
lean_inc(v_x_777_);
v___x_781_ = l_Lean_Syntax_isOfKind(v_x_777_, v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; lean_object* v___x_783_; 
lean_dec_ref(v_a_778_);
lean_dec(v_x_777_);
v___x_782_ = lean_box(1);
v___x_783_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_783_, 0, v___x_782_);
lean_ctor_set(v___x_783_, 1, v_a_779_);
return v___x_783_;
}
else
{
lean_object* v_quotContext_784_; lean_object* v_currMacroScope_785_; lean_object* v_ref_786_; lean_object* v___x_787_; lean_object* v___x_788_; lean_object* v___x_789_; lean_object* v___x_790_; uint8_t v___x_791_; lean_object* v___x_792_; lean_object* v___x_793_; lean_object* v___x_794_; lean_object* v___x_795_; lean_object* v___x_796_; lean_object* v___x_797_; lean_object* v___x_798_; lean_object* v___x_799_; lean_object* v___x_800_; lean_object* v___x_801_; lean_object* v___x_802_; 
v_quotContext_784_ = lean_ctor_get(v_a_778_, 1);
lean_inc(v_quotContext_784_);
v_currMacroScope_785_ = lean_ctor_get(v_a_778_, 2);
lean_inc(v_currMacroScope_785_);
v_ref_786_ = lean_ctor_get(v_a_778_, 5);
lean_inc(v_ref_786_);
lean_dec_ref(v_a_778_);
v___x_787_ = lean_unsigned_to_nat(0u);
v___x_788_ = l_Lean_Syntax_getArg(v_x_777_, v___x_787_);
v___x_789_ = lean_unsigned_to_nat(2u);
v___x_790_ = l_Lean_Syntax_getArg(v_x_777_, v___x_789_);
lean_dec(v_x_777_);
v___x_791_ = 0;
v___x_792_ = l_Lean_SourceInfo_fromRef(v_ref_786_, v___x_791_);
lean_dec(v_ref_786_);
v___x_793_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
v___x_794_ = lean_obj_once(&l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1, &l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1_once, _init_l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__1);
v___x_795_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__3));
v___x_796_ = l_Lean_addMacroScope(v_quotContext_784_, v___x_795_, v_currMacroScope_785_);
v___x_797_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3d_x3c_x3c____1___closed__5));
lean_inc(v___x_792_);
v___x_798_ = lean_alloc_ctor(3, 4, 0);
lean_ctor_set(v___x_798_, 0, v___x_792_);
lean_ctor_set(v___x_798_, 1, v___x_794_);
lean_ctor_set(v___x_798_, 2, v___x_796_);
lean_ctor_set(v___x_798_, 3, v___x_797_);
v___x_799_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__13));
lean_inc(v___x_792_);
v___x_800_ = l_Lean_Syntax_node2(v___x_792_, v___x_799_, v___x_788_, v___x_790_);
v___x_801_ = l_Lean_Syntax_node2(v___x_792_, v___x_793_, v___x_798_, v___x_800_);
v___x_802_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_802_, 0, v___x_801_);
lean_ctor_set(v___x_802_, 1, v_a_779_);
return v___x_802_;
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(lean_object* v_x_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v___x_806_; uint8_t v___x_807_; 
v___x_806_ = ((lean_object*)(l___aux__Init__Control__Basic______macroRules__term___x3c_x26_x3e____1___closed__4));
lean_inc(v_x_803_);
v___x_807_ = l_Lean_Syntax_isOfKind(v_x_803_, v___x_806_);
if (v___x_807_ == 0)
{
lean_object* v___x_808_; lean_object* v___x_809_; 
lean_dec(v_x_803_);
v___x_808_ = lean_box(0);
v___x_809_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_809_, 0, v___x_808_);
lean_ctor_set(v___x_809_, 1, v_a_805_);
return v___x_809_;
}
else
{
lean_object* v___x_810_; lean_object* v___x_811_; lean_object* v___x_812_; uint8_t v___x_813_; 
v___x_810_ = lean_unsigned_to_nat(0u);
v___x_811_ = l_Lean_Syntax_getArg(v_x_803_, v___x_810_);
v___x_812_ = ((lean_object*)(l___aux__Init__Control__Basic______unexpand__Functor__mapRev__1___closed__1));
lean_inc(v___x_811_);
v___x_813_ = l_Lean_Syntax_isOfKind(v___x_811_, v___x_812_);
if (v___x_813_ == 0)
{
lean_object* v___x_814_; lean_object* v___x_815_; 
lean_dec(v___x_811_);
lean_dec(v_x_803_);
v___x_814_ = lean_box(0);
v___x_815_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_815_, 0, v___x_814_);
lean_ctor_set(v___x_815_, 1, v_a_805_);
return v___x_815_;
}
else
{
lean_object* v___x_816_; lean_object* v___x_817_; lean_object* v___x_818_; uint8_t v___x_819_; 
v___x_816_ = lean_unsigned_to_nat(1u);
v___x_817_ = l_Lean_Syntax_getArg(v_x_803_, v___x_816_);
lean_dec(v_x_803_);
v___x_818_ = lean_unsigned_to_nat(2u);
lean_inc(v___x_817_);
v___x_819_ = l_Lean_Syntax_matchesNull(v___x_817_, v___x_818_);
if (v___x_819_ == 0)
{
lean_object* v___x_820_; lean_object* v___x_821_; 
lean_dec(v___x_817_);
lean_dec(v___x_811_);
v___x_820_ = lean_box(0);
v___x_821_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
lean_ctor_set(v___x_821_, 1, v_a_805_);
return v___x_821_;
}
else
{
lean_object* v___x_822_; lean_object* v___x_823_; lean_object* v_ref_824_; uint8_t v___x_825_; lean_object* v___x_826_; lean_object* v___x_827_; lean_object* v___x_828_; lean_object* v___x_829_; lean_object* v___x_830_; lean_object* v___x_831_; 
v___x_822_ = l_Lean_Syntax_getArg(v___x_817_, v___x_810_);
v___x_823_ = l_Lean_Syntax_getArg(v___x_817_, v___x_816_);
lean_dec(v___x_817_);
v_ref_824_ = l_Lean_replaceRef(v___x_811_, v_a_804_);
lean_dec(v___x_811_);
v___x_825_ = 0;
v___x_826_ = l_Lean_SourceInfo_fromRef(v_ref_824_, v___x_825_);
lean_dec(v_ref_824_);
v___x_827_ = ((lean_object*)(l_term___x3d_x3c_x3c___00__closed__1));
v___x_828_ = ((lean_object*)(l_term___x3d_x3c_x3c___00__closed__2));
lean_inc(v___x_826_);
v___x_829_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v___x_829_, 0, v___x_826_);
lean_ctor_set(v___x_829_, 1, v___x_828_);
v___x_830_ = l_Lean_Syntax_node3(v___x_826_, v___x_827_, v___x_822_, v___x_829_, v___x_823_);
v___x_831_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_831_, 0, v___x_830_);
lean_ctor_set(v___x_831_, 1, v_a_805_);
return v___x_831_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1___boxed(lean_object* v_x_832_, lean_object* v_a_833_, lean_object* v_a_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___aux__Init__Control__Basic______unexpand__Bind__bindLeft__1(v_x_832_, v_a_833_, v_a_834_);
lean_dec(v_a_833_);
return v_res_835_;
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
