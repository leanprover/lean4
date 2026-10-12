// Lean compiler output
// Module: Lean.Linter.AmbiguousOpen
// Imports: public import Lean.ResolveName public import Lean.Linter.Init
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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Linter_logLint___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_rootNamespace;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Environment_isNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterTR_loop___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_List_eraseDups___redArg(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Linter_getLinterOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "ambiguousOpen"};
static const lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(55, 219, 89, 241, 127, 128, 208, 200)}};
static const lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 212, .m_capacity = 212, .m_length = 211, .m_data = "if true, warn when the namespace of an `open` declaration could also refer to a namespace that is silently not opened, e.g. `open B` inside `namespace A` only opens `A.B` even if the namespace `B` exists as well"};
static const lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(164, 74, 3, 36, 226, 77, 50, 136)}};
static const lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_ambiguousOpen;
LEAN_EXPORT lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_scopeCandidates(lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "`"};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0(lean_object*);
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ", "};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__0_value;
static const lean_ctor_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__0_value)}};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__1 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__1_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__2;
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3(lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4(uint8_t, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "Ambiguous namespace `"};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__0 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__0_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 33, .m_capacity = 33, .m_length = 32, .m_data = "`: this `open` refers to all of "};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__2 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__2_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = ", while "};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__4 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__4_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = " because the `open` occurs inside `namespace "};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__6 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__6_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "`."};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__8 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__8_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = " Specify the namespace unambiguously, e.g. `"};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__10 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__10_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__11;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`."};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__12 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__12_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__13;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "`: it is interpreted as "};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__14 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__14_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__15;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = " because this `open` occurs inside `namespace "};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__16 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__16_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__17;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "`, while "};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__18 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__18_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__19;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__20_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__20 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__20_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__21_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__21;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = " are silently not opened"};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__22 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__22_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__23_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__23;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__24_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " is silently not opened"};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__24 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__24_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__25_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__25;
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(uint8_t, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0_value;
static const lean_closure_object l_Lean_Linter_checkAmbiguousOpen___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0_value)} };
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___closed__1 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___closed__1_value;
static const lean_closure_object l_Lean_Linter_checkAmbiguousOpen___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___closed__2 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___closed__2_value;
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v_deprecation_x3f_7_; lean_object* v___x_8_; uint8_t v___x_9_; lean_object* v___x_10_; lean_object* v___x_11_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_deprecation_x3f_7_ = lean_ctor_get(v_decl_2_, 2);
v___x_8_ = lean_alloc_ctor(1, 0, 1);
v___x_9_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_8_, 0, v___x_9_);
lean_inc(v_deprecation_x3f_7_);
lean_inc_ref(v_descr_6_);
lean_inc_n(v_name_1_, 2);
v___x_10_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_10_, 0, v_name_1_);
lean_ctor_set(v___x_10_, 1, v_ref_3_);
lean_ctor_set(v___x_10_, 2, v___x_8_);
lean_ctor_set(v___x_10_, 3, v_descr_6_);
lean_ctor_set(v___x_10_, 4, v_deprecation_x3f_7_);
v___x_11_ = lean_register_option(v_name_1_, v___x_10_);
if (lean_obj_tag(v___x_11_) == 0)
{
lean_object* v___x_13_; uint8_t v_isShared_14_; uint8_t v_isSharedCheck_19_; 
v_isSharedCheck_19_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_19_ == 0)
{
lean_object* v_unused_20_; 
v_unused_20_ = lean_ctor_get(v___x_11_, 0);
lean_dec(v_unused_20_);
v___x_13_ = v___x_11_;
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
else
{
lean_dec(v___x_11_);
v___x_13_ = lean_box(0);
v_isShared_14_ = v_isSharedCheck_19_;
goto v_resetjp_12_;
}
v_resetjp_12_:
{
lean_object* v___x_15_; lean_object* v___x_17_; 
lean_inc(v_defValue_5_);
v___x_15_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_15_, 0, v_name_1_);
lean_ctor_set(v___x_15_, 1, v_defValue_5_);
if (v_isShared_14_ == 0)
{
lean_ctor_set(v___x_13_, 0, v___x_15_);
v___x_17_ = v___x_13_;
goto v_reusejp_16_;
}
else
{
lean_object* v_reuseFailAlloc_18_; 
v_reuseFailAlloc_18_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_18_, 0, v___x_15_);
v___x_17_ = v_reuseFailAlloc_18_;
goto v_reusejp_16_;
}
v_reusejp_16_:
{
return v___x_17_;
}
}
}
else
{
lean_object* v_a_21_; lean_object* v___x_23_; uint8_t v_isShared_24_; uint8_t v_isSharedCheck_28_; 
lean_dec(v_name_1_);
v_a_21_ = lean_ctor_get(v___x_11_, 0);
v_isSharedCheck_28_ = !lean_is_exclusive(v___x_11_);
if (v_isSharedCheck_28_ == 0)
{
v___x_23_ = v___x_11_;
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
else
{
lean_inc(v_a_21_);
lean_dec(v___x_11_);
v___x_23_ = lean_box(0);
v_isShared_24_ = v_isSharedCheck_28_;
goto v_resetjp_22_;
}
v_resetjp_22_:
{
lean_object* v___x_26_; 
if (v_isShared_24_ == 0)
{
v___x_26_ = v___x_23_;
goto v_reusejp_25_;
}
else
{
lean_object* v_reuseFailAlloc_27_; 
v_reuseFailAlloc_27_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_27_, 0, v_a_21_);
v___x_26_ = v_reuseFailAlloc_27_;
goto v_reusejp_25_;
}
v_reusejp_25_:
{
return v___x_26_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; 
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_));
v___x_56_ = ((lean_object*)(l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_));
v___x_57_ = l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0(v___x_54_, v___x_55_, v___x_56_);
return v___x_57_;
}
}
LEAN_EXPORT void l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_58_;
v_res_58_ = l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_();
stack->m_obj
 = v_res_58_;
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4____boxed(lean_object* v_a_59_){
_start:
{
lean_object* v_res_60_; 
v_res_60_ = l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_();
return v_res_60_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_scopeCandidates(lean_object* v_env_61_, lean_object* v_id_62_, lean_object* v_x_63_){
_start:
{
if (lean_obj_tag(v_x_63_) == 1)
{
lean_object* v_pre_64_; lean_object* v_rest_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
v_pre_64_ = lean_ctor_get(v_x_63_, 0);
lean_inc(v_pre_64_);
lean_inc(v_id_62_);
lean_inc_ref(v_env_61_);
v_rest_65_ = l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_scopeCandidates(v_env_61_, v_id_62_, v_pre_64_);
v___x_66_ = l_Lean_Name_append(v_x_63_, v_id_62_);
v___x_67_ = l_Lean_Environment_isNamespace(v_env_61_, v___x_66_);
if (v___x_67_ == 0)
{
lean_dec(v___x_66_);
return v_rest_65_;
}
else
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set(v___x_68_, 1, v_rest_65_);
return v___x_68_;
}
}
else
{
lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v_id_71_; uint8_t v___x_72_; 
lean_dec(v_x_63_);
v___x_69_ = l_Lean_rootNamespace;
v___x_70_ = lean_box(0);
v_id_71_ = l_Lean_Name_replacePrefix(v_id_62_, v___x_69_, v___x_70_);
v___x_72_ = l_Lean_Environment_isNamespace(v_env_61_, v_id_71_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; 
lean_dec(v_id_71_);
v___x_73_ = lean_box(0);
return v___x_73_;
}
else
{
lean_object* v___x_74_; lean_object* v___x_75_; 
v___x_74_ = lean_box(0);
v___x_75_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_75_, 0, v_id_71_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
return v___x_75_;
}
}
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_77_; lean_object* v___x_78_; 
v___x_77_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__0));
v___x_78_ = l_Lean_stringToMessageData(v___x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0(lean_object* v_n_79_){
_start:
{
lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; 
v___x_80_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__1, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__1_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__1);
v___x_81_ = l_Lean_rootNamespace;
v___x_82_ = l_Lean_Name_append(v___x_81_, v_n_79_);
v___x_83_ = l_Lean_MessageData_ofName(v___x_82_);
v___x_84_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_80_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set(v___x_85_, 1, v___x_80_);
return v___x_85_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_89_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__1));
v___x_90_ = l_Lean_MessageData_ofFormat(v___x_89_);
return v___x_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1(lean_object* v_display_91_, lean_object* v_ns_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; 
v___x_93_ = lean_box(0);
v___x_94_ = l_List_mapTR_loop___redArg(v_display_91_, v_ns_92_, v___x_93_);
v___x_95_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__2, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__2_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__2);
v___x_96_ = l_Lean_MessageData_joinSep(v___x_94_, v___x_95_);
return v___x_96_;
}
}
uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2(uint8_t v___x_97_, lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
return v___x_97_;
}
else
{
uint8_t v___x_99_; 
v___x_99_ = 0;
return v___x_99_;
}
}
}
LEAN_EXPORT void l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_97_ = stack[0].m_num;
lean_object* v_x_98_ = stack[1].m_obj;
uint8_t v_res_100_;
v_res_100_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2(v___x_97_, v_x_98_);
stack->m_num = v_res_100_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2___boxed(lean_object* v___x_101_, lean_object* v_x_102_){
_start:
{
uint8_t v___x_1244__boxed_103_; uint8_t v_res_104_; lean_object* v_r_105_; 
v___x_1244__boxed_103_ = lean_unbox(v___x_101_);
v_res_104_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2(v___x_1244__boxed_103_, v_x_102_);
lean_dec_ref(v_x_102_);
v_r_105_ = lean_box(v_res_104_);
return v_r_105_;
}
}
uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3(lean_object* v_n_106_, uint8_t v___x_107_, lean_object* v_x_108_){
_start:
{
if (lean_obj_tag(v_x_108_) == 0)
{
lean_object* v_except_109_; 
v_except_109_ = lean_ctor_get(v_x_108_, 1);
if (lean_obj_tag(v_except_109_) == 0)
{
lean_object* v_ns_110_; uint8_t v___x_111_; 
v_ns_110_ = lean_ctor_get(v_x_108_, 0);
v___x_111_ = lean_name_eq(v_ns_110_, v_n_106_);
return v___x_111_;
}
else
{
return v___x_107_;
}
}
else
{
return v___x_107_;
}
}
}
LEAN_EXPORT void l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3_0interp(lean_interpreter_value* stack)
{
lean_object* v_n_106_ = stack[0].m_obj;
uint8_t v___x_107_ = stack[1].m_num;
lean_object* v_x_108_ = stack[2].m_obj;
uint8_t v_res_112_;
v_res_112_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3(v_n_106_, v___x_107_, v_x_108_);
stack->m_num = v_res_112_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3___boxed(lean_object* v_n_113_, lean_object* v___x_114_, lean_object* v_x_115_){
_start:
{
uint8_t v___x_1258__boxed_116_; uint8_t v_res_117_; lean_object* v_r_118_; 
v___x_1258__boxed_116_ = lean_unbox(v___x_114_);
v_res_117_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3(v_n_113_, v___x_1258__boxed_116_, v_x_115_);
lean_dec_ref(v_x_115_);
lean_dec(v_n_113_);
v_r_118_ = lean_box(v_res_117_);
return v_r_118_;
}
}
uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4(uint8_t v___x_119_, lean_object* v_currNamespace_120_, lean_object* v_openDecls_121_, uint8_t v___x_122_, lean_object* v___x_123_, lean_object* v_resolved_124_, lean_object* v_n_125_){
_start:
{
lean_object* v___x_126_; lean_object* v___f_127_; uint8_t v___y_129_; uint8_t v___x_132_; 
v___x_126_ = lean_box(v___x_119_);
lean_inc_n(v_n_125_, 2);
v___f_127_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_127_, 0, v_n_125_);
lean_closure_set(v___f_127_, 1, v___x_126_);
v___x_132_ = l_List_elem___redArg(v___x_123_, v_n_125_, v_resolved_124_);
if (v___x_132_ == 0)
{
v___y_129_ = v___x_122_;
goto v___jp_128_;
}
else
{
v___y_129_ = v___x_119_;
goto v___jp_128_;
}
v___jp_128_:
{
if (v___y_129_ == 0)
{
lean_dec_ref(v___f_127_);
lean_dec(v_n_125_);
lean_dec(v_openDecls_121_);
return v___x_119_;
}
else
{
uint8_t v___x_130_; 
v___x_130_ = l_Lean_Name_isPrefixOf(v_n_125_, v_currNamespace_120_);
lean_dec(v_n_125_);
if (v___x_130_ == 0)
{
uint8_t v___x_131_; 
v___x_131_ = l_List_any___redArg(v_openDecls_121_, v___f_127_);
if (v___x_131_ == 0)
{
return v___x_122_;
}
else
{
return v___x_119_;
}
}
else
{
lean_dec_ref(v___f_127_);
lean_dec(v_openDecls_121_);
return v___x_119_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_119_ = stack[0].m_num;
lean_object* v_currNamespace_120_ = stack[1].m_obj;
lean_object* v_openDecls_121_ = stack[2].m_obj;
uint8_t v___x_122_ = stack[3].m_num;
lean_object* v___x_123_ = stack[4].m_obj;
lean_object* v_resolved_124_ = stack[5].m_obj;
lean_object* v_n_125_ = stack[6].m_obj;
uint8_t v_res_133_;
v_res_133_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4(v___x_119_, v_currNamespace_120_, v_openDecls_121_, v___x_122_, v___x_123_, v_resolved_124_, v_n_125_);
stack->m_num = v_res_133_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4___boxed(lean_object* v___x_134_, lean_object* v_currNamespace_135_, lean_object* v_openDecls_136_, lean_object* v___x_137_, lean_object* v___x_138_, lean_object* v_resolved_139_, lean_object* v_n_140_){
_start:
{
uint8_t v___x_1277__boxed_141_; uint8_t v___x_1278__boxed_142_; uint8_t v_res_143_; lean_object* v_r_144_; 
v___x_1277__boxed_141_ = lean_unbox(v___x_134_);
v___x_1278__boxed_142_ = lean_unbox(v___x_137_);
v_res_143_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4(v___x_1277__boxed_141_, v_currNamespace_135_, v_openDecls_136_, v___x_1278__boxed_142_, v___x_138_, v_resolved_139_, v_n_140_);
lean_dec(v_currNamespace_135_);
v_r_144_ = lean_box(v_res_143_);
return v_r_144_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_146_; lean_object* v___x_147_; 
v___x_146_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__0));
v___x_147_ = l_Lean_stringToMessageData(v___x_146_);
return v___x_147_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_149_; lean_object* v___x_150_; 
v___x_149_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__2));
v___x_150_ = l_Lean_stringToMessageData(v___x_149_);
return v___x_150_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__4));
v___x_153_ = l_Lean_stringToMessageData(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__6));
v___x_156_ = l_Lean_stringToMessageData(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__8));
v___x_159_ = l_Lean_stringToMessageData(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__11(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__10));
v___x_162_ = l_Lean_stringToMessageData(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__13(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__12));
v___x_165_ = l_Lean_stringToMessageData(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__15(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__14));
v___x_168_ = l_Lean_stringToMessageData(v___x_167_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__17(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__16));
v___x_171_ = l_Lean_stringToMessageData(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__19(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__18));
v___x_174_ = l_Lean_stringToMessageData(v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__21(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__20));
v___x_177_ = l_Lean_stringToMessageData(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__23(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__22));
v___x_180_ = l_Lean_stringToMessageData(v___x_179_);
return v___x_180_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__25(void){
_start:
{
lean_object* v___x_182_; lean_object* v___x_183_; 
v___x_182_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__24));
v___x_183_ = l_Lean_stringToMessageData(v___x_182_);
return v___x_183_;
}
}
lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(uint8_t v___x_184_, lean_object* v_currNamespace_185_, uint8_t v___x_186_, lean_object* v___x_187_, lean_object* v_resolved_188_, lean_object* v_env_189_, lean_object* v_val_190_, lean_object* v_displayAll_191_, lean_object* v_inst_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v___x_196_, lean_object* v_nsStx_197_, lean_object* v___x_198_, lean_object* v_display_199_, lean_object* v_toPure_200_, lean_object* v_openDecls_201_){
_start:
{
lean_object* v___y_203_; lean_object* v___y_204_; lean_object* v___y_224_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___f_262_; lean_object* v_candidates_263_; lean_object* v___x_264_; lean_object* v_shadowed_265_; uint8_t v___x_266_; 
v___x_260_ = lean_box(v___x_184_);
v___x_261_ = lean_box(v___x_186_);
lean_inc(v_resolved_188_);
lean_inc_n(v_currNamespace_185_, 2);
v___f_262_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_262_, 0, v___x_260_);
lean_closure_set(v___f_262_, 1, v_currNamespace_185_);
lean_closure_set(v___f_262_, 2, v_openDecls_201_);
lean_closure_set(v___f_262_, 3, v___x_261_);
lean_closure_set(v___f_262_, 4, v___x_187_);
lean_closure_set(v___f_262_, 5, v_resolved_188_);
lean_inc(v_val_190_);
v_candidates_263_ = l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_scopeCandidates(v_env_189_, v_val_190_, v_currNamespace_185_);
v___x_264_ = lean_box(0);
v_shadowed_265_ = l_List_filterTR_loop___redArg(v___f_262_, v_candidates_263_, v___x_264_);
v___x_266_ = l_List_isEmpty___redArg(v_shadowed_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; lean_object* v___x_268_; uint8_t v___x_269_; 
lean_dec(v_toPure_200_);
v___x_267_ = l_List_lengthTR___redArg(v_shadowed_265_);
v___x_268_ = lean_unsigned_to_nat(1u);
v___x_269_ = lean_nat_dec_eq(v___x_267_, v___x_268_);
lean_dec(v___x_267_);
if (v___x_269_ == 0)
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; 
lean_inc_ref(v_displayAll_191_);
v___x_270_ = lean_apply_1(v_displayAll_191_, v_shadowed_265_);
v___x_271_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__23, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__23_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__23);
v___x_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_272_, 0, v___x_270_);
lean_ctor_set(v___x_272_, 1, v___x_271_);
v___y_224_ = v___x_272_;
goto v___jp_223_;
}
else
{
lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
lean_inc_ref(v_displayAll_191_);
v___x_273_ = lean_apply_1(v_displayAll_191_, v_shadowed_265_);
v___x_274_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__25, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__25_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__25);
v___x_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_273_);
lean_ctor_set(v___x_275_, 1, v___x_274_);
v___y_224_ = v___x_275_;
goto v___jp_223_;
}
}
else
{
lean_object* v___x_276_; lean_object* v___x_277_; 
lean_dec(v_shadowed_265_);
lean_dec_ref(v_display_199_);
lean_dec(v_nsStx_197_);
lean_dec_ref(v___x_196_);
lean_dec_ref(v_inst_195_);
lean_dec(v_inst_194_);
lean_dec_ref(v_inst_193_);
lean_dec_ref(v_inst_192_);
lean_dec_ref(v_displayAll_191_);
lean_dec(v_val_190_);
lean_dec(v_resolved_188_);
lean_dec(v_currNamespace_185_);
v___x_276_ = lean_box(0);
v___x_277_ = lean_apply_2(v_toPure_200_, lean_box(0), v___x_276_);
return v___x_277_;
}
v___jp_202_:
{
lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_205_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1);
v___x_206_ = l_Lean_MessageData_ofName(v_val_190_);
v___x_207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3);
v___x_209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_apply_1(v_displayAll_191_, v_resolved_188_);
v___x_211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_209_);
lean_ctor_set(v___x_211_, 1, v___x_210_);
v___x_212_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5);
v___x_213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_211_);
lean_ctor_set(v___x_213_, 1, v___x_212_);
v___x_214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_213_);
lean_ctor_set(v___x_214_, 1, v___y_203_);
v___x_215_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7);
v___x_216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_214_);
lean_ctor_set(v___x_216_, 1, v___x_215_);
v___x_217_ = l_Lean_MessageData_ofName(v_currNamespace_185_);
v___x_218_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_218_, 0, v___x_216_);
lean_ctor_set(v___x_218_, 1, v___x_217_);
v___x_219_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9);
v___x_220_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_220_, 0, v___x_218_);
lean_ctor_set(v___x_220_, 1, v___x_219_);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_220_);
lean_ctor_set(v___x_221_, 1, v___y_204_);
v___x_222_ = l_Lean_Linter_logLint___redArg(v_inst_192_, v_inst_193_, v_inst_194_, v_inst_195_, v___x_196_, v_nsStx_197_, v___x_221_);
return v___x_222_;
}
v___jp_223_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v_hint_232_; 
v___x_225_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__11, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__11_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__11);
v___x_226_ = l_Lean_rootNamespace;
v___x_227_ = l_List_head_x21___redArg(v___x_198_, v_resolved_188_);
v___x_228_ = l_Lean_Name_append(v___x_226_, v___x_227_);
v___x_229_ = l_Lean_MessageData_ofName(v___x_228_);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_225_);
lean_ctor_set(v___x_230_, 1, v___x_229_);
v___x_231_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__13, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__13_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__13);
v_hint_232_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_hint_232_, 0, v___x_230_);
lean_ctor_set(v_hint_232_, 1, v___x_231_);
if (lean_obj_tag(v_resolved_188_) == 1)
{
lean_object* v_tail_233_; 
v_tail_233_ = lean_ctor_get(v_resolved_188_, 1);
if (lean_obj_tag(v_tail_233_) == 0)
{
lean_object* v_head_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_258_; 
lean_dec_ref(v_displayAll_191_);
v_head_234_ = lean_ctor_get(v_resolved_188_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v_resolved_188_);
if (v_isSharedCheck_258_ == 0)
{
lean_object* v_unused_259_; 
v_unused_259_ = lean_ctor_get(v_resolved_188_, 1);
lean_dec(v_unused_259_);
v___x_236_ = v_resolved_188_;
v_isShared_237_ = v_isSharedCheck_258_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_head_234_);
lean_dec(v_resolved_188_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_258_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_238_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1);
v___x_239_ = l_Lean_MessageData_ofName(v_val_190_);
if (v_isShared_237_ == 0)
{
lean_ctor_set_tag(v___x_236_, 7);
lean_ctor_set(v___x_236_, 1, v___x_239_);
lean_ctor_set(v___x_236_, 0, v___x_238_);
v___x_241_ = v___x_236_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_257_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_242_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__15, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__15_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__15);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_apply_1(v_display_199_, v_head_234_);
v___x_245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__17, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__17_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__17);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = l_Lean_MessageData_ofName(v_currNamespace_185_);
v___x_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__19, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__19_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__19);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___y_224_);
v___x_253_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__21, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__21_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__21);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v_hint_232_);
v___x_256_ = l_Lean_Linter_logLint___redArg(v_inst_192_, v_inst_193_, v_inst_194_, v_inst_195_, v___x_196_, v_nsStx_197_, v___x_255_);
return v___x_256_;
}
}
}
else
{
lean_dec_ref(v_display_199_);
v___y_203_ = v___y_224_;
v___y_204_ = v_hint_232_;
goto v___jp_202_;
}
}
else
{
lean_dec_ref(v_display_199_);
v___y_203_ = v___y_224_;
v___y_204_ = v_hint_232_;
goto v___jp_202_;
}
}
}
}
LEAN_EXPORT void l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_184_ = stack[0].m_num;
lean_object* v_currNamespace_185_ = stack[1].m_obj;
uint8_t v___x_186_ = stack[2].m_num;
lean_object* v___x_187_ = stack[3].m_obj;
lean_object* v_resolved_188_ = stack[4].m_obj;
lean_object* v_env_189_ = stack[5].m_obj;
lean_object* v_val_190_ = stack[6].m_obj;
lean_object* v_displayAll_191_ = stack[7].m_obj;
lean_object* v_inst_192_ = stack[8].m_obj;
lean_object* v_inst_193_ = stack[9].m_obj;
lean_object* v_inst_194_ = stack[10].m_obj;
lean_object* v_inst_195_ = stack[11].m_obj;
lean_object* v___x_196_ = stack[12].m_obj;
lean_object* v_nsStx_197_ = stack[13].m_obj;
lean_object* v___x_198_ = stack[14].m_obj;
lean_object* v_display_199_ = stack[15].m_obj;
lean_object* v_toPure_200_ = stack[16].m_obj;
lean_object* v_openDecls_201_ = stack[17].m_obj;
lean_object* v_res_278_;
v_res_278_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(v___x_184_, v_currNamespace_185_, v___x_186_, v___x_187_, v_resolved_188_, v_env_189_, v_val_190_, v_displayAll_191_, v_inst_192_, v_inst_193_, v_inst_194_, v_inst_195_, v___x_196_, v_nsStx_197_, v___x_198_, v_display_199_, v_toPure_200_, v_openDecls_201_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_279_ = _args[0];
lean_object* v_currNamespace_280_ = _args[1];
lean_object* v___x_281_ = _args[2];
lean_object* v___x_282_ = _args[3];
lean_object* v_resolved_283_ = _args[4];
lean_object* v_env_284_ = _args[5];
lean_object* v_val_285_ = _args[6];
lean_object* v_displayAll_286_ = _args[7];
lean_object* v_inst_287_ = _args[8];
lean_object* v_inst_288_ = _args[9];
lean_object* v_inst_289_ = _args[10];
lean_object* v_inst_290_ = _args[11];
lean_object* v___x_291_ = _args[12];
lean_object* v_nsStx_292_ = _args[13];
lean_object* v___x_293_ = _args[14];
lean_object* v_display_294_ = _args[15];
lean_object* v_toPure_295_ = _args[16];
lean_object* v_openDecls_296_ = _args[17];
_start:
{
uint8_t v___x_1394__boxed_297_; uint8_t v___x_1395__boxed_298_; lean_object* v_res_299_; 
v___x_1394__boxed_297_ = lean_unbox(v___x_279_);
v___x_1395__boxed_298_ = lean_unbox(v___x_281_);
v_res_299_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(v___x_1394__boxed_297_, v_currNamespace_280_, v___x_1395__boxed_298_, v___x_282_, v_resolved_283_, v_env_284_, v_val_285_, v_displayAll_286_, v_inst_287_, v_inst_288_, v_inst_289_, v_inst_290_, v___x_291_, v_nsStx_292_, v___x_293_, v_display_294_, v_toPure_295_, v_openDecls_296_);
lean_dec(v___x_293_);
return v_res_299_;
}
}
lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(uint8_t v___x_300_, uint8_t v___x_301_, lean_object* v___x_302_, lean_object* v_resolved_303_, lean_object* v_env_304_, lean_object* v_val_305_, lean_object* v_displayAll_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v___x_311_, lean_object* v_nsStx_312_, lean_object* v___x_313_, lean_object* v_display_314_, lean_object* v_toPure_315_, lean_object* v_toBind_316_, lean_object* v_getOpenDecls_317_, lean_object* v_currNamespace_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___f_321_; lean_object* v___x_322_; 
v___x_319_ = lean_box(v___x_300_);
v___x_320_ = lean_box(v___x_301_);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___boxed), 18, 17);
lean_closure_set(v___f_321_, 0, v___x_319_);
lean_closure_set(v___f_321_, 1, v_currNamespace_318_);
lean_closure_set(v___f_321_, 2, v___x_320_);
lean_closure_set(v___f_321_, 3, v___x_302_);
lean_closure_set(v___f_321_, 4, v_resolved_303_);
lean_closure_set(v___f_321_, 5, v_env_304_);
lean_closure_set(v___f_321_, 6, v_val_305_);
lean_closure_set(v___f_321_, 7, v_displayAll_306_);
lean_closure_set(v___f_321_, 8, v_inst_307_);
lean_closure_set(v___f_321_, 9, v_inst_308_);
lean_closure_set(v___f_321_, 10, v_inst_309_);
lean_closure_set(v___f_321_, 11, v_inst_310_);
lean_closure_set(v___f_321_, 12, v___x_311_);
lean_closure_set(v___f_321_, 13, v_nsStx_312_);
lean_closure_set(v___f_321_, 14, v___x_313_);
lean_closure_set(v___f_321_, 15, v_display_314_);
lean_closure_set(v___f_321_, 16, v_toPure_315_);
v___x_322_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v_getOpenDecls_317_, v___f_321_);
return v___x_322_;
}
}
LEAN_EXPORT void l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_300_ = stack[0].m_num;
uint8_t v___x_301_ = stack[1].m_num;
lean_object* v___x_302_ = stack[2].m_obj;
lean_object* v_resolved_303_ = stack[3].m_obj;
lean_object* v_env_304_ = stack[4].m_obj;
lean_object* v_val_305_ = stack[5].m_obj;
lean_object* v_displayAll_306_ = stack[6].m_obj;
lean_object* v_inst_307_ = stack[7].m_obj;
lean_object* v_inst_308_ = stack[8].m_obj;
lean_object* v_inst_309_ = stack[9].m_obj;
lean_object* v_inst_310_ = stack[10].m_obj;
lean_object* v___x_311_ = stack[11].m_obj;
lean_object* v_nsStx_312_ = stack[12].m_obj;
lean_object* v___x_313_ = stack[13].m_obj;
lean_object* v_display_314_ = stack[14].m_obj;
lean_object* v_toPure_315_ = stack[15].m_obj;
lean_object* v_toBind_316_ = stack[16].m_obj;
lean_object* v_getOpenDecls_317_ = stack[17].m_obj;
lean_object* v_currNamespace_318_ = stack[18].m_obj;
lean_object* v_res_323_;
v_res_323_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(v___x_300_, v___x_301_, v___x_302_, v_resolved_303_, v_env_304_, v_val_305_, v_displayAll_306_, v_inst_307_, v_inst_308_, v_inst_309_, v_inst_310_, v___x_311_, v_nsStx_312_, v___x_313_, v_display_314_, v_toPure_315_, v_toBind_316_, v_getOpenDecls_317_, v_currNamespace_318_);
stack->m_obj
 = v_res_323_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed(lean_object** _args){
lean_object* v___x_324_ = _args[0];
lean_object* v___x_325_ = _args[1];
lean_object* v___x_326_ = _args[2];
lean_object* v_resolved_327_ = _args[3];
lean_object* v_env_328_ = _args[4];
lean_object* v_val_329_ = _args[5];
lean_object* v_displayAll_330_ = _args[6];
lean_object* v_inst_331_ = _args[7];
lean_object* v_inst_332_ = _args[8];
lean_object* v_inst_333_ = _args[9];
lean_object* v_inst_334_ = _args[10];
lean_object* v___x_335_ = _args[11];
lean_object* v_nsStx_336_ = _args[12];
lean_object* v___x_337_ = _args[13];
lean_object* v_display_338_ = _args[14];
lean_object* v_toPure_339_ = _args[15];
lean_object* v_toBind_340_ = _args[16];
lean_object* v_getOpenDecls_341_ = _args[17];
lean_object* v_currNamespace_342_ = _args[18];
_start:
{
uint8_t v___x_1741__boxed_343_; uint8_t v___x_1742__boxed_344_; lean_object* v_res_345_; 
v___x_1741__boxed_343_ = lean_unbox(v___x_324_);
v___x_1742__boxed_344_ = lean_unbox(v___x_325_);
v_res_345_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(v___x_1741__boxed_343_, v___x_1742__boxed_344_, v___x_326_, v_resolved_327_, v_env_328_, v_val_329_, v_displayAll_330_, v_inst_331_, v_inst_332_, v_inst_333_, v_inst_334_, v___x_335_, v_nsStx_336_, v___x_337_, v_display_338_, v_toPure_339_, v_toBind_340_, v_getOpenDecls_341_, v_currNamespace_342_);
return v_res_345_;
}
}
lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(lean_object* v_inst_346_, uint8_t v___x_347_, uint8_t v___x_348_, lean_object* v___x_349_, lean_object* v_resolved_350_, lean_object* v_val_351_, lean_object* v_displayAll_352_, lean_object* v_inst_353_, lean_object* v_inst_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v___x_357_, lean_object* v_nsStx_358_, lean_object* v___x_359_, lean_object* v_display_360_, lean_object* v_toPure_361_, lean_object* v_toBind_362_, lean_object* v_env_363_){
_start:
{
lean_object* v_getCurrNamespace_364_; lean_object* v_getOpenDecls_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___f_368_; lean_object* v___x_369_; 
v_getCurrNamespace_364_ = lean_ctor_get(v_inst_346_, 0);
lean_inc(v_getCurrNamespace_364_);
v_getOpenDecls_365_ = lean_ctor_get(v_inst_346_, 1);
lean_inc(v_getOpenDecls_365_);
lean_dec_ref(v_inst_346_);
v___x_366_ = lean_box(v___x_347_);
v___x_367_ = lean_box(v___x_348_);
lean_inc(v_toBind_362_);
v___f_368_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed), 19, 18);
lean_closure_set(v___f_368_, 0, v___x_366_);
lean_closure_set(v___f_368_, 1, v___x_367_);
lean_closure_set(v___f_368_, 2, v___x_349_);
lean_closure_set(v___f_368_, 3, v_resolved_350_);
lean_closure_set(v___f_368_, 4, v_env_363_);
lean_closure_set(v___f_368_, 5, v_val_351_);
lean_closure_set(v___f_368_, 6, v_displayAll_352_);
lean_closure_set(v___f_368_, 7, v_inst_353_);
lean_closure_set(v___f_368_, 8, v_inst_354_);
lean_closure_set(v___f_368_, 9, v_inst_355_);
lean_closure_set(v___f_368_, 10, v_inst_356_);
lean_closure_set(v___f_368_, 11, v___x_357_);
lean_closure_set(v___f_368_, 12, v_nsStx_358_);
lean_closure_set(v___f_368_, 13, v___x_359_);
lean_closure_set(v___f_368_, 14, v_display_360_);
lean_closure_set(v___f_368_, 15, v_toPure_361_);
lean_closure_set(v___f_368_, 16, v_toBind_362_);
lean_closure_set(v___f_368_, 17, v_getOpenDecls_365_);
v___x_369_ = lean_apply_4(v_toBind_362_, lean_box(0), lean_box(0), v_getCurrNamespace_364_, v___f_368_);
return v___x_369_;
}
}
LEAN_EXPORT void l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_346_ = stack[0].m_obj;
uint8_t v___x_347_ = stack[1].m_num;
uint8_t v___x_348_ = stack[2].m_num;
lean_object* v___x_349_ = stack[3].m_obj;
lean_object* v_resolved_350_ = stack[4].m_obj;
lean_object* v_val_351_ = stack[5].m_obj;
lean_object* v_displayAll_352_ = stack[6].m_obj;
lean_object* v_inst_353_ = stack[7].m_obj;
lean_object* v_inst_354_ = stack[8].m_obj;
lean_object* v_inst_355_ = stack[9].m_obj;
lean_object* v_inst_356_ = stack[10].m_obj;
lean_object* v___x_357_ = stack[11].m_obj;
lean_object* v_nsStx_358_ = stack[12].m_obj;
lean_object* v___x_359_ = stack[13].m_obj;
lean_object* v_display_360_ = stack[14].m_obj;
lean_object* v_toPure_361_ = stack[15].m_obj;
lean_object* v_toBind_362_ = stack[16].m_obj;
lean_object* v_env_363_ = stack[17].m_obj;
lean_object* v_res_370_;
v_res_370_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(v_inst_346_, v___x_347_, v___x_348_, v___x_349_, v_resolved_350_, v_val_351_, v_displayAll_352_, v_inst_353_, v_inst_354_, v_inst_355_, v_inst_356_, v___x_357_, v_nsStx_358_, v___x_359_, v_display_360_, v_toPure_361_, v_toBind_362_, v_env_363_);
stack->m_obj
 = v_res_370_;
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_inst_371_ = _args[0];
lean_object* v___x_372_ = _args[1];
lean_object* v___x_373_ = _args[2];
lean_object* v___x_374_ = _args[3];
lean_object* v_resolved_375_ = _args[4];
lean_object* v_val_376_ = _args[5];
lean_object* v_displayAll_377_ = _args[6];
lean_object* v_inst_378_ = _args[7];
lean_object* v_inst_379_ = _args[8];
lean_object* v_inst_380_ = _args[9];
lean_object* v_inst_381_ = _args[10];
lean_object* v___x_382_ = _args[11];
lean_object* v_nsStx_383_ = _args[12];
lean_object* v___x_384_ = _args[13];
lean_object* v_display_385_ = _args[14];
lean_object* v_toPure_386_ = _args[15];
lean_object* v_toBind_387_ = _args[16];
lean_object* v_env_388_ = _args[17];
_start:
{
uint8_t v___x_1804__boxed_389_; uint8_t v___x_1805__boxed_390_; lean_object* v_res_391_; 
v___x_1804__boxed_389_ = lean_unbox(v___x_372_);
v___x_1805__boxed_390_ = lean_unbox(v___x_373_);
v_res_391_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(v_inst_371_, v___x_1804__boxed_389_, v___x_1805__boxed_390_, v___x_374_, v_resolved_375_, v_val_376_, v_displayAll_377_, v_inst_378_, v_inst_379_, v_inst_380_, v_inst_381_, v___x_382_, v_nsStx_383_, v___x_384_, v_display_385_, v_toPure_386_, v_toBind_387_, v_env_388_);
return v_res_391_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(lean_object* v_toPure_392_, lean_object* v_nsStx_393_, lean_object* v_inst_394_, lean_object* v___x_395_, lean_object* v_resolved_396_, lean_object* v_inst_397_, lean_object* v_displayAll_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v___x_403_, lean_object* v_display_404_, lean_object* v_toBind_405_, lean_object* v_____do__lift_406_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = l_Lean_Linter_linter_ambiguousOpen;
v___x_408_ = l_Lean_Linter_getLinterValue(v___x_407_, v_____do__lift_406_);
if (v___x_408_ == 0)
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v_toBind_405_);
lean_dec_ref(v_display_404_);
lean_dec(v___x_403_);
lean_dec_ref(v_inst_402_);
lean_dec(v_inst_401_);
lean_dec_ref(v_inst_400_);
lean_dec_ref(v_inst_399_);
lean_dec_ref(v_displayAll_398_);
lean_dec_ref(v_inst_397_);
lean_dec(v_resolved_396_);
lean_dec_ref(v___x_395_);
lean_dec_ref(v_inst_394_);
lean_dec(v_nsStx_393_);
v___x_409_ = lean_box(0);
v___x_410_ = lean_apply_2(v_toPure_392_, lean_box(0), v___x_409_);
return v___x_410_;
}
else
{
if (lean_obj_tag(v_nsStx_393_) == 3)
{
lean_object* v_info_411_; 
v_info_411_ = lean_ctor_get(v_nsStx_393_, 0);
if (lean_obj_tag(v_info_411_) == 0)
{
lean_object* v_val_412_; lean_object* v_preresolved_413_; lean_object* v___x_414_; lean_object* v___f_415_; uint8_t v___x_416_; 
v_val_412_ = lean_ctor_get(v_nsStx_393_, 2);
lean_inc(v_val_412_);
v_preresolved_413_ = lean_ctor_get(v_nsStx_393_, 3);
v___x_414_ = lean_box(v___x_408_);
v___f_415_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_415_, 0, v___x_414_);
lean_inc(v_preresolved_413_);
v___x_416_ = l_List_any___redArg(v_preresolved_413_, v___f_415_);
if (v___x_416_ == 0)
{
lean_object* v_getEnv_417_; lean_object* v_resolved_418_; lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___f_421_; lean_object* v___x_422_; 
v_getEnv_417_ = lean_ctor_get(v_inst_394_, 0);
lean_inc(v_getEnv_417_);
lean_dec_ref(v_inst_394_);
lean_inc_ref(v___x_395_);
v_resolved_418_ = l_List_eraseDups___redArg(v___x_395_, v_resolved_396_);
v___x_419_ = lean_box(v___x_416_);
v___x_420_ = lean_box(v___x_408_);
lean_inc(v_toBind_405_);
v___f_421_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed), 18, 17);
lean_closure_set(v___f_421_, 0, v_inst_397_);
lean_closure_set(v___f_421_, 1, v___x_419_);
lean_closure_set(v___f_421_, 2, v___x_420_);
lean_closure_set(v___f_421_, 3, v___x_395_);
lean_closure_set(v___f_421_, 4, v_resolved_418_);
lean_closure_set(v___f_421_, 5, v_val_412_);
lean_closure_set(v___f_421_, 6, v_displayAll_398_);
lean_closure_set(v___f_421_, 7, v_inst_399_);
lean_closure_set(v___f_421_, 8, v_inst_400_);
lean_closure_set(v___f_421_, 9, v_inst_401_);
lean_closure_set(v___f_421_, 10, v_inst_402_);
lean_closure_set(v___f_421_, 11, v___x_407_);
lean_closure_set(v___f_421_, 12, v_nsStx_393_);
lean_closure_set(v___f_421_, 13, v___x_403_);
lean_closure_set(v___f_421_, 14, v_display_404_);
lean_closure_set(v___f_421_, 15, v_toPure_392_);
lean_closure_set(v___f_421_, 16, v_toBind_405_);
v___x_422_ = lean_apply_4(v_toBind_405_, lean_box(0), lean_box(0), v_getEnv_417_, v___f_421_);
return v___x_422_;
}
else
{
lean_object* v___x_423_; lean_object* v___x_424_; 
lean_dec(v_val_412_);
lean_dec_ref_known(v_nsStx_393_, 4);
lean_dec(v_toBind_405_);
lean_dec_ref(v_display_404_);
lean_dec(v___x_403_);
lean_dec_ref(v_inst_402_);
lean_dec(v_inst_401_);
lean_dec_ref(v_inst_400_);
lean_dec_ref(v_inst_399_);
lean_dec_ref(v_displayAll_398_);
lean_dec_ref(v_inst_397_);
lean_dec(v_resolved_396_);
lean_dec_ref(v___x_395_);
lean_dec_ref(v_inst_394_);
v___x_423_ = lean_box(0);
v___x_424_ = lean_apply_2(v_toPure_392_, lean_box(0), v___x_423_);
return v___x_424_;
}
}
else
{
lean_object* v___x_425_; lean_object* v___x_426_; 
lean_dec_ref_known(v_nsStx_393_, 4);
lean_dec(v_toBind_405_);
lean_dec_ref(v_display_404_);
lean_dec(v___x_403_);
lean_dec_ref(v_inst_402_);
lean_dec(v_inst_401_);
lean_dec_ref(v_inst_400_);
lean_dec_ref(v_inst_399_);
lean_dec_ref(v_displayAll_398_);
lean_dec_ref(v_inst_397_);
lean_dec(v_resolved_396_);
lean_dec_ref(v___x_395_);
lean_dec_ref(v_inst_394_);
v___x_425_ = lean_box(0);
v___x_426_ = lean_apply_2(v_toPure_392_, lean_box(0), v___x_425_);
return v___x_426_;
}
}
else
{
lean_object* v___x_427_; lean_object* v___x_428_; 
lean_dec(v_toBind_405_);
lean_dec_ref(v_display_404_);
lean_dec(v___x_403_);
lean_dec_ref(v_inst_402_);
lean_dec(v_inst_401_);
lean_dec_ref(v_inst_400_);
lean_dec_ref(v_inst_399_);
lean_dec_ref(v_displayAll_398_);
lean_dec_ref(v_inst_397_);
lean_dec(v_resolved_396_);
lean_dec_ref(v___x_395_);
lean_dec_ref(v_inst_394_);
lean_dec(v_nsStx_393_);
v___x_427_ = lean_box(0);
v___x_428_ = lean_apply_2(v_toPure_392_, lean_box(0), v___x_427_);
return v___x_428_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed(lean_object* v_toPure_429_, lean_object* v_nsStx_430_, lean_object* v_inst_431_, lean_object* v___x_432_, lean_object* v_resolved_433_, lean_object* v_inst_434_, lean_object* v_displayAll_435_, lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v___x_440_, lean_object* v_display_441_, lean_object* v_toBind_442_, lean_object* v_____do__lift_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(v_toPure_429_, v_nsStx_430_, v_inst_431_, v___x_432_, v_resolved_433_, v_inst_434_, v_displayAll_435_, v_inst_436_, v_inst_437_, v_inst_438_, v_inst_439_, v___x_440_, v_display_441_, v_toBind_442_, v_____do__lift_443_);
lean_dec_ref(v_____do__lift_443_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg(lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_nsStx_455_, lean_object* v_resolved_456_){
_start:
{
lean_object* v_toApplicative_457_; lean_object* v_toBind_458_; lean_object* v_toPure_459_; lean_object* v_display_460_; lean_object* v_displayAll_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___f_465_; lean_object* v___x_466_; 
v_toApplicative_457_ = lean_ctor_get(v_inst_449_, 0);
v_toBind_458_ = lean_ctor_get(v_inst_449_, 1);
lean_inc_n(v_toBind_458_, 2);
v_toPure_459_ = lean_ctor_get(v_toApplicative_457_, 1);
lean_inc(v_toPure_459_);
v_display_460_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0));
v_displayAll_461_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___closed__1));
v___x_462_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___closed__2));
v___x_463_ = lean_box(0);
lean_inc_ref(v_inst_450_);
lean_inc_ref(v_inst_451_);
lean_inc_ref(v_inst_449_);
v___x_464_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_449_, v_inst_451_, v_inst_450_);
v___f_465_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed), 15, 14);
lean_closure_set(v___f_465_, 0, v_toPure_459_);
lean_closure_set(v___f_465_, 1, v_nsStx_455_);
lean_closure_set(v___f_465_, 2, v_inst_450_);
lean_closure_set(v___f_465_, 3, v___x_462_);
lean_closure_set(v___f_465_, 4, v_resolved_456_);
lean_closure_set(v___f_465_, 5, v_inst_454_);
lean_closure_set(v___f_465_, 6, v_displayAll_461_);
lean_closure_set(v___f_465_, 7, v_inst_449_);
lean_closure_set(v___f_465_, 8, v_inst_452_);
lean_closure_set(v___f_465_, 9, v_inst_453_);
lean_closure_set(v___f_465_, 10, v_inst_451_);
lean_closure_set(v___f_465_, 11, v___x_463_);
lean_closure_set(v___f_465_, 12, v_display_460_);
lean_closure_set(v___f_465_, 13, v_toBind_458_);
v___x_466_ = lean_apply_4(v_toBind_458_, lean_box(0), lean_box(0), v___x_464_, v___f_465_);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen(lean_object* v_m_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_nsStx_474_, lean_object* v_resolved_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v_inst_468_, v_inst_469_, v_inst_470_, v_inst_471_, v_inst_472_, v_inst_473_, v_nsStx_474_, v_resolved_475_);
return v___x_476_;
}
}
lean_object* runtime_initialize_Lean_ResolveName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_AmbiguousOpen(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_ResolveName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_ambiguousOpen = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_ambiguousOpen);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_AmbiguousOpen(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_ResolveName(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_AmbiguousOpen(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_ResolveName(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_AmbiguousOpen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_AmbiguousOpen(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_AmbiguousOpen(builtin);
}
#ifdef __cplusplus
}
#endif
