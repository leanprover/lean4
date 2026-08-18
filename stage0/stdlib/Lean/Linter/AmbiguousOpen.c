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
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterTR_loop___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
lean_object* l_List_eraseDups___redArg(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofFormat(lean_object*);
lean_object* l_Lean_MessageData_joinSep(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed(lean_object**);
static const lean_closure_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___closed__0 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0_value;
static const lean_closure_object l_Lean_Linter_checkAmbiguousOpen___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0_value)} };
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___closed__1 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v___x_53_ = ((lean_object*)(l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_));
v___x_54_ = ((lean_object*)(l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_));
v___x_55_ = ((lean_object*)(l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_));
v___x_56_ = l_Lean_Option_register___at___00__private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4__spec__0(v___x_53_, v___x_54_, v___x_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4____boxed(lean_object* v_a_57_){
_start:
{
lean_object* v_res_58_; 
v_res_58_ = l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_initFn_00___x40_Lean_Linter_AmbiguousOpen_603296505____hygCtx___hyg_4_();
return v_res_58_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_scopeCandidates(lean_object* v_env_59_, lean_object* v_id_60_, lean_object* v_x_61_){
_start:
{
if (lean_obj_tag(v_x_61_) == 1)
{
lean_object* v_pre_62_; lean_object* v_rest_63_; lean_object* v___x_64_; uint8_t v___x_65_; 
v_pre_62_ = lean_ctor_get(v_x_61_, 0);
lean_inc(v_pre_62_);
lean_inc(v_id_60_);
lean_inc_ref(v_env_59_);
v_rest_63_ = l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_scopeCandidates(v_env_59_, v_id_60_, v_pre_62_);
v___x_64_ = l_Lean_Name_append(v_x_61_, v_id_60_);
v___x_65_ = l_Lean_Environment_isNamespace(v_env_59_, v___x_64_);
if (v___x_65_ == 0)
{
lean_dec(v___x_64_);
return v_rest_63_;
}
else
{
lean_object* v___x_66_; 
v___x_66_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v_rest_63_);
return v___x_66_;
}
}
else
{
lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v_id_69_; uint8_t v___x_70_; 
lean_dec(v_x_61_);
v___x_67_ = l_Lean_rootNamespace;
v___x_68_ = lean_box(0);
v_id_69_ = l_Lean_Name_replacePrefix(v_id_60_, v___x_67_, v___x_68_);
v___x_70_ = l_Lean_Environment_isNamespace(v_env_59_, v_id_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec(v_id_69_);
v___x_71_ = lean_box(0);
return v___x_71_;
}
else
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_box(0);
v___x_73_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_73_, 0, v_id_69_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
return v___x_73_;
}
}
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_75_; lean_object* v___x_76_; 
v___x_75_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__0));
v___x_76_ = l_Lean_stringToMessageData(v___x_75_);
return v___x_76_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0(lean_object* v_n_77_){
_start:
{
lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; 
v___x_78_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__1, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__1_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__0___closed__1);
v___x_79_ = l_Lean_rootNamespace;
v___x_80_ = l_Lean_Name_append(v___x_79_, v_n_77_);
v___x_81_ = l_Lean_MessageData_ofName(v___x_80_);
v___x_82_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_82_, 0, v___x_78_);
lean_ctor_set(v___x_82_, 1, v___x_81_);
v___x_83_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
lean_ctor_set(v___x_83_, 1, v___x_78_);
return v___x_83_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__2(void){
_start:
{
lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_87_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__1));
v___x_88_ = l_Lean_MessageData_ofFormat(v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1(lean_object* v_display_89_, lean_object* v_ns_90_){
_start:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_91_ = lean_box(0);
v___x_92_ = l_List_mapTR_loop___redArg(v_display_89_, v_ns_90_, v___x_91_);
v___x_93_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__2, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__2_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__1___closed__2);
v___x_94_ = l_Lean_MessageData_joinSep(v___x_92_, v___x_93_);
return v___x_94_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2(uint8_t v___x_95_, lean_object* v_x_96_){
_start:
{
if (lean_obj_tag(v_x_96_) == 0)
{
return v___x_95_;
}
else
{
uint8_t v___x_97_; 
v___x_97_ = 0;
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2___boxed(lean_object* v___x_98_, lean_object* v_x_99_){
_start:
{
uint8_t v___x_2228__boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v___x_2228__boxed_100_ = lean_unbox(v___x_98_);
v_res_101_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2(v___x_2228__boxed_100_, v_x_99_);
lean_dec_ref(v_x_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3(lean_object* v_n_103_, uint8_t v___x_104_, lean_object* v_x_105_){
_start:
{
if (lean_obj_tag(v_x_105_) == 0)
{
lean_object* v_except_106_; 
v_except_106_ = lean_ctor_get(v_x_105_, 1);
if (lean_obj_tag(v_except_106_) == 0)
{
lean_object* v_ns_107_; uint8_t v___x_108_; 
v_ns_107_ = lean_ctor_get(v_x_105_, 0);
v___x_108_ = lean_name_eq(v_ns_107_, v_n_103_);
return v___x_108_;
}
else
{
return v___x_104_;
}
}
else
{
return v___x_104_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3___boxed(lean_object* v_n_109_, lean_object* v___x_110_, lean_object* v_x_111_){
_start:
{
uint8_t v___x_2237__boxed_112_; uint8_t v_res_113_; lean_object* v_r_114_; 
v___x_2237__boxed_112_ = lean_unbox(v___x_110_);
v_res_113_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3(v_n_109_, v___x_2237__boxed_112_, v_x_111_);
lean_dec_ref(v_x_111_);
lean_dec(v_n_109_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4(lean_object* v___x_115_, lean_object* v_resolved_116_, lean_object* v_currNamespace_117_, lean_object* v_openDecls_118_, uint8_t v___x_119_, uint8_t v___x_120_, lean_object* v_n_121_){
_start:
{
uint8_t v___x_122_; 
lean_inc(v_n_121_);
v___x_122_ = l_List_elem___redArg(v___x_115_, v_n_121_, v_resolved_116_);
if (v___x_122_ == 0)
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_Name_isPrefixOf(v_n_121_, v_currNamespace_117_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___f_125_; uint8_t v___x_126_; 
v___x_124_ = lean_box(v___x_123_);
v___f_125_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_125_, 0, v_n_121_);
lean_closure_set(v___f_125_, 1, v___x_124_);
v___x_126_ = l_List_any___redArg(v_openDecls_118_, v___f_125_);
if (v___x_126_ == 0)
{
return v___x_119_;
}
else
{
return v___x_122_;
}
}
else
{
lean_dec(v_n_121_);
lean_dec(v_openDecls_118_);
return v___x_122_;
}
}
else
{
lean_dec(v_n_121_);
lean_dec(v_openDecls_118_);
return v___x_120_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4___boxed(lean_object* v___x_127_, lean_object* v_resolved_128_, lean_object* v_currNamespace_129_, lean_object* v_openDecls_130_, lean_object* v___x_131_, lean_object* v___x_132_, lean_object* v_n_133_){
_start:
{
uint8_t v___x_2250__boxed_134_; uint8_t v___x_2251__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v___x_2250__boxed_134_ = lean_unbox(v___x_131_);
v___x_2251__boxed_135_ = lean_unbox(v___x_132_);
v_res_136_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4(v___x_127_, v_resolved_128_, v_currNamespace_129_, v_openDecls_130_, v___x_2250__boxed_134_, v___x_2251__boxed_135_, v_n_133_);
lean_dec(v_currNamespace_129_);
v_r_137_ = lean_box(v_res_136_);
return v_r_137_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1(void){
_start:
{
lean_object* v___x_139_; lean_object* v___x_140_; 
v___x_139_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__0));
v___x_140_ = l_Lean_stringToMessageData(v___x_139_);
return v___x_140_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3(void){
_start:
{
lean_object* v___x_142_; lean_object* v___x_143_; 
v___x_142_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__2));
v___x_143_ = l_Lean_stringToMessageData(v___x_142_);
return v___x_143_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5(void){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__4));
v___x_146_ = l_Lean_stringToMessageData(v___x_145_);
return v___x_146_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7(void){
_start:
{
lean_object* v___x_148_; lean_object* v___x_149_; 
v___x_148_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__6));
v___x_149_ = l_Lean_stringToMessageData(v___x_148_);
return v___x_149_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9(void){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__8));
v___x_152_ = l_Lean_stringToMessageData(v___x_151_);
return v___x_152_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__11(void){
_start:
{
lean_object* v___x_154_; lean_object* v___x_155_; 
v___x_154_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__10));
v___x_155_ = l_Lean_stringToMessageData(v___x_154_);
return v___x_155_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__13(void){
_start:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__12));
v___x_158_ = l_Lean_stringToMessageData(v___x_157_);
return v___x_158_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__15(void){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_160_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__14));
v___x_161_ = l_Lean_stringToMessageData(v___x_160_);
return v___x_161_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__17(void){
_start:
{
lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_163_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__16));
v___x_164_ = l_Lean_stringToMessageData(v___x_163_);
return v___x_164_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__19(void){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__18));
v___x_167_ = l_Lean_stringToMessageData(v___x_166_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__21(void){
_start:
{
lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_169_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__20));
v___x_170_ = l_Lean_stringToMessageData(v___x_169_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__23(void){
_start:
{
lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_172_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__22));
v___x_173_ = l_Lean_stringToMessageData(v___x_172_);
return v___x_173_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__25(void){
_start:
{
lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_175_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__24));
v___x_176_ = l_Lean_stringToMessageData(v___x_175_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(lean_object* v___x_177_, lean_object* v_resolved_178_, lean_object* v_currNamespace_179_, uint8_t v___x_180_, uint8_t v___x_181_, lean_object* v_env_182_, lean_object* v_val_183_, lean_object* v_displayAll_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v___x_189_, lean_object* v_nsStx_190_, lean_object* v_display_191_, lean_object* v_toApplicative_192_, lean_object* v_openDecls_193_){
_start:
{
lean_object* v___y_195_; lean_object* v___y_196_; lean_object* v___y_216_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___f_255_; lean_object* v_candidates_256_; lean_object* v___x_257_; lean_object* v_shadowed_258_; uint8_t v___x_259_; 
v___x_253_ = lean_box(v___x_180_);
v___x_254_ = lean_box(v___x_181_);
lean_inc_n(v_currNamespace_179_, 2);
lean_inc(v_resolved_178_);
v___f_255_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_255_, 0, v___x_177_);
lean_closure_set(v___f_255_, 1, v_resolved_178_);
lean_closure_set(v___f_255_, 2, v_currNamespace_179_);
lean_closure_set(v___f_255_, 3, v_openDecls_193_);
lean_closure_set(v___f_255_, 4, v___x_253_);
lean_closure_set(v___f_255_, 5, v___x_254_);
lean_inc(v_val_183_);
v_candidates_256_ = l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_scopeCandidates(v_env_182_, v_val_183_, v_currNamespace_179_);
v___x_257_ = lean_box(0);
v_shadowed_258_ = l_List_filterTR_loop___redArg(v___f_255_, v_candidates_256_, v___x_257_);
v___x_259_ = l_List_isEmpty___redArg(v_shadowed_258_);
if (v___x_259_ == 0)
{
lean_object* v___x_260_; lean_object* v___x_261_; uint8_t v___x_262_; 
lean_dec_ref(v_toApplicative_192_);
v___x_260_ = l_List_lengthTR___redArg(v_shadowed_258_);
v___x_261_ = lean_unsigned_to_nat(1u);
v___x_262_ = lean_nat_dec_eq(v___x_260_, v___x_261_);
lean_dec(v___x_260_);
if (v___x_262_ == 0)
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
lean_inc_ref(v_displayAll_184_);
v___x_263_ = lean_apply_1(v_displayAll_184_, v_shadowed_258_);
v___x_264_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__23, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__23_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__23);
v___x_265_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_265_, 0, v___x_263_);
lean_ctor_set(v___x_265_, 1, v___x_264_);
v___y_216_ = v___x_265_;
goto v___jp_215_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
lean_inc_ref(v_displayAll_184_);
v___x_266_ = lean_apply_1(v_displayAll_184_, v_shadowed_258_);
v___x_267_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__25, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__25_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__25);
v___x_268_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_268_, 0, v___x_266_);
lean_ctor_set(v___x_268_, 1, v___x_267_);
v___y_216_ = v___x_268_;
goto v___jp_215_;
}
}
else
{
lean_object* v_toPure_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
lean_dec(v_shadowed_258_);
lean_dec_ref(v_display_191_);
lean_dec(v_nsStx_190_);
lean_dec_ref(v___x_189_);
lean_dec(v_inst_188_);
lean_dec(v_inst_187_);
lean_dec_ref(v_inst_186_);
lean_dec_ref(v_inst_185_);
lean_dec_ref(v_displayAll_184_);
lean_dec(v_val_183_);
lean_dec(v_currNamespace_179_);
lean_dec(v_resolved_178_);
v_toPure_269_ = lean_ctor_get(v_toApplicative_192_, 1);
lean_inc(v_toPure_269_);
lean_dec_ref(v_toApplicative_192_);
v___x_270_ = lean_box(0);
v___x_271_ = lean_apply_2(v_toPure_269_, lean_box(0), v___x_270_);
return v___x_271_;
}
v___jp_194_:
{
lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_197_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1);
v___x_198_ = l_Lean_MessageData_ofName(v_val_183_);
v___x_199_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_199_, 0, v___x_197_);
lean_ctor_set(v___x_199_, 1, v___x_198_);
v___x_200_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3);
v___x_201_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_201_, 0, v___x_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
v___x_202_ = lean_apply_1(v_displayAll_184_, v_resolved_178_);
v___x_203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5);
v___x_205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___y_195_);
v___x_207_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7);
v___x_208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = l_Lean_MessageData_ofName(v_currNamespace_179_);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9);
v___x_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_213_, 0, v___x_212_);
lean_ctor_set(v___x_213_, 1, v___y_196_);
v___x_214_ = l_Lean_Linter_logLint___redArg(v_inst_185_, v_inst_186_, v_inst_187_, v_inst_188_, v___x_189_, v_nsStx_190_, v___x_213_);
return v___x_214_;
}
v___jp_215_:
{
lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v_hint_225_; 
v___x_217_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__11, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__11_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__11);
v___x_218_ = l_Lean_rootNamespace;
v___x_219_ = lean_box(0);
v___x_220_ = l_List_head_x21___redArg(v___x_219_, v_resolved_178_);
v___x_221_ = l_Lean_Name_append(v___x_218_, v___x_220_);
v___x_222_ = l_Lean_MessageData_ofName(v___x_221_);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_217_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__13, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__13_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__13);
v_hint_225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_hint_225_, 0, v___x_223_);
lean_ctor_set(v_hint_225_, 1, v___x_224_);
if (lean_obj_tag(v_resolved_178_) == 1)
{
lean_object* v_tail_226_; 
v_tail_226_ = lean_ctor_get(v_resolved_178_, 1);
if (lean_obj_tag(v_tail_226_) == 0)
{
lean_object* v_head_227_; lean_object* v___x_229_; uint8_t v_isShared_230_; uint8_t v_isSharedCheck_251_; 
lean_dec_ref(v_displayAll_184_);
v_head_227_ = lean_ctor_get(v_resolved_178_, 0);
v_isSharedCheck_251_ = !lean_is_exclusive(v_resolved_178_);
if (v_isSharedCheck_251_ == 0)
{
lean_object* v_unused_252_; 
v_unused_252_ = lean_ctor_get(v_resolved_178_, 1);
lean_dec(v_unused_252_);
v___x_229_ = v_resolved_178_;
v_isShared_230_ = v_isSharedCheck_251_;
goto v_resetjp_228_;
}
else
{
lean_inc(v_head_227_);
lean_dec(v_resolved_178_);
v___x_229_ = lean_box(0);
v_isShared_230_ = v_isSharedCheck_251_;
goto v_resetjp_228_;
}
v_resetjp_228_:
{
lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_234_; 
v___x_231_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1);
v___x_232_ = l_Lean_MessageData_ofName(v_val_183_);
if (v_isShared_230_ == 0)
{
lean_ctor_set_tag(v___x_229_, 7);
lean_ctor_set(v___x_229_, 1, v___x_232_);
lean_ctor_set(v___x_229_, 0, v___x_231_);
v___x_234_ = v___x_229_;
goto v_reusejp_233_;
}
else
{
lean_object* v_reuseFailAlloc_250_; 
v_reuseFailAlloc_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_250_, 0, v___x_231_);
lean_ctor_set(v_reuseFailAlloc_250_, 1, v___x_232_);
v___x_234_ = v_reuseFailAlloc_250_;
goto v_reusejp_233_;
}
v_reusejp_233_:
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; 
v___x_235_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__15, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__15_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__15);
v___x_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_236_, 0, v___x_234_);
lean_ctor_set(v___x_236_, 1, v___x_235_);
v___x_237_ = lean_apply_1(v_display_191_, v_head_227_);
v___x_238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__17, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__17_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__17);
v___x_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = l_Lean_MessageData_ofName(v_currNamespace_179_);
v___x_242_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_242_, 0, v___x_240_);
lean_ctor_set(v___x_242_, 1, v___x_241_);
v___x_243_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__19, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__19_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__19);
v___x_244_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_244_, 0, v___x_242_);
lean_ctor_set(v___x_244_, 1, v___x_243_);
v___x_245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_244_);
lean_ctor_set(v___x_245_, 1, v___y_216_);
v___x_246_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__21, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__21_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__21);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_247_);
lean_ctor_set(v___x_248_, 1, v_hint_225_);
v___x_249_ = l_Lean_Linter_logLint___redArg(v_inst_185_, v_inst_186_, v_inst_187_, v_inst_188_, v___x_189_, v_nsStx_190_, v___x_248_);
return v___x_249_;
}
}
}
else
{
lean_dec_ref(v_display_191_);
v___y_195_ = v___y_216_;
v___y_196_ = v_hint_225_;
goto v___jp_194_;
}
}
else
{
lean_dec_ref(v_display_191_);
v___y_195_ = v___y_216_;
v___y_196_ = v_hint_225_;
goto v___jp_194_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___boxed(lean_object** _args){
lean_object* v___x_272_ = _args[0];
lean_object* v_resolved_273_ = _args[1];
lean_object* v_currNamespace_274_ = _args[2];
lean_object* v___x_275_ = _args[3];
lean_object* v___x_276_ = _args[4];
lean_object* v_env_277_ = _args[5];
lean_object* v_val_278_ = _args[6];
lean_object* v_displayAll_279_ = _args[7];
lean_object* v_inst_280_ = _args[8];
lean_object* v_inst_281_ = _args[9];
lean_object* v_inst_282_ = _args[10];
lean_object* v_inst_283_ = _args[11];
lean_object* v___x_284_ = _args[12];
lean_object* v_nsStx_285_ = _args[13];
lean_object* v_display_286_ = _args[14];
lean_object* v_toApplicative_287_ = _args[15];
lean_object* v_openDecls_288_ = _args[16];
_start:
{
uint8_t v___x_2350__boxed_289_; uint8_t v___x_2351__boxed_290_; lean_object* v_res_291_; 
v___x_2350__boxed_289_ = lean_unbox(v___x_275_);
v___x_2351__boxed_290_ = lean_unbox(v___x_276_);
v_res_291_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(v___x_272_, v_resolved_273_, v_currNamespace_274_, v___x_2350__boxed_289_, v___x_2351__boxed_290_, v_env_277_, v_val_278_, v_displayAll_279_, v_inst_280_, v_inst_281_, v_inst_282_, v_inst_283_, v___x_284_, v_nsStx_285_, v_display_286_, v_toApplicative_287_, v_openDecls_288_);
return v_res_291_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(lean_object* v___x_292_, lean_object* v_resolved_293_, uint8_t v___x_294_, uint8_t v___x_295_, lean_object* v_env_296_, lean_object* v_val_297_, lean_object* v_displayAll_298_, lean_object* v_inst_299_, lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v___x_303_, lean_object* v_nsStx_304_, lean_object* v_display_305_, lean_object* v_toApplicative_306_, lean_object* v_toBind_307_, lean_object* v_getOpenDecls_308_, lean_object* v_currNamespace_309_){
_start:
{
lean_object* v___x_310_; lean_object* v___x_311_; lean_object* v___f_312_; lean_object* v___x_313_; 
v___x_310_ = lean_box(v___x_294_);
v___x_311_ = lean_box(v___x_295_);
v___f_312_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___boxed), 17, 16);
lean_closure_set(v___f_312_, 0, v___x_292_);
lean_closure_set(v___f_312_, 1, v_resolved_293_);
lean_closure_set(v___f_312_, 2, v_currNamespace_309_);
lean_closure_set(v___f_312_, 3, v___x_310_);
lean_closure_set(v___f_312_, 4, v___x_311_);
lean_closure_set(v___f_312_, 5, v_env_296_);
lean_closure_set(v___f_312_, 6, v_val_297_);
lean_closure_set(v___f_312_, 7, v_displayAll_298_);
lean_closure_set(v___f_312_, 8, v_inst_299_);
lean_closure_set(v___f_312_, 9, v_inst_300_);
lean_closure_set(v___f_312_, 10, v_inst_301_);
lean_closure_set(v___f_312_, 11, v_inst_302_);
lean_closure_set(v___f_312_, 12, v___x_303_);
lean_closure_set(v___f_312_, 13, v_nsStx_304_);
lean_closure_set(v___f_312_, 14, v_display_305_);
lean_closure_set(v___f_312_, 15, v_toApplicative_306_);
v___x_313_ = lean_apply_4(v_toBind_307_, lean_box(0), lean_box(0), v_getOpenDecls_308_, v___f_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed(lean_object** _args){
lean_object* v___x_314_ = _args[0];
lean_object* v_resolved_315_ = _args[1];
lean_object* v___x_316_ = _args[2];
lean_object* v___x_317_ = _args[3];
lean_object* v_env_318_ = _args[4];
lean_object* v_val_319_ = _args[5];
lean_object* v_displayAll_320_ = _args[6];
lean_object* v_inst_321_ = _args[7];
lean_object* v_inst_322_ = _args[8];
lean_object* v_inst_323_ = _args[9];
lean_object* v_inst_324_ = _args[10];
lean_object* v___x_325_ = _args[11];
lean_object* v_nsStx_326_ = _args[12];
lean_object* v_display_327_ = _args[13];
lean_object* v_toApplicative_328_ = _args[14];
lean_object* v_toBind_329_ = _args[15];
lean_object* v_getOpenDecls_330_ = _args[16];
lean_object* v_currNamespace_331_ = _args[17];
_start:
{
uint8_t v___x_2564__boxed_332_; uint8_t v___x_2565__boxed_333_; lean_object* v_res_334_; 
v___x_2564__boxed_332_ = lean_unbox(v___x_316_);
v___x_2565__boxed_333_ = lean_unbox(v___x_317_);
v_res_334_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(v___x_314_, v_resolved_315_, v___x_2564__boxed_332_, v___x_2565__boxed_333_, v_env_318_, v_val_319_, v_displayAll_320_, v_inst_321_, v_inst_322_, v_inst_323_, v_inst_324_, v___x_325_, v_nsStx_326_, v_display_327_, v_toApplicative_328_, v_toBind_329_, v_getOpenDecls_330_, v_currNamespace_331_);
return v_res_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(lean_object* v_inst_335_, lean_object* v___x_336_, lean_object* v_resolved_337_, uint8_t v___x_338_, uint8_t v___x_339_, lean_object* v_val_340_, lean_object* v_displayAll_341_, lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_inst_345_, lean_object* v___x_346_, lean_object* v_nsStx_347_, lean_object* v_display_348_, lean_object* v_toApplicative_349_, lean_object* v_toBind_350_, lean_object* v_env_351_){
_start:
{
lean_object* v_getCurrNamespace_352_; lean_object* v_getOpenDecls_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___f_356_; lean_object* v___x_357_; 
v_getCurrNamespace_352_ = lean_ctor_get(v_inst_335_, 0);
lean_inc(v_getCurrNamespace_352_);
v_getOpenDecls_353_ = lean_ctor_get(v_inst_335_, 1);
lean_inc(v_getOpenDecls_353_);
lean_dec_ref(v_inst_335_);
v___x_354_ = lean_box(v___x_338_);
v___x_355_ = lean_box(v___x_339_);
lean_inc(v_toBind_350_);
v___f_356_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed), 18, 17);
lean_closure_set(v___f_356_, 0, v___x_336_);
lean_closure_set(v___f_356_, 1, v_resolved_337_);
lean_closure_set(v___f_356_, 2, v___x_354_);
lean_closure_set(v___f_356_, 3, v___x_355_);
lean_closure_set(v___f_356_, 4, v_env_351_);
lean_closure_set(v___f_356_, 5, v_val_340_);
lean_closure_set(v___f_356_, 6, v_displayAll_341_);
lean_closure_set(v___f_356_, 7, v_inst_342_);
lean_closure_set(v___f_356_, 8, v_inst_343_);
lean_closure_set(v___f_356_, 9, v_inst_344_);
lean_closure_set(v___f_356_, 10, v_inst_345_);
lean_closure_set(v___f_356_, 11, v___x_346_);
lean_closure_set(v___f_356_, 12, v_nsStx_347_);
lean_closure_set(v___f_356_, 13, v_display_348_);
lean_closure_set(v___f_356_, 14, v_toApplicative_349_);
lean_closure_set(v___f_356_, 15, v_toBind_350_);
lean_closure_set(v___f_356_, 16, v_getOpenDecls_353_);
v___x_357_ = lean_apply_4(v_toBind_350_, lean_box(0), lean_box(0), v_getCurrNamespace_352_, v___f_356_);
return v___x_357_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed(lean_object** _args){
lean_object* v_inst_358_ = _args[0];
lean_object* v___x_359_ = _args[1];
lean_object* v_resolved_360_ = _args[2];
lean_object* v___x_361_ = _args[3];
lean_object* v___x_362_ = _args[4];
lean_object* v_val_363_ = _args[5];
lean_object* v_displayAll_364_ = _args[6];
lean_object* v_inst_365_ = _args[7];
lean_object* v_inst_366_ = _args[8];
lean_object* v_inst_367_ = _args[9];
lean_object* v_inst_368_ = _args[10];
lean_object* v___x_369_ = _args[11];
lean_object* v_nsStx_370_ = _args[12];
lean_object* v_display_371_ = _args[13];
lean_object* v_toApplicative_372_ = _args[14];
lean_object* v_toBind_373_ = _args[15];
lean_object* v_env_374_ = _args[16];
_start:
{
uint8_t v___x_2600__boxed_375_; uint8_t v___x_2601__boxed_376_; lean_object* v_res_377_; 
v___x_2600__boxed_375_ = lean_unbox(v___x_361_);
v___x_2601__boxed_376_ = lean_unbox(v___x_362_);
v_res_377_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(v_inst_358_, v___x_359_, v_resolved_360_, v___x_2600__boxed_375_, v___x_2601__boxed_376_, v_val_363_, v_displayAll_364_, v_inst_365_, v_inst_366_, v_inst_367_, v_inst_368_, v___x_369_, v_nsStx_370_, v_display_371_, v_toApplicative_372_, v_toBind_373_, v_env_374_);
return v_res_377_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(lean_object* v_toApplicative_379_, lean_object* v_nsStx_380_, lean_object* v_inst_381_, lean_object* v_resolved_382_, lean_object* v_inst_383_, lean_object* v_displayAll_384_, lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_display_389_, lean_object* v_toBind_390_, lean_object* v_____do__lift_391_){
_start:
{
lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_392_ = l_Lean_Linter_linter_ambiguousOpen;
v___x_393_ = l_Lean_Linter_getLinterValue(v___x_392_, v_____do__lift_391_);
if (v___x_393_ == 0)
{
lean_object* v_toPure_394_; lean_object* v___x_395_; lean_object* v___x_396_; 
lean_dec(v_toBind_390_);
lean_dec_ref(v_display_389_);
lean_dec(v_inst_388_);
lean_dec(v_inst_387_);
lean_dec_ref(v_inst_386_);
lean_dec_ref(v_inst_385_);
lean_dec_ref(v_displayAll_384_);
lean_dec_ref(v_inst_383_);
lean_dec(v_resolved_382_);
lean_dec_ref(v_inst_381_);
lean_dec(v_nsStx_380_);
v_toPure_394_ = lean_ctor_get(v_toApplicative_379_, 1);
lean_inc(v_toPure_394_);
lean_dec_ref(v_toApplicative_379_);
v___x_395_ = lean_box(0);
v___x_396_ = lean_apply_2(v_toPure_394_, lean_box(0), v___x_395_);
return v___x_396_;
}
else
{
if (lean_obj_tag(v_nsStx_380_) == 3)
{
lean_object* v_info_397_; 
v_info_397_ = lean_ctor_get(v_nsStx_380_, 0);
if (lean_obj_tag(v_info_397_) == 0)
{
lean_object* v_val_398_; lean_object* v_preresolved_399_; lean_object* v___x_400_; lean_object* v___f_401_; uint8_t v___x_402_; 
v_val_398_ = lean_ctor_get(v_nsStx_380_, 2);
lean_inc(v_val_398_);
v_preresolved_399_ = lean_ctor_get(v_nsStx_380_, 3);
v___x_400_ = lean_box(v___x_393_);
v___f_401_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_401_, 0, v___x_400_);
lean_inc(v_preresolved_399_);
v___x_402_ = l_List_any___redArg(v_preresolved_399_, v___f_401_);
if (v___x_402_ == 0)
{
lean_object* v_getEnv_403_; lean_object* v___x_404_; lean_object* v_resolved_405_; lean_object* v___x_406_; lean_object* v___x_407_; lean_object* v___f_408_; lean_object* v___x_409_; 
v_getEnv_403_ = lean_ctor_get(v_inst_381_, 0);
lean_inc(v_getEnv_403_);
lean_dec_ref(v_inst_381_);
v___x_404_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___closed__0));
v_resolved_405_ = l_List_eraseDups___redArg(v___x_404_, v_resolved_382_);
v___x_406_ = lean_box(v___x_393_);
v___x_407_ = lean_box(v___x_402_);
lean_inc(v_toBind_390_);
v___f_408_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_408_, 0, v_inst_383_);
lean_closure_set(v___f_408_, 1, v___x_404_);
lean_closure_set(v___f_408_, 2, v_resolved_405_);
lean_closure_set(v___f_408_, 3, v___x_406_);
lean_closure_set(v___f_408_, 4, v___x_407_);
lean_closure_set(v___f_408_, 5, v_val_398_);
lean_closure_set(v___f_408_, 6, v_displayAll_384_);
lean_closure_set(v___f_408_, 7, v_inst_385_);
lean_closure_set(v___f_408_, 8, v_inst_386_);
lean_closure_set(v___f_408_, 9, v_inst_387_);
lean_closure_set(v___f_408_, 10, v_inst_388_);
lean_closure_set(v___f_408_, 11, v___x_392_);
lean_closure_set(v___f_408_, 12, v_nsStx_380_);
lean_closure_set(v___f_408_, 13, v_display_389_);
lean_closure_set(v___f_408_, 14, v_toApplicative_379_);
lean_closure_set(v___f_408_, 15, v_toBind_390_);
v___x_409_ = lean_apply_4(v_toBind_390_, lean_box(0), lean_box(0), v_getEnv_403_, v___f_408_);
return v___x_409_;
}
else
{
lean_object* v_toPure_410_; lean_object* v___x_411_; lean_object* v___x_412_; 
lean_dec(v_val_398_);
lean_dec_ref_known(v_nsStx_380_, 4);
lean_dec(v_toBind_390_);
lean_dec_ref(v_display_389_);
lean_dec(v_inst_388_);
lean_dec(v_inst_387_);
lean_dec_ref(v_inst_386_);
lean_dec_ref(v_inst_385_);
lean_dec_ref(v_displayAll_384_);
lean_dec_ref(v_inst_383_);
lean_dec(v_resolved_382_);
lean_dec_ref(v_inst_381_);
v_toPure_410_ = lean_ctor_get(v_toApplicative_379_, 1);
lean_inc(v_toPure_410_);
lean_dec_ref(v_toApplicative_379_);
v___x_411_ = lean_box(0);
v___x_412_ = lean_apply_2(v_toPure_410_, lean_box(0), v___x_411_);
return v___x_412_;
}
}
else
{
lean_object* v_toPure_413_; lean_object* v___x_414_; lean_object* v___x_415_; 
lean_dec_ref_known(v_nsStx_380_, 4);
lean_dec(v_toBind_390_);
lean_dec_ref(v_display_389_);
lean_dec(v_inst_388_);
lean_dec(v_inst_387_);
lean_dec_ref(v_inst_386_);
lean_dec_ref(v_inst_385_);
lean_dec_ref(v_displayAll_384_);
lean_dec_ref(v_inst_383_);
lean_dec(v_resolved_382_);
lean_dec_ref(v_inst_381_);
v_toPure_413_ = lean_ctor_get(v_toApplicative_379_, 1);
lean_inc(v_toPure_413_);
lean_dec_ref(v_toApplicative_379_);
v___x_414_ = lean_box(0);
v___x_415_ = lean_apply_2(v_toPure_413_, lean_box(0), v___x_414_);
return v___x_415_;
}
}
else
{
lean_object* v_toPure_416_; lean_object* v___x_417_; lean_object* v___x_418_; 
lean_dec(v_toBind_390_);
lean_dec_ref(v_display_389_);
lean_dec(v_inst_388_);
lean_dec(v_inst_387_);
lean_dec_ref(v_inst_386_);
lean_dec_ref(v_inst_385_);
lean_dec_ref(v_displayAll_384_);
lean_dec_ref(v_inst_383_);
lean_dec(v_resolved_382_);
lean_dec_ref(v_inst_381_);
lean_dec(v_nsStx_380_);
v_toPure_416_ = lean_ctor_get(v_toApplicative_379_, 1);
lean_inc(v_toPure_416_);
lean_dec_ref(v_toApplicative_379_);
v___x_417_ = lean_box(0);
v___x_418_ = lean_apply_2(v_toPure_416_, lean_box(0), v___x_417_);
return v___x_418_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed(lean_object* v_toApplicative_419_, lean_object* v_nsStx_420_, lean_object* v_inst_421_, lean_object* v_resolved_422_, lean_object* v_inst_423_, lean_object* v_displayAll_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_display_429_, lean_object* v_toBind_430_, lean_object* v_____do__lift_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(v_toApplicative_419_, v_nsStx_420_, v_inst_421_, v_resolved_422_, v_inst_423_, v_displayAll_424_, v_inst_425_, v_inst_426_, v_inst_427_, v_inst_428_, v_display_429_, v_toBind_430_, v_____do__lift_431_);
lean_dec_ref(v_____do__lift_431_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg(lean_object* v_inst_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_nsStx_442_, lean_object* v_resolved_443_){
_start:
{
lean_object* v_toApplicative_444_; lean_object* v_toBind_445_; lean_object* v_display_446_; lean_object* v_displayAll_447_; lean_object* v___f_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v_toApplicative_444_ = lean_ctor_get(v_inst_436_, 0);
v_toBind_445_ = lean_ctor_get(v_inst_436_, 1);
lean_inc_n(v_toBind_445_, 2);
v_display_446_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0));
v_displayAll_447_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___closed__1));
lean_inc(v_inst_438_);
lean_inc_ref(v_inst_436_);
lean_inc_ref(v_inst_437_);
lean_inc_ref(v_toApplicative_444_);
v___f_448_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed), 13, 12);
lean_closure_set(v___f_448_, 0, v_toApplicative_444_);
lean_closure_set(v___f_448_, 1, v_nsStx_442_);
lean_closure_set(v___f_448_, 2, v_inst_437_);
lean_closure_set(v___f_448_, 3, v_resolved_443_);
lean_closure_set(v___f_448_, 4, v_inst_441_);
lean_closure_set(v___f_448_, 5, v_displayAll_447_);
lean_closure_set(v___f_448_, 6, v_inst_436_);
lean_closure_set(v___f_448_, 7, v_inst_439_);
lean_closure_set(v___f_448_, 8, v_inst_440_);
lean_closure_set(v___f_448_, 9, v_inst_438_);
lean_closure_set(v___f_448_, 10, v_display_446_);
lean_closure_set(v___f_448_, 11, v_toBind_445_);
v___x_449_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_436_, v_inst_438_, v_inst_437_);
v___x_450_ = lean_apply_4(v_toBind_445_, lean_box(0), lean_box(0), v___x_449_, v___f_448_);
return v___x_450_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen(lean_object* v_m_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_nsStx_458_, lean_object* v_resolved_459_){
_start:
{
lean_object* v___x_460_; 
v___x_460_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v_inst_452_, v_inst_453_, v_inst_454_, v_inst_455_, v_inst_456_, v_inst_457_, v_nsStx_458_, v_resolved_459_);
return v___x_460_;
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
