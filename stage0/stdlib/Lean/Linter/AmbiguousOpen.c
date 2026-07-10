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
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
uint8_t l_List_any___redArg(lean_object*, lean_object*);
lean_object* l_List_eraseDups___redArg(lean_object*, lean_object*);
extern lean_object* l_Lean_rootNamespace;
lean_object* l_List_head_x21___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_append(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Linter_logLint___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t l_List_elem___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
uint8_t l_Lean_Name_isPrefixOf(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
uint8_t l_Lean_Environment_isNamespace(lean_object*, lean_object*);
lean_object* l_Lean_Name_replacePrefix(lean_object*, lean_object*, lean_object*);
lean_object* l_List_filterTR_loop___redArg(lean_object*, lean_object*, lean_object*);
uint8_t l_List_isEmpty___redArg(lean_object*);
lean_object* l_List_lengthTR___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 45, .m_capacity = 45, .m_length = 44, .m_data = " Specify the namespace unambiguously, e.g. `"};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__0 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__0_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__1;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 108, .m_capacity = 108, .m_length = 107, .m_data = "`. The warning can sometimes also be addressed by moving the `open` outside of the surrounding `namespace`."};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__2 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__2_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__3;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "`: it is interpreted as "};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__4 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__4_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__5;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 47, .m_capacity = 47, .m_length = 46, .m_data = " because this `open` occurs inside `namespace "};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__6 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__6_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__7;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "`, while "};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__8 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__8_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__9;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "."};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__10 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__10_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__11;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = " are silently not opened"};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__12 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__12_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__13;
static const lean_string_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = " is silently not opened"};
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__14 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__14_value;
static lean_once_cell_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__15;
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9___closed__0 = (const lean_object*)&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
uint8_t v___x_2189__boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v___x_2189__boxed_100_ = lean_unbox(v___x_98_);
v_res_101_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2(v___x_2189__boxed_100_, v_x_99_);
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
uint8_t v___x_2198__boxed_112_; uint8_t v_res_113_; lean_object* v_r_114_; 
v___x_2198__boxed_112_ = lean_unbox(v___x_110_);
v_res_113_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3(v_n_109_, v___x_2198__boxed_112_, v_x_111_);
lean_dec_ref(v_x_111_);
lean_dec(v_n_109_);
v_r_114_ = lean_box(v_res_113_);
return v_r_114_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4(lean_object* v___x_115_, lean_object* v_resolved_116_, lean_object* v_currNamespace_117_, lean_object* v_openDecls_118_, uint8_t v___x_119_, lean_object* v_n_120_){
_start:
{
uint8_t v___x_121_; uint8_t v___x_122_; 
lean_inc(v_n_120_);
v___x_121_ = l_List_elem___redArg(v___x_115_, v_n_120_, v_resolved_116_);
v___x_122_ = lean_bool_not(v___x_121_);
if (v___x_122_ == 0)
{
lean_dec(v_n_120_);
lean_dec(v_openDecls_118_);
return v___x_122_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = l_Lean_Name_isPrefixOf(v_n_120_, v_currNamespace_117_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v___f_125_; uint8_t v___x_126_; uint8_t v___x_127_; 
v___x_124_ = lean_box(v___x_123_);
v___f_125_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3___boxed), 3, 2);
lean_closure_set(v___f_125_, 0, v_n_120_);
lean_closure_set(v___f_125_, 1, v___x_124_);
v___x_126_ = l_List_any___redArg(v_openDecls_118_, v___f_125_);
v___x_127_ = lean_bool_not(v___x_126_);
return v___x_127_;
}
else
{
uint8_t v___x_128_; 
lean_dec(v_n_120_);
lean_dec(v_openDecls_118_);
v___x_128_ = lean_bool_not(v___x_119_);
return v___x_128_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4___boxed(lean_object* v___x_129_, lean_object* v_resolved_130_, lean_object* v_currNamespace_131_, lean_object* v_openDecls_132_, lean_object* v___x_133_, lean_object* v_n_134_){
_start:
{
uint8_t v___x_2211__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v___x_2211__boxed_135_ = lean_unbox(v___x_133_);
v_res_136_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4(v___x_129_, v_resolved_130_, v_currNamespace_131_, v_openDecls_132_, v___x_2211__boxed_135_, v_n_134_);
lean_dec(v_currNamespace_131_);
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
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(lean_object* v_val_153_, lean_object* v_displayAll_154_, lean_object* v_resolved_155_, lean_object* v___y_156_, lean_object* v_currNamespace_157_, lean_object* v_hint_158_, lean_object* v_x_159_){
_start:
{
lean_object* v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___x_160_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1);
v___x_161_ = l_Lean_MessageData_ofName(v_val_153_);
v___x_162_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_162_, 0, v___x_160_);
lean_ctor_set(v___x_162_, 1, v___x_161_);
v___x_163_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__3);
v___x_164_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_164_, 0, v___x_162_);
lean_ctor_set(v___x_164_, 1, v___x_163_);
v___x_165_ = lean_apply_1(v_displayAll_154_, v_resolved_155_);
v___x_166_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_166_, 0, v___x_164_);
lean_ctor_set(v___x_166_, 1, v___x_165_);
v___x_167_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__5);
v___x_168_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_168_, 0, v___x_166_);
lean_ctor_set(v___x_168_, 1, v___x_167_);
v___x_169_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_169_, 0, v___x_168_);
lean_ctor_set(v___x_169_, 1, v___y_156_);
v___x_170_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__7);
v___x_171_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_171_, 0, v___x_169_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
v___x_172_ = l_Lean_MessageData_ofName(v_currNamespace_157_);
v___x_173_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_171_);
lean_ctor_set(v___x_173_, 1, v___x_172_);
v___x_174_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__9);
v___x_175_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_175_, 0, v___x_173_);
lean_ctor_set(v___x_175_, 1, v___x_174_);
v___x_176_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v_hint_158_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___boxed(lean_object* v_val_177_, lean_object* v_displayAll_178_, lean_object* v_resolved_179_, lean_object* v___y_180_, lean_object* v_currNamespace_181_, lean_object* v_hint_182_, lean_object* v_x_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(v_val_177_, v_displayAll_178_, v_resolved_179_, v___y_180_, v_currNamespace_181_, v_hint_182_, v_x_183_);
lean_dec(v_x_183_);
return v_res_184_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__1(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__0));
v___x_187_ = l_Lean_stringToMessageData(v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__3(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__2));
v___x_190_ = l_Lean_stringToMessageData(v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__5(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__4));
v___x_193_ = l_Lean_stringToMessageData(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__7(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__6));
v___x_196_ = l_Lean_stringToMessageData(v___x_195_);
return v___x_196_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__9(void){
_start:
{
lean_object* v___x_198_; lean_object* v___x_199_; 
v___x_198_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__8));
v___x_199_ = l_Lean_stringToMessageData(v___x_198_);
return v___x_199_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__11(void){
_start:
{
lean_object* v___x_201_; lean_object* v___x_202_; 
v___x_201_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__10));
v___x_202_ = l_Lean_stringToMessageData(v___x_201_);
return v___x_202_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__13(void){
_start:
{
lean_object* v___x_204_; lean_object* v___x_205_; 
v___x_204_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__12));
v___x_205_ = l_Lean_stringToMessageData(v___x_204_);
return v___x_205_;
}
}
static lean_object* _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__15(void){
_start:
{
lean_object* v___x_207_; lean_object* v___x_208_; 
v___x_207_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__14));
v___x_208_ = l_Lean_stringToMessageData(v___x_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(lean_object* v___x_209_, lean_object* v_resolved_210_, lean_object* v_currNamespace_211_, uint8_t v___x_212_, lean_object* v_env_213_, lean_object* v_val_214_, lean_object* v_displayAll_215_, lean_object* v_display_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v___x_221_, lean_object* v_nsStx_222_, lean_object* v_toApplicative_223_, lean_object* v_openDecls_224_){
_start:
{
lean_object* v___y_226_; lean_object* v___x_267_; lean_object* v___f_268_; lean_object* v_candidates_269_; lean_object* v___x_270_; lean_object* v_shadowed_271_; uint8_t v___x_272_; 
v___x_267_ = lean_box(v___x_212_);
lean_inc_n(v_currNamespace_211_, 2);
lean_inc(v_resolved_210_);
v___f_268_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4___boxed), 6, 5);
lean_closure_set(v___f_268_, 0, v___x_209_);
lean_closure_set(v___f_268_, 1, v_resolved_210_);
lean_closure_set(v___f_268_, 2, v_currNamespace_211_);
lean_closure_set(v___f_268_, 3, v_openDecls_224_);
lean_closure_set(v___f_268_, 4, v___x_267_);
lean_inc(v_val_214_);
v_candidates_269_ = l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_scopeCandidates(v_env_213_, v_val_214_, v_currNamespace_211_);
v___x_270_ = lean_box(0);
v_shadowed_271_ = l_List_filterTR_loop___redArg(v___f_268_, v_candidates_269_, v___x_270_);
v___x_272_ = l_List_isEmpty___redArg(v_shadowed_271_);
if (v___x_272_ == 0)
{
lean_object* v___x_273_; lean_object* v___x_274_; uint8_t v___x_275_; 
lean_dec_ref(v_toApplicative_223_);
v___x_273_ = l_List_lengthTR___redArg(v_shadowed_271_);
v___x_274_ = lean_unsigned_to_nat(1u);
v___x_275_ = lean_nat_dec_eq(v___x_273_, v___x_274_);
lean_dec(v___x_273_);
if (v___x_275_ == 0)
{
lean_object* v___x_276_; lean_object* v___x_277_; lean_object* v___x_278_; 
lean_inc_ref(v_displayAll_215_);
v___x_276_ = lean_apply_1(v_displayAll_215_, v_shadowed_271_);
v___x_277_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__13, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__13_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__13);
v___x_278_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_278_, 0, v___x_276_);
lean_ctor_set(v___x_278_, 1, v___x_277_);
v___y_226_ = v___x_278_;
goto v___jp_225_;
}
else
{
lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
lean_inc_ref(v_displayAll_215_);
v___x_279_ = lean_apply_1(v_displayAll_215_, v_shadowed_271_);
v___x_280_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__15, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__15_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__15);
v___x_281_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_281_, 0, v___x_279_);
lean_ctor_set(v___x_281_, 1, v___x_280_);
v___y_226_ = v___x_281_;
goto v___jp_225_;
}
}
else
{
lean_object* v_toPure_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
lean_dec(v_shadowed_271_);
lean_dec(v_nsStx_222_);
lean_dec_ref(v___x_221_);
lean_dec(v_inst_220_);
lean_dec(v_inst_219_);
lean_dec_ref(v_inst_218_);
lean_dec_ref(v_inst_217_);
lean_dec_ref(v_display_216_);
lean_dec_ref(v_displayAll_215_);
lean_dec(v_val_214_);
lean_dec(v_currNamespace_211_);
lean_dec(v_resolved_210_);
v_toPure_282_ = lean_ctor_get(v_toApplicative_223_, 1);
lean_inc(v_toPure_282_);
lean_dec_ref(v_toApplicative_223_);
v___x_283_ = lean_box(0);
v___x_284_ = lean_apply_2(v_toPure_282_, lean_box(0), v___x_283_);
return v___x_284_;
}
v___jp_225_:
{
lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v_hint_235_; 
v___x_227_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__1, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__1_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__1);
v___x_228_ = l_Lean_rootNamespace;
v___x_229_ = lean_box(0);
v___x_230_ = l_List_head_x21___redArg(v___x_229_, v_resolved_210_);
v___x_231_ = l_Lean_Name_append(v___x_228_, v___x_230_);
v___x_232_ = l_Lean_MessageData_ofName(v___x_231_);
v___x_233_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_233_, 0, v___x_227_);
lean_ctor_set(v___x_233_, 1, v___x_232_);
v___x_234_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__3, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__3_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__3);
v_hint_235_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_hint_235_, 0, v___x_233_);
lean_ctor_set(v_hint_235_, 1, v___x_234_);
if (lean_obj_tag(v_resolved_210_) == 1)
{
lean_object* v_tail_236_; 
v_tail_236_ = lean_ctor_get(v_resolved_210_, 1);
if (lean_obj_tag(v_tail_236_) == 0)
{
lean_object* v_head_237_; lean_object* v___x_239_; uint8_t v_isShared_240_; uint8_t v_isSharedCheck_261_; 
lean_dec_ref(v_displayAll_215_);
v_head_237_ = lean_ctor_get(v_resolved_210_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v_resolved_210_);
if (v_isSharedCheck_261_ == 0)
{
lean_object* v_unused_262_; 
v_unused_262_ = lean_ctor_get(v_resolved_210_, 1);
lean_dec(v_unused_262_);
v___x_239_ = v_resolved_210_;
v_isShared_240_ = v_isSharedCheck_261_;
goto v_resetjp_238_;
}
else
{
lean_inc(v_head_237_);
lean_dec(v_resolved_210_);
v___x_239_ = lean_box(0);
v_isShared_240_ = v_isSharedCheck_261_;
goto v_resetjp_238_;
}
v_resetjp_238_:
{
lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_244_; 
v___x_241_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1);
v___x_242_ = l_Lean_MessageData_ofName(v_val_214_);
if (v_isShared_240_ == 0)
{
lean_ctor_set_tag(v___x_239_, 7);
lean_ctor_set(v___x_239_, 1, v___x_242_);
lean_ctor_set(v___x_239_, 0, v___x_241_);
v___x_244_ = v___x_239_;
goto v_reusejp_243_;
}
else
{
lean_object* v_reuseFailAlloc_260_; 
v_reuseFailAlloc_260_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_260_, 0, v___x_241_);
lean_ctor_set(v_reuseFailAlloc_260_, 1, v___x_242_);
v___x_244_ = v_reuseFailAlloc_260_;
goto v_reusejp_243_;
}
v_reusejp_243_:
{
lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; 
v___x_245_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__5, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__5_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__5);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_244_);
lean_ctor_set(v___x_246_, 1, v___x_245_);
v___x_247_ = lean_apply_1(v_display_216_, v_head_237_);
v___x_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_248_, 0, v___x_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
v___x_249_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__7, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__7_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__7);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_248_);
lean_ctor_set(v___x_250_, 1, v___x_249_);
v___x_251_ = l_Lean_MessageData_ofName(v_currNamespace_211_);
v___x_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_252_, 0, v___x_250_);
lean_ctor_set(v___x_252_, 1, v___x_251_);
v___x_253_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__9, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__9_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__9);
v___x_254_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_254_, 0, v___x_252_);
lean_ctor_set(v___x_254_, 1, v___x_253_);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_254_);
lean_ctor_set(v___x_255_, 1, v___y_226_);
v___x_256_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__11, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__11_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__11);
v___x_257_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_257_, 0, v___x_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_257_);
lean_ctor_set(v___x_258_, 1, v_hint_235_);
v___x_259_ = l_Lean_Linter_logLint___redArg(v_inst_217_, v_inst_218_, v_inst_219_, v_inst_220_, v___x_221_, v_nsStx_222_, v___x_258_);
return v___x_259_;
}
}
}
else
{
lean_object* v___x_263_; lean_object* v___x_264_; 
lean_dec_ref(v_display_216_);
lean_inc_ref(v_resolved_210_);
v___x_263_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(v_val_214_, v_displayAll_215_, v_resolved_210_, v___y_226_, v_currNamespace_211_, v_hint_235_, v_resolved_210_);
lean_dec_ref_known(v_resolved_210_, 2);
v___x_264_ = l_Lean_Linter_logLint___redArg(v_inst_217_, v_inst_218_, v_inst_219_, v_inst_220_, v___x_221_, v_nsStx_222_, v___x_263_);
return v___x_264_;
}
}
else
{
lean_object* v___x_265_; lean_object* v___x_266_; 
lean_dec_ref(v_display_216_);
lean_inc(v_resolved_210_);
v___x_265_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(v_val_214_, v_displayAll_215_, v_resolved_210_, v___y_226_, v_currNamespace_211_, v_hint_235_, v_resolved_210_);
lean_dec(v_resolved_210_);
v___x_266_ = l_Lean_Linter_logLint___redArg(v_inst_217_, v_inst_218_, v_inst_219_, v_inst_220_, v___x_221_, v_nsStx_222_, v___x_265_);
return v___x_266_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed(lean_object* v___x_285_, lean_object* v_resolved_286_, lean_object* v_currNamespace_287_, lean_object* v___x_288_, lean_object* v_env_289_, lean_object* v_val_290_, lean_object* v_displayAll_291_, lean_object* v_display_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v___x_297_, lean_object* v_nsStx_298_, lean_object* v_toApplicative_299_, lean_object* v_openDecls_300_){
_start:
{
uint8_t v___x_2372__boxed_301_; lean_object* v_res_302_; 
v___x_2372__boxed_301_ = lean_unbox(v___x_288_);
v_res_302_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(v___x_285_, v_resolved_286_, v_currNamespace_287_, v___x_2372__boxed_301_, v_env_289_, v_val_290_, v_displayAll_291_, v_display_292_, v_inst_293_, v_inst_294_, v_inst_295_, v_inst_296_, v___x_297_, v_nsStx_298_, v_toApplicative_299_, v_openDecls_300_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(lean_object* v___x_303_, lean_object* v_resolved_304_, uint8_t v___x_305_, lean_object* v_env_306_, lean_object* v_val_307_, lean_object* v_displayAll_308_, lean_object* v_display_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v___x_314_, lean_object* v_nsStx_315_, lean_object* v_toApplicative_316_, lean_object* v_toBind_317_, lean_object* v_getOpenDecls_318_, lean_object* v_currNamespace_319_){
_start:
{
lean_object* v___x_320_; lean_object* v___f_321_; lean_object* v___x_322_; 
v___x_320_ = lean_box(v___x_305_);
v___f_321_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed), 16, 15);
lean_closure_set(v___f_321_, 0, v___x_303_);
lean_closure_set(v___f_321_, 1, v_resolved_304_);
lean_closure_set(v___f_321_, 2, v_currNamespace_319_);
lean_closure_set(v___f_321_, 3, v___x_320_);
lean_closure_set(v___f_321_, 4, v_env_306_);
lean_closure_set(v___f_321_, 5, v_val_307_);
lean_closure_set(v___f_321_, 6, v_displayAll_308_);
lean_closure_set(v___f_321_, 7, v_display_309_);
lean_closure_set(v___f_321_, 8, v_inst_310_);
lean_closure_set(v___f_321_, 9, v_inst_311_);
lean_closure_set(v___f_321_, 10, v_inst_312_);
lean_closure_set(v___f_321_, 11, v_inst_313_);
lean_closure_set(v___f_321_, 12, v___x_314_);
lean_closure_set(v___f_321_, 13, v_nsStx_315_);
lean_closure_set(v___f_321_, 14, v_toApplicative_316_);
v___x_322_ = lean_apply_4(v_toBind_317_, lean_box(0), lean_box(0), v_getOpenDecls_318_, v___f_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed(lean_object** _args){
lean_object* v___x_323_ = _args[0];
lean_object* v_resolved_324_ = _args[1];
lean_object* v___x_325_ = _args[2];
lean_object* v_env_326_ = _args[3];
lean_object* v_val_327_ = _args[4];
lean_object* v_displayAll_328_ = _args[5];
lean_object* v_display_329_ = _args[6];
lean_object* v_inst_330_ = _args[7];
lean_object* v_inst_331_ = _args[8];
lean_object* v_inst_332_ = _args[9];
lean_object* v_inst_333_ = _args[10];
lean_object* v___x_334_ = _args[11];
lean_object* v_nsStx_335_ = _args[12];
lean_object* v_toApplicative_336_ = _args[13];
lean_object* v_toBind_337_ = _args[14];
lean_object* v_getOpenDecls_338_ = _args[15];
lean_object* v_currNamespace_339_ = _args[16];
_start:
{
uint8_t v___x_2532__boxed_340_; lean_object* v_res_341_; 
v___x_2532__boxed_340_ = lean_unbox(v___x_325_);
v_res_341_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(v___x_323_, v_resolved_324_, v___x_2532__boxed_340_, v_env_326_, v_val_327_, v_displayAll_328_, v_display_329_, v_inst_330_, v_inst_331_, v_inst_332_, v_inst_333_, v___x_334_, v_nsStx_335_, v_toApplicative_336_, v_toBind_337_, v_getOpenDecls_338_, v_currNamespace_339_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(lean_object* v_inst_342_, lean_object* v___x_343_, lean_object* v_resolved_344_, uint8_t v___x_345_, lean_object* v_val_346_, lean_object* v_displayAll_347_, lean_object* v_display_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_inst_351_, lean_object* v_inst_352_, lean_object* v___x_353_, lean_object* v_nsStx_354_, lean_object* v_toApplicative_355_, lean_object* v_toBind_356_, lean_object* v_env_357_){
_start:
{
lean_object* v_getCurrNamespace_358_; lean_object* v_getOpenDecls_359_; lean_object* v___x_360_; lean_object* v___f_361_; lean_object* v___x_362_; 
v_getCurrNamespace_358_ = lean_ctor_get(v_inst_342_, 0);
lean_inc(v_getCurrNamespace_358_);
v_getOpenDecls_359_ = lean_ctor_get(v_inst_342_, 1);
lean_inc(v_getOpenDecls_359_);
lean_dec_ref(v_inst_342_);
v___x_360_ = lean_box(v___x_345_);
lean_inc(v_toBind_356_);
v___f_361_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed), 17, 16);
lean_closure_set(v___f_361_, 0, v___x_343_);
lean_closure_set(v___f_361_, 1, v_resolved_344_);
lean_closure_set(v___f_361_, 2, v___x_360_);
lean_closure_set(v___f_361_, 3, v_env_357_);
lean_closure_set(v___f_361_, 4, v_val_346_);
lean_closure_set(v___f_361_, 5, v_displayAll_347_);
lean_closure_set(v___f_361_, 6, v_display_348_);
lean_closure_set(v___f_361_, 7, v_inst_349_);
lean_closure_set(v___f_361_, 8, v_inst_350_);
lean_closure_set(v___f_361_, 9, v_inst_351_);
lean_closure_set(v___f_361_, 10, v_inst_352_);
lean_closure_set(v___f_361_, 11, v___x_353_);
lean_closure_set(v___f_361_, 12, v_nsStx_354_);
lean_closure_set(v___f_361_, 13, v_toApplicative_355_);
lean_closure_set(v___f_361_, 14, v_toBind_356_);
lean_closure_set(v___f_361_, 15, v_getOpenDecls_359_);
v___x_362_ = lean_apply_4(v_toBind_356_, lean_box(0), lean_box(0), v_getCurrNamespace_358_, v___f_361_);
return v___x_362_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed(lean_object* v_inst_363_, lean_object* v___x_364_, lean_object* v_resolved_365_, lean_object* v___x_366_, lean_object* v_val_367_, lean_object* v_displayAll_368_, lean_object* v_display_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v___x_374_, lean_object* v_nsStx_375_, lean_object* v_toApplicative_376_, lean_object* v_toBind_377_, lean_object* v_env_378_){
_start:
{
uint8_t v___x_2563__boxed_379_; lean_object* v_res_380_; 
v___x_2563__boxed_379_ = lean_unbox(v___x_366_);
v_res_380_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(v_inst_363_, v___x_364_, v_resolved_365_, v___x_2563__boxed_379_, v_val_367_, v_displayAll_368_, v_display_369_, v_inst_370_, v_inst_371_, v_inst_372_, v_inst_373_, v___x_374_, v_nsStx_375_, v_toApplicative_376_, v_toBind_377_, v_env_378_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9(lean_object* v_toApplicative_382_, lean_object* v_nsStx_383_, lean_object* v_inst_384_, lean_object* v_resolved_385_, lean_object* v_inst_386_, lean_object* v_displayAll_387_, lean_object* v_display_388_, lean_object* v_inst_389_, lean_object* v_inst_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_toBind_393_, lean_object* v_____do__lift_394_){
_start:
{
lean_object* v___x_395_; uint8_t v___x_396_; 
v___x_395_ = l_Lean_Linter_linter_ambiguousOpen;
v___x_396_ = l_Lean_Linter_getLinterValue(v___x_395_, v_____do__lift_394_);
if (v___x_396_ == 0)
{
lean_object* v_toPure_397_; lean_object* v___x_398_; lean_object* v___x_399_; 
lean_dec(v_toBind_393_);
lean_dec(v_inst_392_);
lean_dec(v_inst_391_);
lean_dec_ref(v_inst_390_);
lean_dec_ref(v_inst_389_);
lean_dec_ref(v_display_388_);
lean_dec_ref(v_displayAll_387_);
lean_dec_ref(v_inst_386_);
lean_dec(v_resolved_385_);
lean_dec_ref(v_inst_384_);
lean_dec(v_nsStx_383_);
v_toPure_397_ = lean_ctor_get(v_toApplicative_382_, 1);
lean_inc(v_toPure_397_);
lean_dec_ref(v_toApplicative_382_);
v___x_398_ = lean_box(0);
v___x_399_ = lean_apply_2(v_toPure_397_, lean_box(0), v___x_398_);
return v___x_399_;
}
else
{
if (lean_obj_tag(v_nsStx_383_) == 3)
{
lean_object* v_info_400_; 
v_info_400_ = lean_ctor_get(v_nsStx_383_, 0);
if (lean_obj_tag(v_info_400_) == 0)
{
lean_object* v_val_401_; lean_object* v_preresolved_402_; lean_object* v___x_403_; lean_object* v___f_404_; uint8_t v___x_405_; 
v_val_401_ = lean_ctor_get(v_nsStx_383_, 2);
lean_inc(v_val_401_);
v_preresolved_402_ = lean_ctor_get(v_nsStx_383_, 3);
v___x_403_ = lean_box(v___x_396_);
v___f_404_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_404_, 0, v___x_403_);
lean_inc(v_preresolved_402_);
v___x_405_ = l_List_any___redArg(v_preresolved_402_, v___f_404_);
if (v___x_405_ == 0)
{
lean_object* v_getEnv_406_; lean_object* v___x_407_; lean_object* v_resolved_408_; lean_object* v___x_409_; lean_object* v___f_410_; lean_object* v___x_411_; 
v_getEnv_406_ = lean_ctor_get(v_inst_384_, 0);
lean_inc(v_getEnv_406_);
lean_dec_ref(v_inst_384_);
v___x_407_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9___closed__0));
v_resolved_408_ = l_List_eraseDups___redArg(v___x_407_, v_resolved_385_);
v___x_409_ = lean_box(v___x_396_);
lean_inc(v_toBind_393_);
v___f_410_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed), 16, 15);
lean_closure_set(v___f_410_, 0, v_inst_386_);
lean_closure_set(v___f_410_, 1, v___x_407_);
lean_closure_set(v___f_410_, 2, v_resolved_408_);
lean_closure_set(v___f_410_, 3, v___x_409_);
lean_closure_set(v___f_410_, 4, v_val_401_);
lean_closure_set(v___f_410_, 5, v_displayAll_387_);
lean_closure_set(v___f_410_, 6, v_display_388_);
lean_closure_set(v___f_410_, 7, v_inst_389_);
lean_closure_set(v___f_410_, 8, v_inst_390_);
lean_closure_set(v___f_410_, 9, v_inst_391_);
lean_closure_set(v___f_410_, 10, v_inst_392_);
lean_closure_set(v___f_410_, 11, v___x_395_);
lean_closure_set(v___f_410_, 12, v_nsStx_383_);
lean_closure_set(v___f_410_, 13, v_toApplicative_382_);
lean_closure_set(v___f_410_, 14, v_toBind_393_);
v___x_411_ = lean_apply_4(v_toBind_393_, lean_box(0), lean_box(0), v_getEnv_406_, v___f_410_);
return v___x_411_;
}
else
{
lean_object* v_toPure_412_; lean_object* v___x_413_; lean_object* v___x_414_; 
lean_dec(v_val_401_);
lean_dec_ref_known(v_nsStx_383_, 4);
lean_dec(v_toBind_393_);
lean_dec(v_inst_392_);
lean_dec(v_inst_391_);
lean_dec_ref(v_inst_390_);
lean_dec_ref(v_inst_389_);
lean_dec_ref(v_display_388_);
lean_dec_ref(v_displayAll_387_);
lean_dec_ref(v_inst_386_);
lean_dec(v_resolved_385_);
lean_dec_ref(v_inst_384_);
v_toPure_412_ = lean_ctor_get(v_toApplicative_382_, 1);
lean_inc(v_toPure_412_);
lean_dec_ref(v_toApplicative_382_);
v___x_413_ = lean_box(0);
v___x_414_ = lean_apply_2(v_toPure_412_, lean_box(0), v___x_413_);
return v___x_414_;
}
}
else
{
lean_object* v_toPure_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
lean_dec_ref_known(v_nsStx_383_, 4);
lean_dec(v_toBind_393_);
lean_dec(v_inst_392_);
lean_dec(v_inst_391_);
lean_dec_ref(v_inst_390_);
lean_dec_ref(v_inst_389_);
lean_dec_ref(v_display_388_);
lean_dec_ref(v_displayAll_387_);
lean_dec_ref(v_inst_386_);
lean_dec(v_resolved_385_);
lean_dec_ref(v_inst_384_);
v_toPure_415_ = lean_ctor_get(v_toApplicative_382_, 1);
lean_inc(v_toPure_415_);
lean_dec_ref(v_toApplicative_382_);
v___x_416_ = lean_box(0);
v___x_417_ = lean_apply_2(v_toPure_415_, lean_box(0), v___x_416_);
return v___x_417_;
}
}
else
{
lean_object* v_toPure_418_; lean_object* v___x_419_; lean_object* v___x_420_; 
lean_dec(v_toBind_393_);
lean_dec(v_inst_392_);
lean_dec(v_inst_391_);
lean_dec_ref(v_inst_390_);
lean_dec_ref(v_inst_389_);
lean_dec_ref(v_display_388_);
lean_dec_ref(v_displayAll_387_);
lean_dec_ref(v_inst_386_);
lean_dec(v_resolved_385_);
lean_dec_ref(v_inst_384_);
lean_dec(v_nsStx_383_);
v_toPure_418_ = lean_ctor_get(v_toApplicative_382_, 1);
lean_inc(v_toPure_418_);
lean_dec_ref(v_toApplicative_382_);
v___x_419_ = lean_box(0);
v___x_420_ = lean_apply_2(v_toPure_418_, lean_box(0), v___x_419_);
return v___x_420_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9___boxed(lean_object* v_toApplicative_421_, lean_object* v_nsStx_422_, lean_object* v_inst_423_, lean_object* v_resolved_424_, lean_object* v_inst_425_, lean_object* v_displayAll_426_, lean_object* v_display_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_inst_430_, lean_object* v_inst_431_, lean_object* v_toBind_432_, lean_object* v_____do__lift_433_){
_start:
{
lean_object* v_res_434_; 
v_res_434_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9(v_toApplicative_421_, v_nsStx_422_, v_inst_423_, v_resolved_424_, v_inst_425_, v_displayAll_426_, v_display_427_, v_inst_428_, v_inst_429_, v_inst_430_, v_inst_431_, v_toBind_432_, v_____do__lift_433_);
lean_dec_ref(v_____do__lift_433_);
return v_res_434_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg(lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_nsStx_444_, lean_object* v_resolved_445_){
_start:
{
lean_object* v_toApplicative_446_; lean_object* v_toBind_447_; lean_object* v_display_448_; lean_object* v_displayAll_449_; lean_object* v___f_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_toApplicative_446_ = lean_ctor_get(v_inst_438_, 0);
v_toBind_447_ = lean_ctor_get(v_inst_438_, 1);
lean_inc_n(v_toBind_447_, 2);
v_display_448_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0));
v_displayAll_449_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___closed__1));
lean_inc(v_inst_440_);
lean_inc_ref(v_inst_438_);
lean_inc_ref(v_inst_439_);
lean_inc_ref(v_toApplicative_446_);
v___f_450_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9___boxed), 13, 12);
lean_closure_set(v___f_450_, 0, v_toApplicative_446_);
lean_closure_set(v___f_450_, 1, v_nsStx_444_);
lean_closure_set(v___f_450_, 2, v_inst_439_);
lean_closure_set(v___f_450_, 3, v_resolved_445_);
lean_closure_set(v___f_450_, 4, v_inst_443_);
lean_closure_set(v___f_450_, 5, v_displayAll_449_);
lean_closure_set(v___f_450_, 6, v_display_448_);
lean_closure_set(v___f_450_, 7, v_inst_438_);
lean_closure_set(v___f_450_, 8, v_inst_441_);
lean_closure_set(v___f_450_, 9, v_inst_442_);
lean_closure_set(v___f_450_, 10, v_inst_440_);
lean_closure_set(v___f_450_, 11, v_toBind_447_);
v___x_451_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_438_, v_inst_440_, v_inst_439_);
v___x_452_ = lean_apply_4(v_toBind_447_, lean_box(0), lean_box(0), v___x_451_, v___f_450_);
return v___x_452_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen(lean_object* v_m_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_nsStx_460_, lean_object* v_resolved_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v_inst_454_, v_inst_455_, v_inst_456_, v_inst_457_, v_inst_458_, v_inst_459_, v_nsStx_460_, v_resolved_461_);
return v___x_462_;
}
}
lean_object* runtime_initialize_Lean_ResolveName(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_AmbiguousOpen(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
