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
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed(lean_object**);
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
uint8_t v___x_2237__boxed_100_; uint8_t v_res_101_; lean_object* v_r_102_; 
v___x_2237__boxed_100_ = lean_unbox(v___x_98_);
v_res_101_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2(v___x_2237__boxed_100_, v_x_99_);
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
uint8_t v___x_2246__boxed_112_; uint8_t v_res_113_; lean_object* v_r_114_; 
v___x_2246__boxed_112_ = lean_unbox(v___x_110_);
v_res_113_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__3(v_n_109_, v___x_2246__boxed_112_, v_x_111_);
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
uint8_t v___x_2259__boxed_134_; uint8_t v___x_2260__boxed_135_; uint8_t v_res_136_; lean_object* v_r_137_; 
v___x_2259__boxed_134_ = lean_unbox(v___x_131_);
v___x_2260__boxed_135_ = lean_unbox(v___x_132_);
v_res_136_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4(v___x_127_, v_resolved_128_, v_currNamespace_129_, v_openDecls_130_, v___x_2259__boxed_134_, v___x_2260__boxed_135_, v_n_133_);
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
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(lean_object* v___x_209_, lean_object* v_resolved_210_, lean_object* v_currNamespace_211_, uint8_t v___x_212_, uint8_t v___x_213_, lean_object* v_env_214_, lean_object* v_val_215_, lean_object* v_displayAll_216_, lean_object* v_display_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v___x_222_, lean_object* v_nsStx_223_, lean_object* v_toApplicative_224_, lean_object* v_openDecls_225_){
_start:
{
lean_object* v___y_227_; lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___f_270_; lean_object* v_candidates_271_; lean_object* v___x_272_; lean_object* v_shadowed_273_; uint8_t v___x_274_; 
v___x_268_ = lean_box(v___x_212_);
v___x_269_ = lean_box(v___x_213_);
lean_inc_n(v_currNamespace_211_, 2);
lean_inc(v_resolved_210_);
v___f_270_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__4___boxed), 7, 6);
lean_closure_set(v___f_270_, 0, v___x_209_);
lean_closure_set(v___f_270_, 1, v_resolved_210_);
lean_closure_set(v___f_270_, 2, v_currNamespace_211_);
lean_closure_set(v___f_270_, 3, v_openDecls_225_);
lean_closure_set(v___f_270_, 4, v___x_268_);
lean_closure_set(v___f_270_, 5, v___x_269_);
lean_inc(v_val_215_);
v_candidates_271_ = l___private_Lean_Linter_AmbiguousOpen_0__Lean_Linter_scopeCandidates(v_env_214_, v_val_215_, v_currNamespace_211_);
v___x_272_ = lean_box(0);
v_shadowed_273_ = l_List_filterTR_loop___redArg(v___f_270_, v_candidates_271_, v___x_272_);
v___x_274_ = l_List_isEmpty___redArg(v_shadowed_273_);
if (v___x_274_ == 0)
{
lean_object* v___x_275_; lean_object* v___x_276_; uint8_t v___x_277_; 
lean_dec_ref(v_toApplicative_224_);
v___x_275_ = l_List_lengthTR___redArg(v_shadowed_273_);
v___x_276_ = lean_unsigned_to_nat(1u);
v___x_277_ = lean_nat_dec_eq(v___x_275_, v___x_276_);
lean_dec(v___x_275_);
if (v___x_277_ == 0)
{
lean_object* v___x_278_; lean_object* v___x_279_; lean_object* v___x_280_; 
lean_inc_ref(v_displayAll_216_);
v___x_278_ = lean_apply_1(v_displayAll_216_, v_shadowed_273_);
v___x_279_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__13, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__13_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__13);
v___x_280_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_280_, 0, v___x_278_);
lean_ctor_set(v___x_280_, 1, v___x_279_);
v___y_227_ = v___x_280_;
goto v___jp_226_;
}
else
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
lean_inc_ref(v_displayAll_216_);
v___x_281_ = lean_apply_1(v_displayAll_216_, v_shadowed_273_);
v___x_282_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__15, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__15_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__15);
v___x_283_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_281_);
lean_ctor_set(v___x_283_, 1, v___x_282_);
v___y_227_ = v___x_283_;
goto v___jp_226_;
}
}
else
{
lean_object* v_toPure_284_; lean_object* v___x_285_; lean_object* v___x_286_; 
lean_dec(v_shadowed_273_);
lean_dec(v_nsStx_223_);
lean_dec_ref(v___x_222_);
lean_dec(v_inst_221_);
lean_dec(v_inst_220_);
lean_dec_ref(v_inst_219_);
lean_dec_ref(v_inst_218_);
lean_dec_ref(v_display_217_);
lean_dec_ref(v_displayAll_216_);
lean_dec(v_val_215_);
lean_dec(v_currNamespace_211_);
lean_dec(v_resolved_210_);
v_toPure_284_ = lean_ctor_get(v_toApplicative_224_, 1);
lean_inc(v_toPure_284_);
lean_dec_ref(v_toApplicative_224_);
v___x_285_ = lean_box(0);
v___x_286_ = lean_apply_2(v_toPure_284_, lean_box(0), v___x_285_);
return v___x_286_;
}
v___jp_226_:
{
lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; lean_object* v___x_232_; lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v_hint_236_; 
v___x_228_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__1, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__1_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__1);
v___x_229_ = l_Lean_rootNamespace;
v___x_230_ = lean_box(0);
v___x_231_ = l_List_head_x21___redArg(v___x_230_, v_resolved_210_);
v___x_232_ = l_Lean_Name_append(v___x_229_, v___x_231_);
v___x_233_ = l_Lean_MessageData_ofName(v___x_232_);
v___x_234_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_234_, 0, v___x_228_);
lean_ctor_set(v___x_234_, 1, v___x_233_);
v___x_235_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__3, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__3_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__3);
v_hint_236_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_hint_236_, 0, v___x_234_);
lean_ctor_set(v_hint_236_, 1, v___x_235_);
if (lean_obj_tag(v_resolved_210_) == 1)
{
lean_object* v_tail_237_; 
v_tail_237_ = lean_ctor_get(v_resolved_210_, 1);
if (lean_obj_tag(v_tail_237_) == 0)
{
lean_object* v_head_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_262_; 
lean_dec_ref(v_displayAll_216_);
v_head_238_ = lean_ctor_get(v_resolved_210_, 0);
v_isSharedCheck_262_ = !lean_is_exclusive(v_resolved_210_);
if (v_isSharedCheck_262_ == 0)
{
lean_object* v_unused_263_; 
v_unused_263_ = lean_ctor_get(v_resolved_210_, 1);
lean_dec(v_unused_263_);
v___x_240_ = v_resolved_210_;
v_isShared_241_ = v_isSharedCheck_262_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_head_238_);
lean_dec(v_resolved_210_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_262_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_242_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5___closed__1);
v___x_243_ = l_Lean_MessageData_ofName(v_val_215_);
if (v_isShared_241_ == 0)
{
lean_ctor_set_tag(v___x_240_, 7);
lean_ctor_set(v___x_240_, 1, v___x_243_);
lean_ctor_set(v___x_240_, 0, v___x_242_);
v___x_245_ = v___x_240_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_261_; 
v_reuseFailAlloc_261_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_261_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_261_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_261_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; lean_object* v___x_257_; lean_object* v___x_258_; lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_246_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__5, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__5_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__5);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_apply_1(v_display_217_, v_head_238_);
v___x_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__7, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__7_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__7);
v___x_251_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_251_, 0, v___x_249_);
lean_ctor_set(v___x_251_, 1, v___x_250_);
v___x_252_ = l_Lean_MessageData_ofName(v_currNamespace_211_);
v___x_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_253_, 0, v___x_251_);
lean_ctor_set(v___x_253_, 1, v___x_252_);
v___x_254_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__9, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__9_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__9);
v___x_255_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_255_, 0, v___x_253_);
lean_ctor_set(v___x_255_, 1, v___x_254_);
v___x_256_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_256_, 0, v___x_255_);
lean_ctor_set(v___x_256_, 1, v___y_227_);
v___x_257_ = lean_obj_once(&l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__11, &l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__11_once, _init_l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___closed__11);
v___x_258_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_258_, 0, v___x_256_);
lean_ctor_set(v___x_258_, 1, v___x_257_);
v___x_259_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_259_, 0, v___x_258_);
lean_ctor_set(v___x_259_, 1, v_hint_236_);
v___x_260_ = l_Lean_Linter_logLint___redArg(v_inst_218_, v_inst_219_, v_inst_220_, v_inst_221_, v___x_222_, v_nsStx_223_, v___x_259_);
return v___x_260_;
}
}
}
else
{
lean_object* v___x_264_; lean_object* v___x_265_; 
lean_dec_ref(v_display_217_);
lean_inc_ref(v_resolved_210_);
v___x_264_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(v_val_215_, v_displayAll_216_, v_resolved_210_, v___y_227_, v_currNamespace_211_, v_hint_236_, v_resolved_210_);
lean_dec_ref_known(v_resolved_210_, 2);
v___x_265_ = l_Lean_Linter_logLint___redArg(v_inst_218_, v_inst_219_, v_inst_220_, v_inst_221_, v___x_222_, v_nsStx_223_, v___x_264_);
return v___x_265_;
}
}
else
{
lean_object* v___x_266_; lean_object* v___x_267_; 
lean_dec_ref(v_display_217_);
lean_inc(v_resolved_210_);
v___x_266_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__5(v_val_215_, v_displayAll_216_, v_resolved_210_, v___y_227_, v_currNamespace_211_, v_hint_236_, v_resolved_210_);
lean_dec(v_resolved_210_);
v___x_267_ = l_Lean_Linter_logLint___redArg(v_inst_218_, v_inst_219_, v_inst_220_, v_inst_221_, v___x_222_, v_nsStx_223_, v___x_266_);
return v___x_267_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed(lean_object** _args){
lean_object* v___x_287_ = _args[0];
lean_object* v_resolved_288_ = _args[1];
lean_object* v_currNamespace_289_ = _args[2];
lean_object* v___x_290_ = _args[3];
lean_object* v___x_291_ = _args[4];
lean_object* v_env_292_ = _args[5];
lean_object* v_val_293_ = _args[6];
lean_object* v_displayAll_294_ = _args[7];
lean_object* v_display_295_ = _args[8];
lean_object* v_inst_296_ = _args[9];
lean_object* v_inst_297_ = _args[10];
lean_object* v_inst_298_ = _args[11];
lean_object* v_inst_299_ = _args[12];
lean_object* v___x_300_ = _args[13];
lean_object* v_nsStx_301_ = _args[14];
lean_object* v_toApplicative_302_ = _args[15];
lean_object* v_openDecls_303_ = _args[16];
_start:
{
uint8_t v___x_2417__boxed_304_; uint8_t v___x_2418__boxed_305_; lean_object* v_res_306_; 
v___x_2417__boxed_304_ = lean_unbox(v___x_290_);
v___x_2418__boxed_305_ = lean_unbox(v___x_291_);
v_res_306_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6(v___x_287_, v_resolved_288_, v_currNamespace_289_, v___x_2417__boxed_304_, v___x_2418__boxed_305_, v_env_292_, v_val_293_, v_displayAll_294_, v_display_295_, v_inst_296_, v_inst_297_, v_inst_298_, v_inst_299_, v___x_300_, v_nsStx_301_, v_toApplicative_302_, v_openDecls_303_);
return v_res_306_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(lean_object* v___x_307_, lean_object* v_resolved_308_, uint8_t v___x_309_, uint8_t v___x_310_, lean_object* v_env_311_, lean_object* v_val_312_, lean_object* v_displayAll_313_, lean_object* v_display_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v___x_319_, lean_object* v_nsStx_320_, lean_object* v_toApplicative_321_, lean_object* v_toBind_322_, lean_object* v_getOpenDecls_323_, lean_object* v_currNamespace_324_){
_start:
{
lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___f_327_; lean_object* v___x_328_; 
v___x_325_ = lean_box(v___x_309_);
v___x_326_ = lean_box(v___x_310_);
v___f_327_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__6___boxed), 17, 16);
lean_closure_set(v___f_327_, 0, v___x_307_);
lean_closure_set(v___f_327_, 1, v_resolved_308_);
lean_closure_set(v___f_327_, 2, v_currNamespace_324_);
lean_closure_set(v___f_327_, 3, v___x_325_);
lean_closure_set(v___f_327_, 4, v___x_326_);
lean_closure_set(v___f_327_, 5, v_env_311_);
lean_closure_set(v___f_327_, 6, v_val_312_);
lean_closure_set(v___f_327_, 7, v_displayAll_313_);
lean_closure_set(v___f_327_, 8, v_display_314_);
lean_closure_set(v___f_327_, 9, v_inst_315_);
lean_closure_set(v___f_327_, 10, v_inst_316_);
lean_closure_set(v___f_327_, 11, v_inst_317_);
lean_closure_set(v___f_327_, 12, v_inst_318_);
lean_closure_set(v___f_327_, 13, v___x_319_);
lean_closure_set(v___f_327_, 14, v_nsStx_320_);
lean_closure_set(v___f_327_, 15, v_toApplicative_321_);
v___x_328_ = lean_apply_4(v_toBind_322_, lean_box(0), lean_box(0), v_getOpenDecls_323_, v___f_327_);
return v___x_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed(lean_object** _args){
lean_object* v___x_329_ = _args[0];
lean_object* v_resolved_330_ = _args[1];
lean_object* v___x_331_ = _args[2];
lean_object* v___x_332_ = _args[3];
lean_object* v_env_333_ = _args[4];
lean_object* v_val_334_ = _args[5];
lean_object* v_displayAll_335_ = _args[6];
lean_object* v_display_336_ = _args[7];
lean_object* v_inst_337_ = _args[8];
lean_object* v_inst_338_ = _args[9];
lean_object* v_inst_339_ = _args[10];
lean_object* v_inst_340_ = _args[11];
lean_object* v___x_341_ = _args[12];
lean_object* v_nsStx_342_ = _args[13];
lean_object* v_toApplicative_343_ = _args[14];
lean_object* v_toBind_344_ = _args[15];
lean_object* v_getOpenDecls_345_ = _args[16];
lean_object* v_currNamespace_346_ = _args[17];
_start:
{
uint8_t v___x_2582__boxed_347_; uint8_t v___x_2583__boxed_348_; lean_object* v_res_349_; 
v___x_2582__boxed_347_ = lean_unbox(v___x_331_);
v___x_2583__boxed_348_ = lean_unbox(v___x_332_);
v_res_349_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7(v___x_329_, v_resolved_330_, v___x_2582__boxed_347_, v___x_2583__boxed_348_, v_env_333_, v_val_334_, v_displayAll_335_, v_display_336_, v_inst_337_, v_inst_338_, v_inst_339_, v_inst_340_, v___x_341_, v_nsStx_342_, v_toApplicative_343_, v_toBind_344_, v_getOpenDecls_345_, v_currNamespace_346_);
return v_res_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(lean_object* v_inst_350_, lean_object* v___x_351_, lean_object* v_resolved_352_, uint8_t v___x_353_, uint8_t v___x_354_, lean_object* v_val_355_, lean_object* v_displayAll_356_, lean_object* v_display_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_inst_360_, lean_object* v_inst_361_, lean_object* v___x_362_, lean_object* v_nsStx_363_, lean_object* v_toApplicative_364_, lean_object* v_toBind_365_, lean_object* v_env_366_){
_start:
{
lean_object* v_getCurrNamespace_367_; lean_object* v_getOpenDecls_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___f_371_; lean_object* v___x_372_; 
v_getCurrNamespace_367_ = lean_ctor_get(v_inst_350_, 0);
lean_inc(v_getCurrNamespace_367_);
v_getOpenDecls_368_ = lean_ctor_get(v_inst_350_, 1);
lean_inc(v_getOpenDecls_368_);
lean_dec_ref(v_inst_350_);
v___x_369_ = lean_box(v___x_353_);
v___x_370_ = lean_box(v___x_354_);
lean_inc(v_toBind_365_);
v___f_371_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__7___boxed), 18, 17);
lean_closure_set(v___f_371_, 0, v___x_351_);
lean_closure_set(v___f_371_, 1, v_resolved_352_);
lean_closure_set(v___f_371_, 2, v___x_369_);
lean_closure_set(v___f_371_, 3, v___x_370_);
lean_closure_set(v___f_371_, 4, v_env_366_);
lean_closure_set(v___f_371_, 5, v_val_355_);
lean_closure_set(v___f_371_, 6, v_displayAll_356_);
lean_closure_set(v___f_371_, 7, v_display_357_);
lean_closure_set(v___f_371_, 8, v_inst_358_);
lean_closure_set(v___f_371_, 9, v_inst_359_);
lean_closure_set(v___f_371_, 10, v_inst_360_);
lean_closure_set(v___f_371_, 11, v_inst_361_);
lean_closure_set(v___f_371_, 12, v___x_362_);
lean_closure_set(v___f_371_, 13, v_nsStx_363_);
lean_closure_set(v___f_371_, 14, v_toApplicative_364_);
lean_closure_set(v___f_371_, 15, v_toBind_365_);
lean_closure_set(v___f_371_, 16, v_getOpenDecls_368_);
v___x_372_ = lean_apply_4(v_toBind_365_, lean_box(0), lean_box(0), v_getCurrNamespace_367_, v___f_371_);
return v___x_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed(lean_object** _args){
lean_object* v_inst_373_ = _args[0];
lean_object* v___x_374_ = _args[1];
lean_object* v_resolved_375_ = _args[2];
lean_object* v___x_376_ = _args[3];
lean_object* v___x_377_ = _args[4];
lean_object* v_val_378_ = _args[5];
lean_object* v_displayAll_379_ = _args[6];
lean_object* v_display_380_ = _args[7];
lean_object* v_inst_381_ = _args[8];
lean_object* v_inst_382_ = _args[9];
lean_object* v_inst_383_ = _args[10];
lean_object* v_inst_384_ = _args[11];
lean_object* v___x_385_ = _args[12];
lean_object* v_nsStx_386_ = _args[13];
lean_object* v_toApplicative_387_ = _args[14];
lean_object* v_toBind_388_ = _args[15];
lean_object* v_env_389_ = _args[16];
_start:
{
uint8_t v___x_2618__boxed_390_; uint8_t v___x_2619__boxed_391_; lean_object* v_res_392_; 
v___x_2618__boxed_390_ = lean_unbox(v___x_376_);
v___x_2619__boxed_391_ = lean_unbox(v___x_377_);
v_res_392_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8(v_inst_373_, v___x_374_, v_resolved_375_, v___x_2618__boxed_390_, v___x_2619__boxed_391_, v_val_378_, v_displayAll_379_, v_display_380_, v_inst_381_, v_inst_382_, v_inst_383_, v_inst_384_, v___x_385_, v_nsStx_386_, v_toApplicative_387_, v_toBind_388_, v_env_389_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9(lean_object* v_toApplicative_394_, lean_object* v_nsStx_395_, lean_object* v_inst_396_, lean_object* v_resolved_397_, lean_object* v_inst_398_, lean_object* v_displayAll_399_, lean_object* v_display_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_toBind_405_, lean_object* v_____do__lift_406_){
_start:
{
lean_object* v___x_407_; uint8_t v___x_408_; 
v___x_407_ = l_Lean_Linter_linter_ambiguousOpen;
v___x_408_ = l_Lean_Linter_getLinterValue(v___x_407_, v_____do__lift_406_);
if (v___x_408_ == 0)
{
lean_object* v_toPure_409_; lean_object* v___x_410_; lean_object* v___x_411_; 
lean_dec(v_toBind_405_);
lean_dec(v_inst_404_);
lean_dec(v_inst_403_);
lean_dec_ref(v_inst_402_);
lean_dec_ref(v_inst_401_);
lean_dec_ref(v_display_400_);
lean_dec_ref(v_displayAll_399_);
lean_dec_ref(v_inst_398_);
lean_dec(v_resolved_397_);
lean_dec_ref(v_inst_396_);
lean_dec(v_nsStx_395_);
v_toPure_409_ = lean_ctor_get(v_toApplicative_394_, 1);
lean_inc(v_toPure_409_);
lean_dec_ref(v_toApplicative_394_);
v___x_410_ = lean_box(0);
v___x_411_ = lean_apply_2(v_toPure_409_, lean_box(0), v___x_410_);
return v___x_411_;
}
else
{
if (lean_obj_tag(v_nsStx_395_) == 3)
{
lean_object* v_info_412_; 
v_info_412_ = lean_ctor_get(v_nsStx_395_, 0);
if (lean_obj_tag(v_info_412_) == 0)
{
lean_object* v_val_413_; lean_object* v_preresolved_414_; lean_object* v___x_415_; lean_object* v___f_416_; uint8_t v___x_417_; 
v_val_413_ = lean_ctor_get(v_nsStx_395_, 2);
lean_inc(v_val_413_);
v_preresolved_414_ = lean_ctor_get(v_nsStx_395_, 3);
v___x_415_ = lean_box(v___x_408_);
v___f_416_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__2___boxed), 2, 1);
lean_closure_set(v___f_416_, 0, v___x_415_);
lean_inc(v_preresolved_414_);
v___x_417_ = l_List_any___redArg(v_preresolved_414_, v___f_416_);
if (v___x_417_ == 0)
{
lean_object* v_getEnv_418_; lean_object* v___x_419_; lean_object* v_resolved_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___f_423_; lean_object* v___x_424_; 
v_getEnv_418_ = lean_ctor_get(v_inst_396_, 0);
lean_inc(v_getEnv_418_);
lean_dec_ref(v_inst_396_);
v___x_419_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9___closed__0));
v_resolved_420_ = l_List_eraseDups___redArg(v___x_419_, v_resolved_397_);
v___x_421_ = lean_box(v___x_408_);
v___x_422_ = lean_box(v___x_417_);
lean_inc(v_toBind_405_);
v___f_423_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__8___boxed), 17, 16);
lean_closure_set(v___f_423_, 0, v_inst_398_);
lean_closure_set(v___f_423_, 1, v___x_419_);
lean_closure_set(v___f_423_, 2, v_resolved_420_);
lean_closure_set(v___f_423_, 3, v___x_421_);
lean_closure_set(v___f_423_, 4, v___x_422_);
lean_closure_set(v___f_423_, 5, v_val_413_);
lean_closure_set(v___f_423_, 6, v_displayAll_399_);
lean_closure_set(v___f_423_, 7, v_display_400_);
lean_closure_set(v___f_423_, 8, v_inst_401_);
lean_closure_set(v___f_423_, 9, v_inst_402_);
lean_closure_set(v___f_423_, 10, v_inst_403_);
lean_closure_set(v___f_423_, 11, v_inst_404_);
lean_closure_set(v___f_423_, 12, v___x_407_);
lean_closure_set(v___f_423_, 13, v_nsStx_395_);
lean_closure_set(v___f_423_, 14, v_toApplicative_394_);
lean_closure_set(v___f_423_, 15, v_toBind_405_);
v___x_424_ = lean_apply_4(v_toBind_405_, lean_box(0), lean_box(0), v_getEnv_418_, v___f_423_);
return v___x_424_;
}
else
{
lean_object* v_toPure_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
lean_dec(v_val_413_);
lean_dec_ref_known(v_nsStx_395_, 4);
lean_dec(v_toBind_405_);
lean_dec(v_inst_404_);
lean_dec(v_inst_403_);
lean_dec_ref(v_inst_402_);
lean_dec_ref(v_inst_401_);
lean_dec_ref(v_display_400_);
lean_dec_ref(v_displayAll_399_);
lean_dec_ref(v_inst_398_);
lean_dec(v_resolved_397_);
lean_dec_ref(v_inst_396_);
v_toPure_425_ = lean_ctor_get(v_toApplicative_394_, 1);
lean_inc(v_toPure_425_);
lean_dec_ref(v_toApplicative_394_);
v___x_426_ = lean_box(0);
v___x_427_ = lean_apply_2(v_toPure_425_, lean_box(0), v___x_426_);
return v___x_427_;
}
}
else
{
lean_object* v_toPure_428_; lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec_ref_known(v_nsStx_395_, 4);
lean_dec(v_toBind_405_);
lean_dec(v_inst_404_);
lean_dec(v_inst_403_);
lean_dec_ref(v_inst_402_);
lean_dec_ref(v_inst_401_);
lean_dec_ref(v_display_400_);
lean_dec_ref(v_displayAll_399_);
lean_dec_ref(v_inst_398_);
lean_dec(v_resolved_397_);
lean_dec_ref(v_inst_396_);
v_toPure_428_ = lean_ctor_get(v_toApplicative_394_, 1);
lean_inc(v_toPure_428_);
lean_dec_ref(v_toApplicative_394_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_apply_2(v_toPure_428_, lean_box(0), v___x_429_);
return v___x_430_;
}
}
else
{
lean_object* v_toPure_431_; lean_object* v___x_432_; lean_object* v___x_433_; 
lean_dec(v_toBind_405_);
lean_dec(v_inst_404_);
lean_dec(v_inst_403_);
lean_dec_ref(v_inst_402_);
lean_dec_ref(v_inst_401_);
lean_dec_ref(v_display_400_);
lean_dec_ref(v_displayAll_399_);
lean_dec_ref(v_inst_398_);
lean_dec(v_resolved_397_);
lean_dec_ref(v_inst_396_);
lean_dec(v_nsStx_395_);
v_toPure_431_ = lean_ctor_get(v_toApplicative_394_, 1);
lean_inc(v_toPure_431_);
lean_dec_ref(v_toApplicative_394_);
v___x_432_ = lean_box(0);
v___x_433_ = lean_apply_2(v_toPure_431_, lean_box(0), v___x_432_);
return v___x_433_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9___boxed(lean_object* v_toApplicative_434_, lean_object* v_nsStx_435_, lean_object* v_inst_436_, lean_object* v_resolved_437_, lean_object* v_inst_438_, lean_object* v_displayAll_439_, lean_object* v_display_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_toBind_445_, lean_object* v_____do__lift_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9(v_toApplicative_434_, v_nsStx_435_, v_inst_436_, v_resolved_437_, v_inst_438_, v_displayAll_439_, v_display_440_, v_inst_441_, v_inst_442_, v_inst_443_, v_inst_444_, v_toBind_445_, v_____do__lift_446_);
lean_dec_ref(v_____do__lift_446_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen___redArg(lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_inst_456_, lean_object* v_nsStx_457_, lean_object* v_resolved_458_){
_start:
{
lean_object* v_toApplicative_459_; lean_object* v_toBind_460_; lean_object* v_display_461_; lean_object* v_displayAll_462_; lean_object* v___f_463_; lean_object* v___x_464_; lean_object* v___x_465_; 
v_toApplicative_459_ = lean_ctor_get(v_inst_451_, 0);
v_toBind_460_ = lean_ctor_get(v_inst_451_, 1);
lean_inc_n(v_toBind_460_, 2);
v_display_461_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___closed__0));
v_displayAll_462_ = ((lean_object*)(l_Lean_Linter_checkAmbiguousOpen___redArg___closed__1));
lean_inc(v_inst_453_);
lean_inc_ref(v_inst_451_);
lean_inc_ref(v_inst_452_);
lean_inc_ref(v_toApplicative_459_);
v___f_463_ = lean_alloc_closure((void*)(l_Lean_Linter_checkAmbiguousOpen___redArg___lam__9___boxed), 13, 12);
lean_closure_set(v___f_463_, 0, v_toApplicative_459_);
lean_closure_set(v___f_463_, 1, v_nsStx_457_);
lean_closure_set(v___f_463_, 2, v_inst_452_);
lean_closure_set(v___f_463_, 3, v_resolved_458_);
lean_closure_set(v___f_463_, 4, v_inst_456_);
lean_closure_set(v___f_463_, 5, v_displayAll_462_);
lean_closure_set(v___f_463_, 6, v_display_461_);
lean_closure_set(v___f_463_, 7, v_inst_451_);
lean_closure_set(v___f_463_, 8, v_inst_454_);
lean_closure_set(v___f_463_, 9, v_inst_455_);
lean_closure_set(v___f_463_, 10, v_inst_453_);
lean_closure_set(v___f_463_, 11, v_toBind_460_);
v___x_464_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_451_, v_inst_453_, v_inst_452_);
v___x_465_ = lean_apply_4(v_toBind_460_, lean_box(0), lean_box(0), v___x_464_, v___f_463_);
return v___x_465_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_checkAmbiguousOpen(lean_object* v_m_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_inst_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_nsStx_473_, lean_object* v_resolved_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_Linter_checkAmbiguousOpen___redArg(v_inst_467_, v_inst_468_, v_inst_469_, v_inst_470_, v_inst_471_, v_inst_472_, v_nsStx_473_, v_resolved_474_);
return v___x_475_;
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
