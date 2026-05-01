// Lean compiler output
// Module: Lean.Linter.EnvLinter.Nolint
// Imports: public import Lean.Attributes import Init.Linter
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
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t l_Lean_Syntax_isOfKind(lean_object*, lean_object*);
extern lean_object* l_Lean_Elab_unsupportedSyntaxExceptionId;
lean_object* l_Lean_Syntax_getArg(lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getArgs(lean_object*);
size_t lean_array_size(lean_object*);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
size_t lean_usize_add(size_t, size_t);
lean_object* l_Lean_TSyntax_getId(lean_object*);
lean_object* lean_erase_macro_scopes(lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerParametricAttribute___redArg(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
uint8_t l_Array_contains___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ParametricAttribute_getParam_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Array_instInhabited(lean_object*);
static lean_once_cell_t l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0;
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg();
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__2(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__1(size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed, .m_arity = 5, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "EnvLinter"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = "builtinNolintAttr"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__3_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(251, 76, 236, 169, 217, 120, 18, 80)}};
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value_aux_2),((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__4_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(97, 211, 244, 233, 213, 84, 203, 93)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 15, .m_capacity = 15, .m_length = 14, .m_data = "builtin_nolint"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__6_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(96, 180, 230, 115, 242, 101, 35, 113)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed, .m_arity = 6, .m_num_fixed = 1, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value)} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 74, .m_capacity = 74, .m_length = 73, .m_data = "Do not report this declaration in any of the tests of `lake builtin-lint`"};
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__5_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__7_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__9_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*4 + 8, .m_other = 4, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__10_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__8_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__11_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_builtinNolintAttr;
static const lean_array_object l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1;
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = lean_box(0);
v___x_2_ = l_Lean_Elab_unsupportedSyntaxExceptionId;
v___x_3_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_1_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg(){
_start:
{
lean_object* v___x_5_; lean_object* v___x_6_; 
v___x_5_ = lean_obj_once(&l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0, &l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0_once, _init_l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___closed__0);
v___x_6_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_6_, 0, v___x_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v___y_7_){
_start:
{
lean_object* v_res_8_; 
v_res_8_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg();
return v_res_8_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b1_9_, lean_object* v___y_10_, lean_object* v___y_11_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg();
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b1_14_, lean_object* v___y_15_, lean_object* v___y_16_, lean_object* v___y_17_){
_start:
{
lean_object* v_res_18_; 
v_res_18_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0(v_00_u03b1_14_, v___y_15_, v___y_16_);
lean_dec(v___y_16_);
lean_dec_ref(v___y_15_);
return v_res_18_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(lean_object* v_x_19_, lean_object* v_x_20_, lean_object* v_x_21_, lean_object* v___y_22_){
_start:
{
lean_object* v___x_24_; lean_object* v___x_25_; 
v___x_24_ = lean_box(0);
v___x_25_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_25_, 0, v___x_24_);
return v___x_25_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(lean_object* v_x_26_, lean_object* v_x_27_, lean_object* v_x_28_, lean_object* v___y_29_, lean_object* v___y_30_){
_start:
{
lean_object* v_res_31_; 
v_res_31_ = l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__0_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(v_x_26_, v_x_27_, v_x_28_, v___y_29_);
lean_dec(v___y_29_);
lean_dec_ref(v_x_28_);
lean_dec_ref(v_x_27_);
lean_dec(v_x_26_);
return v_res_31_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__2(size_t v_sz_32_, size_t v_i_33_, lean_object* v_bs_34_){
_start:
{
uint8_t v___x_35_; 
v___x_35_ = lean_usize_dec_lt(v_i_33_, v_sz_32_);
if (v___x_35_ == 0)
{
return v_bs_34_;
}
else
{
lean_object* v_v_36_; lean_object* v___x_37_; lean_object* v_bs_x27_38_; lean_object* v___x_39_; lean_object* v___x_40_; size_t v___x_41_; size_t v___x_42_; lean_object* v___x_43_; 
v_v_36_ = lean_array_uget(v_bs_34_, v_i_33_);
v___x_37_ = lean_unsigned_to_nat(0u);
v_bs_x27_38_ = lean_array_uset(v_bs_34_, v_i_33_, v___x_37_);
v___x_39_ = l_Lean_TSyntax_getId(v_v_36_);
lean_dec(v_v_36_);
v___x_40_ = lean_erase_macro_scopes(v___x_39_);
v___x_41_ = ((size_t)1ULL);
v___x_42_ = lean_usize_add(v_i_33_, v___x_41_);
v___x_43_ = lean_array_uset(v_bs_x27_38_, v_i_33_, v___x_40_);
v_i_33_ = v___x_42_;
v_bs_34_ = v___x_43_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__2___boxed(lean_object* v_sz_45_, lean_object* v_i_46_, lean_object* v_bs_47_){
_start:
{
size_t v_sz_boxed_48_; size_t v_i_boxed_49_; lean_object* v_res_50_; 
v_sz_boxed_48_ = lean_unbox_usize(v_sz_45_);
lean_dec(v_sz_45_);
v_i_boxed_49_ = lean_unbox_usize(v_i_46_);
lean_dec(v_i_46_);
v_res_50_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__2(v_sz_boxed_48_, v_i_boxed_49_, v_bs_47_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__1(size_t v_sz_51_, size_t v_i_52_, lean_object* v_bs_53_){
_start:
{
uint8_t v___x_54_; 
v___x_54_ = lean_usize_dec_lt(v_i_52_, v_sz_51_);
if (v___x_54_ == 0)
{
lean_object* v___x_55_; 
v___x_55_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_55_, 0, v_bs_53_);
return v___x_55_;
}
else
{
lean_object* v_v_56_; lean_object* v___x_57_; lean_object* v_bs_x27_58_; size_t v___x_59_; size_t v___x_60_; lean_object* v___x_61_; 
v_v_56_ = lean_array_uget(v_bs_53_, v_i_52_);
v___x_57_ = lean_unsigned_to_nat(0u);
v_bs_x27_58_ = lean_array_uset(v_bs_53_, v_i_52_, v___x_57_);
v___x_59_ = ((size_t)1ULL);
v___x_60_ = lean_usize_add(v_i_52_, v___x_59_);
v___x_61_ = lean_array_uset(v_bs_x27_58_, v_i_52_, v_v_56_);
v_i_52_ = v___x_60_;
v_bs_53_ = v___x_61_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__1___boxed(lean_object* v_sz_63_, lean_object* v_i_64_, lean_object* v_bs_65_){
_start:
{
size_t v_sz_boxed_66_; size_t v_i_boxed_67_; lean_object* v_res_68_; 
v_sz_boxed_66_ = lean_unbox_usize(v_sz_63_);
lean_dec(v_sz_63_);
v_i_boxed_67_ = lean_unbox_usize(v_i_64_);
lean_dec(v_i_64_);
v_res_68_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__1(v_sz_boxed_66_, v_i_boxed_67_, v_bs_65_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(lean_object* v___x_69_, lean_object* v_x_70_, lean_object* v_x_71_, lean_object* v___y_72_, lean_object* v___y_73_){
_start:
{
uint8_t v___x_75_; 
lean_inc(v_x_71_);
v___x_75_ = l_Lean_Syntax_isOfKind(v_x_71_, v___x_69_);
if (v___x_75_ == 0)
{
lean_object* v___x_76_; 
lean_dec(v_x_71_);
v___x_76_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg();
return v___x_76_;
}
else
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; size_t v_sz_80_; size_t v___x_81_; lean_object* v___x_82_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = l_Lean_Syntax_getArg(v_x_71_, v___x_77_);
lean_dec(v_x_71_);
v___x_79_ = l_Lean_Syntax_getArgs(v___x_78_);
lean_dec(v___x_78_);
v_sz_80_ = lean_array_size(v___x_79_);
v___x_81_ = ((size_t)0ULL);
v___x_82_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__1(v_sz_80_, v___x_81_, v___x_79_);
if (lean_obj_tag(v___x_82_) == 0)
{
lean_object* v___x_83_; 
v___x_83_ = l_Lean_Elab_throwUnsupportedSyntax___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__0___redArg();
return v___x_83_;
}
else
{
lean_object* v_val_84_; lean_object* v___x_86_; uint8_t v_isShared_87_; uint8_t v_isSharedCheck_93_; 
v_val_84_ = lean_ctor_get(v___x_82_, 0);
v_isSharedCheck_93_ = !lean_is_exclusive(v___x_82_);
if (v_isSharedCheck_93_ == 0)
{
v___x_86_ = v___x_82_;
v_isShared_87_ = v_isSharedCheck_93_;
goto v_resetjp_85_;
}
else
{
lean_inc(v_val_84_);
lean_dec(v___x_82_);
v___x_86_ = lean_box(0);
v_isShared_87_ = v_isSharedCheck_93_;
goto v_resetjp_85_;
}
v_resetjp_85_:
{
size_t v_sz_88_; lean_object* v___x_89_; lean_object* v___x_91_; 
v_sz_88_ = lean_array_size(v_val_84_);
v___x_89_ = l___private_Init_Data_Array_Basic_0__Array_mapMUnsafe_map___at___00__private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2__spec__2(v_sz_88_, v___x_81_, v_val_84_);
if (v_isShared_87_ == 0)
{
lean_ctor_set_tag(v___x_86_, 0);
lean_ctor_set(v___x_86_, 0, v___x_89_);
v___x_91_ = v___x_86_;
goto v_reusejp_90_;
}
else
{
lean_object* v_reuseFailAlloc_92_; 
v_reuseFailAlloc_92_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_92_, 0, v___x_89_);
v___x_91_ = v_reuseFailAlloc_92_;
goto v_reusejp_90_;
}
v_reusejp_90_:
{
return v___x_91_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(lean_object* v___x_94_, lean_object* v_x_95_, lean_object* v_x_96_, lean_object* v___y_97_, lean_object* v___y_98_, lean_object* v___y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__1_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(v___x_94_, v_x_95_, v_x_96_, v___y_97_, v___y_98_);
lean_dec(v___y_98_);
lean_dec_ref(v___y_97_);
lean_dec(v_x_95_);
lean_dec(v___x_94_);
return v_res_100_;
}
}
LEAN_EXPORT uint8_t l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(uint8_t v___x_101_, lean_object* v_env_102_, lean_object* v_n_103_, lean_object* v_x_104_){
_start:
{
uint8_t v___x_105_; 
v___x_105_ = l_Lean_Environment_contains(v_env_102_, v_n_103_, v___x_101_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(lean_object* v___x_106_, lean_object* v_env_107_, lean_object* v_n_108_, lean_object* v_x_109_){
_start:
{
uint8_t v___x_779__boxed_110_; uint8_t v_res_111_; lean_object* v_r_112_; 
v___x_779__boxed_110_ = lean_unbox(v___x_106_);
v_res_111_ = l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___lam__2_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(v___x_779__boxed_110_, v_env_107_, v_n_108_, v_x_109_);
lean_dec_ref(v_x_109_);
v_r_112_ = lean_box(v_res_111_);
return v_r_112_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn___closed__12_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_));
v___x_145_ = l_Lean_registerParametricAttribute___redArg(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2____boxed(lean_object* v_a_146_){
_start:
{
lean_object* v_res_147_; 
v_res_147_ = l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_();
return v_res_147_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0(lean_object* v___x_150_, lean_object* v_linter_151_, lean_object* v_toPure_152_, lean_object* v___x_153_, lean_object* v_decl_154_, lean_object* v_____do__lift_155_){
_start:
{
lean_object* v___y_157_; lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = l_Lean_Linter_EnvLinter_builtinNolintAttr;
v___x_166_ = l_Lean_ParametricAttribute_getParam_x3f___redArg(v___x_153_, v___x_165_, v_____do__lift_155_, v_decl_154_);
if (lean_obj_tag(v___x_166_) == 0)
{
lean_object* v___x_167_; 
v___x_167_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0___closed__0));
v___y_157_ = v___x_167_;
goto v___jp_156_;
}
else
{
lean_object* v_val_168_; 
v_val_168_ = lean_ctor_get(v___x_166_, 0);
lean_inc(v_val_168_);
lean_dec_ref(v___x_166_);
v___y_157_ = v_val_168_;
goto v___jp_156_;
}
v___jp_156_:
{
uint8_t v___x_158_; 
v___x_158_ = l_Array_contains___redArg(v___x_150_, v___y_157_, v_linter_151_);
if (v___x_158_ == 0)
{
uint8_t v___x_159_; lean_object* v___x_160_; lean_object* v___x_161_; 
v___x_159_ = 1;
v___x_160_ = lean_box(v___x_159_);
v___x_161_ = lean_apply_2(v_toPure_152_, lean_box(0), v___x_160_);
return v___x_161_;
}
else
{
uint8_t v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; 
v___x_162_ = 0;
v___x_163_ = lean_box(v___x_162_);
v___x_164_ = lean_apply_2(v_toPure_152_, lean_box(0), v___x_163_);
return v___x_164_;
}
}
}
}
static lean_object* _init_l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1(void){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_Array_instInhabited(lean_box(0));
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted___redArg(lean_object* v_inst_171_, lean_object* v_inst_172_, lean_object* v_linter_173_, lean_object* v_decl_174_){
_start:
{
lean_object* v_toApplicative_175_; lean_object* v_toBind_176_; lean_object* v_getEnv_177_; lean_object* v_toPure_178_; lean_object* v___x_179_; lean_object* v___x_180_; lean_object* v___f_181_; lean_object* v___x_182_; 
v_toApplicative_175_ = lean_ctor_get(v_inst_171_, 0);
lean_inc_ref(v_toApplicative_175_);
v_toBind_176_ = lean_ctor_get(v_inst_171_, 1);
lean_inc(v_toBind_176_);
lean_dec_ref(v_inst_171_);
v_getEnv_177_ = lean_ctor_get(v_inst_172_, 0);
lean_inc(v_getEnv_177_);
lean_dec_ref(v_inst_172_);
v_toPure_178_ = lean_ctor_get(v_toApplicative_175_, 1);
lean_inc(v_toPure_178_);
lean_dec_ref(v_toApplicative_175_);
v___x_179_ = ((lean_object*)(l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__0));
v___x_180_ = lean_obj_once(&l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1, &l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1_once, _init_l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___closed__1);
v___f_181_ = lean_alloc_closure((void*)(l_Lean_Linter_EnvLinter_shouldBeLinted___redArg___lam__0), 6, 5);
lean_closure_set(v___f_181_, 0, v___x_179_);
lean_closure_set(v___f_181_, 1, v_linter_173_);
lean_closure_set(v___f_181_, 2, v_toPure_178_);
lean_closure_set(v___f_181_, 3, v___x_180_);
lean_closure_set(v___f_181_, 4, v_decl_174_);
v___x_182_ = lean_apply_4(v_toBind_176_, lean_box(0), lean_box(0), v_getEnv_177_, v___f_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_EnvLinter_shouldBeLinted(lean_object* v_m_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_linter_186_, lean_object* v_decl_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Lean_Linter_EnvLinter_shouldBeLinted___redArg(v_inst_184_, v_inst_185_, v_linter_186_, v_decl_187_);
return v___x_188_;
}
}
lean_object* runtime_initialize_Lean_Attributes(uint8_t builtin);
lean_object* runtime_initialize_Init_Linter(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_EnvLinter_Nolint(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Linter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Linter_EnvLinter_Nolint_0__Lean_Linter_EnvLinter_initFn_00___x40_Lean_Linter_EnvLinter_Nolint_1926768071____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_EnvLinter_builtinNolintAttr = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_EnvLinter_builtinNolintAttr);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_EnvLinter_Nolint(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Attributes(uint8_t builtin);
lean_object* initialize_Init_Linter(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_EnvLinter_Nolint(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Attributes(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Linter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_EnvLinter_Nolint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_EnvLinter_Nolint(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_EnvLinter_Nolint(builtin);
}
#ifdef __cplusplus
}
#endif
