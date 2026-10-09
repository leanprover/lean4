// Lean compiler output
// Module: Lean.Elab.DeprecatedSyntax
// Imports: public import Lean.MonadEnv public import Lean.Linter.Init public import Lean.Elab.Util
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
lean_object* lean_array_mk(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Linter_logLintIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Syntax_getHeadInfo(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
uint8_t l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 99, 57, 49, 46, 156, 253, 187)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(214, 149, 21, 131, 183, 70, 101, 25)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "if true, generate warnings when deprecated syntax is used"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(248, 165, 85, 201, 27, 48, 185, 203)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_3),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(73, 92, 249, 154, 145, 175, 141, 131)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_deprecated_syntax;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "deprecatedSyntaxExt"};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_1),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 151, 2, 103, 84, 175, 195, 226)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 8, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_deprecatedSyntaxExt;
LEAN_EXPORT uint8_t l_Lean_Elab_isDeprecatedSyntax(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_isDeprecatedSyntax___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0(lean_object*, lean_object*);
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "macro '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__0 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__1;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__2 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__2_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__3;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " produces deprecated syntax '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__4 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__4_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__5;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "syntax '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__6 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__6_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__7;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "' has been deprecated"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__8 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__8_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__9;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "' produces deprecated syntax '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__10 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__10_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__11;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " (expanded from '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__12 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__12_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__13;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "')"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__14 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__14_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__15;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__16 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__16_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__17;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__18 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__18_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_1_ = stack[0].m_obj;
lean_object* v_decl_2_ = stack[1].m_obj;
lean_object* v_ref_3_ = stack[2].m_obj;
lean_object* v_res_29_;
v_res_29_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(v_name_1_, v_decl_2_, v_ref_3_);
stack->m_obj
 = v_res_29_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_30_, lean_object* v_decl_31_, lean_object* v_ref_32_, lean_object* v_a_33_){
_start:
{
lean_object* v_res_34_; 
v_res_34_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(v_name_30_, v_decl_31_, v_ref_32_);
lean_dec_ref(v_decl_31_);
return v_res_34_;
}
}
lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_));
v___x_60_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(v___x_57_, v___x_58_, v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_61_;
v_res_61_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
stack->m_obj
 = v_res_61_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(lean_object* v_m_64_, lean_object* v_e_65_){
_start:
{
lean_object* v_kind_66_; lean_object* v___x_67_; 
v_kind_66_ = lean_ctor_get(v_e_65_, 0);
lean_inc(v_kind_66_);
v___x_67_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_kind_66_, v_e_65_, v_m_64_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(lean_object* v_es_68_){
_start:
{
lean_object* v___x_69_; 
v___x_69_ = lean_array_mk(v_es_68_);
return v___x_69_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_70_, size_t v_i_71_, size_t v_stop_72_, lean_object* v_b_73_){
_start:
{
uint8_t v___x_74_; 
v___x_74_ = lean_usize_dec_eq(v_i_71_, v_stop_72_);
if (v___x_74_ == 0)
{
lean_object* v___x_75_; lean_object* v_kind_76_; lean_object* v___x_77_; size_t v___x_78_; size_t v___x_79_; 
v___x_75_ = lean_array_uget_borrowed(v_as_70_, v_i_71_);
v_kind_76_ = lean_ctor_get(v___x_75_, 0);
lean_inc(v___x_75_);
lean_inc(v_kind_76_);
v___x_77_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_kind_76_, v___x_75_, v_b_73_);
v___x_78_ = ((size_t)1ULL);
v___x_79_ = lean_usize_add(v_i_71_, v___x_78_);
v_i_71_ = v___x_79_;
v_b_73_ = v___x_77_;
goto _start;
}
else
{
return v_b_73_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_70_ = stack[0].m_obj;
size_t v_i_71_ = stack[1].m_num;
size_t v_stop_72_ = stack[2].m_num;
lean_object* v_b_73_ = stack[3].m_obj;
lean_object* v_res_81_;
v_res_81_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v_as_70_, v_i_71_, v_stop_72_, v_b_73_);
stack->m_obj
 = v_res_81_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_82_, lean_object* v_i_83_, lean_object* v_stop_84_, lean_object* v_b_85_){
_start:
{
size_t v_i_boxed_86_; size_t v_stop_boxed_87_; lean_object* v_res_88_; 
v_i_boxed_86_ = lean_unbox_usize(v_i_83_);
lean_dec(v_i_83_);
v_stop_boxed_87_ = lean_unbox_usize(v_stop_84_);
lean_dec(v_stop_84_);
v_res_88_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v_as_82_, v_i_boxed_86_, v_stop_boxed_87_, v_b_85_);
lean_dec_ref(v_as_82_);
return v_res_88_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_89_, size_t v_i_90_, size_t v_stop_91_, lean_object* v_b_92_){
_start:
{
lean_object* v___y_94_; uint8_t v___x_98_; 
v___x_98_ = lean_usize_dec_eq(v_i_90_, v_stop_91_);
if (v___x_98_ == 0)
{
lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; uint8_t v___x_102_; 
v___x_99_ = lean_array_uget_borrowed(v_as_89_, v_i_90_);
v___x_100_ = lean_unsigned_to_nat(0u);
v___x_101_ = lean_array_get_size(v___x_99_);
v___x_102_ = lean_nat_dec_lt(v___x_100_, v___x_101_);
if (v___x_102_ == 0)
{
v___y_94_ = v_b_92_;
goto v___jp_93_;
}
else
{
size_t v___x_103_; size_t v___x_104_; lean_object* v___x_105_; 
v___x_103_ = ((size_t)0ULL);
v___x_104_ = lean_usize_of_nat(v___x_101_);
v___x_105_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v___x_99_, v___x_103_, v___x_104_, v_b_92_);
v___y_94_ = v___x_105_;
goto v___jp_93_;
}
}
else
{
return v_b_92_;
}
v___jp_93_:
{
size_t v___x_95_; size_t v___x_96_; 
v___x_95_ = ((size_t)1ULL);
v___x_96_ = lean_usize_add(v_i_90_, v___x_95_);
v_i_90_ = v___x_96_;
v_b_92_ = v___y_94_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_89_ = stack[0].m_obj;
size_t v_i_90_ = stack[1].m_num;
size_t v_stop_91_ = stack[2].m_num;
lean_object* v_b_92_ = stack[3].m_obj;
lean_object* v_res_106_;
v_res_106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_89_, v_i_90_, v_stop_91_, v_b_92_);
stack->m_obj
 = v_res_106_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_107_, lean_object* v_i_108_, lean_object* v_stop_109_, lean_object* v_b_110_){
_start:
{
size_t v_i_boxed_111_; size_t v_stop_boxed_112_; lean_object* v_res_113_; 
v_i_boxed_111_ = lean_unbox_usize(v_i_108_);
lean_dec(v_i_108_);
v_stop_boxed_112_ = lean_unbox_usize(v_stop_109_);
lean_dec(v_stop_109_);
v_res_113_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_107_, v_i_boxed_111_, v_stop_boxed_112_, v_b_110_);
lean_dec_ref(v_as_107_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0(lean_object* v_initState_114_, lean_object* v_as_115_){
_start:
{
lean_object* v___x_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v___x_116_ = lean_unsigned_to_nat(0u);
v___x_117_ = lean_array_get_size(v_as_115_);
v___x_118_ = lean_nat_dec_lt(v___x_116_, v___x_117_);
if (v___x_118_ == 0)
{
return v_initState_114_;
}
else
{
size_t v___x_119_; size_t v___x_120_; lean_object* v___x_121_; 
v___x_119_ = ((size_t)0ULL);
v___x_120_ = lean_usize_of_nat(v___x_117_);
v___x_121_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_115_, v___x_119_, v___x_120_, v_initState_114_);
return v___x_121_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_122_, lean_object* v_as_123_){
_start:
{
lean_object* v_res_124_; 
v_res_124_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0(v_initState_122_, v_as_123_);
lean_dec_ref(v_as_123_);
return v_res_124_;
}
}
lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_144_; lean_object* v___x_145_; 
v___x_144_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_));
v___x_145_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_144_);
return v___x_145_;
}
}
LEAN_EXPORT void l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_146_;
v_res_146_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
stack->m_obj
 = v_res_146_;
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2____boxed(lean_object* v_a_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
return v_res_148_;
}
}
uint8_t l_Lean_Elab_isDeprecatedSyntax(lean_object* v_env_149_, lean_object* v_kind_150_){
_start:
{
lean_object* v___x_151_; lean_object* v_toEnvExtension_152_; lean_object* v_asyncMode_153_; lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; uint8_t v___x_157_; 
v___x_151_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_152_ = lean_ctor_get(v___x_151_, 0);
v_asyncMode_153_ = lean_ctor_get(v_toEnvExtension_152_, 2);
v___x_154_ = lean_box(1);
v___x_155_ = lean_box(0);
v___x_156_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_154_, v___x_151_, v_env_149_, v_asyncMode_153_, v___x_155_);
v___x_157_ = l_Std_DTreeMap_Internal_Impl_contains___at___00Lean_NameMap_contains_spec__0___redArg(v_kind_150_, v___x_156_);
lean_dec(v___x_156_);
return v___x_157_;
}
}
LEAN_EXPORT void l_Lean_Elab_isDeprecatedSyntax_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_149_ = stack[0].m_obj;
lean_object* v_kind_150_ = stack[1].m_obj;
uint8_t v_res_158_;
v_res_158_ = l_Lean_Elab_isDeprecatedSyntax(v_env_149_, v_kind_150_);
stack->m_num = v_res_158_;
}
LEAN_EXPORT lean_object* l_Lean_Elab_isDeprecatedSyntax___boxed(lean_object* v_env_159_, lean_object* v_kind_160_){
_start:
{
uint8_t v_res_161_; lean_object* v_r_162_; 
v_res_161_ = l_Lean_Elab_isDeprecatedSyntax(v_env_159_, v_kind_160_);
lean_dec(v_kind_160_);
v_r_162_ = lean_box(v_res_161_);
return v_r_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0(lean_object* v_toPure_163_, lean_object* v_____r_164_){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = lean_box(0);
v___x_166_ = lean_apply_2(v_toPure_163_, lean_box(0), v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__1(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__0));
v___x_169_ = l_Lean_stringToMessageData(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__3(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__2));
v___x_172_ = l_Lean_stringToMessageData(v___x_171_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__5(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__4));
v___x_175_ = l_Lean_stringToMessageData(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__7(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__6));
v___x_178_ = l_Lean_stringToMessageData(v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__9(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__8));
v___x_181_ = l_Lean_stringToMessageData(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__11(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__10));
v___x_184_ = l_Lean_stringToMessageData(v___x_183_);
return v___x_184_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__13(void){
_start:
{
lean_object* v___x_186_; lean_object* v___x_187_; 
v___x_186_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__12));
v___x_187_ = l_Lean_stringToMessageData(v___x_186_);
return v___x_187_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__15(void){
_start:
{
lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_189_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__14));
v___x_190_ = l_Lean_stringToMessageData(v___x_189_);
return v___x_190_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__17(void){
_start:
{
lean_object* v___x_192_; lean_object* v___x_193_; 
v___x_192_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__16));
v___x_193_ = l_Lean_stringToMessageData(v___x_192_);
return v___x_193_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__19(void){
_start:
{
lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_195_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__18));
v___x_196_ = l_Lean_stringToMessageData(v___x_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1(lean_object* v_stx_197_, lean_object* v___x_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_toBind_204_, lean_object* v___f_205_, lean_object* v_macroStack_206_, lean_object* v_toPure_207_, lean_object* v_env_208_){
_start:
{
lean_object* v___x_209_; lean_object* v_toEnvExtension_210_; lean_object* v_asyncMode_211_; lean_object* v_kind_212_; lean_object* v___y_214_; lean_object* v___y_215_; lean_object* v___y_216_; lean_object* v___y_217_; lean_object* v___y_233_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; 
v___x_209_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_210_ = lean_ctor_get(v___x_209_, 0);
v_asyncMode_211_ = lean_ctor_get(v_toEnvExtension_210_, 2);
lean_inc(v_stx_197_);
v_kind_212_ = l_Lean_Syntax_getKind(v_stx_197_);
v___x_307_ = lean_box(0);
v___x_308_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_198_, v___x_209_, v_env_208_, v_asyncMode_211_, v___x_307_);
v___x_309_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_308_, v_kind_212_);
lean_dec(v___x_308_);
if (lean_obj_tag(v___x_309_) == 1)
{
lean_object* v_val_310_; lean_object* v_text_x3f_311_; 
lean_dec(v_toPure_207_);
v_val_310_ = lean_ctor_get(v___x_309_, 0);
lean_inc(v_val_310_);
lean_dec_ref_known(v___x_309_, 1);
v_text_x3f_311_ = lean_ctor_get(v_val_310_, 1);
lean_inc(v_text_x3f_311_);
lean_dec(v_val_310_);
if (lean_obj_tag(v_text_x3f_311_) == 0)
{
lean_object* v___x_312_; 
v___x_312_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__17, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__17_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__17);
v___y_233_ = v___x_312_;
goto v___jp_232_;
}
else
{
lean_object* v_val_313_; lean_object* v___x_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
v_val_313_ = lean_ctor_get(v_text_x3f_311_, 0);
lean_inc(v_val_313_);
lean_dec_ref_known(v_text_x3f_311_, 1);
v___x_314_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__19, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__19_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__19);
v___x_315_ = l_Lean_stringToMessageData(v_val_313_);
v___x_316_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_316_, 0, v___x_314_);
lean_ctor_set(v___x_316_, 1, v___x_315_);
v___y_233_ = v___x_316_;
goto v___jp_232_;
}
}
else
{
lean_object* v___x_317_; lean_object* v___x_318_; 
lean_dec(v___x_309_);
lean_dec(v_kind_212_);
lean_dec(v_macroStack_206_);
lean_dec(v___f_205_);
lean_dec(v_toBind_204_);
lean_dec_ref(v_inst_203_);
lean_dec_ref(v_inst_202_);
lean_dec(v_inst_201_);
lean_dec_ref(v_inst_200_);
lean_dec_ref(v_inst_199_);
lean_dec(v_stx_197_);
v___x_317_ = lean_box(0);
v___x_318_ = lean_apply_2(v_toPure_207_, lean_box(0), v___x_317_);
return v___x_318_;
}
v___jp_213_:
{
lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_228_; lean_object* v___x_229_; lean_object* v___x_230_; lean_object* v___x_231_; 
v___x_218_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_219_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__1);
v___x_220_ = l_Lean_MessageData_ofName(v___y_216_);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__3);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_224_, 0, v___x_223_);
lean_ctor_set(v___x_224_, 1, v___y_217_);
v___x_225_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__5, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__5_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__5);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_224_);
lean_ctor_set(v___x_226_, 1, v___x_225_);
v___x_227_ = l_Lean_MessageData_ofName(v_kind_212_);
v___x_228_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_228_, 0, v___x_226_);
lean_ctor_set(v___x_228_, 1, v___x_227_);
v___x_229_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_229_, 0, v___x_228_);
lean_ctor_set(v___x_229_, 1, v___x_222_);
v___x_230_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_230_, 0, v___x_229_);
lean_ctor_set(v___x_230_, 1, v___y_215_);
v___x_231_ = l_Lean_Linter_logLintIf___redArg(v_inst_199_, v_inst_200_, v_inst_201_, v_inst_202_, v_inst_203_, v___x_218_, v___y_214_, v___x_230_);
return v___x_231_;
}
v___jp_232_:
{
lean_object* v___x_234_; 
v___x_234_ = l_Lean_Syntax_getHeadInfo(v_stx_197_);
if (lean_obj_tag(v___x_234_) == 0)
{
lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec_ref_known(v___x_234_, 4);
lean_dec(v_macroStack_206_);
v___x_235_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_236_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__7, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__7_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__7);
v___x_237_ = l_Lean_MessageData_ofName(v_kind_212_);
v___x_238_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_238_, 0, v___x_236_);
lean_ctor_set(v___x_238_, 1, v___x_237_);
v___x_239_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__9);
v___x_240_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_240_, 0, v___x_238_);
lean_ctor_set(v___x_240_, 1, v___x_239_);
v___x_241_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_241_, 0, v___x_240_);
lean_ctor_set(v___x_241_, 1, v___y_233_);
v___x_242_ = l_Lean_Linter_logLintIf___redArg(v_inst_199_, v_inst_200_, v_inst_201_, v_inst_202_, v_inst_203_, v___x_235_, v_stx_197_, v___x_241_);
v___x_243_ = lean_apply_4(v_toBind_204_, lean_box(0), lean_box(0), v___x_242_, v___f_205_);
return v___x_243_;
}
else
{
lean_dec(v___x_234_);
lean_dec(v___f_205_);
lean_dec(v_toBind_204_);
if (lean_obj_tag(v_macroStack_206_) == 0)
{
lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_244_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_245_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__7, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__7_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__7);
v___x_246_ = l_Lean_MessageData_ofName(v_kind_212_);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__9);
v___x_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___y_233_);
v___x_251_ = l_Lean_Linter_logLintIf___redArg(v_inst_199_, v_inst_200_, v_inst_201_, v_inst_202_, v_inst_203_, v___x_244_, v_stx_197_, v___x_250_);
return v___x_251_;
}
else
{
lean_object* v_head_252_; lean_object* v_tail_253_; lean_object* v___x_255_; uint8_t v_isShared_256_; uint8_t v_isSharedCheck_306_; 
lean_dec(v_stx_197_);
v_head_252_ = lean_ctor_get(v_macroStack_206_, 0);
v_tail_253_ = lean_ctor_get(v_macroStack_206_, 1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_macroStack_206_);
if (v_isSharedCheck_306_ == 0)
{
v___x_255_ = v_macroStack_206_;
v_isShared_256_ = v_isSharedCheck_306_;
goto v_resetjp_254_;
}
else
{
lean_inc(v_tail_253_);
lean_inc(v_head_252_);
lean_dec(v_macroStack_206_);
v___x_255_ = lean_box(0);
v_isShared_256_ = v_isSharedCheck_306_;
goto v_resetjp_254_;
}
v_resetjp_254_:
{
if (lean_obj_tag(v_tail_253_) == 0)
{
lean_object* v_before_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_278_; 
v_before_257_ = lean_ctor_get(v_head_252_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_head_252_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v_head_252_, 1);
lean_dec(v_unused_279_);
v___x_259_ = v_head_252_;
v_isShared_260_ = v_isSharedCheck_278_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_before_257_);
lean_dec(v_head_252_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_278_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_266_; 
v___x_261_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_262_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__1);
lean_inc(v_before_257_);
v___x_263_ = l_Lean_Syntax_getKind(v_before_257_);
v___x_264_ = l_Lean_MessageData_ofName(v___x_263_);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 7);
lean_ctor_set(v___x_259_, 1, v___x_264_);
lean_ctor_set(v___x_259_, 0, v___x_262_);
v___x_266_ = v___x_259_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_277_; 
v_reuseFailAlloc_277_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_277_, 0, v___x_262_);
lean_ctor_set(v_reuseFailAlloc_277_, 1, v___x_264_);
v___x_266_ = v_reuseFailAlloc_277_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
lean_object* v___x_267_; lean_object* v___x_269_; 
v___x_267_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__11, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__11_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__11);
if (v_isShared_256_ == 0)
{
lean_ctor_set_tag(v___x_255_, 7);
lean_ctor_set(v___x_255_, 1, v___x_267_);
lean_ctor_set(v___x_255_, 0, v___x_266_);
v___x_269_ = v___x_255_;
goto v_reusejp_268_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_267_);
v___x_269_ = v_reuseFailAlloc_276_;
goto v_reusejp_268_;
}
v_reusejp_268_:
{
lean_object* v___x_270_; lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_270_ = l_Lean_MessageData_ofName(v_kind_212_);
v___x_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_271_, 0, v___x_269_);
lean_ctor_set(v___x_271_, 1, v___x_270_);
v___x_272_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__3);
v___x_273_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_271_);
lean_ctor_set(v___x_273_, 1, v___x_272_);
v___x_274_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_274_, 0, v___x_273_);
lean_ctor_set(v___x_274_, 1, v___y_233_);
v___x_275_ = l_Lean_Linter_logLintIf___redArg(v_inst_199_, v_inst_200_, v_inst_201_, v_inst_202_, v_inst_203_, v___x_261_, v_before_257_, v___x_274_);
return v___x_275_;
}
}
}
}
else
{
lean_object* v_head_280_; lean_object* v___x_282_; uint8_t v_isShared_283_; uint8_t v_isSharedCheck_304_; 
lean_del_object(v___x_255_);
v_head_280_ = lean_ctor_get(v_tail_253_, 0);
v_isSharedCheck_304_ = !lean_is_exclusive(v_tail_253_);
if (v_isSharedCheck_304_ == 0)
{
lean_object* v_unused_305_; 
v_unused_305_ = lean_ctor_get(v_tail_253_, 1);
lean_dec(v_unused_305_);
v___x_282_ = v_tail_253_;
v_isShared_283_ = v_isSharedCheck_304_;
goto v_resetjp_281_;
}
else
{
lean_inc(v_head_280_);
lean_dec(v_tail_253_);
v___x_282_ = lean_box(0);
v_isShared_283_ = v_isSharedCheck_304_;
goto v_resetjp_281_;
}
v_resetjp_281_:
{
lean_object* v_before_284_; lean_object* v_before_285_; lean_object* v___x_287_; uint8_t v_isShared_288_; uint8_t v_isSharedCheck_302_; 
v_before_284_ = lean_ctor_get(v_head_252_, 0);
lean_inc(v_before_284_);
lean_dec(v_head_252_);
v_before_285_ = lean_ctor_get(v_head_280_, 0);
v_isSharedCheck_302_ = !lean_is_exclusive(v_head_280_);
if (v_isSharedCheck_302_ == 0)
{
lean_object* v_unused_303_; 
v_unused_303_ = lean_ctor_get(v_head_280_, 1);
lean_dec(v_unused_303_);
v___x_287_ = v_head_280_;
v_isShared_288_ = v_isSharedCheck_302_;
goto v_resetjp_286_;
}
else
{
lean_inc(v_before_285_);
lean_dec(v_head_280_);
v___x_287_ = lean_box(0);
v_isShared_288_ = v_isSharedCheck_302_;
goto v_resetjp_286_;
}
v_resetjp_286_:
{
lean_object* v___x_289_; lean_object* v___x_290_; uint8_t v___x_291_; 
v___x_289_ = l_Lean_Syntax_getKind(v_before_285_);
lean_inc(v_before_284_);
v___x_290_ = l_Lean_Syntax_getKind(v_before_284_);
v___x_291_ = lean_name_eq(v___x_289_, v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v___x_292_; lean_object* v___x_293_; lean_object* v___x_295_; 
v___x_292_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__13, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__13_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__13);
v___x_293_ = l_Lean_MessageData_ofName(v___x_289_);
if (v_isShared_288_ == 0)
{
lean_ctor_set_tag(v___x_287_, 7);
lean_ctor_set(v___x_287_, 1, v___x_293_);
lean_ctor_set(v___x_287_, 0, v___x_292_);
v___x_295_ = v___x_287_;
goto v_reusejp_294_;
}
else
{
lean_object* v_reuseFailAlloc_300_; 
v_reuseFailAlloc_300_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_300_, 0, v___x_292_);
lean_ctor_set(v_reuseFailAlloc_300_, 1, v___x_293_);
v___x_295_ = v_reuseFailAlloc_300_;
goto v_reusejp_294_;
}
v_reusejp_294_:
{
lean_object* v___x_296_; lean_object* v___x_298_; 
v___x_296_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__15, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__15_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__15);
if (v_isShared_283_ == 0)
{
lean_ctor_set_tag(v___x_282_, 7);
lean_ctor_set(v___x_282_, 1, v___x_296_);
lean_ctor_set(v___x_282_, 0, v___x_295_);
v___x_298_ = v___x_282_;
goto v_reusejp_297_;
}
else
{
lean_object* v_reuseFailAlloc_299_; 
v_reuseFailAlloc_299_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_299_, 0, v___x_295_);
lean_ctor_set(v_reuseFailAlloc_299_, 1, v___x_296_);
v___x_298_ = v_reuseFailAlloc_299_;
goto v_reusejp_297_;
}
v_reusejp_297_:
{
v___y_214_ = v_before_284_;
v___y_215_ = v___y_233_;
v___y_216_ = v___x_290_;
v___y_217_ = v___x_298_;
goto v___jp_213_;
}
}
}
else
{
lean_object* v___x_301_; 
lean_dec(v___x_289_);
lean_del_object(v___x_287_);
lean_del_object(v___x_282_);
v___x_301_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__17, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__17_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1___closed__17);
v___y_214_ = v_before_284_;
v___y_215_ = v___y_233_;
v___y_216_ = v___x_290_;
v___y_217_ = v___x_301_;
goto v___jp_213_;
}
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg(lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_stx_324_, lean_object* v_macroStack_325_){
_start:
{
lean_object* v_toApplicative_326_; lean_object* v_toBind_327_; lean_object* v_getEnv_328_; lean_object* v_toPure_329_; lean_object* v___x_330_; lean_object* v___f_331_; lean_object* v___f_332_; lean_object* v___x_333_; 
v_toApplicative_326_ = lean_ctor_get(v_inst_319_, 0);
v_toBind_327_ = lean_ctor_get(v_inst_319_, 1);
lean_inc_n(v_toBind_327_, 2);
v_getEnv_328_ = lean_ctor_get(v_inst_320_, 0);
lean_inc(v_getEnv_328_);
v_toPure_329_ = lean_ctor_get(v_toApplicative_326_, 1);
lean_inc_n(v_toPure_329_, 2);
v___x_330_ = lean_box(1);
v___f_331_ = lean_alloc_closure((void*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0), 2, 1);
lean_closure_set(v___f_331_, 0, v_toPure_329_);
v___f_332_ = lean_alloc_closure((void*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__1), 12, 11);
lean_closure_set(v___f_332_, 0, v_stx_324_);
lean_closure_set(v___f_332_, 1, v___x_330_);
lean_closure_set(v___f_332_, 2, v_inst_319_);
lean_closure_set(v___f_332_, 3, v_inst_321_);
lean_closure_set(v___f_332_, 4, v_inst_323_);
lean_closure_set(v___f_332_, 5, v_inst_322_);
lean_closure_set(v___f_332_, 6, v_inst_320_);
lean_closure_set(v___f_332_, 7, v_toBind_327_);
lean_closure_set(v___f_332_, 8, v___f_331_);
lean_closure_set(v___f_332_, 9, v_macroStack_325_);
lean_closure_set(v___f_332_, 10, v_toPure_329_);
v___x_333_ = lean_apply_4(v_toBind_327_, lean_box(0), lean_box(0), v_getEnv_328_, v___f_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax(lean_object* v_m_334_, lean_object* v_inst_335_, lean_object* v_inst_336_, lean_object* v_inst_337_, lean_object* v_inst_338_, lean_object* v_inst_339_, lean_object* v_inst_340_, lean_object* v_stx_341_, lean_object* v_macroStack_342_){
_start:
{
lean_object* v___x_343_; 
v___x_343_ = l_Lean_Elab_checkDeprecatedSyntax___redArg(v_inst_335_, v_inst_336_, v_inst_337_, v_inst_338_, v_inst_339_, v_stx_341_, v_macroStack_342_);
return v___x_343_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___boxed(lean_object* v_m_344_, lean_object* v_inst_345_, lean_object* v_inst_346_, lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_inst_350_, lean_object* v_stx_351_, lean_object* v_macroStack_352_){
_start:
{
lean_object* v_res_353_; 
v_res_353_ = l_Lean_Elab_checkDeprecatedSyntax(v_m_344_, v_inst_345_, v_inst_346_, v_inst_347_, v_inst_348_, v_inst_349_, v_inst_350_, v_stx_351_, v_macroStack_352_);
lean_dec_ref(v_inst_350_);
return v_res_353_;
}
}
lean_object* runtime_initialize_Lean_MonadEnv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeprecatedSyntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_deprecated_syntax = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_deprecated_syntax);
lean_dec_ref(res);
res = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Elab_deprecatedSyntaxExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Elab_deprecatedSyntaxExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Elab_DeprecatedSyntax(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_MonadEnv(uint8_t builtin);
lean_object* initialize_Lean_Linter_Init(uint8_t builtin);
lean_object* initialize_Lean_Elab_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeprecatedSyntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Init(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Elab_Util(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Elab_DeprecatedSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Elab_DeprecatedSyntax(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Elab_DeprecatedSyntax(builtin);
}
#ifdef __cplusplus
}
#endif
