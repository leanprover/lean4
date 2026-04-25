// Lean compiler output
// Module: Lean.Elab.DeprecatedSyntax
// Imports: public import Lean.MonadEnv public import Lean.Linter.Basic public import Lean.Elab.Util
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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Linter_logLintIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
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
static const lean_ctor_object l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_deprecatedSyntaxExt;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "macro '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "'"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 30, .m_capacity = 30, .m_length = 29, .m_data = " produces deprecated syntax '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "syntax '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 22, .m_capacity = 22, .m_length = 21, .m_data = "' has been deprecated"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 31, .m_capacity = 31, .m_length = 30, .m_data = "' produces deprecated syntax '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 18, .m_capacity = 18, .m_length = 17, .m_data = " (expanded from '"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "')"};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17;
static const lean_string_object l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = ": "};
static const lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18 = (const lean_object*)&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18_value;
static lean_once_cell_t l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19;
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_29_, lean_object* v_decl_30_, lean_object* v_ref_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(v_name_29_, v_decl_30_, v_ref_31_);
lean_dec_ref(v_decl_30_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; 
v___x_56_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_));
v___x_57_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_));
v___x_58_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_));
v___x_59_ = l_Lean_Option_register___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(v___x_56_, v___x_57_, v___x_58_);
return v___x_59_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4____boxed(lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(lean_object* v_m_62_, lean_object* v_e_63_){
_start:
{
lean_object* v_kind_64_; lean_object* v___x_65_; 
v_kind_64_ = lean_ctor_get(v_e_63_, 0);
lean_inc(v_kind_64_);
v___x_65_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_kind_64_, v_e_63_, v_m_62_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(lean_object* v_es_66_){
_start:
{
lean_object* v___x_67_; 
v___x_67_ = lean_array_mk(v_es_66_);
return v___x_67_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_68_, size_t v_i_69_, size_t v_stop_70_, lean_object* v_b_71_){
_start:
{
uint8_t v___x_72_; 
v___x_72_ = lean_usize_dec_eq(v_i_69_, v_stop_70_);
if (v___x_72_ == 0)
{
lean_object* v___x_73_; lean_object* v_kind_74_; lean_object* v___x_75_; size_t v___x_76_; size_t v___x_77_; 
v___x_73_ = lean_array_uget_borrowed(v_as_68_, v_i_69_);
v_kind_74_ = lean_ctor_get(v___x_73_, 0);
lean_inc(v___x_73_);
lean_inc(v_kind_74_);
v___x_75_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_kind_74_, v___x_73_, v_b_71_);
v___x_76_ = ((size_t)1ULL);
v___x_77_ = lean_usize_add(v_i_69_, v___x_76_);
v_i_69_ = v___x_77_;
v_b_71_ = v___x_75_;
goto _start;
}
else
{
return v_b_71_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_79_, lean_object* v_i_80_, lean_object* v_stop_81_, lean_object* v_b_82_){
_start:
{
size_t v_i_boxed_83_; size_t v_stop_boxed_84_; lean_object* v_res_85_; 
v_i_boxed_83_ = lean_unbox_usize(v_i_80_);
lean_dec(v_i_80_);
v_stop_boxed_84_ = lean_unbox_usize(v_stop_81_);
lean_dec(v_stop_81_);
v_res_85_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v_as_79_, v_i_boxed_83_, v_stop_boxed_84_, v_b_82_);
lean_dec_ref(v_as_79_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_86_, size_t v_i_87_, size_t v_stop_88_, lean_object* v_b_89_){
_start:
{
lean_object* v___y_91_; uint8_t v___x_95_; 
v___x_95_ = lean_usize_dec_eq(v_i_87_, v_stop_88_);
if (v___x_95_ == 0)
{
lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; uint8_t v___x_99_; 
v___x_96_ = lean_array_uget_borrowed(v_as_86_, v_i_87_);
v___x_97_ = lean_unsigned_to_nat(0u);
v___x_98_ = lean_array_get_size(v___x_96_);
v___x_99_ = lean_nat_dec_lt(v___x_97_, v___x_98_);
if (v___x_99_ == 0)
{
v___y_91_ = v_b_89_;
goto v___jp_90_;
}
else
{
uint8_t v___x_100_; 
v___x_100_ = lean_nat_dec_le(v___x_98_, v___x_98_);
if (v___x_100_ == 0)
{
if (v___x_99_ == 0)
{
v___y_91_ = v_b_89_;
goto v___jp_90_;
}
else
{
size_t v___x_101_; size_t v___x_102_; lean_object* v___x_103_; 
v___x_101_ = ((size_t)0ULL);
v___x_102_ = lean_usize_of_nat(v___x_98_);
v___x_103_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v___x_96_, v___x_101_, v___x_102_, v_b_89_);
v___y_91_ = v___x_103_;
goto v___jp_90_;
}
}
else
{
size_t v___x_104_; size_t v___x_105_; lean_object* v___x_106_; 
v___x_104_ = ((size_t)0ULL);
v___x_105_ = lean_usize_of_nat(v___x_98_);
v___x_106_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v___x_96_, v___x_104_, v___x_105_, v_b_89_);
v___y_91_ = v___x_106_;
goto v___jp_90_;
}
}
}
else
{
return v_b_89_;
}
v___jp_90_:
{
size_t v___x_92_; size_t v___x_93_; 
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_add(v_i_87_, v___x_92_);
v_i_87_ = v___x_93_;
v_b_89_ = v___y_91_;
goto _start;
}
}
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
uint8_t v___x_119_; 
v___x_119_ = lean_nat_dec_le(v___x_117_, v___x_117_);
if (v___x_119_ == 0)
{
if (v___x_118_ == 0)
{
return v_initState_114_;
}
else
{
size_t v___x_120_; size_t v___x_121_; lean_object* v___x_122_; 
v___x_120_ = ((size_t)0ULL);
v___x_121_ = lean_usize_of_nat(v___x_117_);
v___x_122_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_115_, v___x_120_, v___x_121_, v_initState_114_);
return v___x_122_;
}
}
else
{
size_t v___x_123_; size_t v___x_124_; lean_object* v___x_125_; 
v___x_123_ = ((size_t)0ULL);
v___x_124_ = lean_usize_of_nat(v___x_117_);
v___x_125_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_115_, v___x_123_, v___x_124_, v_initState_114_);
return v___x_125_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_126_, lean_object* v_as_127_){
_start:
{
lean_object* v_res_128_; 
v_res_128_ = l_Lean_mkStateFromImportedEntries___at___00__private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0(v_initState_126_, v_as_127_);
lean_dec_ref(v_as_127_);
return v_res_128_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = ((lean_object*)(l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_));
v___x_148_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2____boxed(lean_object* v_a_149_){
_start:
{
lean_object* v_res_150_; 
v_res_150_ = l___private_Lean_Elab_DeprecatedSyntax_0__Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
return v_res_150_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_152_; lean_object* v___x_153_; 
v___x_152_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0));
v___x_153_ = l_Lean_stringToMessageData(v___x_152_);
return v___x_153_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; 
v___x_155_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2));
v___x_156_ = l_Lean_stringToMessageData(v___x_155_);
return v___x_156_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_158_; lean_object* v___x_159_; 
v___x_158_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4));
v___x_159_ = l_Lean_stringToMessageData(v___x_158_);
return v___x_159_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_161_; lean_object* v___x_162_; 
v___x_161_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6));
v___x_162_ = l_Lean_stringToMessageData(v___x_161_);
return v___x_162_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8));
v___x_165_ = l_Lean_stringToMessageData(v___x_164_);
return v___x_165_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_167_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10));
v___x_168_ = l_Lean_stringToMessageData(v___x_167_);
return v___x_168_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_170_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12));
v___x_171_ = l_Lean_stringToMessageData(v___x_170_);
return v___x_171_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_173_; lean_object* v___x_174_; 
v___x_173_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14));
v___x_174_ = l_Lean_stringToMessageData(v___x_173_);
return v___x_174_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17(void){
_start:
{
lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_176_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16));
v___x_177_ = l_Lean_stringToMessageData(v___x_176_);
return v___x_177_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19(void){
_start:
{
lean_object* v___x_179_; lean_object* v___x_180_; 
v___x_179_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18));
v___x_180_ = l_Lean_stringToMessageData(v___x_179_);
return v___x_180_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0(lean_object* v_stx_181_, lean_object* v___x_182_, lean_object* v_inst_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_macroStack_188_, lean_object* v_toPure_189_, lean_object* v_env_190_){
_start:
{
lean_object* v___x_191_; lean_object* v_toEnvExtension_192_; lean_object* v_asyncMode_193_; lean_object* v_kind_194_; lean_object* v___y_196_; lean_object* v___y_197_; lean_object* v___y_198_; lean_object* v___y_199_; lean_object* v___y_215_; lean_object* v___x_279_; lean_object* v___x_280_; lean_object* v___x_281_; 
v___x_191_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_192_ = lean_ctor_get(v___x_191_, 0);
v_asyncMode_193_ = lean_ctor_get(v_toEnvExtension_192_, 2);
lean_inc(v_stx_181_);
v_kind_194_ = l_Lean_Syntax_getKind(v_stx_181_);
v___x_279_ = lean_box(0);
v___x_280_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_182_, v___x_191_, v_env_190_, v_asyncMode_193_, v___x_279_);
v___x_281_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_280_, v_kind_194_);
lean_dec(v___x_280_);
if (lean_obj_tag(v___x_281_) == 1)
{
lean_object* v_val_282_; lean_object* v_text_x3f_283_; 
lean_dec(v_toPure_189_);
v_val_282_ = lean_ctor_get(v___x_281_, 0);
lean_inc(v_val_282_);
lean_dec_ref(v___x_281_);
v_text_x3f_283_ = lean_ctor_get(v_val_282_, 1);
lean_inc(v_text_x3f_283_);
lean_dec(v_val_282_);
if (lean_obj_tag(v_text_x3f_283_) == 0)
{
lean_object* v___x_284_; 
v___x_284_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17);
v___y_215_ = v___x_284_;
goto v___jp_214_;
}
else
{
lean_object* v_val_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; 
v_val_285_ = lean_ctor_get(v_text_x3f_283_, 0);
lean_inc(v_val_285_);
lean_dec_ref(v_text_x3f_283_);
v___x_286_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19);
v___x_287_ = l_Lean_stringToMessageData(v_val_285_);
v___x_288_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_288_, 0, v___x_286_);
lean_ctor_set(v___x_288_, 1, v___x_287_);
v___y_215_ = v___x_288_;
goto v___jp_214_;
}
}
else
{
lean_object* v___x_289_; lean_object* v___x_290_; 
lean_dec(v___x_281_);
lean_dec(v_kind_194_);
lean_dec(v_macroStack_188_);
lean_dec_ref(v_inst_187_);
lean_dec(v_inst_186_);
lean_dec(v_inst_185_);
lean_dec_ref(v_inst_184_);
lean_dec_ref(v_inst_183_);
lean_dec(v_stx_181_);
v___x_289_ = lean_box(0);
v___x_290_ = lean_apply_2(v_toPure_189_, lean_box(0), v___x_289_);
return v___x_290_;
}
v___jp_195_:
{
lean_object* v___x_200_; lean_object* v___x_201_; lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; 
v___x_200_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_201_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1);
v___x_202_ = l_Lean_MessageData_ofName(v___y_198_);
v___x_203_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_203_, 0, v___x_201_);
lean_ctor_set(v___x_203_, 1, v___x_202_);
v___x_204_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3);
v___x_205_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_205_, 0, v___x_203_);
lean_ctor_set(v___x_205_, 1, v___x_204_);
v___x_206_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_206_, 0, v___x_205_);
lean_ctor_set(v___x_206_, 1, v___y_199_);
v___x_207_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5);
v___x_208_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_208_, 0, v___x_206_);
lean_ctor_set(v___x_208_, 1, v___x_207_);
v___x_209_ = l_Lean_MessageData_ofName(v_kind_194_);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_208_);
lean_ctor_set(v___x_210_, 1, v___x_209_);
v___x_211_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_211_, 0, v___x_210_);
lean_ctor_set(v___x_211_, 1, v___x_204_);
v___x_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_211_);
lean_ctor_set(v___x_212_, 1, v___y_196_);
v___x_213_ = l_Lean_Linter_logLintIf___redArg(v_inst_183_, v_inst_184_, v_inst_185_, v_inst_186_, v_inst_187_, v___x_200_, v___y_197_, v___x_212_);
return v___x_213_;
}
v___jp_214_:
{
if (lean_obj_tag(v_macroStack_188_) == 0)
{
lean_object* v___x_216_; lean_object* v___x_217_; lean_object* v___x_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_216_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_217_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7);
v___x_218_ = l_Lean_MessageData_ofName(v_kind_194_);
v___x_219_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_219_, 0, v___x_217_);
lean_ctor_set(v___x_219_, 1, v___x_218_);
v___x_220_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9);
v___x_221_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_221_, 0, v___x_219_);
lean_ctor_set(v___x_221_, 1, v___x_220_);
v___x_222_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_222_, 0, v___x_221_);
lean_ctor_set(v___x_222_, 1, v___y_215_);
v___x_223_ = l_Lean_Linter_logLintIf___redArg(v_inst_183_, v_inst_184_, v_inst_185_, v_inst_186_, v_inst_187_, v___x_216_, v_stx_181_, v___x_222_);
return v___x_223_;
}
else
{
lean_object* v_head_224_; lean_object* v_tail_225_; lean_object* v___x_227_; uint8_t v_isShared_228_; uint8_t v_isSharedCheck_278_; 
lean_dec(v_stx_181_);
v_head_224_ = lean_ctor_get(v_macroStack_188_, 0);
v_tail_225_ = lean_ctor_get(v_macroStack_188_, 1);
v_isSharedCheck_278_ = !lean_is_exclusive(v_macroStack_188_);
if (v_isSharedCheck_278_ == 0)
{
v___x_227_ = v_macroStack_188_;
v_isShared_228_ = v_isSharedCheck_278_;
goto v_resetjp_226_;
}
else
{
lean_inc(v_tail_225_);
lean_inc(v_head_224_);
lean_dec(v_macroStack_188_);
v___x_227_ = lean_box(0);
v_isShared_228_ = v_isSharedCheck_278_;
goto v_resetjp_226_;
}
v_resetjp_226_:
{
if (lean_obj_tag(v_tail_225_) == 0)
{
lean_object* v_before_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_250_; 
v_before_229_ = lean_ctor_get(v_head_224_, 0);
v_isSharedCheck_250_ = !lean_is_exclusive(v_head_224_);
if (v_isSharedCheck_250_ == 0)
{
lean_object* v_unused_251_; 
v_unused_251_ = lean_ctor_get(v_head_224_, 1);
lean_dec(v_unused_251_);
v___x_231_ = v_head_224_;
v_isShared_232_ = v_isSharedCheck_250_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_before_229_);
lean_dec(v_head_224_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_250_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
lean_object* v___x_233_; lean_object* v___x_234_; lean_object* v___x_235_; lean_object* v___x_236_; lean_object* v___x_238_; 
v___x_233_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_234_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1);
lean_inc(v_before_229_);
v___x_235_ = l_Lean_Syntax_getKind(v_before_229_);
v___x_236_ = l_Lean_MessageData_ofName(v___x_235_);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 7);
lean_ctor_set(v___x_231_, 1, v___x_236_);
lean_ctor_set(v___x_231_, 0, v___x_234_);
v___x_238_ = v___x_231_;
goto v_reusejp_237_;
}
else
{
lean_object* v_reuseFailAlloc_249_; 
v_reuseFailAlloc_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_249_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_249_, 1, v___x_236_);
v___x_238_ = v_reuseFailAlloc_249_;
goto v_reusejp_237_;
}
v_reusejp_237_:
{
lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_239_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11);
if (v_isShared_228_ == 0)
{
lean_ctor_set_tag(v___x_227_, 7);
lean_ctor_set(v___x_227_, 1, v___x_239_);
lean_ctor_set(v___x_227_, 0, v___x_238_);
v___x_241_ = v___x_227_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_248_; 
v_reuseFailAlloc_248_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_248_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_248_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_248_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; lean_object* v___x_247_; 
v___x_242_ = l_Lean_MessageData_ofName(v_kind_194_);
v___x_243_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_243_, 0, v___x_241_);
lean_ctor_set(v___x_243_, 1, v___x_242_);
v___x_244_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3);
v___x_245_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_245_, 0, v___x_243_);
lean_ctor_set(v___x_245_, 1, v___x_244_);
v___x_246_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___y_215_);
v___x_247_ = l_Lean_Linter_logLintIf___redArg(v_inst_183_, v_inst_184_, v_inst_185_, v_inst_186_, v_inst_187_, v___x_233_, v_before_229_, v___x_246_);
return v___x_247_;
}
}
}
}
else
{
lean_object* v_head_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_276_; 
lean_del_object(v___x_227_);
v_head_252_ = lean_ctor_get(v_tail_225_, 0);
v_isSharedCheck_276_ = !lean_is_exclusive(v_tail_225_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v_tail_225_, 1);
lean_dec(v_unused_277_);
v___x_254_ = v_tail_225_;
v_isShared_255_ = v_isSharedCheck_276_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_head_252_);
lean_dec(v_tail_225_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_276_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_before_256_; lean_object* v_before_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_274_; 
v_before_256_ = lean_ctor_get(v_head_224_, 0);
lean_inc(v_before_256_);
lean_dec(v_head_224_);
v_before_257_ = lean_ctor_get(v_head_252_, 0);
v_isSharedCheck_274_ = !lean_is_exclusive(v_head_252_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v_head_252_, 1);
lean_dec(v_unused_275_);
v___x_259_ = v_head_252_;
v_isShared_260_ = v_isSharedCheck_274_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_before_257_);
lean_dec(v_head_252_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_274_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_261_; lean_object* v___x_262_; uint8_t v___x_263_; 
v___x_261_ = l_Lean_Syntax_getKind(v_before_257_);
lean_inc(v_before_256_);
v___x_262_ = l_Lean_Syntax_getKind(v_before_256_);
v___x_263_ = lean_name_eq(v___x_261_, v___x_262_);
if (v___x_263_ == 0)
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_264_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13);
v___x_265_ = l_Lean_MessageData_ofName(v___x_261_);
if (v_isShared_260_ == 0)
{
lean_ctor_set_tag(v___x_259_, 7);
lean_ctor_set(v___x_259_, 1, v___x_265_);
lean_ctor_set(v___x_259_, 0, v___x_264_);
v___x_267_ = v___x_259_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v___x_265_);
v___x_267_ = v_reuseFailAlloc_272_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_270_; 
v___x_268_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15);
if (v_isShared_255_ == 0)
{
lean_ctor_set_tag(v___x_254_, 7);
lean_ctor_set(v___x_254_, 1, v___x_268_);
lean_ctor_set(v___x_254_, 0, v___x_267_);
v___x_270_ = v___x_254_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_267_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
v___y_196_ = v___y_215_;
v___y_197_ = v_before_256_;
v___y_198_ = v___x_262_;
v___y_199_ = v___x_270_;
goto v___jp_195_;
}
}
}
else
{
lean_object* v___x_273_; 
lean_dec(v___x_261_);
lean_del_object(v___x_259_);
lean_del_object(v___x_254_);
v___x_273_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17);
v___y_196_ = v___y_215_;
v___y_197_ = v_before_256_;
v___y_198_ = v___x_262_;
v___y_199_ = v___x_273_;
goto v___jp_195_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg(lean_object* v_inst_291_, lean_object* v_inst_292_, lean_object* v_inst_293_, lean_object* v_inst_294_, lean_object* v_inst_295_, lean_object* v_stx_296_, lean_object* v_macroStack_297_){
_start:
{
lean_object* v_toApplicative_298_; lean_object* v_toBind_299_; lean_object* v_getEnv_300_; lean_object* v_toPure_301_; lean_object* v___x_302_; lean_object* v___f_303_; lean_object* v___x_304_; 
v_toApplicative_298_ = lean_ctor_get(v_inst_291_, 0);
v_toBind_299_ = lean_ctor_get(v_inst_291_, 1);
lean_inc(v_toBind_299_);
v_getEnv_300_ = lean_ctor_get(v_inst_292_, 0);
lean_inc(v_getEnv_300_);
v_toPure_301_ = lean_ctor_get(v_toApplicative_298_, 1);
lean_inc(v_toPure_301_);
v___x_302_ = lean_box(1);
v___f_303_ = lean_alloc_closure((void*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0), 10, 9);
lean_closure_set(v___f_303_, 0, v_stx_296_);
lean_closure_set(v___f_303_, 1, v___x_302_);
lean_closure_set(v___f_303_, 2, v_inst_291_);
lean_closure_set(v___f_303_, 3, v_inst_293_);
lean_closure_set(v___f_303_, 4, v_inst_295_);
lean_closure_set(v___f_303_, 5, v_inst_294_);
lean_closure_set(v___f_303_, 6, v_inst_292_);
lean_closure_set(v___f_303_, 7, v_macroStack_297_);
lean_closure_set(v___f_303_, 8, v_toPure_301_);
v___x_304_ = lean_apply_4(v_toBind_299_, lean_box(0), lean_box(0), v_getEnv_300_, v___f_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax(lean_object* v_m_305_, lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_stx_312_, lean_object* v_macroStack_313_){
_start:
{
lean_object* v___x_314_; 
v___x_314_ = l_Lean_Elab_checkDeprecatedSyntax___redArg(v_inst_306_, v_inst_307_, v_inst_308_, v_inst_309_, v_inst_310_, v_stx_312_, v_macroStack_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___boxed(lean_object* v_m_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_stx_322_, lean_object* v_macroStack_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Elab_checkDeprecatedSyntax(v_m_315_, v_inst_316_, v_inst_317_, v_inst_318_, v_inst_319_, v_inst_320_, v_inst_321_, v_stx_322_, v_macroStack_323_);
lean_dec_ref(v_inst_321_);
return v_res_324_;
}
}
lean_object* runtime_initialize_Lean_MonadEnv(uint8_t builtin);
lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Lean_Elab_Util(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Elab_DeprecatedSyntax(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
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
lean_object* initialize_Lean_Linter_Basic(uint8_t builtin);
lean_object* initialize_Lean_Elab_Util(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Elab_DeprecatedSyntax(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Linter_Basic(builtin);
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
