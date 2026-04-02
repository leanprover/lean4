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
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Syntax_getKind(lean_object*);
lean_object* l_Lean_Name_mkStr5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_Linter_logLintIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l_Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "syntax"};
static const lean_object* l_Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 99, 57, 49, 46, 156, 253, 187)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(214, 149, 21, 131, 183, 70, 101, 25)}};
static const lean_object* l_Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 58, .m_capacity = 58, .m_length = 57, .m_data = "if true, generate warnings when deprecated syntax is used"};
static const lean_object* l_Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_3 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(248, 165, 85, 201, 27, 48, 185, 203)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value_aux_3),((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(73, 92, 249, 154, 145, 175, 141, 131)}};
static const lean_object* l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_deprecated_syntax;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Elab"};
static const lean_object* l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "deprecatedSyntaxExt"};
static const lean_object* l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Elab_initFn___closed__2_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(52, 247, 248, 201, 92, 23, 188, 159)}};
static const lean_ctor_object l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Elab_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(216, 151, 2, 103, 84, 175, 195, 226)}};
static const lean_object* l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Elab_initFn___closed__4_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_initFn___closed__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Elab_initFn___closed__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2____boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(lean_object* v_name_1_, lean_object* v_decl_2_, lean_object* v_ref_3_){
_start:
{
lean_object* v_defValue_5_; lean_object* v_descr_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_33_; 
v_defValue_5_ = lean_ctor_get(v_decl_2_, 0);
v_descr_6_ = lean_ctor_get(v_decl_2_, 1);
v_isSharedCheck_33_ = !lean_is_exclusive(v_decl_2_);
if (v_isSharedCheck_33_ == 0)
{
v___x_8_ = v_decl_2_;
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_descr_6_);
lean_inc(v_defValue_5_);
lean_dec(v_decl_2_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_33_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v___x_10_; uint8_t v___x_11_; lean_object* v___x_12_; lean_object* v___x_13_; 
v___x_10_ = lean_alloc_ctor(1, 0, 1);
v___x_11_ = lean_unbox(v_defValue_5_);
lean_ctor_set_uint8(v___x_10_, 0, v___x_11_);
lean_inc_n(v_name_1_, 2);
v___x_12_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_12_, 0, v_name_1_);
lean_ctor_set(v___x_12_, 1, v_ref_3_);
lean_ctor_set(v___x_12_, 2, v___x_10_);
lean_ctor_set(v___x_12_, 3, v_descr_6_);
v___x_13_ = lean_register_option(v_name_1_, v___x_12_);
if (lean_obj_tag(v___x_13_) == 0)
{
lean_object* v___x_15_; uint8_t v_isShared_16_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_13_, 0);
lean_dec(v_unused_24_);
v___x_15_ = v___x_13_;
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
else
{
lean_dec(v___x_13_);
v___x_15_ = lean_box(0);
v_isShared_16_ = v_isSharedCheck_23_;
goto v_resetjp_14_;
}
v_resetjp_14_:
{
lean_object* v___x_18_; 
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 1, v_defValue_5_);
lean_ctor_set(v___x_8_, 0, v_name_1_);
v___x_18_ = v___x_8_;
goto v_reusejp_17_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v_name_1_);
lean_ctor_set(v_reuseFailAlloc_22_, 1, v_defValue_5_);
v___x_18_ = v_reuseFailAlloc_22_;
goto v_reusejp_17_;
}
v_reusejp_17_:
{
lean_object* v___x_20_; 
if (v_isShared_16_ == 0)
{
lean_ctor_set(v___x_15_, 0, v___x_18_);
v___x_20_ = v___x_15_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_21_; 
v_reuseFailAlloc_21_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_21_, 0, v___x_18_);
v___x_20_ = v_reuseFailAlloc_21_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
return v___x_20_;
}
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_del_object(v___x_8_);
lean_dec(v_defValue_5_);
lean_dec(v_name_1_);
v_a_25_ = lean_ctor_get(v___x_13_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_13_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_13_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_13_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_30_; 
if (v_isShared_28_ == 0)
{
v___x_30_ = v___x_27_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_a_25_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
return v_res_38_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; 
v___x_60_ = ((lean_object*)(l_Lean_Linter_initFn___closed__3_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_));
v___x_61_ = ((lean_object*)(l_Lean_Linter_initFn___closed__5_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_));
v___x_62_ = ((lean_object*)(l_Lean_Linter_initFn___closed__8_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_));
v___x_63_ = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4__spec__0(v___x_60_, v___x_61_, v___x_62_);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4____boxed(lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l_Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
return v_res_65_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn___lam__0_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(lean_object* v_m_66_, lean_object* v_e_67_){
_start:
{
lean_object* v_kind_68_; lean_object* v___x_69_; 
v_kind_68_ = lean_ctor_get(v_e_67_, 0);
lean_inc(v_kind_68_);
v___x_69_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_kind_68_, v_e_67_, v_m_66_);
return v___x_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn___lam__1_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(lean_object* v_es_70_){
_start:
{
lean_object* v___x_71_; 
v___x_71_ = lean_array_mk(v_es_70_);
return v___x_71_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_72_, size_t v_i_73_, size_t v_stop_74_, lean_object* v_b_75_){
_start:
{
uint8_t v___x_76_; 
v___x_76_ = lean_usize_dec_eq(v_i_73_, v_stop_74_);
if (v___x_76_ == 0)
{
lean_object* v___x_77_; lean_object* v_kind_78_; lean_object* v___x_79_; size_t v___x_80_; size_t v___x_81_; 
v___x_77_ = lean_array_uget_borrowed(v_as_72_, v_i_73_);
v_kind_78_ = lean_ctor_get(v___x_77_, 0);
lean_inc(v___x_77_);
lean_inc(v_kind_78_);
v___x_79_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_kind_78_, v___x_77_, v_b_75_);
v___x_80_ = ((size_t)1ULL);
v___x_81_ = lean_usize_add(v_i_73_, v___x_80_);
v_i_73_ = v___x_81_;
v_b_75_ = v___x_79_;
goto _start;
}
else
{
return v_b_75_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_83_, lean_object* v_i_84_, lean_object* v_stop_85_, lean_object* v_b_86_){
_start:
{
size_t v_i_boxed_87_; size_t v_stop_boxed_88_; lean_object* v_res_89_; 
v_i_boxed_87_ = lean_unbox_usize(v_i_84_);
lean_dec(v_i_84_);
v_stop_boxed_88_ = lean_unbox_usize(v_stop_85_);
lean_dec(v_stop_85_);
v_res_89_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v_as_83_, v_i_boxed_87_, v_stop_boxed_88_, v_b_86_);
lean_dec_ref(v_as_83_);
return v_res_89_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_90_, size_t v_i_91_, size_t v_stop_92_, lean_object* v_b_93_){
_start:
{
lean_object* v___y_95_; uint8_t v___x_99_; 
v___x_99_ = lean_usize_dec_eq(v_i_91_, v_stop_92_);
if (v___x_99_ == 0)
{
lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; uint8_t v___x_103_; 
v___x_100_ = lean_array_uget_borrowed(v_as_90_, v_i_91_);
v___x_101_ = lean_unsigned_to_nat(0u);
v___x_102_ = lean_array_get_size(v___x_100_);
v___x_103_ = lean_nat_dec_lt(v___x_101_, v___x_102_);
if (v___x_103_ == 0)
{
v___y_95_ = v_b_93_;
goto v___jp_94_;
}
else
{
uint8_t v___x_104_; 
v___x_104_ = lean_nat_dec_le(v___x_102_, v___x_102_);
if (v___x_104_ == 0)
{
if (v___x_103_ == 0)
{
v___y_95_ = v_b_93_;
goto v___jp_94_;
}
else
{
size_t v___x_105_; size_t v___x_106_; lean_object* v___x_107_; 
v___x_105_ = ((size_t)0ULL);
v___x_106_ = lean_usize_of_nat(v___x_102_);
v___x_107_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v___x_100_, v___x_105_, v___x_106_, v_b_93_);
v___y_95_ = v___x_107_;
goto v___jp_94_;
}
}
else
{
size_t v___x_108_; size_t v___x_109_; lean_object* v___x_110_; 
v___x_108_ = ((size_t)0ULL);
v___x_109_ = lean_usize_of_nat(v___x_102_);
v___x_110_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__0(v___x_100_, v___x_108_, v___x_109_, v_b_93_);
v___y_95_ = v___x_110_;
goto v___jp_94_;
}
}
}
else
{
return v_b_93_;
}
v___jp_94_:
{
size_t v___x_96_; size_t v___x_97_; 
v___x_96_ = ((size_t)1ULL);
v___x_97_ = lean_usize_add(v_i_91_, v___x_96_);
v_i_91_ = v___x_97_;
v_b_93_ = v___y_95_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_111_, lean_object* v_i_112_, lean_object* v_stop_113_, lean_object* v_b_114_){
_start:
{
size_t v_i_boxed_115_; size_t v_stop_boxed_116_; lean_object* v_res_117_; 
v_i_boxed_115_ = lean_unbox_usize(v_i_112_);
lean_dec(v_i_112_);
v_stop_boxed_116_ = lean_unbox_usize(v_stop_113_);
lean_dec(v_stop_113_);
v_res_117_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_111_, v_i_boxed_115_, v_stop_boxed_116_, v_b_114_);
lean_dec_ref(v_as_111_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0(lean_object* v_initState_118_, lean_object* v_as_119_){
_start:
{
lean_object* v___x_120_; lean_object* v___x_121_; uint8_t v___x_122_; 
v___x_120_ = lean_unsigned_to_nat(0u);
v___x_121_ = lean_array_get_size(v_as_119_);
v___x_122_ = lean_nat_dec_lt(v___x_120_, v___x_121_);
if (v___x_122_ == 0)
{
return v_initState_118_;
}
else
{
uint8_t v___x_123_; 
v___x_123_ = lean_nat_dec_le(v___x_121_, v___x_121_);
if (v___x_123_ == 0)
{
if (v___x_122_ == 0)
{
return v_initState_118_;
}
else
{
size_t v___x_124_; size_t v___x_125_; lean_object* v___x_126_; 
v___x_124_ = ((size_t)0ULL);
v___x_125_ = lean_usize_of_nat(v___x_121_);
v___x_126_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_119_, v___x_124_, v___x_125_, v_initState_118_);
return v___x_126_;
}
}
else
{
size_t v___x_127_; size_t v___x_128_; lean_object* v___x_129_; 
v___x_127_ = ((size_t)0ULL);
v___x_128_ = lean_usize_of_nat(v___x_121_);
v___x_129_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0_spec__1(v_as_119_, v___x_127_, v___x_128_, v_initState_118_);
return v___x_129_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_130_, lean_object* v_as_131_){
_start:
{
lean_object* v_res_132_; 
v_res_132_ = l_Lean_mkStateFromImportedEntries___at___00Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2__spec__0(v_initState_130_, v_as_131_);
lean_dec_ref(v_as_131_);
return v_res_132_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_151_; lean_object* v___x_152_; 
v___x_151_ = ((lean_object*)(l_Lean_Elab_initFn___closed__6_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_));
v___x_152_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2____boxed(lean_object* v_a_153_){
_start:
{
lean_object* v_res_154_; 
v_res_154_ = l_Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
return v_res_154_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1(void){
_start:
{
lean_object* v___x_156_; lean_object* v___x_157_; 
v___x_156_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__0));
v___x_157_ = l_Lean_stringToMessageData(v___x_156_);
return v___x_157_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3(void){
_start:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__2));
v___x_160_ = l_Lean_stringToMessageData(v___x_159_);
return v___x_160_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5(void){
_start:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__4));
v___x_163_ = l_Lean_stringToMessageData(v___x_162_);
return v___x_163_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; 
v___x_165_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__6));
v___x_166_ = l_Lean_stringToMessageData(v___x_165_);
return v___x_166_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_168_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__8));
v___x_169_ = l_Lean_stringToMessageData(v___x_168_);
return v___x_169_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_171_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__10));
v___x_172_ = l_Lean_stringToMessageData(v___x_171_);
return v___x_172_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13(void){
_start:
{
lean_object* v___x_174_; lean_object* v___x_175_; 
v___x_174_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__12));
v___x_175_ = l_Lean_stringToMessageData(v___x_174_);
return v___x_175_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15(void){
_start:
{
lean_object* v___x_177_; lean_object* v___x_178_; 
v___x_177_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__14));
v___x_178_ = l_Lean_stringToMessageData(v___x_177_);
return v___x_178_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17(void){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__16));
v___x_181_ = l_Lean_stringToMessageData(v___x_180_);
return v___x_181_;
}
}
static lean_object* _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19(void){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = ((lean_object*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__18));
v___x_184_ = l_Lean_stringToMessageData(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0(lean_object* v_stx_185_, lean_object* v___x_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_inst_190_, lean_object* v_inst_191_, lean_object* v_macroStack_192_, lean_object* v_toPure_193_, lean_object* v_env_194_){
_start:
{
lean_object* v___x_195_; lean_object* v_toEnvExtension_196_; lean_object* v_asyncMode_197_; lean_object* v_kind_198_; lean_object* v___y_200_; lean_object* v___y_201_; lean_object* v___y_202_; lean_object* v___y_203_; lean_object* v___y_219_; lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_285_; 
v___x_195_ = l_Lean_Elab_deprecatedSyntaxExt;
v_toEnvExtension_196_ = lean_ctor_get(v___x_195_, 0);
v_asyncMode_197_ = lean_ctor_get(v_toEnvExtension_196_, 2);
lean_inc(v_stx_185_);
v_kind_198_ = l_Lean_Syntax_getKind(v_stx_185_);
v___x_283_ = lean_box(0);
v___x_284_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_186_, v___x_195_, v_env_194_, v_asyncMode_197_, v___x_283_);
v___x_285_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v___x_284_, v_kind_198_);
lean_dec(v___x_284_);
if (lean_obj_tag(v___x_285_) == 1)
{
lean_object* v_val_286_; lean_object* v_text_x3f_287_; 
lean_dec(v_toPure_193_);
v_val_286_ = lean_ctor_get(v___x_285_, 0);
lean_inc(v_val_286_);
lean_dec_ref(v___x_285_);
v_text_x3f_287_ = lean_ctor_get(v_val_286_, 1);
lean_inc(v_text_x3f_287_);
lean_dec(v_val_286_);
if (lean_obj_tag(v_text_x3f_287_) == 0)
{
lean_object* v___x_288_; 
v___x_288_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17);
v___y_219_ = v___x_288_;
goto v___jp_218_;
}
else
{
lean_object* v_val_289_; lean_object* v___x_290_; lean_object* v___x_291_; lean_object* v___x_292_; 
v_val_289_ = lean_ctor_get(v_text_x3f_287_, 0);
lean_inc(v_val_289_);
lean_dec_ref(v_text_x3f_287_);
v___x_290_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__19);
v___x_291_ = l_Lean_stringToMessageData(v_val_289_);
v___x_292_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_292_, 0, v___x_290_);
lean_ctor_set(v___x_292_, 1, v___x_291_);
v___y_219_ = v___x_292_;
goto v___jp_218_;
}
}
else
{
lean_object* v___x_293_; lean_object* v___x_294_; 
lean_dec(v___x_285_);
lean_dec(v_kind_198_);
lean_dec(v_macroStack_192_);
lean_dec_ref(v_inst_191_);
lean_dec(v_inst_190_);
lean_dec(v_inst_189_);
lean_dec_ref(v_inst_188_);
lean_dec_ref(v_inst_187_);
lean_dec(v_stx_185_);
v___x_293_ = lean_box(0);
v___x_294_ = lean_apply_2(v_toPure_193_, lean_box(0), v___x_293_);
return v___x_294_;
}
v___jp_199_:
{
lean_object* v___x_204_; lean_object* v___x_205_; lean_object* v___x_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_204_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_205_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1);
v___x_206_ = l_Lean_MessageData_ofName(v___y_202_);
v___x_207_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_207_, 0, v___x_205_);
lean_ctor_set(v___x_207_, 1, v___x_206_);
v___x_208_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3);
v___x_209_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_209_, 0, v___x_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
v___x_210_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_210_, 0, v___x_209_);
lean_ctor_set(v___x_210_, 1, v___y_203_);
v___x_211_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__5);
v___x_212_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_212_, 0, v___x_210_);
lean_ctor_set(v___x_212_, 1, v___x_211_);
v___x_213_ = l_Lean_MessageData_ofName(v_kind_198_);
v___x_214_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_214_, 0, v___x_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
v___x_215_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
lean_ctor_set(v___x_215_, 1, v___x_208_);
v___x_216_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_216_, 0, v___x_215_);
lean_ctor_set(v___x_216_, 1, v___y_201_);
v___x_217_ = l_Lean_Linter_logLintIf___redArg(v_inst_187_, v_inst_188_, v_inst_189_, v_inst_190_, v_inst_191_, v___x_204_, v___y_200_, v___x_216_);
return v___x_217_;
}
v___jp_218_:
{
if (lean_obj_tag(v_macroStack_192_) == 0)
{
lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; lean_object* v___x_223_; lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; 
v___x_220_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_221_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__7);
v___x_222_ = l_Lean_MessageData_ofName(v_kind_198_);
v___x_223_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_223_, 0, v___x_221_);
lean_ctor_set(v___x_223_, 1, v___x_222_);
v___x_224_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__9);
v___x_225_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_225_, 0, v___x_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
v___x_226_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_226_, 0, v___x_225_);
lean_ctor_set(v___x_226_, 1, v___y_219_);
v___x_227_ = l_Lean_Linter_logLintIf___redArg(v_inst_187_, v_inst_188_, v_inst_189_, v_inst_190_, v_inst_191_, v___x_220_, v_stx_185_, v___x_226_);
return v___x_227_;
}
else
{
lean_object* v_head_228_; lean_object* v_tail_229_; lean_object* v___x_231_; uint8_t v_isShared_232_; uint8_t v_isSharedCheck_282_; 
lean_dec(v_stx_185_);
v_head_228_ = lean_ctor_get(v_macroStack_192_, 0);
v_tail_229_ = lean_ctor_get(v_macroStack_192_, 1);
v_isSharedCheck_282_ = !lean_is_exclusive(v_macroStack_192_);
if (v_isSharedCheck_282_ == 0)
{
v___x_231_ = v_macroStack_192_;
v_isShared_232_ = v_isSharedCheck_282_;
goto v_resetjp_230_;
}
else
{
lean_inc(v_tail_229_);
lean_inc(v_head_228_);
lean_dec(v_macroStack_192_);
v___x_231_ = lean_box(0);
v_isShared_232_ = v_isSharedCheck_282_;
goto v_resetjp_230_;
}
v_resetjp_230_:
{
if (lean_obj_tag(v_tail_229_) == 0)
{
lean_object* v_before_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_254_; 
v_before_233_ = lean_ctor_get(v_head_228_, 0);
v_isSharedCheck_254_ = !lean_is_exclusive(v_head_228_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v_head_228_, 1);
lean_dec(v_unused_255_);
v___x_235_ = v_head_228_;
v_isShared_236_ = v_isSharedCheck_254_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_before_233_);
lean_dec(v_head_228_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_254_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_237_ = l_Lean_Linter_linter_deprecated_syntax;
v___x_238_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__1);
lean_inc(v_before_233_);
v___x_239_ = l_Lean_Syntax_getKind(v_before_233_);
v___x_240_ = l_Lean_MessageData_ofName(v___x_239_);
if (v_isShared_236_ == 0)
{
lean_ctor_set_tag(v___x_235_, 7);
lean_ctor_set(v___x_235_, 1, v___x_240_);
lean_ctor_set(v___x_235_, 0, v___x_238_);
v___x_242_ = v___x_235_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_253_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
lean_object* v___x_243_; lean_object* v___x_245_; 
v___x_243_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__11);
if (v_isShared_232_ == 0)
{
lean_ctor_set_tag(v___x_231_, 7);
lean_ctor_set(v___x_231_, 1, v___x_243_);
lean_ctor_set(v___x_231_, 0, v___x_242_);
v___x_245_ = v___x_231_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_242_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v___x_243_);
v___x_245_ = v_reuseFailAlloc_252_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
lean_object* v___x_246_; lean_object* v___x_247_; lean_object* v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; lean_object* v___x_251_; 
v___x_246_ = l_Lean_MessageData_ofName(v_kind_198_);
v___x_247_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_247_, 0, v___x_245_);
lean_ctor_set(v___x_247_, 1, v___x_246_);
v___x_248_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__3);
v___x_249_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_249_, 0, v___x_247_);
lean_ctor_set(v___x_249_, 1, v___x_248_);
v___x_250_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
lean_ctor_set(v___x_250_, 1, v___y_219_);
v___x_251_ = l_Lean_Linter_logLintIf___redArg(v_inst_187_, v_inst_188_, v_inst_189_, v_inst_190_, v_inst_191_, v___x_237_, v_before_233_, v___x_250_);
return v___x_251_;
}
}
}
}
else
{
lean_object* v_head_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_280_; 
lean_del_object(v___x_231_);
v_head_256_ = lean_ctor_get(v_tail_229_, 0);
v_isSharedCheck_280_ = !lean_is_exclusive(v_tail_229_);
if (v_isSharedCheck_280_ == 0)
{
lean_object* v_unused_281_; 
v_unused_281_ = lean_ctor_get(v_tail_229_, 1);
lean_dec(v_unused_281_);
v___x_258_ = v_tail_229_;
v_isShared_259_ = v_isSharedCheck_280_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_head_256_);
lean_dec(v_tail_229_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_280_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v_before_260_; lean_object* v_before_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_278_; 
v_before_260_ = lean_ctor_get(v_head_228_, 0);
lean_inc(v_before_260_);
lean_dec(v_head_228_);
v_before_261_ = lean_ctor_get(v_head_256_, 0);
v_isSharedCheck_278_ = !lean_is_exclusive(v_head_256_);
if (v_isSharedCheck_278_ == 0)
{
lean_object* v_unused_279_; 
v_unused_279_ = lean_ctor_get(v_head_256_, 1);
lean_dec(v_unused_279_);
v___x_263_ = v_head_256_;
v_isShared_264_ = v_isSharedCheck_278_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_before_261_);
lean_dec(v_head_256_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_278_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___x_265_; lean_object* v___x_266_; uint8_t v___x_267_; 
v___x_265_ = l_Lean_Syntax_getKind(v_before_261_);
lean_inc(v_before_260_);
v___x_266_ = l_Lean_Syntax_getKind(v_before_260_);
v___x_267_ = lean_name_eq(v___x_265_, v___x_266_);
if (v___x_267_ == 0)
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_268_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__13);
v___x_269_ = l_Lean_MessageData_ofName(v___x_265_);
if (v_isShared_264_ == 0)
{
lean_ctor_set_tag(v___x_263_, 7);
lean_ctor_set(v___x_263_, 1, v___x_269_);
lean_ctor_set(v___x_263_, 0, v___x_268_);
v___x_271_ = v___x_263_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v___x_269_);
v___x_271_ = v_reuseFailAlloc_276_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_272_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__15);
if (v_isShared_259_ == 0)
{
lean_ctor_set_tag(v___x_258_, 7);
lean_ctor_set(v___x_258_, 1, v___x_272_);
lean_ctor_set(v___x_258_, 0, v___x_271_);
v___x_274_ = v___x_258_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_271_);
lean_ctor_set(v_reuseFailAlloc_275_, 1, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
v___y_200_ = v_before_260_;
v___y_201_ = v___y_219_;
v___y_202_ = v___x_266_;
v___y_203_ = v___x_274_;
goto v___jp_199_;
}
}
}
else
{
lean_object* v___x_277_; 
lean_dec(v___x_265_);
lean_del_object(v___x_263_);
lean_del_object(v___x_258_);
v___x_277_ = lean_obj_once(&l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17, &l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17_once, _init_l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0___closed__17);
v___y_200_ = v_before_260_;
v___y_201_ = v___y_219_;
v___y_202_ = v___x_266_;
v___y_203_ = v___x_277_;
goto v___jp_199_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___redArg(lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_inst_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_stx_300_, lean_object* v_macroStack_301_){
_start:
{
lean_object* v_toApplicative_302_; lean_object* v_toBind_303_; lean_object* v_getEnv_304_; lean_object* v_toPure_305_; lean_object* v___x_306_; lean_object* v___f_307_; lean_object* v___x_308_; 
v_toApplicative_302_ = lean_ctor_get(v_inst_295_, 0);
v_toBind_303_ = lean_ctor_get(v_inst_295_, 1);
lean_inc(v_toBind_303_);
v_getEnv_304_ = lean_ctor_get(v_inst_296_, 0);
lean_inc(v_getEnv_304_);
v_toPure_305_ = lean_ctor_get(v_toApplicative_302_, 1);
lean_inc(v_toPure_305_);
v___x_306_ = lean_box(1);
v___f_307_ = lean_alloc_closure((void*)(l_Lean_Elab_checkDeprecatedSyntax___redArg___lam__0), 10, 9);
lean_closure_set(v___f_307_, 0, v_stx_300_);
lean_closure_set(v___f_307_, 1, v___x_306_);
lean_closure_set(v___f_307_, 2, v_inst_295_);
lean_closure_set(v___f_307_, 3, v_inst_297_);
lean_closure_set(v___f_307_, 4, v_inst_299_);
lean_closure_set(v___f_307_, 5, v_inst_298_);
lean_closure_set(v___f_307_, 6, v_inst_296_);
lean_closure_set(v___f_307_, 7, v_macroStack_301_);
lean_closure_set(v___f_307_, 8, v_toPure_305_);
v___x_308_ = lean_apply_4(v_toBind_303_, lean_box(0), lean_box(0), v_getEnv_304_, v___f_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax(lean_object* v_m_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_stx_316_, lean_object* v_macroStack_317_){
_start:
{
lean_object* v___x_318_; 
v___x_318_ = l_Lean_Elab_checkDeprecatedSyntax___redArg(v_inst_310_, v_inst_311_, v_inst_312_, v_inst_313_, v_inst_314_, v_stx_316_, v_macroStack_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Elab_checkDeprecatedSyntax___boxed(lean_object* v_m_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_stx_326_, lean_object* v_macroStack_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Elab_checkDeprecatedSyntax(v_m_319_, v_inst_320_, v_inst_321_, v_inst_322_, v_inst_323_, v_inst_324_, v_inst_325_, v_stx_326_, v_macroStack_327_);
lean_dec_ref(v_inst_325_);
return v_res_328_;
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
res = l_Lean_Linter_initFn_00___x40_Lean_Elab_DeprecatedSyntax_3204438947____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_deprecated_syntax = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_deprecated_syntax);
lean_dec_ref(res);
res = l_Lean_Elab_initFn_00___x40_Lean_Elab_DeprecatedSyntax_2404873452____hygCtx___hyg_2_();
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
