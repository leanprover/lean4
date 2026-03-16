// Lean compiler output
// Module: Lean.Linter.Basic
// Imports: public import Lean.MonadEnv import Init.Data.Function
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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* l_Lean_stringToMessageData(lean_object*);
lean_object* l_Lean_MessageData_ofName(lean_object*);
lean_object* l_Lean_MessageData_note(lean_object*);
lean_object* l_Lean_logWarningAt___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_mk(lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_registerSimplePersistentEnvExtension___redArg(lean_object*);
lean_object* l_Lean_SimplePersistentEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_instEmptyCollectionLinterSets;
LEAN_EXPORT lean_object* l_Lean_Linter_instInhabitedLinterSets;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0 = (const lean_object*)&l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSetEntry(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "Linter"};
static const lean_object* l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 14, .m_capacity = 14, .m_length = 13, .m_data = "linterSetsExt"};
static const lean_object* l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(181, 168, 78, 71, 242, 123, 0, 76)}};
static const lean_object* l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0___boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))} };
static const lean_object* l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*7 + 0, .m_other = 7, .m_tag = 0}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_initFn___closed__6_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linterSetsExt;
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 4, .m_capacity = 4, .m_length = 3, .m_data = "all"};
static const lean_object* l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(242, 180, 119, 173, 178, 109, 102, 175)}};
static const lean_object* l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value;
static const lean_string_object l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 19, .m_capacity = 19, .m_length = 18, .m_data = "enable all linters"};
static const lean_object* l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value)}};
static const lean_object* l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value;
static const lean_ctor_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value_aux_0),((lean_object*)&l_Lean_Linter_initFn___closed__3_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(200, 24, 215, 162, 183, 90, 3, 112)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value_aux_1),((lean_object*)&l_Lean_Linter_initFn___closed__0_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(53, 243, 121, 207, 53, 172, 203, 87)}};
static const lean_ctor_object l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value_aux_2),((lean_object*)&l_Lean_Linter_initFn___closed__1_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(137, 167, 123, 44, 188, 59, 15, 50)}};
static const lean_object* l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_ = (const lean_object*)&l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_linter_all;
LEAN_EXPORT uint8_t l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterAll(lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterAll___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1___boxed(lean_object*, lean_object*);
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0_value;
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(lean_object*, lean_object*, size_t, size_t);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterValue(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterValue___boxed(lean_object*, lean_object*);
static const lean_string_object l_Lean_Linter_logLint___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 46, .m_capacity = 46, .m_length = 45, .m_data = "This linter can be disabled with `set_option "};
static const lean_object* l_Lean_Linter_logLint___redArg___closed__0 = (const lean_object*)&l_Lean_Linter_logLint___redArg___closed__0_value;
static lean_once_cell_t l_Lean_Linter_logLint___redArg___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___redArg___closed__1;
static const lean_string_object l_Lean_Linter_logLint___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = " false`"};
static const lean_object* l_Lean_Linter_logLint___redArg___closed__2 = (const lean_object*)&l_Lean_Linter_logLint___redArg___closed__2_value;
static lean_once_cell_t l_Lean_Linter_logLint___redArg___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Linter_logLint___redArg___closed__3;
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLint(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_object* _init_l_Lean_Linter_instEmptyCollectionLinterSets(void){
_start:
{
lean_object* v___x_1_; 
v___x_1_ = lean_box(1);
return v___x_1_;
}
}
static lean_object* _init_l_Lean_Linter_instInhabitedLinterSets(void){
_start:
{
lean_object* v___x_2_; 
v___x_2_ = lean_box(1);
return v___x_2_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(lean_object* v_t_3_, lean_object* v_k_4_, lean_object* v_fallback_5_){
_start:
{
if (lean_obj_tag(v_t_3_) == 0)
{
lean_object* v_k_6_; lean_object* v_v_7_; lean_object* v_l_8_; lean_object* v_r_9_; uint8_t v___x_10_; 
v_k_6_ = lean_ctor_get(v_t_3_, 1);
v_v_7_ = lean_ctor_get(v_t_3_, 2);
v_l_8_ = lean_ctor_get(v_t_3_, 3);
v_r_9_ = lean_ctor_get(v_t_3_, 4);
v___x_10_ = l___private_Lean_Data_Name_0__Lean_Name_quickCmpImpl(v_k_4_, v_k_6_);
switch(v___x_10_)
{
case 0:
{
v_t_3_ = v_l_8_;
goto _start;
}
case 1:
{
lean_inc(v_v_7_);
return v_v_7_;
}
default: 
{
v_t_3_ = v_r_9_;
goto _start;
}
}
}
else
{
lean_inc(v_fallback_5_);
return v_fallback_5_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg___boxed(lean_object* v_t_13_, lean_object* v_k_14_, lean_object* v_fallback_15_){
_start:
{
lean_object* v_res_16_; 
v_res_16_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_t_13_, v_k_14_, v_fallback_15_);
lean_dec(v_fallback_15_);
lean_dec(v_k_14_);
lean_dec(v_t_13_);
return v_res_16_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(lean_object* v_setName_19_, lean_object* v_init_20_, lean_object* v_x_21_){
_start:
{
if (lean_obj_tag(v_x_21_) == 0)
{
lean_object* v_k_22_; lean_object* v_l_23_; lean_object* v_r_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
v_k_22_ = lean_ctor_get(v_x_21_, 1);
lean_inc(v_k_22_);
v_l_23_ = lean_ctor_get(v_x_21_, 3);
lean_inc(v_l_23_);
v_r_24_ = lean_ctor_get(v_x_21_, 4);
lean_inc(v_r_24_);
lean_dec_ref(v_x_21_);
lean_inc(v_setName_19_);
v___x_25_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_setName_19_, v_init_20_, v_l_23_);
v___x_26_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0));
v___x_27_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v___x_25_, v_k_22_, v___x_26_);
lean_inc(v_setName_19_);
v___x_28_ = lean_array_push(v___x_27_, v_setName_19_);
v___x_29_ = l_Std_DTreeMap_Internal_Impl_insert___at___00Lean_NameMap_insert_spec__0___redArg(v_k_22_, v___x_28_, v___x_25_);
v_init_20_ = v___x_29_;
v_x_21_ = v_r_24_;
goto _start;
}
else
{
lean_dec(v_setName_19_);
return v_init_20_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_insertLinterSetEntry(lean_object* v_map_31_, lean_object* v_setName_32_, lean_object* v_options_33_){
_start:
{
lean_object* v___x_34_; 
v___x_34_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_setName_32_, v_map_31_, v_options_33_);
return v___x_34_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0(lean_object* v_00_u03b4_35_, lean_object* v_t_36_, lean_object* v_k_37_, lean_object* v_fallback_38_){
_start:
{
lean_object* v___x_39_; 
v___x_39_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_t_36_, v_k_37_, v_fallback_38_);
return v___x_39_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___boxed(lean_object* v_00_u03b4_40_, lean_object* v_t_41_, lean_object* v_k_42_, lean_object* v_fallback_43_){
_start:
{
lean_object* v_res_44_; 
v_res_44_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0(v_00_u03b4_40_, v_t_41_, v_k_42_, v_fallback_43_);
lean_dec(v_fallback_43_);
lean_dec(v_k_42_);
lean_dec(v_t_41_);
return v_res_44_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1(lean_object* v_setName_45_, lean_object* v_init_46_, lean_object* v_t_47_){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_setName_45_, v_init_46_, v_t_47_);
return v___x_48_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__0_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_(lean_object* v_x_49_, lean_object* v___y_50_){
_start:
{
lean_object* v_fst_51_; lean_object* v_snd_52_; lean_object* v___x_53_; 
v_fst_51_ = lean_ctor_get(v___y_50_, 0);
lean_inc(v_fst_51_);
v_snd_52_ = lean_ctor_get(v___y_50_, 1);
lean_inc(v_snd_52_);
lean_dec_ref(v___y_50_);
v___x_53_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_fst_51_, v_x_49_, v_snd_52_);
return v___x_53_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn___lam__1_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_(lean_object* v_es_54_){
_start:
{
lean_object* v___x_55_; 
v___x_55_ = lean_array_mk(v_es_54_);
return v___x_55_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_as_56_, size_t v_i_57_, size_t v_stop_58_, lean_object* v_b_59_){
_start:
{
uint8_t v___x_60_; 
v___x_60_ = lean_usize_dec_eq(v_i_57_, v_stop_58_);
if (v___x_60_ == 0)
{
lean_object* v___x_61_; lean_object* v_fst_62_; lean_object* v_snd_63_; lean_object* v___x_64_; size_t v___x_65_; size_t v___x_66_; 
v___x_61_ = lean_array_uget_borrowed(v_as_56_, v_i_57_);
v_fst_62_ = lean_ctor_get(v___x_61_, 0);
v_snd_63_ = lean_ctor_get(v___x_61_, 1);
lean_inc(v_snd_63_);
lean_inc(v_fst_62_);
v___x_64_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1(v_fst_62_, v_b_59_, v_snd_63_);
v___x_65_ = ((size_t)1ULL);
v___x_66_ = lean_usize_add(v_i_57_, v___x_65_);
v_i_57_ = v___x_66_;
v_b_59_ = v___x_64_;
goto _start;
}
else
{
return v_b_59_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_as_68_, lean_object* v_i_69_, lean_object* v_stop_70_, lean_object* v_b_71_){
_start:
{
size_t v_i_boxed_72_; size_t v_stop_boxed_73_; lean_object* v_res_74_; 
v_i_boxed_72_ = lean_unbox_usize(v_i_69_);
lean_dec(v_i_69_);
v_stop_boxed_73_ = lean_unbox_usize(v_stop_70_);
lean_dec(v_stop_70_);
v_res_74_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__0(v_as_68_, v_i_boxed_72_, v_stop_boxed_73_, v_b_71_);
lean_dec_ref(v_as_68_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_as_75_, size_t v_i_76_, size_t v_stop_77_, lean_object* v_b_78_){
_start:
{
lean_object* v___y_80_; uint8_t v___x_84_; 
v___x_84_ = lean_usize_dec_eq(v_i_76_, v_stop_77_);
if (v___x_84_ == 0)
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v___x_85_ = lean_array_uget_borrowed(v_as_75_, v_i_76_);
v___x_86_ = lean_unsigned_to_nat(0u);
v___x_87_ = lean_array_get_size(v___x_85_);
v___x_88_ = lean_nat_dec_lt(v___x_86_, v___x_87_);
if (v___x_88_ == 0)
{
v___y_80_ = v_b_78_;
goto v___jp_79_;
}
else
{
uint8_t v___x_89_; 
v___x_89_ = lean_nat_dec_le(v___x_87_, v___x_87_);
if (v___x_89_ == 0)
{
if (v___x_88_ == 0)
{
v___y_80_ = v_b_78_;
goto v___jp_79_;
}
else
{
size_t v___x_90_; size_t v___x_91_; lean_object* v___x_92_; 
v___x_90_ = ((size_t)0ULL);
v___x_91_ = lean_usize_of_nat(v___x_87_);
v___x_92_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__0(v___x_85_, v___x_90_, v___x_91_, v_b_78_);
v___y_80_ = v___x_92_;
goto v___jp_79_;
}
}
else
{
size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; 
v___x_93_ = ((size_t)0ULL);
v___x_94_ = lean_usize_of_nat(v___x_87_);
v___x_95_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__0(v___x_85_, v___x_93_, v___x_94_, v_b_78_);
v___y_80_ = v___x_95_;
goto v___jp_79_;
}
}
}
else
{
return v_b_78_;
}
v___jp_79_:
{
size_t v___x_81_; size_t v___x_82_; 
v___x_81_ = ((size_t)1ULL);
v___x_82_ = lean_usize_add(v_i_76_, v___x_81_);
v_i_76_ = v___x_82_;
v_b_78_ = v___y_80_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__1___boxed(lean_object* v_as_96_, lean_object* v_i_97_, lean_object* v_stop_98_, lean_object* v_b_99_){
_start:
{
size_t v_i_boxed_100_; size_t v_stop_boxed_101_; lean_object* v_res_102_; 
v_i_boxed_100_ = lean_unbox_usize(v_i_97_);
lean_dec(v_i_97_);
v_stop_boxed_101_ = lean_unbox_usize(v_stop_98_);
lean_dec(v_stop_98_);
v_res_102_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__1(v_as_96_, v_i_boxed_100_, v_stop_boxed_101_, v_b_99_);
lean_dec_ref(v_as_96_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0(lean_object* v_initState_103_, lean_object* v_as_104_){
_start:
{
lean_object* v___x_105_; lean_object* v___x_106_; uint8_t v___x_107_; 
v___x_105_ = lean_unsigned_to_nat(0u);
v___x_106_ = lean_array_get_size(v_as_104_);
v___x_107_ = lean_nat_dec_lt(v___x_105_, v___x_106_);
if (v___x_107_ == 0)
{
return v_initState_103_;
}
else
{
uint8_t v___x_108_; 
v___x_108_ = lean_nat_dec_le(v___x_106_, v___x_106_);
if (v___x_108_ == 0)
{
if (v___x_107_ == 0)
{
return v_initState_103_;
}
else
{
size_t v___x_109_; size_t v___x_110_; lean_object* v___x_111_; 
v___x_109_ = ((size_t)0ULL);
v___x_110_ = lean_usize_of_nat(v___x_106_);
v___x_111_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__1(v_as_104_, v___x_109_, v___x_110_, v_initState_103_);
return v___x_111_;
}
}
else
{
size_t v___x_112_; size_t v___x_113_; lean_object* v___x_114_; 
v___x_112_ = ((size_t)0ULL);
v___x_113_ = lean_usize_of_nat(v___x_106_);
v___x_114_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0_spec__1(v_as_104_, v___x_112_, v___x_113_, v_initState_103_);
return v___x_114_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0___boxed(lean_object* v_initState_115_, lean_object* v_as_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_Lean_mkStateFromImportedEntries___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2__spec__0(v_initState_115_, v_as_116_);
lean_dec_ref(v_as_116_);
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_137_; lean_object* v___x_138_; 
v___x_137_ = ((lean_object*)(l_Lean_Linter_initFn___closed__7_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_));
v___x_138_ = l_Lean_registerSimplePersistentEnvExtension___redArg(v___x_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2____boxed(lean_object* v_a_139_){
_start:
{
lean_object* v_res_140_; 
v_res_140_ = l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_();
return v_res_140_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg(lean_object* v_inst_141_, lean_object* v_o_142_, lean_object* v_k_143_, lean_object* v_defVal_144_){
_start:
{
lean_object* v_toOptions_145_; lean_object* v_map_146_; lean_object* v_ofDataValue_x3f_147_; lean_object* v___x_148_; 
v_toOptions_145_ = lean_ctor_get(v_o_142_, 0);
v_map_146_ = lean_ctor_get(v_toOptions_145_, 0);
v_ofDataValue_x3f_147_ = lean_ctor_get(v_inst_141_, 1);
lean_inc_ref(v_ofDataValue_x3f_147_);
lean_dec_ref(v_inst_141_);
v___x_148_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_146_, v_k_143_);
if (lean_obj_tag(v___x_148_) == 0)
{
lean_dec_ref(v_ofDataValue_x3f_147_);
lean_inc(v_defVal_144_);
return v_defVal_144_;
}
else
{
lean_object* v_val_149_; lean_object* v___x_150_; 
v_val_149_ = lean_ctor_get(v___x_148_, 0);
lean_inc(v_val_149_);
lean_dec_ref(v___x_148_);
v___x_150_ = lean_apply_1(v_ofDataValue_x3f_147_, v_val_149_);
if (lean_obj_tag(v___x_150_) == 0)
{
lean_inc(v_defVal_144_);
return v_defVal_144_;
}
else
{
lean_object* v_val_151_; 
v_val_151_ = lean_ctor_get(v___x_150_, 0);
lean_inc(v_val_151_);
lean_dec_ref(v___x_150_);
return v_val_151_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___redArg___boxed(lean_object* v_inst_152_, lean_object* v_o_153_, lean_object* v_k_154_, lean_object* v_defVal_155_){
_start:
{
lean_object* v_res_156_; 
v_res_156_ = l_Lean_Linter_LinterOptions_get___redArg(v_inst_152_, v_o_153_, v_k_154_, v_defVal_155_);
lean_dec(v_defVal_155_);
lean_dec(v_k_154_);
lean_dec_ref(v_o_153_);
return v_res_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get(lean_object* v_00_u03b1_157_, lean_object* v_inst_158_, lean_object* v_o_159_, lean_object* v_k_160_, lean_object* v_defVal_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_Lean_Linter_LinterOptions_get___redArg(v_inst_158_, v_o_159_, v_k_160_, v_defVal_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___boxed(lean_object* v_00_u03b1_163_, lean_object* v_inst_164_, lean_object* v_o_165_, lean_object* v_k_166_, lean_object* v_defVal_167_){
_start:
{
lean_object* v_res_168_; 
v_res_168_ = l_Lean_Linter_LinterOptions_get(v_00_u03b1_163_, v_inst_164_, v_o_165_, v_k_166_, v_defVal_167_);
lean_dec(v_defVal_167_);
lean_dec(v_k_166_);
lean_dec_ref(v_o_165_);
return v_res_168_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg(lean_object* v_inst_169_, lean_object* v_o_170_, lean_object* v_k_171_){
_start:
{
lean_object* v_toOptions_172_; lean_object* v_map_173_; lean_object* v_ofDataValue_x3f_174_; lean_object* v___x_175_; 
v_toOptions_172_ = lean_ctor_get(v_o_170_, 0);
v_map_173_ = lean_ctor_get(v_toOptions_172_, 0);
v_ofDataValue_x3f_174_ = lean_ctor_get(v_inst_169_, 1);
lean_inc_ref(v_ofDataValue_x3f_174_);
lean_dec_ref(v_inst_169_);
v___x_175_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_173_, v_k_171_);
if (lean_obj_tag(v___x_175_) == 0)
{
lean_object* v___x_176_; 
lean_dec_ref(v_ofDataValue_x3f_174_);
v___x_176_ = lean_box(0);
return v___x_176_;
}
else
{
lean_object* v_val_177_; lean_object* v___x_178_; 
v_val_177_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_val_177_);
lean_dec_ref(v___x_175_);
v___x_178_ = lean_apply_1(v_ofDataValue_x3f_174_, v_val_177_);
return v___x_178_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___redArg___boxed(lean_object* v_inst_179_, lean_object* v_o_180_, lean_object* v_k_181_){
_start:
{
lean_object* v_res_182_; 
v_res_182_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_179_, v_o_180_, v_k_181_);
lean_dec(v_k_181_);
lean_dec_ref(v_o_180_);
return v_res_182_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f(lean_object* v_00_u03b1_183_, lean_object* v_inst_184_, lean_object* v_o_185_, lean_object* v_k_186_){
_start:
{
lean_object* v___x_187_; 
v___x_187_ = l_Lean_Linter_LinterOptions_get_x3f___redArg(v_inst_184_, v_o_185_, v_k_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___boxed(lean_object* v_00_u03b1_188_, lean_object* v_inst_189_, lean_object* v_o_190_, lean_object* v_k_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_Lean_Linter_LinterOptions_get_x3f(v_00_u03b1_188_, v_inst_189_, v_o_190_, v_k_191_);
lean_dec(v_k_191_);
lean_dec_ref(v_o_190_);
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg___lam__0(lean_object* v___x_193_, lean_object* v_o_194_, lean_object* v_toPure_195_, lean_object* v_____do__lift_196_){
_start:
{
lean_object* v___x_197_; lean_object* v_toEnvExtension_198_; lean_object* v_asyncMode_199_; lean_object* v___x_200_; lean_object* v_linterSets_201_; lean_object* v___x_202_; lean_object* v___x_203_; 
v___x_197_ = l_Lean_Linter_linterSetsExt;
v_toEnvExtension_198_ = lean_ctor_get(v___x_197_, 0);
lean_inc_ref(v_toEnvExtension_198_);
v_asyncMode_199_ = lean_ctor_get(v_toEnvExtension_198_, 2);
lean_inc(v_asyncMode_199_);
lean_dec_ref(v_toEnvExtension_198_);
v___x_200_ = lean_box(0);
v_linterSets_201_ = l_Lean_SimplePersistentEnvExtension_getState___redArg(v___x_193_, v___x_197_, v_____do__lift_196_, v_asyncMode_199_, v___x_200_);
lean_dec(v_asyncMode_199_);
v___x_202_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_202_, 0, v_o_194_);
lean_ctor_set(v___x_202_, 1, v_linterSets_201_);
v___x_203_ = lean_apply_2(v_toPure_195_, lean_box(0), v___x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions___redArg(lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_o_206_){
_start:
{
lean_object* v_toApplicative_207_; lean_object* v_toBind_208_; lean_object* v_getEnv_209_; lean_object* v_toPure_210_; lean_object* v___x_211_; lean_object* v___f_212_; lean_object* v___x_213_; 
v_toApplicative_207_ = lean_ctor_get(v_inst_204_, 0);
lean_inc_ref(v_toApplicative_207_);
v_toBind_208_ = lean_ctor_get(v_inst_204_, 1);
lean_inc(v_toBind_208_);
lean_dec_ref(v_inst_204_);
v_getEnv_209_ = lean_ctor_get(v_inst_205_, 0);
lean_inc(v_getEnv_209_);
lean_dec_ref(v_inst_205_);
v_toPure_210_ = lean_ctor_get(v_toApplicative_207_, 1);
lean_inc(v_toPure_210_);
lean_dec_ref(v_toApplicative_207_);
v___x_211_ = lean_box(1);
v___f_212_ = lean_alloc_closure((void*)(l_Lean_Options_toLinterOptions___redArg___lam__0), 4, 3);
lean_closure_set(v___f_212_, 0, v___x_211_);
lean_closure_set(v___f_212_, 1, v_o_206_);
lean_closure_set(v___f_212_, 2, v_toPure_210_);
v___x_213_ = lean_apply_4(v_toBind_208_, lean_box(0), lean_box(0), v_getEnv_209_, v___f_212_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Options_toLinterOptions(lean_object* v_m_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_o_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Lean_Options_toLinterOptions___redArg(v_inst_215_, v_inst_216_, v_o_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg(lean_object* v_o_219_, lean_object* v_opt_220_){
_start:
{
lean_object* v_linterSets_221_; lean_object* v_name_222_; lean_object* v___x_223_; lean_object* v___x_224_; 
v_linterSets_221_ = lean_ctor_get(v_o_219_, 1);
v_name_222_ = lean_ctor_get(v_opt_220_, 0);
v___x_223_ = ((lean_object*)(l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_Linter_insertLinterSetEntry_spec__1_spec__1___closed__0));
v___x_224_ = l_Std_DTreeMap_Internal_Impl_Const_getD___at___00Lean_Linter_insertLinterSetEntry_spec__0___redArg(v_linterSets_221_, v_name_222_, v___x_223_);
return v___x_224_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___redArg___boxed(lean_object* v_o_225_, lean_object* v_opt_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_225_, v_opt_226_);
lean_dec_ref(v_opt_226_);
lean_dec_ref(v_o_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet(lean_object* v_00_u03b1_228_, lean_object* v_o_229_, lean_object* v_opt_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_229_, v_opt_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_getSet___boxed(lean_object* v_00_u03b1_232_, lean_object* v_o_233_, lean_object* v_opt_234_){
_start:
{
lean_object* v_res_235_; 
v_res_235_ = l_Lean_Linter_LinterOptions_getSet(v_00_u03b1_232_, v_o_233_, v_opt_234_);
lean_dec_ref(v_opt_234_);
lean_dec_ref(v_o_233_);
return v_res_235_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg___lam__0(lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_____do__lift_238_){
_start:
{
lean_object* v___x_239_; 
v___x_239_ = l_Lean_Options_toLinterOptions___redArg(v_inst_236_, v_inst_237_, v_____do__lift_238_);
return v___x_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions___redArg(lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_inst_242_){
_start:
{
lean_object* v_toBind_243_; lean_object* v___f_244_; lean_object* v___x_245_; 
v_toBind_243_ = lean_ctor_get(v_inst_240_, 1);
lean_inc(v_toBind_243_);
v___f_244_ = lean_alloc_closure((void*)(l_Lean_Linter_getLinterOptions___redArg___lam__0), 3, 2);
lean_closure_set(v___f_244_, 0, v_inst_240_);
lean_closure_set(v___f_244_, 1, v_inst_242_);
v___x_245_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v_inst_241_, v___f_244_);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterOptions(lean_object* v_m_246_, lean_object* v_inst_247_, lean_object* v_inst_248_, lean_object* v_inst_249_){
_start:
{
lean_object* v___x_250_; 
v___x_250_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_247_, v_inst_248_, v_inst_249_);
return v___x_250_;
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__spec__0(lean_object* v_name_251_, lean_object* v_decl_252_, lean_object* v_ref_253_){
_start:
{
lean_object* v_defValue_255_; lean_object* v_descr_256_; lean_object* v___x_258_; uint8_t v_isShared_259_; uint8_t v_isSharedCheck_283_; 
v_defValue_255_ = lean_ctor_get(v_decl_252_, 0);
v_descr_256_ = lean_ctor_get(v_decl_252_, 1);
v_isSharedCheck_283_ = !lean_is_exclusive(v_decl_252_);
if (v_isSharedCheck_283_ == 0)
{
v___x_258_ = v_decl_252_;
v_isShared_259_ = v_isSharedCheck_283_;
goto v_resetjp_257_;
}
else
{
lean_inc(v_descr_256_);
lean_inc(v_defValue_255_);
lean_dec(v_decl_252_);
v___x_258_ = lean_box(0);
v_isShared_259_ = v_isSharedCheck_283_;
goto v_resetjp_257_;
}
v_resetjp_257_:
{
lean_object* v___x_260_; uint8_t v___x_261_; lean_object* v___x_262_; lean_object* v___x_263_; 
v___x_260_ = lean_alloc_ctor(1, 0, 1);
v___x_261_ = lean_unbox(v_defValue_255_);
lean_ctor_set_uint8(v___x_260_, 0, v___x_261_);
lean_inc(v_name_251_);
v___x_262_ = lean_alloc_ctor(0, 4, 0);
lean_ctor_set(v___x_262_, 0, v_name_251_);
lean_ctor_set(v___x_262_, 1, v_ref_253_);
lean_ctor_set(v___x_262_, 2, v___x_260_);
lean_ctor_set(v___x_262_, 3, v_descr_256_);
lean_inc(v_name_251_);
v___x_263_ = lean_register_option(v_name_251_, v___x_262_);
if (lean_obj_tag(v___x_263_) == 0)
{
lean_object* v___x_265_; uint8_t v_isShared_266_; uint8_t v_isSharedCheck_273_; 
v_isSharedCheck_273_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_273_ == 0)
{
lean_object* v_unused_274_; 
v_unused_274_ = lean_ctor_get(v___x_263_, 0);
lean_dec(v_unused_274_);
v___x_265_ = v___x_263_;
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
else
{
lean_dec(v___x_263_);
v___x_265_ = lean_box(0);
v_isShared_266_ = v_isSharedCheck_273_;
goto v_resetjp_264_;
}
v_resetjp_264_:
{
lean_object* v___x_268_; 
if (v_isShared_259_ == 0)
{
lean_ctor_set(v___x_258_, 1, v_defValue_255_);
lean_ctor_set(v___x_258_, 0, v_name_251_);
v___x_268_ = v___x_258_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_name_251_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_defValue_255_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_270_; 
if (v_isShared_266_ == 0)
{
lean_ctor_set(v___x_265_, 0, v___x_268_);
v___x_270_ = v___x_265_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
else
{
lean_object* v_a_275_; lean_object* v___x_277_; uint8_t v_isShared_278_; uint8_t v_isSharedCheck_282_; 
lean_del_object(v___x_258_);
lean_dec(v_defValue_255_);
lean_dec(v_name_251_);
v_a_275_ = lean_ctor_get(v___x_263_, 0);
v_isSharedCheck_282_ = !lean_is_exclusive(v___x_263_);
if (v_isSharedCheck_282_ == 0)
{
v___x_277_ = v___x_263_;
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
else
{
lean_inc(v_a_275_);
lean_dec(v___x_263_);
v___x_277_ = lean_box(0);
v_isShared_278_ = v_isSharedCheck_282_;
goto v_resetjp_276_;
}
v_resetjp_276_:
{
lean_object* v___x_280_; 
if (v_isShared_278_ == 0)
{
v___x_280_ = v___x_277_;
goto v_reusejp_279_;
}
else
{
lean_object* v_reuseFailAlloc_281_; 
v_reuseFailAlloc_281_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_281_, 0, v_a_275_);
v___x_280_ = v_reuseFailAlloc_281_;
goto v_reusejp_279_;
}
v_reusejp_279_:
{
return v___x_280_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_284_, lean_object* v_decl_285_, lean_object* v_ref_286_, lean_object* v_a_287_){
_start:
{
lean_object* v_res_288_; 
v_res_288_ = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__spec__0(v_name_284_, v_decl_285_, v_ref_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_305_; lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; 
v___x_305_ = ((lean_object*)(l_Lean_Linter_initFn___closed__2_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_));
v___x_306_ = ((lean_object*)(l_Lean_Linter_initFn___closed__4_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_));
v___x_307_ = ((lean_object*)(l_Lean_Linter_initFn___closed__5_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_));
v___x_308_ = l_Lean_Option_register___at___00Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4__spec__0(v___x_305_, v___x_306_, v___x_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4____boxed(lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_();
return v_res_310_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(lean_object* v_o_311_, lean_object* v_k_312_, uint8_t v_defVal_313_){
_start:
{
lean_object* v_toOptions_314_; lean_object* v_map_315_; lean_object* v___x_316_; 
v_toOptions_314_ = lean_ctor_get(v_o_311_, 0);
v_map_315_ = lean_ctor_get(v_toOptions_314_, 0);
v___x_316_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_315_, v_k_312_);
if (lean_obj_tag(v___x_316_) == 0)
{
return v_defVal_313_;
}
else
{
lean_object* v_val_317_; 
v_val_317_ = lean_ctor_get(v___x_316_, 0);
lean_inc(v_val_317_);
lean_dec_ref(v___x_316_);
if (lean_obj_tag(v_val_317_) == 1)
{
uint8_t v_v_318_; 
v_v_318_ = lean_ctor_get_uint8(v_val_317_, 0);
lean_dec_ref(v_val_317_);
return v_v_318_;
}
else
{
lean_dec(v_val_317_);
return v_defVal_313_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0___boxed(lean_object* v_o_319_, lean_object* v_k_320_, lean_object* v_defVal_321_){
_start:
{
uint8_t v_defVal_boxed_322_; uint8_t v_res_323_; lean_object* v_r_324_; 
v_defVal_boxed_322_ = lean_unbox(v_defVal_321_);
v_res_323_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_319_, v_k_320_, v_defVal_boxed_322_);
lean_dec(v_k_320_);
lean_dec_ref(v_o_319_);
v_r_324_ = lean_box(v_res_323_);
return v_r_324_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterAll(lean_object* v_o_325_, uint8_t v_defValue_326_){
_start:
{
lean_object* v___x_327_; lean_object* v_name_328_; uint8_t v___x_329_; 
v___x_327_ = l_Lean_Linter_linter_all;
v_name_328_ = lean_ctor_get(v___x_327_, 0);
lean_inc(v_name_328_);
v___x_329_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_325_, v_name_328_, v_defValue_326_);
lean_dec(v_name_328_);
return v___x_329_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterAll___boxed(lean_object* v_o_330_, lean_object* v_defValue_331_){
_start:
{
uint8_t v_defValue_boxed_332_; uint8_t v_res_333_; lean_object* v_r_334_; 
v_defValue_boxed_332_ = lean_unbox(v_defValue_331_);
v_res_333_ = l_Lean_Linter_getLinterAll(v_o_330_, v_defValue_boxed_332_);
lean_dec_ref(v_o_330_);
v_r_334_ = lean_box(v_res_333_);
return v_r_334_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(lean_object* v_o_335_, lean_object* v_k_336_){
_start:
{
lean_object* v_toOptions_337_; lean_object* v_map_338_; lean_object* v___x_339_; 
v_toOptions_337_ = lean_ctor_get(v_o_335_, 0);
v_map_338_ = lean_ctor_get(v_toOptions_337_, 0);
v___x_339_ = l_Std_DTreeMap_Internal_Impl_Const_get_x3f___at___00Lean_NameMap_find_x3f_spec__0___redArg(v_map_338_, v_k_336_);
if (lean_obj_tag(v___x_339_) == 0)
{
lean_object* v___x_340_; 
v___x_340_ = lean_box(0);
return v___x_340_;
}
else
{
lean_object* v_val_341_; lean_object* v___x_343_; uint8_t v_isShared_344_; uint8_t v_isSharedCheck_351_; 
v_val_341_ = lean_ctor_get(v___x_339_, 0);
v_isSharedCheck_351_ = !lean_is_exclusive(v___x_339_);
if (v_isSharedCheck_351_ == 0)
{
v___x_343_ = v___x_339_;
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
else
{
lean_inc(v_val_341_);
lean_dec(v___x_339_);
v___x_343_ = lean_box(0);
v_isShared_344_ = v_isSharedCheck_351_;
goto v_resetjp_342_;
}
v_resetjp_342_:
{
if (lean_obj_tag(v_val_341_) == 1)
{
uint8_t v_v_345_; lean_object* v___x_346_; lean_object* v___x_348_; 
v_v_345_ = lean_ctor_get_uint8(v_val_341_, 0);
lean_dec_ref(v_val_341_);
v___x_346_ = lean_box(v_v_345_);
if (v_isShared_344_ == 0)
{
lean_ctor_set(v___x_343_, 0, v___x_346_);
v___x_348_ = v___x_343_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v___x_346_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
else
{
lean_object* v___x_350_; 
lean_del_object(v___x_343_);
lean_dec(v_val_341_);
v___x_350_ = lean_box(0);
return v___x_350_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0___boxed(lean_object* v_o_352_, lean_object* v_k_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(v_o_352_, v_k_353_);
lean_dec(v_k_353_);
lean_dec_ref(v_o_352_);
return v_res_354_;
}
}
LEAN_EXPORT uint8_t l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1(lean_object* v_x_355_, lean_object* v_x_356_){
_start:
{
if (lean_obj_tag(v_x_355_) == 0)
{
if (lean_obj_tag(v_x_356_) == 0)
{
uint8_t v___x_357_; 
v___x_357_ = 1;
return v___x_357_;
}
else
{
uint8_t v___x_358_; 
v___x_358_ = 0;
return v___x_358_;
}
}
else
{
if (lean_obj_tag(v_x_356_) == 0)
{
uint8_t v___x_359_; 
v___x_359_ = 0;
return v___x_359_;
}
else
{
lean_object* v_val_360_; uint8_t v___x_361_; 
v_val_360_ = lean_ctor_get(v_x_355_, 0);
v___x_361_ = lean_unbox(v_val_360_);
if (v___x_361_ == 0)
{
lean_object* v_val_362_; uint8_t v___x_363_; 
v_val_362_ = lean_ctor_get(v_x_356_, 0);
v___x_363_ = lean_unbox(v_val_362_);
if (v___x_363_ == 0)
{
uint8_t v___x_364_; 
v___x_364_ = 1;
return v___x_364_;
}
else
{
uint8_t v___x_365_; 
v___x_365_ = lean_unbox(v_val_360_);
return v___x_365_;
}
}
else
{
lean_object* v_val_366_; uint8_t v___x_367_; 
v_val_366_ = lean_ctor_get(v_x_356_, 0);
v___x_367_ = lean_unbox(v_val_366_);
return v___x_367_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1___boxed(lean_object* v_x_368_, lean_object* v_x_369_){
_start:
{
uint8_t v_res_370_; lean_object* v_r_371_; 
v_res_370_ = l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1(v_x_368_, v_x_369_);
lean_dec(v_x_369_);
lean_dec(v_x_368_);
v_r_371_ = lean_box(v_res_370_);
return v_r_371_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(lean_object* v_o_375_, lean_object* v_as_376_, size_t v_i_377_, size_t v_stop_378_){
_start:
{
uint8_t v___x_379_; 
v___x_379_ = lean_usize_dec_eq(v_i_377_, v_stop_378_);
if (v___x_379_ == 0)
{
uint8_t v___x_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; uint8_t v___x_384_; 
v___x_380_ = 1;
v___x_381_ = lean_array_uget_borrowed(v_as_376_, v_i_377_);
v___x_382_ = l_Lean_Linter_LinterOptions_get_x3f___at___00Lean_Linter_getLinterValue_spec__0(v_o_375_, v___x_381_);
v___x_383_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___closed__0));
v___x_384_ = l_Option_instBEq_beq___at___00Lean_Linter_getLinterValue_spec__1(v___x_382_, v___x_383_);
lean_dec(v___x_382_);
if (v___x_384_ == 0)
{
size_t v___x_385_; size_t v___x_386_; 
v___x_385_ = ((size_t)1ULL);
v___x_386_ = lean_usize_add(v_i_377_, v___x_385_);
v_i_377_ = v___x_386_;
goto _start;
}
else
{
return v___x_380_;
}
}
else
{
uint8_t v___x_388_; 
v___x_388_ = 0;
return v___x_388_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2___boxed(lean_object* v_o_389_, lean_object* v_as_390_, lean_object* v_i_391_, lean_object* v_stop_392_){
_start:
{
size_t v_i_boxed_393_; size_t v_stop_boxed_394_; uint8_t v_res_395_; lean_object* v_r_396_; 
v_i_boxed_393_ = lean_unbox_usize(v_i_391_);
lean_dec(v_i_391_);
v_stop_boxed_394_ = lean_unbox_usize(v_stop_392_);
lean_dec(v_stop_392_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_389_, v_as_390_, v_i_boxed_393_, v_stop_boxed_394_);
lean_dec_ref(v_as_390_);
lean_dec_ref(v_o_389_);
v_r_396_ = lean_box(v_res_395_);
return v_r_396_;
}
}
LEAN_EXPORT uint8_t l_Lean_Linter_getLinterValue(lean_object* v_opt_397_, lean_object* v_o_398_){
_start:
{
lean_object* v_name_399_; lean_object* v_defValue_400_; uint8_t v___y_402_; lean_object* v___x_405_; lean_object* v___x_406_; lean_object* v___x_407_; uint8_t v___x_408_; 
v_name_399_ = lean_ctor_get(v_opt_397_, 0);
v_defValue_400_ = lean_ctor_get(v_opt_397_, 1);
v___x_405_ = l_Lean_Linter_LinterOptions_getSet___redArg(v_o_398_, v_opt_397_);
v___x_406_ = lean_unsigned_to_nat(0u);
v___x_407_ = lean_array_get_size(v___x_405_);
v___x_408_ = lean_nat_dec_lt(v___x_406_, v___x_407_);
if (v___x_408_ == 0)
{
uint8_t v___x_409_; 
lean_dec_ref(v___x_405_);
v___x_409_ = lean_unbox(v_defValue_400_);
v___y_402_ = v___x_409_;
goto v___jp_401_;
}
else
{
if (v___x_408_ == 0)
{
uint8_t v___x_410_; 
lean_dec_ref(v___x_405_);
v___x_410_ = lean_unbox(v_defValue_400_);
v___y_402_ = v___x_410_;
goto v___jp_401_;
}
else
{
size_t v___x_411_; size_t v___x_412_; uint8_t v___x_413_; 
v___x_411_ = ((size_t)0ULL);
v___x_412_ = lean_usize_of_nat(v___x_407_);
v___x_413_ = l___private_Init_Data_Array_Basic_0__Array_anyMUnsafe_any___at___00Lean_Linter_getLinterValue_spec__2(v_o_398_, v___x_405_, v___x_411_, v___x_412_);
lean_dec_ref(v___x_405_);
if (v___x_413_ == 0)
{
uint8_t v___x_414_; 
v___x_414_ = lean_unbox(v_defValue_400_);
v___y_402_ = v___x_414_;
goto v___jp_401_;
}
else
{
v___y_402_ = v___x_413_;
goto v___jp_401_;
}
}
}
v___jp_401_:
{
uint8_t v___x_403_; uint8_t v___x_404_; 
v___x_403_ = l_Lean_Linter_getLinterAll(v_o_398_, v___y_402_);
v___x_404_ = l_Lean_Linter_LinterOptions_get___at___00Lean_Linter_getLinterAll_spec__0(v_o_398_, v_name_399_, v___x_403_);
return v___x_404_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_getLinterValue___boxed(lean_object* v_opt_415_, lean_object* v_o_416_){
_start:
{
uint8_t v_res_417_; lean_object* v_r_418_; 
v_res_417_ = l_Lean_Linter_getLinterValue(v_opt_415_, v_o_416_);
lean_dec_ref(v_o_416_);
lean_dec_ref(v_opt_415_);
v_r_418_ = lean_box(v_res_417_);
return v_r_418_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___redArg___closed__1(void){
_start:
{
lean_object* v___x_420_; lean_object* v___x_421_; 
v___x_420_ = ((lean_object*)(l_Lean_Linter_logLint___redArg___closed__0));
v___x_421_ = l_Lean_stringToMessageData(v___x_420_);
return v___x_421_;
}
}
static lean_object* _init_l_Lean_Linter_logLint___redArg___closed__3(void){
_start:
{
lean_object* v___x_423_; lean_object* v___x_424_; 
v___x_423_ = ((lean_object*)(l_Lean_Linter_logLint___redArg___closed__2));
v___x_424_ = l_Lean_stringToMessageData(v___x_423_);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint___redArg(lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_linterOption_429_, lean_object* v_stx_430_, lean_object* v_msg_431_){
_start:
{
lean_object* v_name_432_; lean_object* v___x_434_; uint8_t v_isShared_435_; uint8_t v_isSharedCheck_447_; 
v_name_432_ = lean_ctor_get(v_linterOption_429_, 0);
v_isSharedCheck_447_ = !lean_is_exclusive(v_linterOption_429_);
if (v_isSharedCheck_447_ == 0)
{
lean_object* v_unused_448_; 
v_unused_448_ = lean_ctor_get(v_linterOption_429_, 1);
lean_dec(v_unused_448_);
v___x_434_ = v_linterOption_429_;
v_isShared_435_ = v_isSharedCheck_447_;
goto v_resetjp_433_;
}
else
{
lean_inc(v_name_432_);
lean_dec(v_linterOption_429_);
v___x_434_ = lean_box(0);
v_isShared_435_ = v_isSharedCheck_447_;
goto v_resetjp_433_;
}
v_resetjp_433_:
{
lean_object* v___x_436_; lean_object* v___x_437_; lean_object* v___x_439_; 
v___x_436_ = lean_obj_once(&l_Lean_Linter_logLint___redArg___closed__1, &l_Lean_Linter_logLint___redArg___closed__1_once, _init_l_Lean_Linter_logLint___redArg___closed__1);
lean_inc(v_name_432_);
v___x_437_ = l_Lean_MessageData_ofName(v_name_432_);
if (v_isShared_435_ == 0)
{
lean_ctor_set_tag(v___x_434_, 7);
lean_ctor_set(v___x_434_, 1, v___x_437_);
lean_ctor_set(v___x_434_, 0, v___x_436_);
v___x_439_ = v___x_434_;
goto v_reusejp_438_;
}
else
{
lean_object* v_reuseFailAlloc_446_; 
v_reuseFailAlloc_446_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_446_, 0, v___x_436_);
lean_ctor_set(v_reuseFailAlloc_446_, 1, v___x_437_);
v___x_439_ = v_reuseFailAlloc_446_;
goto v_reusejp_438_;
}
v_reusejp_438_:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v_disable_442_; lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; 
v___x_440_ = lean_obj_once(&l_Lean_Linter_logLint___redArg___closed__3, &l_Lean_Linter_logLint___redArg___closed__3_once, _init_l_Lean_Linter_logLint___redArg___closed__3);
v___x_441_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_441_, 0, v___x_439_);
lean_ctor_set(v___x_441_, 1, v___x_440_);
v_disable_442_ = l_Lean_MessageData_note(v___x_441_);
v___x_443_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v___x_443_, 0, v_msg_431_);
lean_ctor_set(v___x_443_, 1, v_disable_442_);
v___x_444_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v___x_444_, 0, v_name_432_);
lean_ctor_set(v___x_444_, 1, v___x_443_);
v___x_445_ = l_Lean_logWarningAt___redArg(v_inst_425_, v_inst_426_, v_inst_427_, v_inst_428_, v_stx_430_, v___x_444_);
return v___x_445_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLint(lean_object* v_m_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_linterOption_454_, lean_object* v_stx_455_, lean_object* v_msg_456_){
_start:
{
lean_object* v___x_457_; 
v___x_457_ = l_Lean_Linter_logLint___redArg(v_inst_450_, v_inst_451_, v_inst_452_, v_inst_453_, v_linterOption_454_, v_stx_455_, v_msg_456_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0(lean_object* v_linterOption_458_, lean_object* v_toApplicative_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_stx_464_, lean_object* v_msg_465_, lean_object* v_____do__lift_466_){
_start:
{
uint8_t v___x_467_; 
v___x_467_ = l_Lean_Linter_getLinterValue(v_linterOption_458_, v_____do__lift_466_);
if (v___x_467_ == 0)
{
lean_object* v_toPure_468_; lean_object* v___x_469_; lean_object* v___x_470_; 
lean_dec_ref(v_msg_465_);
lean_dec(v_stx_464_);
lean_dec(v_inst_463_);
lean_dec(v_inst_462_);
lean_dec_ref(v_inst_461_);
lean_dec_ref(v_inst_460_);
lean_dec_ref(v_linterOption_458_);
v_toPure_468_ = lean_ctor_get(v_toApplicative_459_, 1);
lean_inc(v_toPure_468_);
lean_dec_ref(v_toApplicative_459_);
v___x_469_ = lean_box(0);
v___x_470_ = lean_apply_2(v_toPure_468_, lean_box(0), v___x_469_);
return v___x_470_;
}
else
{
lean_object* v___x_471_; 
lean_dec_ref(v_toApplicative_459_);
v___x_471_ = l_Lean_Linter_logLint___redArg(v_inst_460_, v_inst_461_, v_inst_462_, v_inst_463_, v_linterOption_458_, v_stx_464_, v_msg_465_);
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg___lam__0___boxed(lean_object* v_linterOption_472_, lean_object* v_toApplicative_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_stx_478_, lean_object* v_msg_479_, lean_object* v_____do__lift_480_){
_start:
{
lean_object* v_res_481_; 
v_res_481_ = l_Lean_Linter_logLintIf___redArg___lam__0(v_linterOption_472_, v_toApplicative_473_, v_inst_474_, v_inst_475_, v_inst_476_, v_inst_477_, v_stx_478_, v_msg_479_, v_____do__lift_480_);
lean_dec_ref(v_____do__lift_480_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf___redArg(lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_linterOption_487_, lean_object* v_stx_488_, lean_object* v_msg_489_){
_start:
{
lean_object* v_toApplicative_490_; lean_object* v_toBind_491_; lean_object* v___f_492_; lean_object* v___x_493_; lean_object* v___x_494_; 
v_toApplicative_490_ = lean_ctor_get(v_inst_482_, 0);
v_toBind_491_ = lean_ctor_get(v_inst_482_, 1);
lean_inc(v_toBind_491_);
lean_inc(v_inst_485_);
lean_inc_ref(v_inst_482_);
lean_inc_ref(v_toApplicative_490_);
v___f_492_ = lean_alloc_closure((void*)(l_Lean_Linter_logLintIf___redArg___lam__0___boxed), 9, 8);
lean_closure_set(v___f_492_, 0, v_linterOption_487_);
lean_closure_set(v___f_492_, 1, v_toApplicative_490_);
lean_closure_set(v___f_492_, 2, v_inst_482_);
lean_closure_set(v___f_492_, 3, v_inst_483_);
lean_closure_set(v___f_492_, 4, v_inst_484_);
lean_closure_set(v___f_492_, 5, v_inst_485_);
lean_closure_set(v___f_492_, 6, v_stx_488_);
lean_closure_set(v___f_492_, 7, v_msg_489_);
v___x_493_ = l_Lean_Linter_getLinterOptions___redArg(v_inst_482_, v_inst_485_, v_inst_486_);
v___x_494_ = lean_apply_4(v_toBind_491_, lean_box(0), lean_box(0), v___x_493_, v___f_492_);
return v___x_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Linter_logLintIf(lean_object* v_m_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_linterOption_501_, lean_object* v_stx_502_, lean_object* v_msg_503_){
_start:
{
lean_object* v___x_504_; 
v___x_504_ = l_Lean_Linter_logLintIf___redArg(v_inst_496_, v_inst_497_, v_inst_498_, v_inst_499_, v_inst_500_, v_linterOption_501_, v_stx_502_, v_msg_503_);
return v___x_504_;
}
}
lean_object* runtime_initialize_Lean_MonadEnv(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Function(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Linter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_Lean_Linter_instEmptyCollectionLinterSets = _init_l_Lean_Linter_instEmptyCollectionLinterSets();
lean_mark_persistent(l_Lean_Linter_instEmptyCollectionLinterSets);
l_Lean_Linter_instInhabitedLinterSets = _init_l_Lean_Linter_instInhabitedLinterSets();
lean_mark_persistent(l_Lean_Linter_instInhabitedLinterSets);
res = l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_1102181608____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linterSetsExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linterSetsExt);
lean_dec_ref(res);
res = l_Lean_Linter_initFn_00___x40_Lean_Linter_Basic_3413348210____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Linter_linter_all = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Linter_linter_all);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Linter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_MonadEnv(uint8_t builtin);
lean_object* initialize_Init_Data_Function(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Linter_Basic(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_MonadEnv(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Function(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Linter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Linter_Basic(builtin);
}
#ifdef __cplusplus
}
#endif
