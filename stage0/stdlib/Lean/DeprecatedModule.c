// Lean compiler output
// Module: Lean.DeprecatedModule
// Imports: public import Lean.Compiler.ModPkgExt
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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr3(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr4(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_register_option(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_registerModuleEnvExtension___redArg(lean_object*, lean_object*);
lean_object* l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(lean_object*, uint8_t);
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
extern lean_object* l_Lean_instInhabitedModuleData_default;
lean_object* l_Lean_Environment_header(lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_PersistentEnvExtension_setState___redArg(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedDeprecatedModuleEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_instInhabitedDeprecatedModuleEntry_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedDeprecatedModuleEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedDeprecatedModuleEntry_default = (const lean_object*)&l_Lean_instInhabitedDeprecatedModuleEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedDeprecatedModuleEntry = (const lean_object*)&l_Lean_instInhabitedDeprecatedModuleEntry_default___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "linter"};
static const lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 11, .m_capacity = 11, .m_length = 10, .m_data = "deprecated"};
static const lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 7, .m_capacity = 7, .m_length = 6, .m_data = "module"};
static const lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(186, 218, 113, 226, 101, 176, 32, 79)}};
static const lean_ctor_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(227, 99, 57, 49, 46, 156, 253, 187)}};
static const lean_ctor_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(63, 185, 113, 121, 126, 234, 80, 96)}};
static const lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__4_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 61, .m_capacity = 61, .m_length = 60, .m_data = "if true, generate warnings when importing deprecated modules"};
static const lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__4_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__4_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__5_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1)),((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__4_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__5_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__5_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value;
static const lean_string_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__6_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__6_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__6_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value;
static const lean_ctor_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__6_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_1 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_0),((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(219, 182, 224, 198, 198, 122, 225, 30)}};
static const lean_ctor_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_2 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_1),((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(46, 222, 165, 126, 146, 126, 79, 254)}};
static const lean_ctor_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value_aux_2),((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(102, 206, 7, 61, 37, 149, 52, 137)}};
static const lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_ = (const lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value;
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_();
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_linter_deprecated_module;
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "deprecatedModuleExt"};
static const lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__6_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__1_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(112, 167, 11, 228, 166, 253, 145, 197)}};
static const lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_deprecatedModuleExt;
LEAN_EXPORT lean_object* l_Lean_Environment_getDeprecatedModuleByIdx_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getDeprecatedModuleByIdx_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_setDeprecatedModule(lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 8, .m_capacity = 8, .m_length = 7, .m_data = "import "};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__0_value;
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "\n"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Init"};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__0 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__0_value;
static const lean_ctor_object l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__0_value),LEAN_SCALAR_PTR_LITERAL(152, 102, 12, 179, 200, 220, 30, 26)}};
static const lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__1 = (const lean_object*)&l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__1_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_string_object l_Lean_formatDeprecatedModuleWarning___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "\n'"};
static const lean_object* l_Lean_formatDeprecatedModuleWarning___closed__0 = (const lean_object*)&l_Lean_formatDeprecatedModuleWarning___closed__0_value;
static const lean_string_object l_Lean_formatDeprecatedModuleWarning___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 55, .m_capacity = 55, .m_length = 54, .m_data = "' has been deprecated: please replace this import by\n\n"};
static const lean_object* l_Lean_formatDeprecatedModuleWarning___closed__1 = (const lean_object*)&l_Lean_formatDeprecatedModuleWarning___closed__1_value;
static const lean_string_object l_Lean_formatDeprecatedModuleWarning___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_Lean_formatDeprecatedModuleWarning___closed__2 = (const lean_object*)&l_Lean_formatDeprecatedModuleWarning___closed__2_value;
static const lean_array_object l_Lean_formatDeprecatedModuleWarning___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_formatDeprecatedModuleWarning___closed__3 = (const lean_object*)&l_Lean_formatDeprecatedModuleWarning___closed__3_value;
LEAN_EXPORT lean_object* l_Lean_formatDeprecatedModuleWarning(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_formatDeprecatedModuleWarning___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0(lean_object* v_name_5_, lean_object* v_decl_6_, lean_object* v_ref_7_){
_start:
{
lean_object* v_defValue_9_; lean_object* v_descr_10_; lean_object* v_deprecation_x3f_11_; lean_object* v___x_12_; uint8_t v___x_13_; lean_object* v___x_14_; lean_object* v___x_15_; 
v_defValue_9_ = lean_ctor_get(v_decl_6_, 0);
v_descr_10_ = lean_ctor_get(v_decl_6_, 1);
v_deprecation_x3f_11_ = lean_ctor_get(v_decl_6_, 2);
v___x_12_ = lean_alloc_ctor(1, 0, 1);
v___x_13_ = lean_unbox(v_defValue_9_);
lean_ctor_set_uint8(v___x_12_, 0, v___x_13_);
lean_inc(v_deprecation_x3f_11_);
lean_inc_ref(v_descr_10_);
lean_inc_n(v_name_5_, 2);
v___x_14_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_14_, 0, v_name_5_);
lean_ctor_set(v___x_14_, 1, v_ref_7_);
lean_ctor_set(v___x_14_, 2, v___x_12_);
lean_ctor_set(v___x_14_, 3, v_descr_10_);
lean_ctor_set(v___x_14_, 4, v_deprecation_x3f_11_);
v___x_15_ = lean_register_option(v_name_5_, v___x_14_);
if (lean_obj_tag(v___x_15_) == 0)
{
lean_object* v___x_17_; uint8_t v_isShared_18_; uint8_t v_isSharedCheck_23_; 
v_isSharedCheck_23_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_23_ == 0)
{
lean_object* v_unused_24_; 
v_unused_24_ = lean_ctor_get(v___x_15_, 0);
lean_dec(v_unused_24_);
v___x_17_ = v___x_15_;
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
else
{
lean_dec(v___x_15_);
v___x_17_ = lean_box(0);
v_isShared_18_ = v_isSharedCheck_23_;
goto v_resetjp_16_;
}
v_resetjp_16_:
{
lean_object* v___x_19_; lean_object* v___x_21_; 
lean_inc(v_defValue_9_);
v___x_19_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_19_, 0, v_name_5_);
lean_ctor_set(v___x_19_, 1, v_defValue_9_);
if (v_isShared_18_ == 0)
{
lean_ctor_set(v___x_17_, 0, v___x_19_);
v___x_21_ = v___x_17_;
goto v_reusejp_20_;
}
else
{
lean_object* v_reuseFailAlloc_22_; 
v_reuseFailAlloc_22_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_22_, 0, v___x_19_);
v___x_21_ = v_reuseFailAlloc_22_;
goto v_reusejp_20_;
}
v_reusejp_20_:
{
return v___x_21_;
}
}
}
else
{
lean_object* v_a_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_32_; 
lean_dec(v_name_5_);
v_a_25_ = lean_ctor_get(v___x_15_, 0);
v_isSharedCheck_32_ = !lean_is_exclusive(v___x_15_);
if (v_isSharedCheck_32_ == 0)
{
v___x_27_ = v___x_15_;
v_isShared_28_ = v_isSharedCheck_32_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_a_25_);
lean_dec(v___x_15_);
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
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_33_, lean_object* v_decl_34_, lean_object* v_ref_35_, lean_object* v_a_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0(v_name_33_, v_decl_34_, v_ref_35_);
lean_dec_ref(v_decl_34_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v___x_58_ = ((lean_object*)(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_));
v___x_59_ = ((lean_object*)(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__5_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_));
v___x_61_ = l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0(v___x_58_, v___x_59_, v___x_60_);
return v___x_61_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4____boxed(lean_object* v_a_62_){
_start:
{
lean_object* v_res_63_; 
v_res_63_ = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_();
return v_res_63_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_(lean_object* v___x_64_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2____boxed(lean_object* v___x_67_, lean_object* v___y_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_(v___x_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v___f_77_ = ((lean_object*)(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_));
v___x_78_ = ((lean_object*)(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_));
v___x_79_ = l_Lean_registerModuleEnvExtension___redArg(v___f_77_, v___x_78_);
return v___x_79_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2____boxed(lean_object* v_a_80_){
_start:
{
lean_object* v_res_81_; 
v_res_81_ = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_();
return v_res_81_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getDeprecatedModuleByIdx_x3f(lean_object* v_env_82_, lean_object* v_idx_83_){
_start:
{
lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v___x_84_ = lean_box(0);
v___x_85_ = l_Lean_deprecatedModuleExt;
v___x_86_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(v___x_84_, v___x_85_, v_env_82_, v_idx_83_);
if (lean_obj_tag(v___x_86_) == 0)
{
return v___x_84_;
}
else
{
lean_object* v_val_87_; 
v_val_87_ = lean_ctor_get(v___x_86_, 0);
lean_inc(v_val_87_);
lean_dec_ref(v___x_86_);
return v_val_87_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getDeprecatedModuleByIdx_x3f___boxed(lean_object* v_env_88_, lean_object* v_idx_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_Lean_Environment_getDeprecatedModuleByIdx_x3f(v_env_88_, v_idx_89_);
lean_dec(v_idx_89_);
lean_dec_ref(v_env_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setDeprecatedModule(lean_object* v_entry_91_, lean_object* v_env_92_){
_start:
{
lean_object* v___x_93_; lean_object* v___x_94_; 
v___x_93_ = l_Lean_deprecatedModuleExt;
v___x_94_ = l_Lean_PersistentEnvExtension_setState___redArg(v___x_93_, v_env_92_, v_entry_91_);
return v___x_94_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(lean_object* v_as_97_, size_t v_i_98_, size_t v_stop_99_, lean_object* v_b_100_){
_start:
{
uint8_t v___x_101_; 
v___x_101_ = lean_usize_dec_eq(v_i_98_, v_stop_99_);
if (v___x_101_ == 0)
{
lean_object* v___x_102_; lean_object* v_module_103_; lean_object* v___x_104_; uint8_t v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; lean_object* v___x_110_; size_t v___x_111_; size_t v___x_112_; 
v___x_102_ = lean_array_uget_borrowed(v_as_97_, v_i_98_);
v_module_103_ = lean_ctor_get(v___x_102_, 0);
v___x_104_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__0));
v___x_105_ = 1;
lean_inc(v_module_103_);
v___x_106_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_103_, v___x_105_);
v___x_107_ = lean_string_append(v___x_104_, v___x_106_);
lean_dec_ref(v___x_106_);
v___x_108_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__1));
v___x_109_ = lean_string_append(v___x_107_, v___x_108_);
v___x_110_ = lean_string_append(v_b_100_, v___x_109_);
lean_dec_ref(v___x_109_);
v___x_111_ = ((size_t)1ULL);
v___x_112_ = lean_usize_add(v_i_98_, v___x_111_);
v_i_98_ = v___x_112_;
v_b_100_ = v___x_110_;
goto _start;
}
else
{
return v_b_100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___boxed(lean_object* v_as_114_, lean_object* v_i_115_, lean_object* v_stop_116_, lean_object* v_b_117_){
_start:
{
size_t v_i_boxed_118_; size_t v_stop_boxed_119_; lean_object* v_res_120_; 
v_i_boxed_118_ = lean_unbox_usize(v_i_115_);
lean_dec(v_i_115_);
v_stop_boxed_119_ = lean_unbox_usize(v_stop_116_);
lean_dec(v_stop_116_);
v_res_120_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(v_as_114_, v_i_boxed_118_, v_stop_boxed_119_, v_b_117_);
lean_dec_ref(v_as_114_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(lean_object* v_as_124_, size_t v_i_125_, size_t v_stop_126_, lean_object* v_b_127_){
_start:
{
lean_object* v___y_129_; uint8_t v___x_133_; 
v___x_133_ = lean_usize_dec_eq(v_i_125_, v_stop_126_);
if (v___x_133_ == 0)
{
lean_object* v___x_134_; lean_object* v_module_135_; lean_object* v___x_136_; uint8_t v___x_137_; 
v___x_134_ = lean_array_uget_borrowed(v_as_124_, v_i_125_);
v_module_135_ = lean_ctor_get(v___x_134_, 0);
v___x_136_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__1));
v___x_137_ = lean_name_eq(v_module_135_, v___x_136_);
if (v___x_137_ == 0)
{
lean_object* v___x_138_; 
lean_inc(v___x_134_);
v___x_138_ = lean_array_push(v_b_127_, v___x_134_);
v___y_129_ = v___x_138_;
goto v___jp_128_;
}
else
{
v___y_129_ = v_b_127_;
goto v___jp_128_;
}
}
else
{
return v_b_127_;
}
v___jp_128_:
{
size_t v___x_130_; size_t v___x_131_; 
v___x_130_ = ((size_t)1ULL);
v___x_131_ = lean_usize_add(v_i_125_, v___x_130_);
v_i_125_ = v___x_131_;
v_b_127_ = v___y_129_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___boxed(lean_object* v_as_139_, lean_object* v_i_140_, lean_object* v_stop_141_, lean_object* v_b_142_){
_start:
{
size_t v_i_boxed_143_; size_t v_stop_boxed_144_; lean_object* v_res_145_; 
v_i_boxed_143_ = lean_unbox_usize(v_i_140_);
lean_dec(v_i_140_);
v_stop_boxed_144_ = lean_unbox_usize(v_stop_141_);
lean_dec(v_stop_141_);
v_res_145_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(v_as_139_, v_i_boxed_143_, v_stop_boxed_144_, v_b_142_);
lean_dec_ref(v_as_139_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatDeprecatedModuleWarning(lean_object* v_env_151_, lean_object* v_idx_152_, lean_object* v_modName_153_, lean_object* v_entry_154_){
_start:
{
lean_object* v___y_156_; lean_object* v___y_157_; lean_object* v___y_167_; lean_object* v___y_168_; lean_object* v___y_169_; lean_object* v_message_x3f_180_; lean_object* v___x_181_; lean_object* v___y_183_; 
v_message_x3f_180_ = lean_ctor_get(v_entry_154_, 0);
lean_inc(v_message_x3f_180_);
lean_dec_ref(v_entry_154_);
v___x_181_ = l_Lean_instInhabitedModuleData_default;
if (lean_obj_tag(v_message_x3f_180_) == 0)
{
lean_object* v___x_199_; 
v___x_199_ = ((lean_object*)(l_Lean_formatDeprecatedModuleWarning___closed__2));
v___y_183_ = v___x_199_;
goto v___jp_182_;
}
else
{
lean_object* v_val_200_; 
v_val_200_ = lean_ctor_get(v_message_x3f_180_, 0);
lean_inc(v_val_200_);
lean_dec_ref(v_message_x3f_180_);
v___y_183_ = v_val_200_;
goto v___jp_182_;
}
v___jp_155_:
{
lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; lean_object* v___x_161_; lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_158_ = ((lean_object*)(l_Lean_formatDeprecatedModuleWarning___closed__0));
v___x_159_ = lean_string_append(v___y_156_, v___x_158_);
v___x_160_ = 1;
v___x_161_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_modName_153_, v___x_160_);
v___x_162_ = lean_string_append(v___x_159_, v___x_161_);
lean_dec_ref(v___x_161_);
v___x_163_ = ((lean_object*)(l_Lean_formatDeprecatedModuleWarning___closed__1));
v___x_164_ = lean_string_append(v___x_162_, v___x_163_);
v___x_165_ = lean_string_append(v___x_164_, v___y_157_);
lean_dec_ref(v___y_157_);
return v___x_165_;
}
v___jp_166_:
{
lean_object* v___x_170_; lean_object* v___x_171_; uint8_t v___x_172_; 
v___x_170_ = ((lean_object*)(l_Lean_formatDeprecatedModuleWarning___closed__2));
v___x_171_ = lean_array_get_size(v___y_169_);
v___x_172_ = lean_nat_dec_lt(v___y_167_, v___x_171_);
if (v___x_172_ == 0)
{
lean_dec_ref(v___y_169_);
v___y_156_ = v___y_168_;
v___y_157_ = v___x_170_;
goto v___jp_155_;
}
else
{
uint8_t v___x_173_; 
v___x_173_ = lean_nat_dec_le(v___x_171_, v___x_171_);
if (v___x_173_ == 0)
{
if (v___x_172_ == 0)
{
lean_dec_ref(v___y_169_);
v___y_156_ = v___y_168_;
v___y_157_ = v___x_170_;
goto v___jp_155_;
}
else
{
size_t v___x_174_; size_t v___x_175_; lean_object* v___x_176_; 
v___x_174_ = ((size_t)0ULL);
v___x_175_ = lean_usize_of_nat(v___x_171_);
v___x_176_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(v___y_169_, v___x_174_, v___x_175_, v___x_170_);
lean_dec_ref(v___y_169_);
v___y_156_ = v___y_168_;
v___y_157_ = v___x_176_;
goto v___jp_155_;
}
}
else
{
size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((size_t)0ULL);
v___x_178_ = lean_usize_of_nat(v___x_171_);
v___x_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(v___y_169_, v___x_177_, v___x_178_, v___x_170_);
lean_dec_ref(v___y_169_);
v___y_156_ = v___y_168_;
v___y_157_ = v___x_179_;
goto v___jp_155_;
}
}
}
v___jp_182_:
{
lean_object* v___x_184_; lean_object* v_moduleData_185_; lean_object* v___x_186_; lean_object* v_imports_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; uint8_t v___x_191_; 
v___x_184_ = l_Lean_Environment_header(v_env_151_);
v_moduleData_185_ = lean_ctor_get(v___x_184_, 6);
lean_inc_ref(v_moduleData_185_);
lean_dec_ref(v___x_184_);
v___x_186_ = lean_array_get(v___x_181_, v_moduleData_185_, v_idx_152_);
lean_dec_ref(v_moduleData_185_);
v_imports_187_ = lean_ctor_get(v___x_186_, 0);
lean_inc_ref(v_imports_187_);
lean_dec(v___x_186_);
v___x_188_ = lean_unsigned_to_nat(0u);
v___x_189_ = lean_array_get_size(v_imports_187_);
v___x_190_ = ((lean_object*)(l_Lean_formatDeprecatedModuleWarning___closed__3));
v___x_191_ = lean_nat_dec_lt(v___x_188_, v___x_189_);
if (v___x_191_ == 0)
{
lean_dec_ref(v_imports_187_);
v___y_167_ = v___x_188_;
v___y_168_ = v___y_183_;
v___y_169_ = v___x_190_;
goto v___jp_166_;
}
else
{
uint8_t v___x_192_; 
v___x_192_ = lean_nat_dec_le(v___x_189_, v___x_189_);
if (v___x_192_ == 0)
{
if (v___x_191_ == 0)
{
lean_dec_ref(v_imports_187_);
v___y_167_ = v___x_188_;
v___y_168_ = v___y_183_;
v___y_169_ = v___x_190_;
goto v___jp_166_;
}
else
{
size_t v___x_193_; size_t v___x_194_; lean_object* v___x_195_; 
v___x_193_ = ((size_t)0ULL);
v___x_194_ = lean_usize_of_nat(v___x_189_);
v___x_195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(v_imports_187_, v___x_193_, v___x_194_, v___x_190_);
lean_dec_ref(v_imports_187_);
v___y_167_ = v___x_188_;
v___y_168_ = v___y_183_;
v___y_169_ = v___x_195_;
goto v___jp_166_;
}
}
else
{
size_t v___x_196_; size_t v___x_197_; lean_object* v___x_198_; 
v___x_196_ = ((size_t)0ULL);
v___x_197_ = lean_usize_of_nat(v___x_189_);
v___x_198_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(v_imports_187_, v___x_196_, v___x_197_, v___x_190_);
lean_dec_ref(v_imports_187_);
v___y_167_ = v___x_188_;
v___y_168_ = v___y_183_;
v___y_169_ = v___x_198_;
goto v___jp_166_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_formatDeprecatedModuleWarning___boxed(lean_object* v_env_201_, lean_object* v_idx_202_, lean_object* v_modName_203_, lean_object* v_entry_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_Lean_formatDeprecatedModuleWarning(v_env_201_, v_idx_202_, v_modName_203_, v_entry_204_);
lean_dec(v_idx_202_);
lean_dec_ref(v_env_201_);
return v_res_205_;
}
}
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DeprecatedModule(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Compiler_ModPkgExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_();
if (lean_io_result_is_error(res)) return res;
l_Lean_linter_deprecated_module = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_linter_deprecated_module);
lean_dec_ref(res);
res = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_deprecatedModuleExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_deprecatedModuleExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_DeprecatedModule(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_DeprecatedModule(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Compiler_ModPkgExt(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_DeprecatedModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_DeprecatedModule(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_DeprecatedModule(builtin);
}
#ifdef __cplusplus
}
#endif
