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
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Lean_Environment_setDeprecatedModule___lam__0(lean_object*, lean_object*);
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
lean_object* l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0(lean_object* v_name_5_, lean_object* v_decl_6_, lean_object* v_ref_7_){
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
LEAN_EXPORT void l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_name_5_ = stack[0].m_obj;
lean_object* v_decl_6_ = stack[1].m_obj;
lean_object* v_ref_7_ = stack[2].m_obj;
lean_object* v_res_33_;
v_res_33_ = l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0(v_name_5_, v_decl_6_, v_ref_7_);
stack->m_obj
 = v_res_33_;
}
LEAN_EXPORT lean_object* l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0___boxed(lean_object* v_name_34_, lean_object* v_decl_35_, lean_object* v_ref_36_, lean_object* v_a_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0(v_name_34_, v_decl_35_, v_ref_36_);
lean_dec_ref(v_decl_35_);
return v_res_38_;
}
}
lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_(){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v___x_59_ = ((lean_object*)(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__3_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_));
v___x_60_ = ((lean_object*)(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__5_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_));
v___x_61_ = ((lean_object*)(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__7_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_));
v___x_62_ = l_Lean_Option_register___at___00__private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__spec__0(v___x_59_, v___x_60_, v___x_61_);
return v___x_62_;
}
}
LEAN_EXPORT void l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_63_;
v_res_63_ = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_();
stack->m_obj
 = v_res_63_;
}
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4____boxed(lean_object* v_a_64_){
_start:
{
lean_object* v_res_65_; 
v_res_65_ = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_2653774227____hygCtx___hyg_4_();
return v_res_65_;
}
}
lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_(lean_object* v___x_66_){
_start:
{
lean_object* v___x_68_; 
v___x_68_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_68_, 0, v___x_66_);
return v___x_68_;
}
}
LEAN_EXPORT void l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v___x_66_ = stack[0].m_obj;
lean_object* v_res_69_;
v_res_69_ = l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_(v___x_66_);
stack->m_obj
 = v_res_69_;
}
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2____boxed(lean_object* v___x_70_, lean_object* v___y_71_){
_start:
{
lean_object* v_res_72_; 
v_res_72_ = l___private_Lean_DeprecatedModule_0__Lean_initFn___lam__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_(v___x_70_);
return v_res_72_;
}
}
lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v___f_80_ = ((lean_object*)(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__0_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_));
v___x_81_ = ((lean_object*)(l___private_Lean_DeprecatedModule_0__Lean_initFn___closed__2_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_));
v___x_82_ = l_Lean_registerModuleEnvExtension___redArg(v___f_80_, v___x_81_);
return v___x_82_;
}
}
LEAN_EXPORT void l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_83_;
v_res_83_ = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_();
stack->m_obj
 = v_res_83_;
}
LEAN_EXPORT lean_object* l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2____boxed(lean_object* v_a_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l___private_Lean_DeprecatedModule_0__Lean_initFn_00___x40_Lean_DeprecatedModule_3390955509____hygCtx___hyg_2_();
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getDeprecatedModuleByIdx_x3f(lean_object* v_env_86_, lean_object* v_idx_87_){
_start:
{
lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; 
v___x_88_ = lean_box(0);
v___x_89_ = l_Lean_deprecatedModuleExt;
v___x_90_ = l_Lean_ModuleEnvExtension_getStateByIdx_x3f___redArg(v___x_88_, v___x_89_, v_env_86_, v_idx_87_);
if (lean_obj_tag(v___x_90_) == 0)
{
return v___x_88_;
}
else
{
lean_object* v_val_91_; 
v_val_91_ = lean_ctor_get(v___x_90_, 0);
lean_inc(v_val_91_);
lean_dec_ref_known(v___x_90_, 1);
return v_val_91_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getDeprecatedModuleByIdx_x3f___boxed(lean_object* v_env_92_, lean_object* v_idx_93_){
_start:
{
lean_object* v_res_94_; 
v_res_94_ = l_Lean_Environment_getDeprecatedModuleByIdx_x3f(v_env_92_, v_idx_93_);
lean_dec(v_idx_93_);
lean_dec_ref(v_env_92_);
return v_res_94_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setDeprecatedModule___lam__0(lean_object* v_entry_95_, lean_object* v_ps_96_){
_start:
{
lean_object* v_importedEntries_97_; lean_object* v___x_99_; uint8_t v_isShared_100_; uint8_t v_isSharedCheck_104_; 
v_importedEntries_97_ = lean_ctor_get(v_ps_96_, 0);
v_isSharedCheck_104_ = !lean_is_exclusive(v_ps_96_);
if (v_isSharedCheck_104_ == 0)
{
lean_object* v_unused_105_; 
v_unused_105_ = lean_ctor_get(v_ps_96_, 1);
lean_dec(v_unused_105_);
v___x_99_ = v_ps_96_;
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
else
{
lean_inc(v_importedEntries_97_);
lean_dec(v_ps_96_);
v___x_99_ = lean_box(0);
v_isShared_100_ = v_isSharedCheck_104_;
goto v_resetjp_98_;
}
v_resetjp_98_:
{
lean_object* v___x_102_; 
if (v_isShared_100_ == 0)
{
lean_ctor_set(v___x_99_, 1, v_entry_95_);
v___x_102_ = v___x_99_;
goto v_reusejp_101_;
}
else
{
lean_object* v_reuseFailAlloc_103_; 
v_reuseFailAlloc_103_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_103_, 0, v_importedEntries_97_);
lean_ctor_set(v_reuseFailAlloc_103_, 1, v_entry_95_);
v___x_102_ = v_reuseFailAlloc_103_;
goto v_reusejp_101_;
}
v_reusejp_101_:
{
return v___x_102_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_setDeprecatedModule(lean_object* v_entry_106_, lean_object* v_env_107_){
_start:
{
lean_object* v___x_108_; lean_object* v_toEnvExtension_109_; lean_object* v_asyncMode_110_; uint8_t v_logWrites_111_; lean_object* v___f_112_; lean_object* v___x_113_; uint8_t v___x_114_; 
v___x_108_ = l_Lean_deprecatedModuleExt;
v_toEnvExtension_109_ = lean_ctor_get(v___x_108_, 0);
v_asyncMode_110_ = lean_ctor_get(v_toEnvExtension_109_, 2);
v_logWrites_111_ = lean_ctor_get_uint8(v_toEnvExtension_109_, sizeof(void*)*6);
v___f_112_ = lean_alloc_closure((void*)(l_Lean_Environment_setDeprecatedModule___lam__0), 2, 1);
lean_closure_set(v___f_112_, 0, v_entry_106_);
v___x_113_ = lean_box(0);
v___x_114_ = 1;
if (v_logWrites_111_ == 0)
{
lean_object* v___x_115_; 
lean_inc_ref(v_toEnvExtension_109_);
v___x_115_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_109_, v_env_107_, v___f_112_, v_asyncMode_110_, v___x_113_, v___x_114_);
return v___x_115_;
}
else
{
lean_object* v___x_116_; lean_object* v___x_117_; 
lean_inc_ref_n(v_toEnvExtension_109_, 2);
v___x_116_ = l___private_Lean_Environment_0__Lean_EnvExtension_panicUnloggedWrite(lean_box(0), v_toEnvExtension_109_, v_env_107_);
lean_dec_ref(v_env_107_);
v___x_117_ = l___private_Lean_Environment_0__Lean_EnvExtension_modifyStateCore(lean_box(0), v_toEnvExtension_109_, v___x_116_, v___f_112_, v_asyncMode_110_, v___x_113_, v___x_114_);
return v___x_117_;
}
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(lean_object* v_as_120_, size_t v_i_121_, size_t v_stop_122_, lean_object* v_b_123_){
_start:
{
uint8_t v___x_124_; 
v___x_124_ = lean_usize_dec_eq(v_i_121_, v_stop_122_);
if (v___x_124_ == 0)
{
lean_object* v___x_125_; lean_object* v_module_126_; lean_object* v___x_127_; uint8_t v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; size_t v___x_134_; size_t v___x_135_; 
v___x_125_ = lean_array_uget_borrowed(v_as_120_, v_i_121_);
v_module_126_ = lean_ctor_get(v___x_125_, 0);
v___x_127_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__0));
v___x_128_ = 1;
lean_inc(v_module_126_);
v___x_129_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_module_126_, v___x_128_);
v___x_130_ = lean_string_append(v___x_127_, v___x_129_);
lean_dec_ref(v___x_129_);
v___x_131_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___closed__1));
v___x_132_ = lean_string_append(v___x_130_, v___x_131_);
v___x_133_ = lean_string_append(v_b_123_, v___x_132_);
lean_dec_ref(v___x_132_);
v___x_134_ = ((size_t)1ULL);
v___x_135_ = lean_usize_add(v_i_121_, v___x_134_);
v_i_121_ = v___x_135_;
v_b_123_ = v___x_133_;
goto _start;
}
else
{
return v_b_123_;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_120_ = stack[0].m_obj;
size_t v_i_121_ = stack[1].m_num;
size_t v_stop_122_ = stack[2].m_num;
lean_object* v_b_123_ = stack[3].m_obj;
lean_object* v_res_137_;
v_res_137_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(v_as_120_, v_i_121_, v_stop_122_, v_b_123_);
stack->m_obj
 = v_res_137_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0___boxed(lean_object* v_as_138_, lean_object* v_i_139_, lean_object* v_stop_140_, lean_object* v_b_141_){
_start:
{
size_t v_i_boxed_142_; size_t v_stop_boxed_143_; lean_object* v_res_144_; 
v_i_boxed_142_ = lean_unbox_usize(v_i_139_);
lean_dec(v_i_139_);
v_stop_boxed_143_ = lean_unbox_usize(v_stop_140_);
lean_dec(v_stop_140_);
v_res_144_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(v_as_138_, v_i_boxed_142_, v_stop_boxed_143_, v_b_141_);
lean_dec_ref(v_as_138_);
return v_res_144_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(lean_object* v_as_148_, size_t v_i_149_, size_t v_stop_150_, lean_object* v_b_151_){
_start:
{
lean_object* v___y_153_; uint8_t v___x_157_; 
v___x_157_ = lean_usize_dec_eq(v_i_149_, v_stop_150_);
if (v___x_157_ == 0)
{
lean_object* v___x_158_; lean_object* v_module_159_; lean_object* v___x_160_; uint8_t v___x_161_; 
v___x_158_ = lean_array_uget_borrowed(v_as_148_, v_i_149_);
v_module_159_ = lean_ctor_get(v___x_158_, 0);
v___x_160_ = ((lean_object*)(l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___closed__1));
v___x_161_ = lean_name_eq(v_module_159_, v___x_160_);
if (v___x_161_ == 0)
{
lean_object* v___x_162_; 
lean_inc(v___x_158_);
v___x_162_ = lean_array_push(v_b_151_, v___x_158_);
v___y_153_ = v___x_162_;
goto v___jp_152_;
}
else
{
v___y_153_ = v_b_151_;
goto v___jp_152_;
}
}
else
{
return v_b_151_;
}
v___jp_152_:
{
size_t v___x_154_; size_t v___x_155_; 
v___x_154_ = ((size_t)1ULL);
v___x_155_ = lean_usize_add(v_i_149_, v___x_154_);
v_i_149_ = v___x_155_;
v_b_151_ = v___y_153_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_148_ = stack[0].m_obj;
size_t v_i_149_ = stack[1].m_num;
size_t v_stop_150_ = stack[2].m_num;
lean_object* v_b_151_ = stack[3].m_obj;
lean_object* v_res_163_;
v_res_163_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(v_as_148_, v_i_149_, v_stop_150_, v_b_151_);
stack->m_obj
 = v_res_163_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1___boxed(lean_object* v_as_164_, lean_object* v_i_165_, lean_object* v_stop_166_, lean_object* v_b_167_){
_start:
{
size_t v_i_boxed_168_; size_t v_stop_boxed_169_; lean_object* v_res_170_; 
v_i_boxed_168_ = lean_unbox_usize(v_i_165_);
lean_dec(v_i_165_);
v_stop_boxed_169_ = lean_unbox_usize(v_stop_166_);
lean_dec(v_stop_166_);
v_res_170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(v_as_164_, v_i_boxed_168_, v_stop_boxed_169_, v_b_167_);
lean_dec_ref(v_as_164_);
return v_res_170_;
}
}
LEAN_EXPORT lean_object* l_Lean_formatDeprecatedModuleWarning(lean_object* v_env_176_, lean_object* v_idx_177_, lean_object* v_modName_178_, lean_object* v_entry_179_){
_start:
{
lean_object* v___y_181_; lean_object* v___y_182_; lean_object* v___y_192_; lean_object* v___y_193_; lean_object* v___y_194_; lean_object* v_message_x3f_205_; lean_object* v___x_206_; lean_object* v___y_208_; 
v_message_x3f_205_ = lean_ctor_get(v_entry_179_, 0);
lean_inc(v_message_x3f_205_);
lean_dec_ref(v_entry_179_);
v___x_206_ = l_Lean_instInhabitedModuleData_default;
if (lean_obj_tag(v_message_x3f_205_) == 0)
{
lean_object* v___x_224_; 
v___x_224_ = ((lean_object*)(l_Lean_formatDeprecatedModuleWarning___closed__2));
v___y_208_ = v___x_224_;
goto v___jp_207_;
}
else
{
lean_object* v_val_225_; 
v_val_225_ = lean_ctor_get(v_message_x3f_205_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v_message_x3f_205_, 1);
v___y_208_ = v_val_225_;
goto v___jp_207_;
}
v___jp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_190_; 
v___x_183_ = ((lean_object*)(l_Lean_formatDeprecatedModuleWarning___closed__0));
v___x_184_ = lean_string_append(v___y_181_, v___x_183_);
v___x_185_ = 1;
v___x_186_ = l_Lean_Name_toStringWithToken___at___00Lean_Name_toString_spec__0(v_modName_178_, v___x_185_);
v___x_187_ = lean_string_append(v___x_184_, v___x_186_);
lean_dec_ref(v___x_186_);
v___x_188_ = ((lean_object*)(l_Lean_formatDeprecatedModuleWarning___closed__1));
v___x_189_ = lean_string_append(v___x_187_, v___x_188_);
v___x_190_ = lean_string_append(v___x_189_, v___y_182_);
lean_dec_ref(v___y_182_);
return v___x_190_;
}
v___jp_191_:
{
lean_object* v___x_195_; lean_object* v___x_196_; uint8_t v___x_197_; 
v___x_195_ = ((lean_object*)(l_Lean_formatDeprecatedModuleWarning___closed__2));
v___x_196_ = lean_array_get_size(v___y_194_);
v___x_197_ = lean_nat_dec_lt(v___y_193_, v___x_196_);
if (v___x_197_ == 0)
{
lean_dec_ref(v___y_194_);
v___y_181_ = v___y_192_;
v___y_182_ = v___x_195_;
goto v___jp_180_;
}
else
{
uint8_t v___x_198_; 
v___x_198_ = lean_nat_dec_le(v___x_196_, v___x_196_);
if (v___x_198_ == 0)
{
if (v___x_197_ == 0)
{
lean_dec_ref(v___y_194_);
v___y_181_ = v___y_192_;
v___y_182_ = v___x_195_;
goto v___jp_180_;
}
else
{
size_t v___x_199_; size_t v___x_200_; lean_object* v___x_201_; 
v___x_199_ = ((size_t)0ULL);
v___x_200_ = lean_usize_of_nat(v___x_196_);
v___x_201_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(v___y_194_, v___x_199_, v___x_200_, v___x_195_);
lean_dec_ref(v___y_194_);
v___y_181_ = v___y_192_;
v___y_182_ = v___x_201_;
goto v___jp_180_;
}
}
else
{
size_t v___x_202_; size_t v___x_203_; lean_object* v___x_204_; 
v___x_202_ = ((size_t)0ULL);
v___x_203_ = lean_usize_of_nat(v___x_196_);
v___x_204_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__0(v___y_194_, v___x_202_, v___x_203_, v___x_195_);
lean_dec_ref(v___y_194_);
v___y_181_ = v___y_192_;
v___y_182_ = v___x_204_;
goto v___jp_180_;
}
}
}
v___jp_207_:
{
lean_object* v___x_209_; lean_object* v_moduleData_210_; lean_object* v___x_211_; lean_object* v_imports_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_209_ = l_Lean_Environment_header(v_env_176_);
v_moduleData_210_ = lean_ctor_get(v___x_209_, 7);
lean_inc_ref(v_moduleData_210_);
lean_dec_ref(v___x_209_);
v___x_211_ = lean_array_get(v___x_206_, v_moduleData_210_, v_idx_177_);
lean_dec_ref(v_moduleData_210_);
v_imports_212_ = lean_ctor_get(v___x_211_, 0);
lean_inc_ref(v_imports_212_);
lean_dec(v___x_211_);
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_array_get_size(v_imports_212_);
v___x_215_ = ((lean_object*)(l_Lean_formatDeprecatedModuleWarning___closed__3));
v___x_216_ = lean_nat_dec_lt(v___x_213_, v___x_214_);
if (v___x_216_ == 0)
{
lean_dec_ref(v_imports_212_);
v___y_192_ = v___y_208_;
v___y_193_ = v___x_213_;
v___y_194_ = v___x_215_;
goto v___jp_191_;
}
else
{
uint8_t v___x_217_; 
v___x_217_ = lean_nat_dec_le(v___x_214_, v___x_214_);
if (v___x_217_ == 0)
{
if (v___x_216_ == 0)
{
lean_dec_ref(v_imports_212_);
v___y_192_ = v___y_208_;
v___y_193_ = v___x_213_;
v___y_194_ = v___x_215_;
goto v___jp_191_;
}
else
{
size_t v___x_218_; size_t v___x_219_; lean_object* v___x_220_; 
v___x_218_ = ((size_t)0ULL);
v___x_219_ = lean_usize_of_nat(v___x_214_);
v___x_220_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(v_imports_212_, v___x_218_, v___x_219_, v___x_215_);
lean_dec_ref(v_imports_212_);
v___y_192_ = v___y_208_;
v___y_193_ = v___x_213_;
v___y_194_ = v___x_220_;
goto v___jp_191_;
}
}
else
{
size_t v___x_221_; size_t v___x_222_; lean_object* v___x_223_; 
v___x_221_ = ((size_t)0ULL);
v___x_222_ = lean_usize_of_nat(v___x_214_);
v___x_223_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_formatDeprecatedModuleWarning_spec__1(v_imports_212_, v___x_221_, v___x_222_, v___x_215_);
lean_dec_ref(v_imports_212_);
v___y_192_ = v___y_208_;
v___y_193_ = v___x_213_;
v___y_194_ = v___x_223_;
goto v___jp_191_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_formatDeprecatedModuleWarning___boxed(lean_object* v_env_226_, lean_object* v_idx_227_, lean_object* v_modName_228_, lean_object* v_entry_229_){
_start:
{
lean_object* v_res_230_; 
v_res_230_ = l_Lean_formatDeprecatedModuleWarning(v_env_226_, v_idx_227_, v_modName_228_, v_entry_229_);
lean_dec(v_idx_227_);
lean_dec_ref(v_env_226_);
return v_res_230_;
}
}
lean_object* runtime_initialize_Lean_Compiler_ModPkgExt(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_DeprecatedModule(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
