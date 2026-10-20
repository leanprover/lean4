// Lean compiler output
// Module: Lean.ProjFns
// Imports: public import Lean.EnvExtension
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
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Lean_Name_reprPrec(lean_object*, lean_object*);
lean_object* l_Nat_reprFast(lean_object*);
lean_object* l_Bool_repr___redArg(uint8_t);
lean_object* lean_string_length(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
lean_object* l_Lean_Environment_setExporting(lean_object*, uint8_t);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, uint8_t, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Environment_find_x3f(lean_object*, lean_object*, uint8_t);
static const lean_ctor_object l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 8, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedProjectionFunctionInfo_default = (const lean_object*)&l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedProjectionFunctionInfo = (const lean_object*)&l_Lean_instInhabitedProjectionFunctionInfo_default___closed__0_value;
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprProjectionFunctionInfo_repr_spec__0(lean_object*);
static const lean_string_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = "{ "};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0_value;
static const lean_string_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 9, .m_capacity = 9, .m_length = 8, .m_data = "ctorName"};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1_value;
static const lean_ctor_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__1_value)}};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2_value;
static const lean_ctor_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__2_value)}};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3_value;
static const lean_string_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = " := "};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4_value;
static const lean_ctor_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__4_value)}};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value;
static const lean_ctor_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__3_value),((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6_value;
static lean_once_cell_t l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7;
static const lean_string_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = ","};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8_value;
static const lean_ctor_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__8_value)}};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9_value;
static const lean_string_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "numParams"};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10_value;
static const lean_ctor_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__10_value)}};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11_value;
static lean_once_cell_t l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12;
static const lean_string_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 2, .m_capacity = 2, .m_length = 1, .m_data = "i"};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13_value;
static const lean_ctor_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__13_value)}};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14_value;
static lean_once_cell_t l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15;
static const lean_string_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 10, .m_capacity = 10, .m_length = 9, .m_data = "fromClass"};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16_value;
static const lean_ctor_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__16_value)}};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17_value;
static const lean_string_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 3, .m_capacity = 3, .m_length = 2, .m_data = " }"};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18_value;
static lean_once_cell_t l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19;
static lean_once_cell_t l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20;
static const lean_ctor_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0_value)}};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21_value;
static const lean_ctor_object l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__18_value)}};
static const lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22_value;
LEAN_EXPORT lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprProjectionFunctionInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprProjectionFunctionInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprProjectionFunctionInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprProjectionFunctionInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprProjectionFunctionInfo___closed__0 = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprProjectionFunctionInfo = (const lean_object*)&l_Lean_instReprProjectionFunctionInfo___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "projectionFnInfoExt"};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 172, 107, 39, 139, 106, 85, 71)}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_projectionFnInfoExt;
LEAN_EXPORT lean_object* l_Lean_addProjectionFnInfo(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_addProjectionFnInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Environment_isProjectionFn(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_isProjectionFn___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_isProjectionFn(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0 = (const lean_object*)&l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAuxParentProjectionInfo_default = (const lean_object*)&l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instInhabitedAuxParentProjectionInfo = (const lean_object*)&l_Lean_instInhabitedAuxParentProjectionInfo_default___closed__0_value;
static const lean_ctor_object l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11_value)}};
static const lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0 = (const lean_object*)&l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0_value;
static const lean_ctor_object l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 5}, .m_objs = {((lean_object*)&l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__0_value),((lean_object*)&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5_value)}};
static const lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1 = (const lean_object*)&l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_instReprAuxParentProjectionInfo___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_instReprAuxParentProjectionInfo_repr___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_instReprAuxParentProjectionInfo___closed__0 = (const lean_object*)&l_Lean_instReprAuxParentProjectionInfo___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_instReprAuxParentProjectionInfo = (const lean_object*)&l_Lean_instReprAuxParentProjectionInfo___closed__0_value;
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "auxParentProjInfoExt"};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 64, 229, 66, 82, 134, 114, 43)}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_auxParentProjInfoExt;
LEAN_EXPORT lean_object* l_Lean_addAuxParentProjectionInfo(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_addAuxParentProjectionInfo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Environment_getAuxParentProjectionInfo_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Nat_cast___at___00Lean_instReprProjectionFunctionInfo_repr_spec__0(lean_object* v_a_7_){
_start:
{
lean_object* v___x_8_; 
v___x_8_ = lean_nat_to_int(v_a_7_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7(void){
_start:
{
lean_object* v___x_22_; lean_object* v___x_23_; 
v___x_22_ = lean_unsigned_to_nat(12u);
v___x_23_ = lean_nat_to_int(v___x_22_);
return v___x_23_;
}
}
static lean_object* _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12(void){
_start:
{
lean_object* v___x_30_; lean_object* v___x_31_; 
v___x_30_ = lean_unsigned_to_nat(13u);
v___x_31_ = lean_nat_to_int(v___x_30_);
return v___x_31_;
}
}
static lean_object* _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15(void){
_start:
{
lean_object* v___x_35_; lean_object* v___x_36_; 
v___x_35_ = lean_unsigned_to_nat(5u);
v___x_36_ = lean_nat_to_int(v___x_35_);
return v___x_36_;
}
}
static lean_object* _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__0));
v___x_42_ = lean_string_length(v___x_41_);
return v___x_42_;
}
}
static lean_object* _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20(void){
_start:
{
lean_object* v___x_43_; lean_object* v___x_44_; 
v___x_43_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__19);
v___x_44_ = lean_nat_to_int(v___x_43_);
return v___x_44_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprProjectionFunctionInfo_repr___redArg(lean_object* v_x_49_){
_start:
{
lean_object* v_ctorName_50_; lean_object* v_numParams_51_; lean_object* v_i_52_; uint8_t v_fromClass_53_; lean_object* v___x_54_; lean_object* v___x_55_; lean_object* v___x_56_; lean_object* v___x_57_; lean_object* v___x_58_; lean_object* v___x_59_; uint8_t v___x_60_; lean_object* v___x_61_; lean_object* v___x_62_; lean_object* v___x_63_; lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; lean_object* v___x_73_; lean_object* v___x_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; lean_object* v___x_80_; lean_object* v___x_81_; lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v___x_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; lean_object* v___x_100_; lean_object* v___x_101_; lean_object* v___x_102_; 
v_ctorName_50_ = lean_ctor_get(v_x_49_, 0);
lean_inc(v_ctorName_50_);
v_numParams_51_ = lean_ctor_get(v_x_49_, 1);
lean_inc(v_numParams_51_);
v_i_52_ = lean_ctor_get(v_x_49_, 2);
lean_inc(v_i_52_);
v_fromClass_53_ = lean_ctor_get_uint8(v_x_49_, sizeof(void*)*3);
lean_dec_ref(v_x_49_);
v___x_54_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5));
v___x_55_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__6));
v___x_56_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__7);
v___x_57_ = lean_unsigned_to_nat(0u);
v___x_58_ = l_Lean_Name_reprPrec(v_ctorName_50_, v___x_57_);
v___x_59_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_59_, 0, v___x_56_);
lean_ctor_set(v___x_59_, 1, v___x_58_);
v___x_60_ = 0;
v___x_61_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_61_, 0, v___x_59_);
lean_ctor_set_uint8(v___x_61_, sizeof(void*)*1, v___x_60_);
v___x_62_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_62_, 0, v___x_55_);
lean_ctor_set(v___x_62_, 1, v___x_61_);
v___x_63_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9));
v___x_64_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_64_, 0, v___x_62_);
lean_ctor_set(v___x_64_, 1, v___x_63_);
v___x_65_ = lean_box(1);
v___x_66_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_66_, 0, v___x_64_);
lean_ctor_set(v___x_66_, 1, v___x_65_);
v___x_67_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__11));
v___x_68_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_68_, 0, v___x_66_);
lean_ctor_set(v___x_68_, 1, v___x_67_);
v___x_69_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_69_, 0, v___x_68_);
lean_ctor_set(v___x_69_, 1, v___x_54_);
v___x_70_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12);
v___x_71_ = l_Nat_reprFast(v_numParams_51_);
v___x_72_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_72_, 0, v___x_71_);
v___x_73_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_73_, 0, v___x_70_);
lean_ctor_set(v___x_73_, 1, v___x_72_);
v___x_74_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_74_, 0, v___x_73_);
lean_ctor_set_uint8(v___x_74_, sizeof(void*)*1, v___x_60_);
v___x_75_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_75_, 0, v___x_69_);
lean_ctor_set(v___x_75_, 1, v___x_74_);
v___x_76_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_76_, 0, v___x_75_);
lean_ctor_set(v___x_76_, 1, v___x_63_);
v___x_77_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_77_, 0, v___x_76_);
lean_ctor_set(v___x_77_, 1, v___x_65_);
v___x_78_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__14));
v___x_79_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
v___x_80_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_80_, 0, v___x_79_);
lean_ctor_set(v___x_80_, 1, v___x_54_);
v___x_81_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__15);
v___x_82_ = l_Nat_reprFast(v_i_52_);
v___x_83_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_83_, 0, v___x_82_);
v___x_84_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_84_, 0, v___x_81_);
lean_ctor_set(v___x_84_, 1, v___x_83_);
v___x_85_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_85_, 0, v___x_84_);
lean_ctor_set_uint8(v___x_85_, sizeof(void*)*1, v___x_60_);
v___x_86_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_86_, 0, v___x_80_);
lean_ctor_set(v___x_86_, 1, v___x_85_);
v___x_87_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_87_, 0, v___x_86_);
lean_ctor_set(v___x_87_, 1, v___x_63_);
v___x_88_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_88_, 0, v___x_87_);
lean_ctor_set(v___x_88_, 1, v___x_65_);
v___x_89_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17));
v___x_90_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_90_, 0, v___x_88_);
lean_ctor_set(v___x_90_, 1, v___x_89_);
v___x_91_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_91_, 0, v___x_90_);
lean_ctor_set(v___x_91_, 1, v___x_54_);
v___x_92_ = l_Bool_repr___redArg(v_fromClass_53_);
v___x_93_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_93_, 0, v___x_70_);
lean_ctor_set(v___x_93_, 1, v___x_92_);
v___x_94_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_94_, 0, v___x_93_);
lean_ctor_set_uint8(v___x_94_, sizeof(void*)*1, v___x_60_);
v___x_95_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_95_, 0, v___x_91_);
lean_ctor_set(v___x_95_, 1, v___x_94_);
v___x_96_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20);
v___x_97_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21));
v___x_98_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_95_);
v___x_99_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22));
v___x_100_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_100_, 0, v___x_98_);
lean_ctor_set(v___x_100_, 1, v___x_99_);
v___x_101_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_101_, 0, v___x_96_);
lean_ctor_set(v___x_101_, 1, v___x_100_);
v___x_102_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_102_, 0, v___x_101_);
lean_ctor_set_uint8(v___x_102_, sizeof(void*)*1, v___x_60_);
return v___x_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprProjectionFunctionInfo_repr(lean_object* v_x_103_, lean_object* v_prec_104_){
_start:
{
lean_object* v___x_105_; 
v___x_105_ = l_Lean_instReprProjectionFunctionInfo_repr___redArg(v_x_103_);
return v___x_105_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprProjectionFunctionInfo_repr___boxed(lean_object* v_x_106_, lean_object* v_prec_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_Lean_instReprProjectionFunctionInfo_repr(v_x_106_, v_prec_107_);
lean_dec(v_prec_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1(lean_object* v_env_111_, lean_object* v_as_112_, size_t v_i_113_, size_t v_stop_114_, lean_object* v_b_115_){
_start:
{
lean_object* v___y_117_; uint8_t v___x_121_; 
v___x_121_ = lean_usize_dec_eq(v_i_113_, v_stop_114_);
if (v___x_121_ == 0)
{
lean_object* v___x_122_; lean_object* v_fst_123_; uint8_t v___x_124_; lean_object* v___x_125_; uint8_t v___x_126_; 
v___x_122_ = lean_array_uget_borrowed(v_as_112_, v_i_113_);
v_fst_123_ = lean_ctor_get(v___x_122_, 0);
v___x_124_ = 1;
lean_inc_ref(v_env_111_);
v___x_125_ = l_Lean_Environment_setExporting(v_env_111_, v___x_124_);
lean_inc(v_fst_123_);
v___x_126_ = l_Lean_Environment_contains(v___x_125_, v_fst_123_, v___x_121_);
if (v___x_126_ == 0)
{
v___y_117_ = v_b_115_;
goto v___jp_116_;
}
else
{
lean_object* v___x_127_; 
lean_inc(v___x_122_);
v___x_127_ = lean_array_push(v_b_115_, v___x_122_);
v___y_117_ = v___x_127_;
goto v___jp_116_;
}
}
else
{
lean_dec_ref(v_env_111_);
return v_b_115_;
}
v___jp_116_:
{
size_t v___x_118_; size_t v___x_119_; 
v___x_118_ = ((size_t)1ULL);
v___x_119_ = lean_usize_add(v_i_113_, v___x_118_);
v_i_113_ = v___x_119_;
v_b_115_ = v___y_117_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_128_, lean_object* v_as_129_, lean_object* v_i_130_, lean_object* v_stop_131_, lean_object* v_b_132_){
_start:
{
size_t v_i_boxed_133_; size_t v_stop_boxed_134_; lean_object* v_res_135_; 
v_i_boxed_133_ = lean_unbox_usize(v_i_130_);
lean_dec(v_i_130_);
v_stop_boxed_134_ = lean_unbox_usize(v_stop_131_);
lean_dec(v_stop_131_);
v_res_135_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1(v_env_128_, v_as_129_, v_i_boxed_133_, v_stop_boxed_134_, v_b_132_);
lean_dec_ref(v_as_129_);
return v_res_135_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_136_, lean_object* v_x_137_){
_start:
{
if (lean_obj_tag(v_x_137_) == 0)
{
lean_object* v_k_138_; lean_object* v_v_139_; lean_object* v_l_140_; lean_object* v_r_141_; lean_object* v___x_142_; lean_object* v___x_143_; lean_object* v___x_144_; 
v_k_138_ = lean_ctor_get(v_x_137_, 1);
v_v_139_ = lean_ctor_get(v_x_137_, 2);
v_l_140_ = lean_ctor_get(v_x_137_, 3);
v_r_141_ = lean_ctor_get(v_x_137_, 4);
v___x_142_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0(v_init_136_, v_l_140_);
lean_inc(v_v_139_);
lean_inc(v_k_138_);
v___x_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_143_, 0, v_k_138_);
lean_ctor_set(v___x_143_, 1, v_v_139_);
v___x_144_ = lean_array_push(v___x_142_, v___x_143_);
v_init_136_ = v___x_144_;
v_x_137_ = v_r_141_;
goto _start;
}
else
{
return v_init_136_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_146_, lean_object* v_x_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0(v_init_146_, v_x_147_);
lean_dec(v_x_147_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2(lean_object* v_env_149_, lean_object* v_as_150_, size_t v_i_151_, size_t v_stop_152_, lean_object* v_b_153_){
_start:
{
lean_object* v___y_155_; uint8_t v___x_159_; 
v___x_159_ = lean_usize_dec_eq(v_i_151_, v_stop_152_);
if (v___x_159_ == 0)
{
lean_object* v___x_160_; lean_object* v_fst_161_; uint8_t v___x_162_; 
v___x_160_ = lean_array_uget_borrowed(v_as_150_, v_i_151_);
v_fst_161_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_fst_161_);
lean_inc_ref(v_env_149_);
v___x_162_ = l_Lean_Environment_contains(v_env_149_, v_fst_161_, v___x_159_);
if (v___x_162_ == 0)
{
v___y_155_ = v_b_153_;
goto v___jp_154_;
}
else
{
lean_object* v___x_163_; 
lean_inc(v___x_160_);
v___x_163_ = lean_array_push(v_b_153_, v___x_160_);
v___y_155_ = v___x_163_;
goto v___jp_154_;
}
}
else
{
lean_dec_ref(v_env_149_);
return v_b_153_;
}
v___jp_154_:
{
size_t v___x_156_; size_t v___x_157_; 
v___x_156_ = ((size_t)1ULL);
v___x_157_ = lean_usize_add(v_i_151_, v___x_156_);
v_i_151_ = v___x_157_;
v_b_153_ = v___y_155_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_164_, lean_object* v_as_165_, lean_object* v_i_166_, lean_object* v_stop_167_, lean_object* v_b_168_){
_start:
{
size_t v_i_boxed_169_; size_t v_stop_boxed_170_; lean_object* v_res_171_; 
v_i_boxed_169_ = lean_unbox_usize(v_i_166_);
lean_dec(v_i_166_);
v_stop_boxed_170_ = lean_unbox_usize(v_stop_167_);
lean_dec(v_stop_167_);
v_res_171_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2(v_env_164_, v_as_165_, v_i_boxed_169_, v_stop_boxed_170_, v_b_168_);
lean_dec_ref(v_as_165_);
return v_res_171_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_(lean_object* v_env_176_, lean_object* v_s_177_){
_start:
{
lean_object* v___x_178_; lean_object* v___y_180_; lean_object* v___x_189_; lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; uint8_t v___x_193_; 
v___x_178_ = lean_unsigned_to_nat(0u);
v___x_189_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_190_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0(v___x_189_, v_s_177_);
v___x_191_ = lean_array_get_size(v___x_190_);
v___x_192_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_193_ = lean_nat_dec_lt(v___x_178_, v___x_191_);
if (v___x_193_ == 0)
{
lean_dec_ref(v___x_190_);
v___y_180_ = v___x_192_;
goto v___jp_179_;
}
else
{
size_t v___x_194_; size_t v___x_195_; lean_object* v___x_196_; 
v___x_194_ = ((size_t)0ULL);
v___x_195_ = lean_usize_of_nat(v___x_191_);
lean_inc_ref(v_env_176_);
v___x_196_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2(v_env_176_, v___x_190_, v___x_194_, v___x_195_, v___x_192_);
lean_dec_ref(v___x_190_);
v___y_180_ = v___x_196_;
goto v___jp_179_;
}
v___jp_179_:
{
lean_object* v___x_181_; lean_object* v___x_182_; uint8_t v___x_183_; 
v___x_181_ = lean_array_get_size(v___y_180_);
v___x_182_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_183_ = lean_nat_dec_lt(v___x_178_, v___x_181_);
if (v___x_183_ == 0)
{
lean_object* v___x_184_; 
lean_dec_ref(v_env_176_);
v___x_184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_184_, 0, v___x_182_);
lean_ctor_set(v___x_184_, 1, v___x_182_);
lean_ctor_set(v___x_184_, 2, v___y_180_);
return v___x_184_;
}
else
{
size_t v___x_185_; size_t v___x_186_; lean_object* v___x_187_; lean_object* v___x_188_; 
v___x_185_ = ((size_t)0ULL);
v___x_186_ = lean_usize_of_nat(v___x_181_);
v___x_187_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1(v_env_176_, v___y_180_, v___x_185_, v___x_186_, v___x_182_);
lean_inc_ref(v___x_187_);
v___x_188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_188_, 0, v___x_187_);
lean_ctor_set(v___x_188_, 1, v___x_187_);
lean_ctor_set(v___x_188_, 2, v___y_180_);
return v___x_188_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2____boxed(lean_object* v_env_197_, lean_object* v_s_198_){
_start:
{
lean_object* v_res_199_; 
v_res_199_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_(v_env_197_, v_s_198_);
lean_dec(v_s_198_);
return v_res_199_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_209_; lean_object* v___x_210_; lean_object* v___x_211_; uint8_t v___x_212_; lean_object* v___x_213_; 
v___f_209_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_210_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_211_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_212_ = 1;
v___x_213_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_210_, v___x_211_, v___x_212_, v___f_209_);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2____boxed(lean_object* v_a_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_();
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0(lean_object* v_init_216_, lean_object* v_t_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0(v_init_216_, v_t_217_);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_219_, lean_object* v_t_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0(v_init_219_, v_t_220_);
lean_dec(v_t_220_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_Lean_addProjectionFnInfo(lean_object* v_env_222_, lean_object* v_projName_223_, lean_object* v_ctorName_224_, lean_object* v_numParams_225_, lean_object* v_i_226_, uint8_t v_fromClass_227_){
_start:
{
lean_object* v___x_228_; lean_object* v___x_229_; uint8_t v___x_230_; lean_object* v___x_231_; 
v___x_228_ = l_Lean_projectionFnInfoExt;
v___x_229_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_229_, 0, v_ctorName_224_);
lean_ctor_set(v___x_229_, 1, v_numParams_225_);
lean_ctor_set(v___x_229_, 2, v_i_226_);
lean_ctor_set_uint8(v___x_229_, sizeof(void*)*3, v_fromClass_227_);
v___x_230_ = 0;
v___x_231_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_228_, v_env_222_, v_projName_223_, v___x_229_, v___x_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Lean_addProjectionFnInfo___boxed(lean_object* v_env_232_, lean_object* v_projName_233_, lean_object* v_ctorName_234_, lean_object* v_numParams_235_, lean_object* v_i_236_, lean_object* v_fromClass_237_){
_start:
{
uint8_t v_fromClass_boxed_238_; lean_object* v_res_239_; 
v_fromClass_boxed_238_ = lean_unbox(v_fromClass_237_);
v_res_239_ = l_Lean_addProjectionFnInfo(v_env_232_, v_projName_233_, v_ctorName_234_, v_numParams_235_, v_i_236_, v_fromClass_boxed_238_);
return v_res_239_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object* v_env_240_, lean_object* v_projName_241_){
_start:
{
lean_object* v___x_242_; lean_object* v_toEnvExtension_243_; lean_object* v_asyncMode_244_; lean_object* v___x_245_; uint8_t v___x_246_; lean_object* v___x_247_; 
v___x_242_ = l_Lean_projectionFnInfoExt;
v_toEnvExtension_243_ = lean_ctor_get(v___x_242_, 0);
v_asyncMode_244_ = lean_ctor_get(v_toEnvExtension_243_, 2);
v___x_245_ = ((lean_object*)(l_Lean_instInhabitedProjectionFunctionInfo_default));
v___x_246_ = 0;
v___x_247_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_245_, v___x_242_, v_env_240_, v_projName_241_, v_asyncMode_244_, v___x_246_);
return v___x_247_;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_isProjectionFn(lean_object* v_env_248_, lean_object* v_declName_249_){
_start:
{
lean_object* v___x_250_; lean_object* v_toEnvExtension_251_; lean_object* v_asyncMode_252_; lean_object* v___x_253_; uint8_t v___x_254_; 
v___x_250_ = l_Lean_projectionFnInfoExt;
v_toEnvExtension_251_ = lean_ctor_get(v___x_250_, 0);
v_asyncMode_252_ = lean_ctor_get(v_toEnvExtension_251_, 2);
v___x_253_ = ((lean_object*)(l_Lean_instInhabitedProjectionFunctionInfo_default));
v___x_254_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_253_, v___x_250_, v_env_248_, v_declName_249_, v_asyncMode_252_);
return v___x_254_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_isProjectionFn___boxed(lean_object* v_env_255_, lean_object* v_declName_256_){
_start:
{
uint8_t v_res_257_; lean_object* v_r_258_; 
v_res_257_ = l_Lean_Environment_isProjectionFn(v_env_255_, v_declName_256_);
v_r_258_ = lean_box(v_res_257_);
return v_r_258_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object* v_env_259_, lean_object* v_projName_260_){
_start:
{
lean_object* v___x_261_; 
lean_inc_ref(v_env_259_);
v___x_261_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_259_, v_projName_260_);
if (lean_obj_tag(v___x_261_) == 0)
{
lean_object* v___x_262_; 
lean_dec_ref(v_env_259_);
v___x_262_ = lean_box(0);
return v___x_262_;
}
else
{
lean_object* v_val_263_; lean_object* v_ctorName_264_; uint8_t v___x_265_; lean_object* v___x_266_; 
v_val_263_ = lean_ctor_get(v___x_261_, 0);
lean_inc(v_val_263_);
lean_dec_ref_known(v___x_261_, 1);
v_ctorName_264_ = lean_ctor_get(v_val_263_, 0);
lean_inc(v_ctorName_264_);
lean_dec(v_val_263_);
v___x_265_ = 0;
v___x_266_ = l_Lean_Environment_find_x3f(v_env_259_, v_ctorName_264_, v___x_265_);
if (lean_obj_tag(v___x_266_) == 1)
{
lean_object* v_val_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_277_; 
v_val_267_ = lean_ctor_get(v___x_266_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_266_);
if (v_isSharedCheck_277_ == 0)
{
v___x_269_ = v___x_266_;
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_val_267_);
lean_dec(v___x_266_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
if (lean_obj_tag(v_val_267_) == 6)
{
lean_object* v_val_271_; lean_object* v_induct_272_; lean_object* v___x_274_; 
v_val_271_ = lean_ctor_get(v_val_267_, 0);
lean_inc_ref(v_val_271_);
lean_dec_ref_known(v_val_267_, 1);
v_induct_272_ = lean_ctor_get(v_val_271_, 1);
lean_inc(v_induct_272_);
lean_dec_ref(v_val_271_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v_induct_272_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v_induct_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
else
{
lean_object* v___x_276_; 
lean_del_object(v___x_269_);
lean_dec(v_val_267_);
v___x_276_ = lean_box(0);
return v___x_276_;
}
}
}
else
{
lean_object* v___x_278_; 
lean_dec(v___x_266_);
v___x_278_ = lean_box(0);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___redArg___lam__0(lean_object* v_declName_279_, lean_object* v_toPure_280_, lean_object* v_____do__lift_281_){
_start:
{
uint8_t v___x_282_; lean_object* v___x_283_; lean_object* v___x_284_; 
v___x_282_ = l_Lean_Environment_isProjectionFn(v_____do__lift_281_, v_declName_279_);
v___x_283_ = lean_box(v___x_282_);
v___x_284_ = lean_apply_2(v_toPure_280_, lean_box(0), v___x_283_);
return v___x_284_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___redArg(lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_declName_287_){
_start:
{
lean_object* v_toApplicative_288_; lean_object* v_toBind_289_; lean_object* v_getEnv_290_; lean_object* v_toPure_291_; lean_object* v___f_292_; lean_object* v___x_293_; 
v_toApplicative_288_ = lean_ctor_get(v_inst_286_, 0);
lean_inc_ref(v_toApplicative_288_);
v_toBind_289_ = lean_ctor_get(v_inst_286_, 1);
lean_inc(v_toBind_289_);
lean_dec_ref(v_inst_286_);
v_getEnv_290_ = lean_ctor_get(v_inst_285_, 0);
lean_inc(v_getEnv_290_);
lean_dec_ref(v_inst_285_);
v_toPure_291_ = lean_ctor_get(v_toApplicative_288_, 1);
lean_inc(v_toPure_291_);
lean_dec_ref(v_toApplicative_288_);
v___f_292_ = lean_alloc_closure((void*)(l_Lean_isProjectionFn___redArg___lam__0), 3, 2);
lean_closure_set(v___f_292_, 0, v_declName_287_);
lean_closure_set(v___f_292_, 1, v_toPure_291_);
v___x_293_ = lean_apply_4(v_toBind_289_, lean_box(0), lean_box(0), v_getEnv_290_, v___f_292_);
return v___x_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn(lean_object* v_m_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_declName_297_){
_start:
{
lean_object* v___x_298_; 
v___x_298_ = l_Lean_isProjectionFn___redArg(v_inst_295_, v_inst_296_, v_declName_297_);
return v___x_298_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___redArg___lam__0(lean_object* v_declName_299_, lean_object* v_toPure_300_, lean_object* v_____do__lift_301_){
_start:
{
lean_object* v___x_302_; lean_object* v___x_303_; 
v___x_302_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_____do__lift_301_, v_declName_299_);
v___x_303_ = lean_apply_2(v_toPure_300_, lean_box(0), v___x_302_);
return v___x_303_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___redArg(lean_object* v_inst_304_, lean_object* v_inst_305_, lean_object* v_declName_306_){
_start:
{
lean_object* v_toApplicative_307_; lean_object* v_toBind_308_; lean_object* v_getEnv_309_; lean_object* v_toPure_310_; lean_object* v___f_311_; lean_object* v___x_312_; 
v_toApplicative_307_ = lean_ctor_get(v_inst_305_, 0);
lean_inc_ref(v_toApplicative_307_);
v_toBind_308_ = lean_ctor_get(v_inst_305_, 1);
lean_inc(v_toBind_308_);
lean_dec_ref(v_inst_305_);
v_getEnv_309_ = lean_ctor_get(v_inst_304_, 0);
lean_inc(v_getEnv_309_);
lean_dec_ref(v_inst_304_);
v_toPure_310_ = lean_ctor_get(v_toApplicative_307_, 1);
lean_inc(v_toPure_310_);
lean_dec_ref(v_toApplicative_307_);
v___f_311_ = lean_alloc_closure((void*)(l_Lean_getProjectionFnInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_311_, 0, v_declName_306_);
lean_closure_set(v___f_311_, 1, v_toPure_310_);
v___x_312_ = lean_apply_4(v_toBind_308_, lean_box(0), lean_box(0), v_getEnv_309_, v___f_311_);
return v___x_312_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f(lean_object* v_m_313_, lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_declName_316_){
_start:
{
lean_object* v___x_317_; 
v___x_317_ = l_Lean_getProjectionFnInfo_x3f___redArg(v_inst_314_, v_inst_315_, v_declName_316_);
return v___x_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___redArg(lean_object* v_x_329_){
_start:
{
lean_object* v_numParams_330_; uint8_t v_fromClass_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_364_; 
v_numParams_330_ = lean_ctor_get(v_x_329_, 0);
v_fromClass_331_ = lean_ctor_get_uint8(v_x_329_, sizeof(void*)*1);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_329_);
if (v_isSharedCheck_364_ == 0)
{
v___x_333_ = v_x_329_;
v_isShared_334_ = v_isSharedCheck_364_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_numParams_330_);
lean_dec(v_x_329_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_364_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; uint8_t v___x_341_; lean_object* v___x_343_; 
v___x_335_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5));
v___x_336_ = ((lean_object*)(l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1));
v___x_337_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12);
v___x_338_ = l_Nat_reprFast(v_numParams_330_);
v___x_339_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_339_, 0, v___x_338_);
v___x_340_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_340_, 0, v___x_337_);
lean_ctor_set(v___x_340_, 1, v___x_339_);
v___x_341_ = 0;
if (v_isShared_334_ == 0)
{
lean_ctor_set_tag(v___x_333_, 6);
lean_ctor_set(v___x_333_, 0, v___x_340_);
v___x_343_ = v___x_333_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_340_);
v___x_343_ = v_reuseFailAlloc_363_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; 
lean_ctor_set_uint8(v___x_343_, sizeof(void*)*1, v___x_341_);
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_336_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9));
v___x_346_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_346_, 0, v___x_344_);
lean_ctor_set(v___x_346_, 1, v___x_345_);
v___x_347_ = lean_box(1);
v___x_348_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_348_, 0, v___x_346_);
lean_ctor_set(v___x_348_, 1, v___x_347_);
v___x_349_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17));
v___x_350_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_350_, 0, v___x_348_);
lean_ctor_set(v___x_350_, 1, v___x_349_);
v___x_351_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_351_, 0, v___x_350_);
lean_ctor_set(v___x_351_, 1, v___x_335_);
v___x_352_ = l_Bool_repr___redArg(v_fromClass_331_);
v___x_353_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_353_, 0, v___x_337_);
lean_ctor_set(v___x_353_, 1, v___x_352_);
v___x_354_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_354_, 0, v___x_353_);
lean_ctor_set_uint8(v___x_354_, sizeof(void*)*1, v___x_341_);
v___x_355_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_351_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20);
v___x_357_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21));
v___x_358_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_358_, 0, v___x_357_);
lean_ctor_set(v___x_358_, 1, v___x_355_);
v___x_359_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22));
v___x_360_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_360_, 0, v___x_358_);
lean_ctor_set(v___x_360_, 1, v___x_359_);
v___x_361_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_356_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_362_, 0, v___x_361_);
lean_ctor_set_uint8(v___x_362_, sizeof(void*)*1, v___x_341_);
return v___x_362_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr(lean_object* v_x_365_, lean_object* v_prec_366_){
_start:
{
lean_object* v___x_367_; 
v___x_367_ = l_Lean_instReprAuxParentProjectionInfo_repr___redArg(v_x_365_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___boxed(lean_object* v_x_368_, lean_object* v_prec_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_instReprAuxParentProjectionInfo_repr(v_x_368_, v_prec_369_);
lean_dec(v_prec_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2(lean_object* v_env_373_, lean_object* v_as_374_, size_t v_i_375_, size_t v_stop_376_, lean_object* v_b_377_){
_start:
{
lean_object* v___y_379_; uint8_t v___x_383_; 
v___x_383_ = lean_usize_dec_eq(v_i_375_, v_stop_376_);
if (v___x_383_ == 0)
{
lean_object* v___x_384_; lean_object* v_fst_385_; uint8_t v___x_386_; 
v___x_384_ = lean_array_uget_borrowed(v_as_374_, v_i_375_);
v_fst_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_fst_385_);
lean_inc_ref(v_env_373_);
v___x_386_ = l_Lean_Environment_contains(v_env_373_, v_fst_385_, v___x_383_);
if (v___x_386_ == 0)
{
v___y_379_ = v_b_377_;
goto v___jp_378_;
}
else
{
lean_object* v___x_387_; 
lean_inc(v___x_384_);
v___x_387_ = lean_array_push(v_b_377_, v___x_384_);
v___y_379_ = v___x_387_;
goto v___jp_378_;
}
}
else
{
lean_dec_ref(v_env_373_);
return v_b_377_;
}
v___jp_378_:
{
size_t v___x_380_; size_t v___x_381_; 
v___x_380_ = ((size_t)1ULL);
v___x_381_ = lean_usize_add(v_i_375_, v___x_380_);
v_i_375_ = v___x_381_;
v_b_377_ = v___y_379_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_388_, lean_object* v_as_389_, lean_object* v_i_390_, lean_object* v_stop_391_, lean_object* v_b_392_){
_start:
{
size_t v_i_boxed_393_; size_t v_stop_boxed_394_; lean_object* v_res_395_; 
v_i_boxed_393_ = lean_unbox_usize(v_i_390_);
lean_dec(v_i_390_);
v_stop_boxed_394_ = lean_unbox_usize(v_stop_391_);
lean_dec(v_stop_391_);
v_res_395_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2(v_env_388_, v_as_389_, v_i_boxed_393_, v_stop_boxed_394_, v_b_392_);
lean_dec_ref(v_as_389_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1(lean_object* v_env_396_, lean_object* v_as_397_, size_t v_i_398_, size_t v_stop_399_, lean_object* v_b_400_){
_start:
{
lean_object* v___y_402_; uint8_t v___x_406_; 
v___x_406_ = lean_usize_dec_eq(v_i_398_, v_stop_399_);
if (v___x_406_ == 0)
{
lean_object* v___x_407_; lean_object* v_fst_408_; uint8_t v___x_409_; lean_object* v___x_410_; uint8_t v___x_411_; 
v___x_407_ = lean_array_uget_borrowed(v_as_397_, v_i_398_);
v_fst_408_ = lean_ctor_get(v___x_407_, 0);
v___x_409_ = 1;
lean_inc_ref(v_env_396_);
v___x_410_ = l_Lean_Environment_setExporting(v_env_396_, v___x_409_);
lean_inc(v_fst_408_);
v___x_411_ = l_Lean_Environment_contains(v___x_410_, v_fst_408_, v___x_406_);
if (v___x_411_ == 0)
{
v___y_402_ = v_b_400_;
goto v___jp_401_;
}
else
{
lean_object* v___x_412_; 
lean_inc(v___x_407_);
v___x_412_ = lean_array_push(v_b_400_, v___x_407_);
v___y_402_ = v___x_412_;
goto v___jp_401_;
}
}
else
{
lean_dec_ref(v_env_396_);
return v_b_400_;
}
v___jp_401_:
{
size_t v___x_403_; size_t v___x_404_; 
v___x_403_ = ((size_t)1ULL);
v___x_404_ = lean_usize_add(v_i_398_, v___x_403_);
v_i_398_ = v___x_404_;
v_b_400_ = v___y_402_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_413_, lean_object* v_as_414_, lean_object* v_i_415_, lean_object* v_stop_416_, lean_object* v_b_417_){
_start:
{
size_t v_i_boxed_418_; size_t v_stop_boxed_419_; lean_object* v_res_420_; 
v_i_boxed_418_ = lean_unbox_usize(v_i_415_);
lean_dec(v_i_415_);
v_stop_boxed_419_ = lean_unbox_usize(v_stop_416_);
lean_dec(v_stop_416_);
v_res_420_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1(v_env_413_, v_as_414_, v_i_boxed_418_, v_stop_boxed_419_, v_b_417_);
lean_dec_ref(v_as_414_);
return v_res_420_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_421_, lean_object* v_x_422_){
_start:
{
if (lean_obj_tag(v_x_422_) == 0)
{
lean_object* v_k_423_; lean_object* v_v_424_; lean_object* v_l_425_; lean_object* v_r_426_; lean_object* v___x_427_; lean_object* v___x_428_; lean_object* v___x_429_; 
v_k_423_ = lean_ctor_get(v_x_422_, 1);
v_v_424_ = lean_ctor_get(v_x_422_, 2);
v_l_425_ = lean_ctor_get(v_x_422_, 3);
v_r_426_ = lean_ctor_get(v_x_422_, 4);
v___x_427_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0(v_init_421_, v_l_425_);
lean_inc(v_v_424_);
lean_inc(v_k_423_);
v___x_428_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_428_, 0, v_k_423_);
lean_ctor_set(v___x_428_, 1, v_v_424_);
v___x_429_ = lean_array_push(v___x_427_, v___x_428_);
v_init_421_ = v___x_429_;
v_x_422_ = v_r_426_;
goto _start;
}
else
{
return v_init_421_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_431_, lean_object* v_x_432_){
_start:
{
lean_object* v_res_433_; 
v_res_433_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0(v_init_431_, v_x_432_);
lean_dec(v_x_432_);
return v_res_433_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_(lean_object* v_env_438_, lean_object* v_s_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___y_442_; lean_object* v___x_451_; lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; uint8_t v___x_455_; 
v___x_440_ = lean_unsigned_to_nat(0u);
v___x_451_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_));
v___x_452_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0(v___x_451_, v_s_439_);
v___x_453_ = lean_array_get_size(v___x_452_);
v___x_454_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_));
v___x_455_ = lean_nat_dec_lt(v___x_440_, v___x_453_);
if (v___x_455_ == 0)
{
lean_dec_ref(v___x_452_);
v___y_442_ = v___x_454_;
goto v___jp_441_;
}
else
{
size_t v___x_456_; size_t v___x_457_; lean_object* v___x_458_; 
v___x_456_ = ((size_t)0ULL);
v___x_457_ = lean_usize_of_nat(v___x_453_);
lean_inc_ref(v_env_438_);
v___x_458_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2(v_env_438_, v___x_452_, v___x_456_, v___x_457_, v___x_454_);
lean_dec_ref(v___x_452_);
v___y_442_ = v___x_458_;
goto v___jp_441_;
}
v___jp_441_:
{
lean_object* v___x_443_; lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_443_ = lean_array_get_size(v___y_442_);
v___x_444_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_));
v___x_445_ = lean_nat_dec_lt(v___x_440_, v___x_443_);
if (v___x_445_ == 0)
{
lean_object* v___x_446_; 
lean_dec_ref(v_env_438_);
v___x_446_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_446_, 0, v___x_444_);
lean_ctor_set(v___x_446_, 1, v___x_444_);
lean_ctor_set(v___x_446_, 2, v___y_442_);
return v___x_446_;
}
else
{
size_t v___x_447_; size_t v___x_448_; lean_object* v___x_449_; lean_object* v___x_450_; 
v___x_447_ = ((size_t)0ULL);
v___x_448_ = lean_usize_of_nat(v___x_443_);
v___x_449_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1(v_env_438_, v___y_442_, v___x_447_, v___x_448_, v___x_444_);
lean_inc_ref(v___x_449_);
v___x_450_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_450_, 0, v___x_449_);
lean_ctor_set(v___x_450_, 1, v___x_449_);
lean_ctor_set(v___x_450_, 2, v___y_442_);
return v___x_450_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2____boxed(lean_object* v_env_459_, lean_object* v_s_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_(v_env_459_, v_s_460_);
lean_dec(v_s_460_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_468_; lean_object* v___x_469_; lean_object* v___x_470_; uint8_t v___x_471_; lean_object* v___x_472_; 
v___f_468_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_));
v___x_469_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_));
v___x_470_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_471_ = 1;
v___x_472_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_469_, v___x_470_, v___x_471_, v___f_468_);
return v___x_472_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2____boxed(lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_();
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0(lean_object* v_init_475_, lean_object* v_t_476_){
_start:
{
lean_object* v___x_477_; 
v___x_477_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0(v_init_475_, v_t_476_);
return v___x_477_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_478_, lean_object* v_t_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0(v_init_478_, v_t_479_);
lean_dec(v_t_479_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAuxParentProjectionInfo(lean_object* v_env_481_, lean_object* v_projName_482_, lean_object* v_numParams_483_, uint8_t v_fromClass_484_){
_start:
{
lean_object* v___x_485_; lean_object* v___x_486_; uint8_t v___x_487_; lean_object* v___x_488_; 
v___x_485_ = l_Lean_auxParentProjInfoExt;
v___x_486_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_486_, 0, v_numParams_483_);
lean_ctor_set_uint8(v___x_486_, sizeof(void*)*1, v_fromClass_484_);
v___x_487_ = 0;
v___x_488_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_485_, v_env_481_, v_projName_482_, v___x_486_, v___x_487_);
return v___x_488_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAuxParentProjectionInfo___boxed(lean_object* v_env_489_, lean_object* v_projName_490_, lean_object* v_numParams_491_, lean_object* v_fromClass_492_){
_start:
{
uint8_t v_fromClass_boxed_493_; lean_object* v_res_494_; 
v_fromClass_boxed_493_ = lean_unbox(v_fromClass_492_);
v_res_494_ = l_Lean_addAuxParentProjectionInfo(v_env_489_, v_projName_490_, v_numParams_491_, v_fromClass_boxed_493_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getAuxParentProjectionInfo_x3f(lean_object* v_env_495_, lean_object* v_projName_496_){
_start:
{
lean_object* v___x_497_; lean_object* v_toEnvExtension_498_; lean_object* v_asyncMode_499_; lean_object* v___x_500_; uint8_t v___x_501_; lean_object* v___x_502_; 
v___x_497_ = l_Lean_auxParentProjInfoExt;
v_toEnvExtension_498_ = lean_ctor_get(v___x_497_, 0);
v_asyncMode_499_ = lean_ctor_get(v_toEnvExtension_498_, 2);
v___x_500_ = ((lean_object*)(l_Lean_instInhabitedAuxParentProjectionInfo_default));
v___x_501_ = 0;
v___x_502_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_500_, v___x_497_, v_env_495_, v_projName_496_, v_asyncMode_499_, v___x_501_);
return v___x_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0(lean_object* v_declName_503_, lean_object* v_toPure_504_, lean_object* v_____do__lift_505_){
_start:
{
lean_object* v___x_506_; lean_object* v___x_507_; 
v___x_506_ = l_Lean_Environment_getAuxParentProjectionInfo_x3f(v_____do__lift_505_, v_declName_503_);
v___x_507_ = lean_apply_2(v_toPure_504_, lean_box(0), v___x_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f___redArg(lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_declName_510_){
_start:
{
lean_object* v_toApplicative_511_; lean_object* v_toBind_512_; lean_object* v_getEnv_513_; lean_object* v_toPure_514_; lean_object* v___f_515_; lean_object* v___x_516_; 
v_toApplicative_511_ = lean_ctor_get(v_inst_509_, 0);
lean_inc_ref(v_toApplicative_511_);
v_toBind_512_ = lean_ctor_get(v_inst_509_, 1);
lean_inc(v_toBind_512_);
lean_dec_ref(v_inst_509_);
v_getEnv_513_ = lean_ctor_get(v_inst_508_, 0);
lean_inc(v_getEnv_513_);
lean_dec_ref(v_inst_508_);
v_toPure_514_ = lean_ctor_get(v_toApplicative_511_, 1);
lean_inc(v_toPure_514_);
lean_dec_ref(v_toApplicative_511_);
v___f_515_ = lean_alloc_closure((void*)(l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_515_, 0, v_declName_510_);
lean_closure_set(v___f_515_, 1, v_toPure_514_);
v___x_516_ = lean_apply_4(v_toBind_512_, lean_box(0), lean_box(0), v_getEnv_513_, v___f_515_);
return v___x_516_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f(lean_object* v_m_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_declName_520_){
_start:
{
lean_object* v___x_521_; 
v___x_521_ = l_Lean_getAuxParentProjectionInfo_x3f___redArg(v_inst_518_, v_inst_519_, v_declName_520_);
return v___x_521_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_projectionFnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_projectionFnInfoExt);
lean_dec_ref(res);
res = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_auxParentProjInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_auxParentProjInfoExt);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_ProjFns(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_ProjFns(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_ProjFns(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_ProjFns(builtin);
}
#ifdef __cplusplus
}
#endif
