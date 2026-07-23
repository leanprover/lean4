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
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_eq(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t l_Lean_Environment_contains(lean_object*, lean_object*, uint8_t);
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
lean_object* l_Lean_mkMapDeclarationExtension___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_find_x3f___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
uint8_t l_Lean_MapDeclarationExtension_contains___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_MapDeclarationExtension_insert___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "projectionFnInfoExt"};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 172, 107, 39, 139, 106, 85, 71)}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value;
static const lean_array_object l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value)}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static const lean_closure_object l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "auxParentProjInfoExt"};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value_aux_0),((lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 64, 229, 66, 82, 134, 114, 43)}};
static const lean_object* l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_111_, lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
lean_object* v_k_113_; lean_object* v_v_114_; lean_object* v_l_115_; lean_object* v_r_116_; lean_object* v___x_117_; lean_object* v___x_118_; lean_object* v___x_119_; 
v_k_113_ = lean_ctor_get(v_x_112_, 1);
v_v_114_ = lean_ctor_get(v_x_112_, 2);
v_l_115_ = lean_ctor_get(v_x_112_, 3);
v_r_116_ = lean_ctor_get(v_x_112_, 4);
v___x_117_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_111_, v_l_115_);
lean_inc(v_v_114_);
lean_inc(v_k_113_);
v___x_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_118_, 0, v_k_113_);
lean_ctor_set(v___x_118_, 1, v_v_114_);
v___x_119_ = lean_array_push(v___x_117_, v___x_118_);
v_init_111_ = v___x_119_;
v_x_112_ = v_r_116_;
goto _start;
}
else
{
return v_init_111_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_121_, lean_object* v_x_122_){
_start:
{
lean_object* v_res_123_; 
v_res_123_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_121_, v_x_122_);
lean_dec(v_x_122_);
return v_res_123_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(lean_object* v_env_124_, lean_object* v_as_125_, size_t v_i_126_, size_t v_stop_127_, lean_object* v_b_128_){
_start:
{
lean_object* v___y_130_; uint8_t v___x_134_; 
v___x_134_ = lean_usize_dec_eq(v_i_126_, v_stop_127_);
if (v___x_134_ == 0)
{
lean_object* v___x_135_; lean_object* v_fst_136_; uint8_t v___x_137_; 
v___x_135_ = lean_array_uget_borrowed(v_as_125_, v_i_126_);
v_fst_136_ = lean_ctor_get(v___x_135_, 0);
lean_inc(v_fst_136_);
lean_inc_ref(v_env_124_);
v___x_137_ = l_Lean_Environment_contains(v_env_124_, v_fst_136_, v___x_134_);
if (v___x_137_ == 0)
{
v___y_130_ = v_b_128_;
goto v___jp_129_;
}
else
{
lean_object* v___x_138_; 
lean_inc(v___x_135_);
v___x_138_ = lean_array_push(v_b_128_, v___x_135_);
v___y_130_ = v___x_138_;
goto v___jp_129_;
}
}
else
{
lean_dec_ref(v_env_124_);
return v_b_128_;
}
v___jp_129_:
{
size_t v___x_131_; size_t v___x_132_; 
v___x_131_ = ((size_t)1ULL);
v___x_132_ = lean_usize_add(v_i_126_, v___x_131_);
v_i_126_ = v___x_132_;
v_b_128_ = v___y_130_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_139_, lean_object* v_as_140_, lean_object* v_i_141_, lean_object* v_stop_142_, lean_object* v_b_143_){
_start:
{
size_t v_i_boxed_144_; size_t v_stop_boxed_145_; lean_object* v_res_146_; 
v_i_boxed_144_ = lean_unbox_usize(v_i_141_);
lean_dec(v_i_141_);
v_stop_boxed_145_ = lean_unbox_usize(v_stop_142_);
lean_dec(v_stop_142_);
v_res_146_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_139_, v_as_140_, v_i_boxed_144_, v_stop_boxed_145_, v_b_143_);
lean_dec_ref(v_as_140_);
return v_res_146_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(lean_object* v_env_153_, lean_object* v_s_154_){
_start:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v___x_158_; lean_object* v___x_159_; uint8_t v___x_160_; 
v___x_155_ = lean_unsigned_to_nat(0u);
v___x_156_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_157_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v___x_156_, v_s_154_);
v___x_158_ = lean_array_get_size(v___x_157_);
v___x_159_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_160_ = lean_nat_dec_lt(v___x_155_, v___x_158_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; 
lean_dec_ref(v___x_157_);
lean_dec_ref(v_env_153_);
v___x_161_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
return v___x_161_;
}
else
{
uint8_t v___x_162_; 
v___x_162_ = lean_nat_dec_le(v___x_158_, v___x_158_);
if (v___x_162_ == 0)
{
if (v___x_160_ == 0)
{
lean_object* v___x_163_; 
lean_dec_ref(v___x_157_);
lean_dec_ref(v_env_153_);
v___x_163_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
return v___x_163_;
}
else
{
size_t v___x_164_; size_t v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_164_ = ((size_t)0ULL);
v___x_165_ = lean_usize_of_nat(v___x_158_);
v___x_166_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_153_, v___x_157_, v___x_164_, v___x_165_, v___x_159_);
lean_dec_ref(v___x_157_);
lean_inc_ref_n(v___x_166_, 2);
v___x_167_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_167_, 0, v___x_166_);
lean_ctor_set(v___x_167_, 1, v___x_166_);
lean_ctor_set(v___x_167_, 2, v___x_166_);
return v___x_167_;
}
}
else
{
size_t v___x_168_; size_t v___x_169_; lean_object* v___x_170_; lean_object* v___x_171_; 
v___x_168_ = ((size_t)0ULL);
v___x_169_ = lean_usize_of_nat(v___x_158_);
v___x_170_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_153_, v___x_157_, v___x_168_, v___x_169_, v___x_159_);
lean_dec_ref(v___x_157_);
lean_inc_ref_n(v___x_170_, 2);
v___x_171_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_171_, 0, v___x_170_);
lean_ctor_set(v___x_171_, 1, v___x_170_);
lean_ctor_set(v___x_171_, 2, v___x_170_);
return v___x_171_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(lean_object* v_env_172_, lean_object* v_s_173_){
_start:
{
lean_object* v_res_174_; 
v_res_174_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(v_env_172_, v_s_173_);
lean_dec(v_s_173_);
return v_res_174_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_184_; lean_object* v___x_185_; lean_object* v___x_186_; lean_object* v___x_187_; 
v___f_184_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_185_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_186_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_187_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_185_, v___x_186_, v___f_184_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(lean_object* v_a_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_();
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0(lean_object* v_init_190_, lean_object* v_t_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_190_, v_t_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_193_, lean_object* v_t_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0(v_init_193_, v_t_194_);
lean_dec(v_t_194_);
return v_res_195_;
}
}
LEAN_EXPORT lean_object* l_Lean_addProjectionFnInfo(lean_object* v_env_196_, lean_object* v_projName_197_, lean_object* v_ctorName_198_, lean_object* v_numParams_199_, lean_object* v_i_200_, uint8_t v_fromClass_201_){
_start:
{
lean_object* v___x_202_; lean_object* v___x_203_; lean_object* v___x_204_; 
v___x_202_ = l_Lean_projectionFnInfoExt;
v___x_203_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_203_, 0, v_ctorName_198_);
lean_ctor_set(v___x_203_, 1, v_numParams_199_);
lean_ctor_set(v___x_203_, 2, v_i_200_);
lean_ctor_set_uint8(v___x_203_, sizeof(void*)*3, v_fromClass_201_);
v___x_204_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_202_, v_env_196_, v_projName_197_, v___x_203_);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l_Lean_addProjectionFnInfo___boxed(lean_object* v_env_205_, lean_object* v_projName_206_, lean_object* v_ctorName_207_, lean_object* v_numParams_208_, lean_object* v_i_209_, lean_object* v_fromClass_210_){
_start:
{
uint8_t v_fromClass_boxed_211_; lean_object* v_res_212_; 
v_fromClass_boxed_211_ = lean_unbox(v_fromClass_210_);
v_res_212_ = l_Lean_addProjectionFnInfo(v_env_205_, v_projName_206_, v_ctorName_207_, v_numParams_208_, v_i_209_, v_fromClass_boxed_211_);
return v_res_212_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object* v_env_213_, lean_object* v_projName_214_){
_start:
{
lean_object* v___x_215_; lean_object* v_toEnvExtension_216_; lean_object* v_asyncMode_217_; lean_object* v___x_218_; uint8_t v___x_219_; lean_object* v___x_220_; 
v___x_215_ = l_Lean_projectionFnInfoExt;
v_toEnvExtension_216_ = lean_ctor_get(v___x_215_, 0);
v_asyncMode_217_ = lean_ctor_get(v_toEnvExtension_216_, 2);
v___x_218_ = ((lean_object*)(l_Lean_instInhabitedProjectionFunctionInfo_default));
v___x_219_ = 0;
v___x_220_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_218_, v___x_215_, v_env_213_, v_projName_214_, v_asyncMode_217_, v___x_219_);
return v___x_220_;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_isProjectionFn(lean_object* v_env_221_, lean_object* v_declName_222_){
_start:
{
lean_object* v___x_223_; lean_object* v___x_224_; uint8_t v___x_225_; 
v___x_223_ = ((lean_object*)(l_Lean_instInhabitedProjectionFunctionInfo_default));
v___x_224_ = l_Lean_projectionFnInfoExt;
v___x_225_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_223_, v___x_224_, v_env_221_, v_declName_222_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_isProjectionFn___boxed(lean_object* v_env_226_, lean_object* v_declName_227_){
_start:
{
uint8_t v_res_228_; lean_object* v_r_229_; 
v_res_228_ = l_Lean_Environment_isProjectionFn(v_env_226_, v_declName_227_);
v_r_229_ = lean_box(v_res_228_);
return v_r_229_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object* v_env_230_, lean_object* v_projName_231_){
_start:
{
lean_object* v___x_232_; 
lean_inc_ref(v_env_230_);
v___x_232_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_230_, v_projName_231_);
if (lean_obj_tag(v___x_232_) == 0)
{
lean_object* v___x_233_; 
lean_dec_ref(v_env_230_);
v___x_233_ = lean_box(0);
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v_ctorName_235_; uint8_t v___x_236_; lean_object* v___x_237_; 
v_val_234_ = lean_ctor_get(v___x_232_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v___x_232_, 1);
v_ctorName_235_ = lean_ctor_get(v_val_234_, 0);
lean_inc(v_ctorName_235_);
lean_dec(v_val_234_);
v___x_236_ = 0;
v___x_237_ = l_Lean_Environment_find_x3f(v_env_230_, v_ctorName_235_, v___x_236_);
if (lean_obj_tag(v___x_237_) == 1)
{
lean_object* v_val_238_; lean_object* v___x_240_; uint8_t v_isShared_241_; uint8_t v_isSharedCheck_248_; 
v_val_238_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_248_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_248_ == 0)
{
v___x_240_ = v___x_237_;
v_isShared_241_ = v_isSharedCheck_248_;
goto v_resetjp_239_;
}
else
{
lean_inc(v_val_238_);
lean_dec(v___x_237_);
v___x_240_ = lean_box(0);
v_isShared_241_ = v_isSharedCheck_248_;
goto v_resetjp_239_;
}
v_resetjp_239_:
{
if (lean_obj_tag(v_val_238_) == 6)
{
lean_object* v_val_242_; lean_object* v_induct_243_; lean_object* v___x_245_; 
v_val_242_ = lean_ctor_get(v_val_238_, 0);
lean_inc_ref(v_val_242_);
lean_dec_ref_known(v_val_238_, 1);
v_induct_243_ = lean_ctor_get(v_val_242_, 1);
lean_inc(v_induct_243_);
lean_dec_ref(v_val_242_);
if (v_isShared_241_ == 0)
{
lean_ctor_set(v___x_240_, 0, v_induct_243_);
v___x_245_ = v___x_240_;
goto v_reusejp_244_;
}
else
{
lean_object* v_reuseFailAlloc_246_; 
v_reuseFailAlloc_246_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_246_, 0, v_induct_243_);
v___x_245_ = v_reuseFailAlloc_246_;
goto v_reusejp_244_;
}
v_reusejp_244_:
{
return v___x_245_;
}
}
else
{
lean_object* v___x_247_; 
lean_del_object(v___x_240_);
lean_dec(v_val_238_);
v___x_247_ = lean_box(0);
return v___x_247_;
}
}
}
else
{
lean_object* v___x_249_; 
lean_dec(v___x_237_);
v___x_249_ = lean_box(0);
return v___x_249_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___redArg___lam__0(lean_object* v_declName_250_, lean_object* v_toPure_251_, lean_object* v_____do__lift_252_){
_start:
{
uint8_t v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = l_Lean_Environment_isProjectionFn(v_____do__lift_252_, v_declName_250_);
v___x_254_ = lean_box(v___x_253_);
v___x_255_ = lean_apply_2(v_toPure_251_, lean_box(0), v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___redArg(lean_object* v_inst_256_, lean_object* v_inst_257_, lean_object* v_declName_258_){
_start:
{
lean_object* v_toApplicative_259_; lean_object* v_toBind_260_; lean_object* v_getEnv_261_; lean_object* v_toPure_262_; lean_object* v___f_263_; lean_object* v___x_264_; 
v_toApplicative_259_ = lean_ctor_get(v_inst_257_, 0);
lean_inc_ref(v_toApplicative_259_);
v_toBind_260_ = lean_ctor_get(v_inst_257_, 1);
lean_inc(v_toBind_260_);
lean_dec_ref(v_inst_257_);
v_getEnv_261_ = lean_ctor_get(v_inst_256_, 0);
lean_inc(v_getEnv_261_);
lean_dec_ref(v_inst_256_);
v_toPure_262_ = lean_ctor_get(v_toApplicative_259_, 1);
lean_inc(v_toPure_262_);
lean_dec_ref(v_toApplicative_259_);
v___f_263_ = lean_alloc_closure((void*)(l_Lean_isProjectionFn___redArg___lam__0), 3, 2);
lean_closure_set(v___f_263_, 0, v_declName_258_);
lean_closure_set(v___f_263_, 1, v_toPure_262_);
v___x_264_ = lean_apply_4(v_toBind_260_, lean_box(0), lean_box(0), v_getEnv_261_, v___f_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn(lean_object* v_m_265_, lean_object* v_inst_266_, lean_object* v_inst_267_, lean_object* v_declName_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Lean_isProjectionFn___redArg(v_inst_266_, v_inst_267_, v_declName_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___redArg___lam__0(lean_object* v_declName_270_, lean_object* v_toPure_271_, lean_object* v_____do__lift_272_){
_start:
{
lean_object* v___x_273_; lean_object* v___x_274_; 
v___x_273_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_____do__lift_272_, v_declName_270_);
v___x_274_ = lean_apply_2(v_toPure_271_, lean_box(0), v___x_273_);
return v___x_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___redArg(lean_object* v_inst_275_, lean_object* v_inst_276_, lean_object* v_declName_277_){
_start:
{
lean_object* v_toApplicative_278_; lean_object* v_toBind_279_; lean_object* v_getEnv_280_; lean_object* v_toPure_281_; lean_object* v___f_282_; lean_object* v___x_283_; 
v_toApplicative_278_ = lean_ctor_get(v_inst_276_, 0);
lean_inc_ref(v_toApplicative_278_);
v_toBind_279_ = lean_ctor_get(v_inst_276_, 1);
lean_inc(v_toBind_279_);
lean_dec_ref(v_inst_276_);
v_getEnv_280_ = lean_ctor_get(v_inst_275_, 0);
lean_inc(v_getEnv_280_);
lean_dec_ref(v_inst_275_);
v_toPure_281_ = lean_ctor_get(v_toApplicative_278_, 1);
lean_inc(v_toPure_281_);
lean_dec_ref(v_toApplicative_278_);
v___f_282_ = lean_alloc_closure((void*)(l_Lean_getProjectionFnInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_282_, 0, v_declName_277_);
lean_closure_set(v___f_282_, 1, v_toPure_281_);
v___x_283_ = lean_apply_4(v_toBind_279_, lean_box(0), lean_box(0), v_getEnv_280_, v___f_282_);
return v___x_283_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f(lean_object* v_m_284_, lean_object* v_inst_285_, lean_object* v_inst_286_, lean_object* v_declName_287_){
_start:
{
lean_object* v___x_288_; 
v___x_288_ = l_Lean_getProjectionFnInfo_x3f___redArg(v_inst_285_, v_inst_286_, v_declName_287_);
return v___x_288_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___redArg(lean_object* v_x_300_){
_start:
{
lean_object* v_numParams_301_; uint8_t v_fromClass_302_; lean_object* v___x_304_; uint8_t v_isShared_305_; uint8_t v_isSharedCheck_335_; 
v_numParams_301_ = lean_ctor_get(v_x_300_, 0);
v_fromClass_302_ = lean_ctor_get_uint8(v_x_300_, sizeof(void*)*1);
v_isSharedCheck_335_ = !lean_is_exclusive(v_x_300_);
if (v_isSharedCheck_335_ == 0)
{
v___x_304_ = v_x_300_;
v_isShared_305_ = v_isSharedCheck_335_;
goto v_resetjp_303_;
}
else
{
lean_inc(v_numParams_301_);
lean_dec(v_x_300_);
v___x_304_ = lean_box(0);
v_isShared_305_ = v_isSharedCheck_335_;
goto v_resetjp_303_;
}
v_resetjp_303_:
{
lean_object* v___x_306_; lean_object* v___x_307_; lean_object* v___x_308_; lean_object* v___x_309_; lean_object* v___x_310_; lean_object* v___x_311_; uint8_t v___x_312_; lean_object* v___x_314_; 
v___x_306_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5));
v___x_307_ = ((lean_object*)(l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1));
v___x_308_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12);
v___x_309_ = l_Nat_reprFast(v_numParams_301_);
v___x_310_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_310_, 0, v___x_309_);
v___x_311_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_311_, 0, v___x_308_);
lean_ctor_set(v___x_311_, 1, v___x_310_);
v___x_312_ = 0;
if (v_isShared_305_ == 0)
{
lean_ctor_set_tag(v___x_304_, 6);
lean_ctor_set(v___x_304_, 0, v___x_311_);
v___x_314_ = v___x_304_;
goto v_reusejp_313_;
}
else
{
lean_object* v_reuseFailAlloc_334_; 
v_reuseFailAlloc_334_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_334_, 0, v___x_311_);
v___x_314_ = v_reuseFailAlloc_334_;
goto v_reusejp_313_;
}
v_reusejp_313_:
{
lean_object* v___x_315_; lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_318_; lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; lean_object* v___x_325_; lean_object* v___x_326_; lean_object* v___x_327_; lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
lean_ctor_set_uint8(v___x_314_, sizeof(void*)*1, v___x_312_);
v___x_315_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_315_, 0, v___x_307_);
lean_ctor_set(v___x_315_, 1, v___x_314_);
v___x_316_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9));
v___x_317_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_317_, 0, v___x_315_);
lean_ctor_set(v___x_317_, 1, v___x_316_);
v___x_318_ = lean_box(1);
v___x_319_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_319_, 0, v___x_317_);
lean_ctor_set(v___x_319_, 1, v___x_318_);
v___x_320_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17));
v___x_321_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_321_, 0, v___x_319_);
lean_ctor_set(v___x_321_, 1, v___x_320_);
v___x_322_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_322_, 0, v___x_321_);
lean_ctor_set(v___x_322_, 1, v___x_306_);
v___x_323_ = l_Bool_repr___redArg(v_fromClass_302_);
v___x_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_308_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_325_, 0, v___x_324_);
lean_ctor_set_uint8(v___x_325_, sizeof(void*)*1, v___x_312_);
v___x_326_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_326_, 0, v___x_322_);
lean_ctor_set(v___x_326_, 1, v___x_325_);
v___x_327_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20);
v___x_328_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21));
v___x_329_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_329_, 0, v___x_328_);
lean_ctor_set(v___x_329_, 1, v___x_326_);
v___x_330_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22));
v___x_331_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_331_, 0, v___x_329_);
lean_ctor_set(v___x_331_, 1, v___x_330_);
v___x_332_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_327_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_333_, 0, v___x_332_);
lean_ctor_set_uint8(v___x_333_, sizeof(void*)*1, v___x_312_);
return v___x_333_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr(lean_object* v_x_336_, lean_object* v_prec_337_){
_start:
{
lean_object* v___x_338_; 
v___x_338_ = l_Lean_instReprAuxParentProjectionInfo_repr___redArg(v_x_336_);
return v___x_338_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___boxed(lean_object* v_x_339_, lean_object* v_prec_340_){
_start:
{
lean_object* v_res_341_; 
v_res_341_ = l_Lean_instReprAuxParentProjectionInfo_repr(v_x_339_, v_prec_340_);
lean_dec(v_prec_340_);
return v_res_341_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_344_, lean_object* v_x_345_){
_start:
{
if (lean_obj_tag(v_x_345_) == 0)
{
lean_object* v_k_346_; lean_object* v_v_347_; lean_object* v_l_348_; lean_object* v_r_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; 
v_k_346_ = lean_ctor_get(v_x_345_, 1);
v_v_347_ = lean_ctor_get(v_x_345_, 2);
v_l_348_ = lean_ctor_get(v_x_345_, 3);
v_r_349_ = lean_ctor_get(v_x_345_, 4);
v___x_350_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_344_, v_l_348_);
lean_inc(v_v_347_);
lean_inc(v_k_346_);
v___x_351_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_351_, 0, v_k_346_);
lean_ctor_set(v___x_351_, 1, v_v_347_);
v___x_352_ = lean_array_push(v___x_350_, v___x_351_);
v_init_344_ = v___x_352_;
v_x_345_ = v_r_349_;
goto _start;
}
else
{
return v_init_344_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_354_, lean_object* v_x_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_354_, v_x_355_);
lean_dec(v_x_355_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(lean_object* v_env_357_, lean_object* v_as_358_, size_t v_i_359_, size_t v_stop_360_, lean_object* v_b_361_){
_start:
{
lean_object* v___y_363_; uint8_t v___x_367_; 
v___x_367_ = lean_usize_dec_eq(v_i_359_, v_stop_360_);
if (v___x_367_ == 0)
{
lean_object* v___x_368_; lean_object* v_fst_369_; uint8_t v___x_370_; 
v___x_368_ = lean_array_uget_borrowed(v_as_358_, v_i_359_);
v_fst_369_ = lean_ctor_get(v___x_368_, 0);
lean_inc(v_fst_369_);
lean_inc_ref(v_env_357_);
v___x_370_ = l_Lean_Environment_contains(v_env_357_, v_fst_369_, v___x_367_);
if (v___x_370_ == 0)
{
v___y_363_ = v_b_361_;
goto v___jp_362_;
}
else
{
lean_object* v___x_371_; 
lean_inc(v___x_368_);
v___x_371_ = lean_array_push(v_b_361_, v___x_368_);
v___y_363_ = v___x_371_;
goto v___jp_362_;
}
}
else
{
lean_dec_ref(v_env_357_);
return v_b_361_;
}
v___jp_362_:
{
size_t v___x_364_; size_t v___x_365_; 
v___x_364_ = ((size_t)1ULL);
v___x_365_ = lean_usize_add(v_i_359_, v___x_364_);
v_i_359_ = v___x_365_;
v_b_361_ = v___y_363_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_372_, lean_object* v_as_373_, lean_object* v_i_374_, lean_object* v_stop_375_, lean_object* v_b_376_){
_start:
{
size_t v_i_boxed_377_; size_t v_stop_boxed_378_; lean_object* v_res_379_; 
v_i_boxed_377_ = lean_unbox_usize(v_i_374_);
lean_dec(v_i_374_);
v_stop_boxed_378_ = lean_unbox_usize(v_stop_375_);
lean_dec(v_stop_375_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_372_, v_as_373_, v_i_boxed_377_, v_stop_boxed_378_, v_b_376_);
lean_dec_ref(v_as_373_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(lean_object* v_env_386_, lean_object* v_s_387_){
_start:
{
lean_object* v___x_388_; lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; uint8_t v___x_393_; 
v___x_388_ = lean_unsigned_to_nat(0u);
v___x_389_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_));
v___x_390_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v___x_389_, v_s_387_);
v___x_391_ = lean_array_get_size(v___x_390_);
v___x_392_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_));
v___x_393_ = lean_nat_dec_lt(v___x_388_, v___x_391_);
if (v___x_393_ == 0)
{
lean_object* v___x_394_; 
lean_dec_ref(v___x_390_);
lean_dec_ref(v_env_386_);
v___x_394_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_));
return v___x_394_;
}
else
{
uint8_t v___x_395_; 
v___x_395_ = lean_nat_dec_le(v___x_391_, v___x_391_);
if (v___x_395_ == 0)
{
if (v___x_393_ == 0)
{
lean_object* v___x_396_; 
lean_dec_ref(v___x_390_);
lean_dec_ref(v_env_386_);
v___x_396_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_));
return v___x_396_;
}
else
{
size_t v___x_397_; size_t v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; 
v___x_397_ = ((size_t)0ULL);
v___x_398_ = lean_usize_of_nat(v___x_391_);
v___x_399_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_386_, v___x_390_, v___x_397_, v___x_398_, v___x_392_);
lean_dec_ref(v___x_390_);
lean_inc_ref_n(v___x_399_, 2);
v___x_400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_400_, 0, v___x_399_);
lean_ctor_set(v___x_400_, 1, v___x_399_);
lean_ctor_set(v___x_400_, 2, v___x_399_);
return v___x_400_;
}
}
else
{
size_t v___x_401_; size_t v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; 
v___x_401_ = ((size_t)0ULL);
v___x_402_ = lean_usize_of_nat(v___x_391_);
v___x_403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_386_, v___x_390_, v___x_401_, v___x_402_, v___x_392_);
lean_dec_ref(v___x_390_);
lean_inc_ref_n(v___x_403_, 2);
v___x_404_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_404_, 0, v___x_403_);
lean_ctor_set(v___x_404_, 1, v___x_403_);
lean_ctor_set(v___x_404_, 2, v___x_403_);
return v___x_404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(lean_object* v_env_405_, lean_object* v_s_406_){
_start:
{
lean_object* v_res_407_; 
v_res_407_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(v_env_405_, v_s_406_);
lean_dec(v_s_406_);
return v_res_407_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_417_; 
v___f_414_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_));
v___x_415_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_));
v___x_416_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_417_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_415_, v___x_416_, v___f_414_);
return v___x_417_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(lean_object* v_a_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_();
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0(lean_object* v_init_420_, lean_object* v_t_421_){
_start:
{
lean_object* v___x_422_; 
v___x_422_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_420_, v_t_421_);
return v___x_422_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_423_, lean_object* v_t_424_){
_start:
{
lean_object* v_res_425_; 
v_res_425_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0(v_init_423_, v_t_424_);
lean_dec(v_t_424_);
return v_res_425_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAuxParentProjectionInfo(lean_object* v_env_426_, lean_object* v_projName_427_, lean_object* v_numParams_428_, uint8_t v_fromClass_429_){
_start:
{
lean_object* v___x_430_; lean_object* v___x_431_; lean_object* v___x_432_; 
v___x_430_ = l_Lean_auxParentProjInfoExt;
v___x_431_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_431_, 0, v_numParams_428_);
lean_ctor_set_uint8(v___x_431_, sizeof(void*)*1, v_fromClass_429_);
v___x_432_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_430_, v_env_426_, v_projName_427_, v___x_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAuxParentProjectionInfo___boxed(lean_object* v_env_433_, lean_object* v_projName_434_, lean_object* v_numParams_435_, lean_object* v_fromClass_436_){
_start:
{
uint8_t v_fromClass_boxed_437_; lean_object* v_res_438_; 
v_fromClass_boxed_437_ = lean_unbox(v_fromClass_436_);
v_res_438_ = l_Lean_addAuxParentProjectionInfo(v_env_433_, v_projName_434_, v_numParams_435_, v_fromClass_boxed_437_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getAuxParentProjectionInfo_x3f(lean_object* v_env_439_, lean_object* v_projName_440_){
_start:
{
lean_object* v___x_441_; lean_object* v_toEnvExtension_442_; lean_object* v_asyncMode_443_; lean_object* v___x_444_; uint8_t v___x_445_; lean_object* v___x_446_; 
v___x_441_ = l_Lean_auxParentProjInfoExt;
v_toEnvExtension_442_ = lean_ctor_get(v___x_441_, 0);
v_asyncMode_443_ = lean_ctor_get(v_toEnvExtension_442_, 2);
v___x_444_ = ((lean_object*)(l_Lean_instInhabitedAuxParentProjectionInfo_default));
v___x_445_ = 0;
v___x_446_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_444_, v___x_441_, v_env_439_, v_projName_440_, v_asyncMode_443_, v___x_445_);
return v___x_446_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0(lean_object* v_declName_447_, lean_object* v_toPure_448_, lean_object* v_____do__lift_449_){
_start:
{
lean_object* v___x_450_; lean_object* v___x_451_; 
v___x_450_ = l_Lean_Environment_getAuxParentProjectionInfo_x3f(v_____do__lift_449_, v_declName_447_);
v___x_451_ = lean_apply_2(v_toPure_448_, lean_box(0), v___x_450_);
return v___x_451_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f___redArg(lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_declName_454_){
_start:
{
lean_object* v_toApplicative_455_; lean_object* v_toBind_456_; lean_object* v_getEnv_457_; lean_object* v_toPure_458_; lean_object* v___f_459_; lean_object* v___x_460_; 
v_toApplicative_455_ = lean_ctor_get(v_inst_453_, 0);
lean_inc_ref(v_toApplicative_455_);
v_toBind_456_ = lean_ctor_get(v_inst_453_, 1);
lean_inc(v_toBind_456_);
lean_dec_ref(v_inst_453_);
v_getEnv_457_ = lean_ctor_get(v_inst_452_, 0);
lean_inc(v_getEnv_457_);
lean_dec_ref(v_inst_452_);
v_toPure_458_ = lean_ctor_get(v_toApplicative_455_, 1);
lean_inc(v_toPure_458_);
lean_dec_ref(v_toApplicative_455_);
v___f_459_ = lean_alloc_closure((void*)(l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_459_, 0, v_declName_454_);
lean_closure_set(v___f_459_, 1, v_toPure_458_);
v___x_460_ = lean_apply_4(v_toBind_456_, lean_box(0), lean_box(0), v_getEnv_457_, v___f_459_);
return v___x_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f(lean_object* v_m_461_, lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_declName_464_){
_start:
{
lean_object* v___x_465_; 
v___x_465_ = l_Lean_getAuxParentProjectionInfo_x3f___redArg(v_inst_462_, v_inst_463_, v_declName_464_);
return v___x_465_;
}
}
lean_object* runtime_initialize_Lean_EnvExtension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_ProjFns(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_EnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_projectionFnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_projectionFnInfoExt);
lean_dec_ref(res);
res = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_();
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
