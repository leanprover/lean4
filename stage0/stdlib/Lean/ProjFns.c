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
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1(lean_object* v_env_111_, lean_object* v_as_112_, size_t v_i_113_, size_t v_stop_114_, lean_object* v_b_115_){
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
v___x_126_ = l_Lean_Environment_contains(v___x_125_, v_fst_123_, v___x_124_);
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
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_111_ = stack[0].m_obj;
lean_object* v_as_112_ = stack[1].m_obj;
size_t v_i_113_ = stack[2].m_num;
size_t v_stop_114_ = stack[3].m_num;
lean_object* v_b_115_ = stack[4].m_obj;
lean_object* v_res_128_;
v_res_128_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1(v_env_111_, v_as_112_, v_i_113_, v_stop_114_, v_b_115_);
stack->m_obj
 = v_res_128_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_129_, lean_object* v_as_130_, lean_object* v_i_131_, lean_object* v_stop_132_, lean_object* v_b_133_){
_start:
{
size_t v_i_boxed_134_; size_t v_stop_boxed_135_; lean_object* v_res_136_; 
v_i_boxed_134_ = lean_unbox_usize(v_i_131_);
lean_dec(v_i_131_);
v_stop_boxed_135_ = lean_unbox_usize(v_stop_132_);
lean_dec(v_stop_132_);
v_res_136_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1(v_env_129_, v_as_130_, v_i_boxed_134_, v_stop_boxed_135_, v_b_133_);
lean_dec_ref(v_as_130_);
return v_res_136_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_137_, lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v_k_139_; lean_object* v_v_140_; lean_object* v_l_141_; lean_object* v_r_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_145_; 
v_k_139_ = lean_ctor_get(v_x_138_, 1);
v_v_140_ = lean_ctor_get(v_x_138_, 2);
v_l_141_ = lean_ctor_get(v_x_138_, 3);
v_r_142_ = lean_ctor_get(v_x_138_, 4);
v___x_143_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0(v_init_137_, v_l_141_);
lean_inc(v_v_140_);
lean_inc(v_k_139_);
v___x_144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_144_, 0, v_k_139_);
lean_ctor_set(v___x_144_, 1, v_v_140_);
v___x_145_ = lean_array_push(v___x_143_, v___x_144_);
v_init_137_ = v___x_145_;
v_x_138_ = v_r_142_;
goto _start;
}
else
{
return v_init_137_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_147_, lean_object* v_x_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0(v_init_147_, v_x_148_);
lean_dec(v_x_148_);
return v_res_149_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2(lean_object* v_env_150_, lean_object* v_as_151_, size_t v_i_152_, size_t v_stop_153_, lean_object* v_b_154_){
_start:
{
lean_object* v___y_156_; uint8_t v___x_160_; 
v___x_160_ = lean_usize_dec_eq(v_i_152_, v_stop_153_);
if (v___x_160_ == 0)
{
lean_object* v___x_161_; lean_object* v_fst_162_; uint8_t v___x_163_; 
v___x_161_ = lean_array_uget_borrowed(v_as_151_, v_i_152_);
v_fst_162_ = lean_ctor_get(v___x_161_, 0);
lean_inc(v_fst_162_);
lean_inc_ref(v_env_150_);
v___x_163_ = l_Lean_Environment_contains(v_env_150_, v_fst_162_, v___x_160_);
if (v___x_163_ == 0)
{
v___y_156_ = v_b_154_;
goto v___jp_155_;
}
else
{
lean_object* v___x_164_; 
lean_inc(v___x_161_);
v___x_164_ = lean_array_push(v_b_154_, v___x_161_);
v___y_156_ = v___x_164_;
goto v___jp_155_;
}
}
else
{
lean_dec_ref(v_env_150_);
return v_b_154_;
}
v___jp_155_:
{
size_t v___x_157_; size_t v___x_158_; 
v___x_157_ = ((size_t)1ULL);
v___x_158_ = lean_usize_add(v_i_152_, v___x_157_);
v_i_152_ = v___x_158_;
v_b_154_ = v___y_156_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_150_ = stack[0].m_obj;
lean_object* v_as_151_ = stack[1].m_obj;
size_t v_i_152_ = stack[2].m_num;
size_t v_stop_153_ = stack[3].m_num;
lean_object* v_b_154_ = stack[4].m_obj;
lean_object* v_res_165_;
v_res_165_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2(v_env_150_, v_as_151_, v_i_152_, v_stop_153_, v_b_154_);
stack->m_obj
 = v_res_165_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_166_, lean_object* v_as_167_, lean_object* v_i_168_, lean_object* v_stop_169_, lean_object* v_b_170_){
_start:
{
size_t v_i_boxed_171_; size_t v_stop_boxed_172_; lean_object* v_res_173_; 
v_i_boxed_171_ = lean_unbox_usize(v_i_168_);
lean_dec(v_i_168_);
v_stop_boxed_172_ = lean_unbox_usize(v_stop_169_);
lean_dec(v_stop_169_);
v_res_173_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2(v_env_166_, v_as_167_, v_i_boxed_171_, v_stop_boxed_172_, v_b_170_);
lean_dec_ref(v_as_167_);
return v_res_173_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_(lean_object* v_env_178_, lean_object* v_s_179_){
_start:
{
lean_object* v___x_180_; lean_object* v___y_182_; lean_object* v___x_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; uint8_t v___x_201_; 
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_197_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_198_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0(v___x_197_, v_s_179_);
v___x_199_ = lean_array_get_size(v___x_198_);
v___x_200_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_201_ = lean_nat_dec_lt(v___x_180_, v___x_199_);
if (v___x_201_ == 0)
{
lean_dec_ref(v___x_198_);
v___y_182_ = v___x_200_;
goto v___jp_181_;
}
else
{
uint8_t v___x_202_; 
v___x_202_ = lean_nat_dec_le(v___x_199_, v___x_199_);
if (v___x_202_ == 0)
{
if (v___x_201_ == 0)
{
lean_dec_ref(v___x_198_);
v___y_182_ = v___x_200_;
goto v___jp_181_;
}
else
{
size_t v___x_203_; size_t v___x_204_; lean_object* v___x_205_; 
v___x_203_ = ((size_t)0ULL);
v___x_204_ = lean_usize_of_nat(v___x_199_);
lean_inc_ref(v_env_178_);
v___x_205_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2(v_env_178_, v___x_198_, v___x_203_, v___x_204_, v___x_200_);
lean_dec_ref(v___x_198_);
v___y_182_ = v___x_205_;
goto v___jp_181_;
}
}
else
{
size_t v___x_206_; size_t v___x_207_; lean_object* v___x_208_; 
v___x_206_ = ((size_t)0ULL);
v___x_207_ = lean_usize_of_nat(v___x_199_);
lean_inc_ref(v_env_178_);
v___x_208_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__2(v_env_178_, v___x_198_, v___x_206_, v___x_207_, v___x_200_);
lean_dec_ref(v___x_198_);
v___y_182_ = v___x_208_;
goto v___jp_181_;
}
}
v___jp_181_:
{
lean_object* v___x_183_; lean_object* v___x_184_; uint8_t v___x_185_; 
v___x_183_ = lean_array_get_size(v___y_182_);
v___x_184_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_185_ = lean_nat_dec_lt(v___x_180_, v___x_183_);
if (v___x_185_ == 0)
{
lean_object* v___x_186_; 
lean_dec_ref(v_env_178_);
v___x_186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_186_, 0, v___x_184_);
lean_ctor_set(v___x_186_, 1, v___x_184_);
lean_ctor_set(v___x_186_, 2, v___y_182_);
return v___x_186_;
}
else
{
uint8_t v___x_187_; 
v___x_187_ = lean_nat_dec_le(v___x_183_, v___x_183_);
if (v___x_187_ == 0)
{
if (v___x_185_ == 0)
{
lean_object* v___x_188_; 
lean_dec_ref(v_env_178_);
v___x_188_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_188_, 0, v___x_184_);
lean_ctor_set(v___x_188_, 1, v___x_184_);
lean_ctor_set(v___x_188_, 2, v___y_182_);
return v___x_188_;
}
else
{
size_t v___x_189_; size_t v___x_190_; lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_189_ = ((size_t)0ULL);
v___x_190_ = lean_usize_of_nat(v___x_183_);
v___x_191_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1(v_env_178_, v___y_182_, v___x_189_, v___x_190_, v___x_184_);
lean_inc_ref(v___x_191_);
v___x_192_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_192_, 0, v___x_191_);
lean_ctor_set(v___x_192_, 1, v___x_191_);
lean_ctor_set(v___x_192_, 2, v___y_182_);
return v___x_192_;
}
}
else
{
size_t v___x_193_; size_t v___x_194_; lean_object* v___x_195_; lean_object* v___x_196_; 
v___x_193_ = ((size_t)0ULL);
v___x_194_ = lean_usize_of_nat(v___x_183_);
v___x_195_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__1(v_env_178_, v___y_182_, v___x_193_, v___x_194_, v___x_184_);
lean_inc_ref(v___x_195_);
v___x_196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_196_, 0, v___x_195_);
lean_ctor_set(v___x_196_, 1, v___x_195_);
lean_ctor_set(v___x_196_, 2, v___y_182_);
return v___x_196_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2____boxed(lean_object* v_env_209_, lean_object* v_s_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_(v_env_209_, v_s_210_);
lean_dec(v_s_210_);
return v_res_211_;
}
}
lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_221_; lean_object* v___x_222_; lean_object* v___x_223_; uint8_t v___x_224_; lean_object* v___x_225_; 
v___f_221_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_222_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__3_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_223_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_224_ = 1;
v___x_225_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_222_, v___x_223_, v___x_224_, v___f_221_);
return v___x_225_;
}
}
LEAN_EXPORT void l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_226_;
v_res_226_ = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_();
stack->m_obj
 = v_res_226_;
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2____boxed(lean_object* v_a_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_();
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0(lean_object* v_init_229_, lean_object* v_t_230_){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0_spec__0(v_init_229_, v_t_230_);
return v___x_231_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_232_, lean_object* v_t_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2__spec__0(v_init_232_, v_t_233_);
lean_dec(v_t_233_);
return v_res_234_;
}
}
lean_object* l_Lean_addProjectionFnInfo(lean_object* v_env_235_, lean_object* v_projName_236_, lean_object* v_ctorName_237_, lean_object* v_numParams_238_, lean_object* v_i_239_, uint8_t v_fromClass_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; uint8_t v___x_243_; lean_object* v___x_244_; 
v___x_241_ = l_Lean_projectionFnInfoExt;
v___x_242_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_242_, 0, v_ctorName_237_);
lean_ctor_set(v___x_242_, 1, v_numParams_238_);
lean_ctor_set(v___x_242_, 2, v_i_239_);
lean_ctor_set_uint8(v___x_242_, sizeof(void*)*3, v_fromClass_240_);
v___x_243_ = 0;
v___x_244_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_241_, v_env_235_, v_projName_236_, v___x_242_, v___x_243_);
return v___x_244_;
}
}
LEAN_EXPORT void l_Lean_addProjectionFnInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_235_ = stack[0].m_obj;
lean_object* v_projName_236_ = stack[1].m_obj;
lean_object* v_ctorName_237_ = stack[2].m_obj;
lean_object* v_numParams_238_ = stack[3].m_obj;
lean_object* v_i_239_ = stack[4].m_obj;
uint8_t v_fromClass_240_ = stack[5].m_num;
lean_object* v_res_245_;
v_res_245_ = l_Lean_addProjectionFnInfo(v_env_235_, v_projName_236_, v_ctorName_237_, v_numParams_238_, v_i_239_, v_fromClass_240_);
stack->m_obj
 = v_res_245_;
}
LEAN_EXPORT lean_object* l_Lean_addProjectionFnInfo___boxed(lean_object* v_env_246_, lean_object* v_projName_247_, lean_object* v_ctorName_248_, lean_object* v_numParams_249_, lean_object* v_i_250_, lean_object* v_fromClass_251_){
_start:
{
uint8_t v_fromClass_boxed_252_; lean_object* v_res_253_; 
v_fromClass_boxed_252_ = lean_unbox(v_fromClass_251_);
v_res_253_ = l_Lean_addProjectionFnInfo(v_env_246_, v_projName_247_, v_ctorName_248_, v_numParams_249_, v_i_250_, v_fromClass_boxed_252_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object* v_env_254_, lean_object* v_projName_255_){
_start:
{
lean_object* v___x_256_; lean_object* v_toEnvExtension_257_; lean_object* v_asyncMode_258_; lean_object* v___x_259_; uint8_t v___x_260_; lean_object* v___x_261_; 
v___x_256_ = l_Lean_projectionFnInfoExt;
v_toEnvExtension_257_ = lean_ctor_get(v___x_256_, 0);
v_asyncMode_258_ = lean_ctor_get(v_toEnvExtension_257_, 2);
v___x_259_ = ((lean_object*)(l_Lean_instInhabitedProjectionFunctionInfo_default));
v___x_260_ = 0;
v___x_261_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_259_, v___x_256_, v_env_254_, v_projName_255_, v_asyncMode_258_, v___x_260_);
return v___x_261_;
}
}
uint8_t l_Lean_Environment_isProjectionFn(lean_object* v_env_262_, lean_object* v_declName_263_){
_start:
{
lean_object* v___x_264_; lean_object* v_toEnvExtension_265_; lean_object* v_asyncMode_266_; lean_object* v___x_267_; uint8_t v___x_268_; 
v___x_264_ = l_Lean_projectionFnInfoExt;
v_toEnvExtension_265_ = lean_ctor_get(v___x_264_, 0);
v_asyncMode_266_ = lean_ctor_get(v_toEnvExtension_265_, 2);
v___x_267_ = ((lean_object*)(l_Lean_instInhabitedProjectionFunctionInfo_default));
v___x_268_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_267_, v___x_264_, v_env_262_, v_declName_263_, v_asyncMode_266_);
return v___x_268_;
}
}
LEAN_EXPORT void l_Lean_Environment_isProjectionFn_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_262_ = stack[0].m_obj;
lean_object* v_declName_263_ = stack[1].m_obj;
uint8_t v_res_269_;
v_res_269_ = l_Lean_Environment_isProjectionFn(v_env_262_, v_declName_263_);
stack->m_num = v_res_269_;
}
LEAN_EXPORT lean_object* l_Lean_Environment_isProjectionFn___boxed(lean_object* v_env_270_, lean_object* v_declName_271_){
_start:
{
uint8_t v_res_272_; lean_object* v_r_273_; 
v_res_272_ = l_Lean_Environment_isProjectionFn(v_env_270_, v_declName_271_);
v_r_273_ = lean_box(v_res_272_);
return v_r_273_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object* v_env_274_, lean_object* v_projName_275_){
_start:
{
lean_object* v___x_276_; 
lean_inc_ref(v_env_274_);
v___x_276_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_274_, v_projName_275_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v___x_277_; 
lean_dec_ref(v_env_274_);
v___x_277_ = lean_box(0);
return v___x_277_;
}
else
{
lean_object* v_val_278_; lean_object* v_ctorName_279_; uint8_t v___x_280_; lean_object* v___x_281_; 
v_val_278_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_val_278_);
lean_dec_ref_known(v___x_276_, 1);
v_ctorName_279_ = lean_ctor_get(v_val_278_, 0);
lean_inc(v_ctorName_279_);
lean_dec(v_val_278_);
v___x_280_ = 0;
v___x_281_ = l_Lean_Environment_find_x3f(v_env_274_, v_ctorName_279_, v___x_280_);
if (lean_obj_tag(v___x_281_) == 1)
{
lean_object* v_val_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_292_; 
v_val_282_ = lean_ctor_get(v___x_281_, 0);
v_isSharedCheck_292_ = !lean_is_exclusive(v___x_281_);
if (v_isSharedCheck_292_ == 0)
{
v___x_284_ = v___x_281_;
v_isShared_285_ = v_isSharedCheck_292_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_val_282_);
lean_dec(v___x_281_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_292_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
if (lean_obj_tag(v_val_282_) == 6)
{
lean_object* v_val_286_; lean_object* v_induct_287_; lean_object* v___x_289_; 
v_val_286_ = lean_ctor_get(v_val_282_, 0);
lean_inc_ref(v_val_286_);
lean_dec_ref_known(v_val_282_, 1);
v_induct_287_ = lean_ctor_get(v_val_286_, 1);
lean_inc(v_induct_287_);
lean_dec_ref(v_val_286_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 0, v_induct_287_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_290_; 
v_reuseFailAlloc_290_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_290_, 0, v_induct_287_);
v___x_289_ = v_reuseFailAlloc_290_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
return v___x_289_;
}
}
else
{
lean_object* v___x_291_; 
lean_del_object(v___x_284_);
lean_dec(v_val_282_);
v___x_291_ = lean_box(0);
return v___x_291_;
}
}
}
else
{
lean_object* v___x_293_; 
lean_dec(v___x_281_);
v___x_293_ = lean_box(0);
return v___x_293_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___redArg___lam__0(lean_object* v_declName_294_, lean_object* v_toPure_295_, lean_object* v_____do__lift_296_){
_start:
{
uint8_t v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v___x_297_ = l_Lean_Environment_isProjectionFn(v_____do__lift_296_, v_declName_294_);
v___x_298_ = lean_box(v___x_297_);
v___x_299_ = lean_apply_2(v_toPure_295_, lean_box(0), v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___redArg(lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_declName_302_){
_start:
{
lean_object* v_toApplicative_303_; lean_object* v_toBind_304_; lean_object* v_getEnv_305_; lean_object* v_toPure_306_; lean_object* v___f_307_; lean_object* v___x_308_; 
v_toApplicative_303_ = lean_ctor_get(v_inst_301_, 0);
lean_inc_ref(v_toApplicative_303_);
v_toBind_304_ = lean_ctor_get(v_inst_301_, 1);
lean_inc(v_toBind_304_);
lean_dec_ref(v_inst_301_);
v_getEnv_305_ = lean_ctor_get(v_inst_300_, 0);
lean_inc(v_getEnv_305_);
lean_dec_ref(v_inst_300_);
v_toPure_306_ = lean_ctor_get(v_toApplicative_303_, 1);
lean_inc(v_toPure_306_);
lean_dec_ref(v_toApplicative_303_);
v___f_307_ = lean_alloc_closure((void*)(l_Lean_isProjectionFn___redArg___lam__0), 3, 2);
lean_closure_set(v___f_307_, 0, v_declName_302_);
lean_closure_set(v___f_307_, 1, v_toPure_306_);
v___x_308_ = lean_apply_4(v_toBind_304_, lean_box(0), lean_box(0), v_getEnv_305_, v___f_307_);
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn(lean_object* v_m_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_declName_312_){
_start:
{
lean_object* v___x_313_; 
v___x_313_ = l_Lean_isProjectionFn___redArg(v_inst_310_, v_inst_311_, v_declName_312_);
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___redArg___lam__0(lean_object* v_declName_314_, lean_object* v_toPure_315_, lean_object* v_____do__lift_316_){
_start:
{
lean_object* v___x_317_; lean_object* v___x_318_; 
v___x_317_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_____do__lift_316_, v_declName_314_);
v___x_318_ = lean_apply_2(v_toPure_315_, lean_box(0), v___x_317_);
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___redArg(lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_declName_321_){
_start:
{
lean_object* v_toApplicative_322_; lean_object* v_toBind_323_; lean_object* v_getEnv_324_; lean_object* v_toPure_325_; lean_object* v___f_326_; lean_object* v___x_327_; 
v_toApplicative_322_ = lean_ctor_get(v_inst_320_, 0);
lean_inc_ref(v_toApplicative_322_);
v_toBind_323_ = lean_ctor_get(v_inst_320_, 1);
lean_inc(v_toBind_323_);
lean_dec_ref(v_inst_320_);
v_getEnv_324_ = lean_ctor_get(v_inst_319_, 0);
lean_inc(v_getEnv_324_);
lean_dec_ref(v_inst_319_);
v_toPure_325_ = lean_ctor_get(v_toApplicative_322_, 1);
lean_inc(v_toPure_325_);
lean_dec_ref(v_toApplicative_322_);
v___f_326_ = lean_alloc_closure((void*)(l_Lean_getProjectionFnInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_326_, 0, v_declName_321_);
lean_closure_set(v___f_326_, 1, v_toPure_325_);
v___x_327_ = lean_apply_4(v_toBind_323_, lean_box(0), lean_box(0), v_getEnv_324_, v___f_326_);
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f(lean_object* v_m_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_declName_331_){
_start:
{
lean_object* v___x_332_; 
v___x_332_ = l_Lean_getProjectionFnInfo_x3f___redArg(v_inst_329_, v_inst_330_, v_declName_331_);
return v___x_332_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___redArg(lean_object* v_x_344_){
_start:
{
lean_object* v_numParams_345_; uint8_t v_fromClass_346_; lean_object* v___x_348_; uint8_t v_isShared_349_; uint8_t v_isSharedCheck_379_; 
v_numParams_345_ = lean_ctor_get(v_x_344_, 0);
v_fromClass_346_ = lean_ctor_get_uint8(v_x_344_, sizeof(void*)*1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_x_344_);
if (v_isSharedCheck_379_ == 0)
{
v___x_348_ = v_x_344_;
v_isShared_349_ = v_isSharedCheck_379_;
goto v_resetjp_347_;
}
else
{
lean_inc(v_numParams_345_);
lean_dec(v_x_344_);
v___x_348_ = lean_box(0);
v_isShared_349_ = v_isSharedCheck_379_;
goto v_resetjp_347_;
}
v_resetjp_347_:
{
lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___x_354_; lean_object* v___x_355_; uint8_t v___x_356_; lean_object* v___x_358_; 
v___x_350_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5));
v___x_351_ = ((lean_object*)(l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1));
v___x_352_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12);
v___x_353_ = l_Nat_reprFast(v_numParams_345_);
v___x_354_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_354_, 0, v___x_353_);
v___x_355_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_355_, 0, v___x_352_);
lean_ctor_set(v___x_355_, 1, v___x_354_);
v___x_356_ = 0;
if (v_isShared_349_ == 0)
{
lean_ctor_set_tag(v___x_348_, 6);
lean_ctor_set(v___x_348_, 0, v___x_355_);
v___x_358_ = v___x_348_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_355_);
v___x_358_ = v_reuseFailAlloc_378_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_361_; lean_object* v___x_362_; lean_object* v___x_363_; lean_object* v___x_364_; lean_object* v___x_365_; lean_object* v___x_366_; lean_object* v___x_367_; lean_object* v___x_368_; lean_object* v___x_369_; lean_object* v___x_370_; lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_375_; lean_object* v___x_376_; lean_object* v___x_377_; 
lean_ctor_set_uint8(v___x_358_, sizeof(void*)*1, v___x_356_);
v___x_359_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_359_, 0, v___x_351_);
lean_ctor_set(v___x_359_, 1, v___x_358_);
v___x_360_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9));
v___x_361_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_361_, 0, v___x_359_);
lean_ctor_set(v___x_361_, 1, v___x_360_);
v___x_362_ = lean_box(1);
v___x_363_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_363_, 0, v___x_361_);
lean_ctor_set(v___x_363_, 1, v___x_362_);
v___x_364_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17));
v___x_365_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_365_, 0, v___x_363_);
lean_ctor_set(v___x_365_, 1, v___x_364_);
v___x_366_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_366_, 0, v___x_365_);
lean_ctor_set(v___x_366_, 1, v___x_350_);
v___x_367_ = l_Bool_repr___redArg(v_fromClass_346_);
v___x_368_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_368_, 0, v___x_352_);
lean_ctor_set(v___x_368_, 1, v___x_367_);
v___x_369_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_369_, 0, v___x_368_);
lean_ctor_set_uint8(v___x_369_, sizeof(void*)*1, v___x_356_);
v___x_370_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_370_, 0, v___x_366_);
lean_ctor_set(v___x_370_, 1, v___x_369_);
v___x_371_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20);
v___x_372_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21));
v___x_373_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_373_, 0, v___x_372_);
lean_ctor_set(v___x_373_, 1, v___x_370_);
v___x_374_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22));
v___x_375_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_375_, 0, v___x_373_);
lean_ctor_set(v___x_375_, 1, v___x_374_);
v___x_376_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_376_, 0, v___x_371_);
lean_ctor_set(v___x_376_, 1, v___x_375_);
v___x_377_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_377_, 0, v___x_376_);
lean_ctor_set_uint8(v___x_377_, sizeof(void*)*1, v___x_356_);
return v___x_377_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr(lean_object* v_x_380_, lean_object* v_prec_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Lean_instReprAuxParentProjectionInfo_repr___redArg(v_x_380_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___boxed(lean_object* v_x_383_, lean_object* v_prec_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Lean_instReprAuxParentProjectionInfo_repr(v_x_383_, v_prec_384_);
lean_dec(v_prec_384_);
return v_res_385_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2(lean_object* v_env_388_, lean_object* v_as_389_, size_t v_i_390_, size_t v_stop_391_, lean_object* v_b_392_){
_start:
{
lean_object* v___y_394_; uint8_t v___x_398_; 
v___x_398_ = lean_usize_dec_eq(v_i_390_, v_stop_391_);
if (v___x_398_ == 0)
{
lean_object* v___x_399_; lean_object* v_fst_400_; uint8_t v___x_401_; 
v___x_399_ = lean_array_uget_borrowed(v_as_389_, v_i_390_);
v_fst_400_ = lean_ctor_get(v___x_399_, 0);
lean_inc(v_fst_400_);
lean_inc_ref(v_env_388_);
v___x_401_ = l_Lean_Environment_contains(v_env_388_, v_fst_400_, v___x_398_);
if (v___x_401_ == 0)
{
v___y_394_ = v_b_392_;
goto v___jp_393_;
}
else
{
lean_object* v___x_402_; 
lean_inc(v___x_399_);
v___x_402_ = lean_array_push(v_b_392_, v___x_399_);
v___y_394_ = v___x_402_;
goto v___jp_393_;
}
}
else
{
lean_dec_ref(v_env_388_);
return v_b_392_;
}
v___jp_393_:
{
size_t v___x_395_; size_t v___x_396_; 
v___x_395_ = ((size_t)1ULL);
v___x_396_ = lean_usize_add(v_i_390_, v___x_395_);
v_i_390_ = v___x_396_;
v_b_392_ = v___y_394_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_388_ = stack[0].m_obj;
lean_object* v_as_389_ = stack[1].m_obj;
size_t v_i_390_ = stack[2].m_num;
size_t v_stop_391_ = stack[3].m_num;
lean_object* v_b_392_ = stack[4].m_obj;
lean_object* v_res_403_;
v_res_403_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2(v_env_388_, v_as_389_, v_i_390_, v_stop_391_, v_b_392_);
stack->m_obj
 = v_res_403_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2___boxed(lean_object* v_env_404_, lean_object* v_as_405_, lean_object* v_i_406_, lean_object* v_stop_407_, lean_object* v_b_408_){
_start:
{
size_t v_i_boxed_409_; size_t v_stop_boxed_410_; lean_object* v_res_411_; 
v_i_boxed_409_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_stop_boxed_410_ = lean_unbox_usize(v_stop_407_);
lean_dec(v_stop_407_);
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2(v_env_404_, v_as_405_, v_i_boxed_409_, v_stop_boxed_410_, v_b_408_);
lean_dec_ref(v_as_405_);
return v_res_411_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1(lean_object* v_env_412_, lean_object* v_as_413_, size_t v_i_414_, size_t v_stop_415_, lean_object* v_b_416_){
_start:
{
lean_object* v___y_418_; uint8_t v___x_422_; 
v___x_422_ = lean_usize_dec_eq(v_i_414_, v_stop_415_);
if (v___x_422_ == 0)
{
lean_object* v___x_423_; lean_object* v_fst_424_; uint8_t v___x_425_; lean_object* v___x_426_; uint8_t v___x_427_; 
v___x_423_ = lean_array_uget_borrowed(v_as_413_, v_i_414_);
v_fst_424_ = lean_ctor_get(v___x_423_, 0);
v___x_425_ = 1;
lean_inc_ref(v_env_412_);
v___x_426_ = l_Lean_Environment_setExporting(v_env_412_, v___x_425_);
lean_inc(v_fst_424_);
v___x_427_ = l_Lean_Environment_contains(v___x_426_, v_fst_424_, v___x_425_);
if (v___x_427_ == 0)
{
v___y_418_ = v_b_416_;
goto v___jp_417_;
}
else
{
lean_object* v___x_428_; 
lean_inc(v___x_423_);
v___x_428_ = lean_array_push(v_b_416_, v___x_423_);
v___y_418_ = v___x_428_;
goto v___jp_417_;
}
}
else
{
lean_dec_ref(v_env_412_);
return v_b_416_;
}
v___jp_417_:
{
size_t v___x_419_; size_t v___x_420_; 
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_add(v_i_414_, v___x_419_);
v_i_414_ = v___x_420_;
v_b_416_ = v___y_418_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_412_ = stack[0].m_obj;
lean_object* v_as_413_ = stack[1].m_obj;
size_t v_i_414_ = stack[2].m_num;
size_t v_stop_415_ = stack[3].m_num;
lean_object* v_b_416_ = stack[4].m_obj;
lean_object* v_res_429_;
v_res_429_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1(v_env_412_, v_as_413_, v_i_414_, v_stop_415_, v_b_416_);
stack->m_obj
 = v_res_429_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_430_, lean_object* v_as_431_, lean_object* v_i_432_, lean_object* v_stop_433_, lean_object* v_b_434_){
_start:
{
size_t v_i_boxed_435_; size_t v_stop_boxed_436_; lean_object* v_res_437_; 
v_i_boxed_435_ = lean_unbox_usize(v_i_432_);
lean_dec(v_i_432_);
v_stop_boxed_436_ = lean_unbox_usize(v_stop_433_);
lean_dec(v_stop_433_);
v_res_437_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1(v_env_430_, v_as_431_, v_i_boxed_435_, v_stop_boxed_436_, v_b_434_);
lean_dec_ref(v_as_431_);
return v_res_437_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_438_, lean_object* v_x_439_){
_start:
{
if (lean_obj_tag(v_x_439_) == 0)
{
lean_object* v_k_440_; lean_object* v_v_441_; lean_object* v_l_442_; lean_object* v_r_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; 
v_k_440_ = lean_ctor_get(v_x_439_, 1);
v_v_441_ = lean_ctor_get(v_x_439_, 2);
v_l_442_ = lean_ctor_get(v_x_439_, 3);
v_r_443_ = lean_ctor_get(v_x_439_, 4);
v___x_444_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0(v_init_438_, v_l_442_);
lean_inc(v_v_441_);
lean_inc(v_k_440_);
v___x_445_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_445_, 0, v_k_440_);
lean_ctor_set(v___x_445_, 1, v_v_441_);
v___x_446_ = lean_array_push(v___x_444_, v___x_445_);
v_init_438_ = v___x_446_;
v_x_439_ = v_r_443_;
goto _start;
}
else
{
return v_init_438_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_448_, lean_object* v_x_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0(v_init_448_, v_x_449_);
lean_dec(v_x_449_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_(lean_object* v_env_455_, lean_object* v_s_456_){
_start:
{
lean_object* v___x_457_; lean_object* v___y_459_; lean_object* v___x_474_; lean_object* v___x_475_; lean_object* v___x_476_; lean_object* v___x_477_; uint8_t v___x_478_; 
v___x_457_ = lean_unsigned_to_nat(0u);
v___x_474_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_));
v___x_475_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0(v___x_474_, v_s_456_);
v___x_476_ = lean_array_get_size(v___x_475_);
v___x_477_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_));
v___x_478_ = lean_nat_dec_lt(v___x_457_, v___x_476_);
if (v___x_478_ == 0)
{
lean_dec_ref(v___x_475_);
v___y_459_ = v___x_477_;
goto v___jp_458_;
}
else
{
uint8_t v___x_479_; 
v___x_479_ = lean_nat_dec_le(v___x_476_, v___x_476_);
if (v___x_479_ == 0)
{
if (v___x_478_ == 0)
{
lean_dec_ref(v___x_475_);
v___y_459_ = v___x_477_;
goto v___jp_458_;
}
else
{
size_t v___x_480_; size_t v___x_481_; lean_object* v___x_482_; 
v___x_480_ = ((size_t)0ULL);
v___x_481_ = lean_usize_of_nat(v___x_476_);
lean_inc_ref(v_env_455_);
v___x_482_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2(v_env_455_, v___x_475_, v___x_480_, v___x_481_, v___x_477_);
lean_dec_ref(v___x_475_);
v___y_459_ = v___x_482_;
goto v___jp_458_;
}
}
else
{
size_t v___x_483_; size_t v___x_484_; lean_object* v___x_485_; 
v___x_483_ = ((size_t)0ULL);
v___x_484_ = lean_usize_of_nat(v___x_476_);
lean_inc_ref(v_env_455_);
v___x_485_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__2(v_env_455_, v___x_475_, v___x_483_, v___x_484_, v___x_477_);
lean_dec_ref(v___x_475_);
v___y_459_ = v___x_485_;
goto v___jp_458_;
}
}
v___jp_458_:
{
lean_object* v___x_460_; lean_object* v___x_461_; uint8_t v___x_462_; 
v___x_460_ = lean_array_get_size(v___y_459_);
v___x_461_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_));
v___x_462_ = lean_nat_dec_lt(v___x_457_, v___x_460_);
if (v___x_462_ == 0)
{
lean_object* v___x_463_; 
lean_dec_ref(v_env_455_);
v___x_463_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_463_, 0, v___x_461_);
lean_ctor_set(v___x_463_, 1, v___x_461_);
lean_ctor_set(v___x_463_, 2, v___y_459_);
return v___x_463_;
}
else
{
uint8_t v___x_464_; 
v___x_464_ = lean_nat_dec_le(v___x_460_, v___x_460_);
if (v___x_464_ == 0)
{
if (v___x_462_ == 0)
{
lean_object* v___x_465_; 
lean_dec_ref(v_env_455_);
v___x_465_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_465_, 0, v___x_461_);
lean_ctor_set(v___x_465_, 1, v___x_461_);
lean_ctor_set(v___x_465_, 2, v___y_459_);
return v___x_465_;
}
else
{
size_t v___x_466_; size_t v___x_467_; lean_object* v___x_468_; lean_object* v___x_469_; 
v___x_466_ = ((size_t)0ULL);
v___x_467_ = lean_usize_of_nat(v___x_460_);
v___x_468_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1(v_env_455_, v___y_459_, v___x_466_, v___x_467_, v___x_461_);
lean_inc_ref(v___x_468_);
v___x_469_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_469_, 0, v___x_468_);
lean_ctor_set(v___x_469_, 1, v___x_468_);
lean_ctor_set(v___x_469_, 2, v___y_459_);
return v___x_469_;
}
}
else
{
size_t v___x_470_; size_t v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; 
v___x_470_ = ((size_t)0ULL);
v___x_471_ = lean_usize_of_nat(v___x_460_);
v___x_472_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__1(v_env_455_, v___y_459_, v___x_470_, v___x_471_, v___x_461_);
lean_inc_ref(v___x_472_);
v___x_473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_473_, 0, v___x_472_);
lean_ctor_set(v___x_473_, 1, v___x_472_);
lean_ctor_set(v___x_473_, 2, v___y_459_);
return v___x_473_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2____boxed(lean_object* v_env_486_, lean_object* v_s_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Lean_ProjFns_0__Lean_initFn___lam__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_(v_env_486_, v_s_487_);
lean_dec(v_s_487_);
return v_res_488_;
}
}
lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_495_; lean_object* v___x_496_; lean_object* v___x_497_; uint8_t v___x_498_; lean_object* v___x_499_; 
v___f_495_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__0_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_));
v___x_496_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__2_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_));
v___x_497_ = ((lean_object*)(l___private_Lean_ProjFns_0__Lean_initFn___closed__4_00___x40_Lean_ProjFns_2949225815____hygCtx___hyg_2_));
v___x_498_ = 1;
v___x_499_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_496_, v___x_497_, v___x_498_, v___f_495_);
return v___x_499_;
}
}
LEAN_EXPORT void l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_500_;
v_res_500_ = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_();
stack->m_obj
 = v_res_500_;
}
LEAN_EXPORT lean_object* l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2____boxed(lean_object* v_a_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2_();
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0(lean_object* v_init_503_, lean_object* v_t_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0_spec__0(v_init_503_, v_t_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_506_, lean_object* v_t_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00__private_Lean_ProjFns_0__Lean_initFn_00___x40_Lean_ProjFns_2425873161____hygCtx___hyg_2__spec__0(v_init_506_, v_t_507_);
lean_dec(v_t_507_);
return v_res_508_;
}
}
lean_object* l_Lean_addAuxParentProjectionInfo(lean_object* v_env_509_, lean_object* v_projName_510_, lean_object* v_numParams_511_, uint8_t v_fromClass_512_){
_start:
{
lean_object* v___x_513_; lean_object* v___x_514_; uint8_t v___x_515_; lean_object* v___x_516_; 
v___x_513_ = l_Lean_auxParentProjInfoExt;
v___x_514_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_514_, 0, v_numParams_511_);
lean_ctor_set_uint8(v___x_514_, sizeof(void*)*1, v_fromClass_512_);
v___x_515_ = 0;
v___x_516_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_513_, v_env_509_, v_projName_510_, v___x_514_, v___x_515_);
return v___x_516_;
}
}
LEAN_EXPORT void l_Lean_addAuxParentProjectionInfo_0interp(lean_interpreter_value* stack)
{
lean_object* v_env_509_ = stack[0].m_obj;
lean_object* v_projName_510_ = stack[1].m_obj;
lean_object* v_numParams_511_ = stack[2].m_obj;
uint8_t v_fromClass_512_ = stack[3].m_num;
lean_object* v_res_517_;
v_res_517_ = l_Lean_addAuxParentProjectionInfo(v_env_509_, v_projName_510_, v_numParams_511_, v_fromClass_512_);
stack->m_obj
 = v_res_517_;
}
LEAN_EXPORT lean_object* l_Lean_addAuxParentProjectionInfo___boxed(lean_object* v_env_518_, lean_object* v_projName_519_, lean_object* v_numParams_520_, lean_object* v_fromClass_521_){
_start:
{
uint8_t v_fromClass_boxed_522_; lean_object* v_res_523_; 
v_fromClass_boxed_522_ = lean_unbox(v_fromClass_521_);
v_res_523_ = l_Lean_addAuxParentProjectionInfo(v_env_518_, v_projName_519_, v_numParams_520_, v_fromClass_boxed_522_);
return v_res_523_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getAuxParentProjectionInfo_x3f(lean_object* v_env_524_, lean_object* v_projName_525_){
_start:
{
lean_object* v___x_526_; lean_object* v_toEnvExtension_527_; lean_object* v_asyncMode_528_; lean_object* v___x_529_; uint8_t v___x_530_; lean_object* v___x_531_; 
v___x_526_ = l_Lean_auxParentProjInfoExt;
v_toEnvExtension_527_ = lean_ctor_get(v___x_526_, 0);
v_asyncMode_528_ = lean_ctor_get(v_toEnvExtension_527_, 2);
v___x_529_ = ((lean_object*)(l_Lean_instInhabitedAuxParentProjectionInfo_default));
v___x_530_ = 0;
v___x_531_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_529_, v___x_526_, v_env_524_, v_projName_525_, v_asyncMode_528_, v___x_530_);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0(lean_object* v_declName_532_, lean_object* v_toPure_533_, lean_object* v_____do__lift_534_){
_start:
{
lean_object* v___x_535_; lean_object* v___x_536_; 
v___x_535_ = l_Lean_Environment_getAuxParentProjectionInfo_x3f(v_____do__lift_534_, v_declName_532_);
v___x_536_ = lean_apply_2(v_toPure_533_, lean_box(0), v___x_535_);
return v___x_536_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f___redArg(lean_object* v_inst_537_, lean_object* v_inst_538_, lean_object* v_declName_539_){
_start:
{
lean_object* v_toApplicative_540_; lean_object* v_toBind_541_; lean_object* v_getEnv_542_; lean_object* v_toPure_543_; lean_object* v___f_544_; lean_object* v___x_545_; 
v_toApplicative_540_ = lean_ctor_get(v_inst_538_, 0);
lean_inc_ref(v_toApplicative_540_);
v_toBind_541_ = lean_ctor_get(v_inst_538_, 1);
lean_inc(v_toBind_541_);
lean_dec_ref(v_inst_538_);
v_getEnv_542_ = lean_ctor_get(v_inst_537_, 0);
lean_inc(v_getEnv_542_);
lean_dec_ref(v_inst_537_);
v_toPure_543_ = lean_ctor_get(v_toApplicative_540_, 1);
lean_inc(v_toPure_543_);
lean_dec_ref(v_toApplicative_540_);
v___f_544_ = lean_alloc_closure((void*)(l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_544_, 0, v_declName_539_);
lean_closure_set(v___f_544_, 1, v_toPure_543_);
v___x_545_ = lean_apply_4(v_toBind_541_, lean_box(0), lean_box(0), v_getEnv_542_, v___f_544_);
return v___x_545_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f(lean_object* v_m_546_, lean_object* v_inst_547_, lean_object* v_inst_548_, lean_object* v_declName_549_){
_start:
{
lean_object* v___x_550_; 
v___x_550_ = l_Lean_getAuxParentProjectionInfo_x3f___redArg(v_inst_547_, v_inst_548_, v_declName_549_);
return v___x_550_;
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
