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
lean_object* l_Lean_Name_mkStr2(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lean_mk_projection_info(lean_object*, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_mkProjectionInfoEx___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t lean_projection_info_from_class(lean_object*);
LEAN_EXPORT lean_object* l_Lean_ProjectionFunctionInfo_fromClassEx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 5, .m_capacity = 5, .m_length = 4, .m_data = "Lean"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "projectionFnInfoExt"};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(16, 172, 107, 39, 139, 106, 85, 71)}};
static const lean_object* l_Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*0 + 8, .m_other = 0, .m_tag = 3}, .m_objs = {LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*);
static const lean_array_object l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value;
static const lean_array_object l_Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed, .m_arity = 3, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 21, .m_capacity = 21, .m_length = 20, .m_data = "auxParentProjInfoExt"};
static const lean_object* l_Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value_aux_0 = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(70, 193, 83, 126, 233, 67, 208, 165)}};
static const lean_ctor_object l_Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value_aux_0),((lean_object*)&l_Lean_initFn___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(4, 64, 229, 66, 82, 134, 114, 43)}};
static const lean_object* l_Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__value;
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* lean_mk_projection_info(lean_object* v_ctorName_111_, lean_object* v_numParams_112_, lean_object* v_i_113_, uint8_t v_fromClass_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_115_, 0, v_ctorName_111_);
lean_ctor_set(v___x_115_, 1, v_numParams_112_);
lean_ctor_set(v___x_115_, 2, v_i_113_);
lean_ctor_set_uint8(v___x_115_, sizeof(void*)*3, v_fromClass_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_mkProjectionInfoEx___boxed(lean_object* v_ctorName_116_, lean_object* v_numParams_117_, lean_object* v_i_118_, lean_object* v_fromClass_119_){
_start:
{
uint8_t v_fromClass_boxed_120_; lean_object* v_res_121_; 
v_fromClass_boxed_120_ = lean_unbox(v_fromClass_119_);
v_res_121_ = lean_mk_projection_info(v_ctorName_116_, v_numParams_117_, v_i_118_, v_fromClass_boxed_120_);
return v_res_121_;
}
}
LEAN_EXPORT uint8_t lean_projection_info_from_class(lean_object* v_info_122_){
_start:
{
uint8_t v_fromClass_123_; 
v_fromClass_123_ = lean_ctor_get_uint8(v_info_122_, sizeof(void*)*3);
lean_dec_ref(v_info_122_);
return v_fromClass_123_;
}
}
LEAN_EXPORT lean_object* l_Lean_ProjectionFunctionInfo_fromClassEx___boxed(lean_object* v_info_124_){
_start:
{
uint8_t v_res_125_; lean_object* v_r_126_; 
v_res_125_ = lean_projection_info_from_class(v_info_124_);
v_r_126_ = lean_box(v_res_125_);
return v_r_126_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_127_, lean_object* v_x_128_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v_k_129_; lean_object* v_v_130_; lean_object* v_l_131_; lean_object* v_r_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; 
v_k_129_ = lean_ctor_get(v_x_128_, 1);
v_v_130_ = lean_ctor_get(v_x_128_, 2);
v_l_131_ = lean_ctor_get(v_x_128_, 3);
v_r_132_ = lean_ctor_get(v_x_128_, 4);
v___x_133_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_127_, v_l_131_);
lean_inc(v_v_130_);
lean_inc(v_k_129_);
v___x_134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_134_, 0, v_k_129_);
lean_ctor_set(v___x_134_, 1, v_v_130_);
v___x_135_ = lean_array_push(v___x_133_, v___x_134_);
v_init_127_ = v___x_135_;
v_x_128_ = v_r_132_;
goto _start;
}
else
{
return v_init_127_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_137_, lean_object* v_x_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_137_, v_x_138_);
lean_dec(v_x_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(lean_object* v_env_140_, lean_object* v_as_141_, size_t v_i_142_, size_t v_stop_143_, lean_object* v_b_144_){
_start:
{
lean_object* v___y_146_; uint8_t v___x_150_; 
v___x_150_ = lean_usize_dec_eq(v_i_142_, v_stop_143_);
if (v___x_150_ == 0)
{
lean_object* v___x_151_; lean_object* v_fst_152_; uint8_t v___x_153_; 
v___x_151_ = lean_array_uget_borrowed(v_as_141_, v_i_142_);
v_fst_152_ = lean_ctor_get(v___x_151_, 0);
lean_inc(v_fst_152_);
lean_inc_ref(v_env_140_);
v___x_153_ = l_Lean_Environment_contains(v_env_140_, v_fst_152_, v___x_150_);
if (v___x_153_ == 0)
{
v___y_146_ = v_b_144_;
goto v___jp_145_;
}
else
{
lean_object* v___x_154_; 
lean_inc(v___x_151_);
v___x_154_ = lean_array_push(v_b_144_, v___x_151_);
v___y_146_ = v___x_154_;
goto v___jp_145_;
}
}
else
{
lean_dec_ref(v_env_140_);
return v_b_144_;
}
v___jp_145_:
{
size_t v___x_147_; size_t v___x_148_; 
v___x_147_ = ((size_t)1ULL);
v___x_148_ = lean_usize_add(v_i_142_, v___x_147_);
v_i_142_ = v___x_148_;
v_b_144_ = v___y_146_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_155_, lean_object* v_as_156_, lean_object* v_i_157_, lean_object* v_stop_158_, lean_object* v_b_159_){
_start:
{
size_t v_i_boxed_160_; size_t v_stop_boxed_161_; lean_object* v_res_162_; 
v_i_boxed_160_ = lean_unbox_usize(v_i_157_);
lean_dec(v_i_157_);
v_stop_boxed_161_ = lean_unbox_usize(v_stop_158_);
lean_dec(v_stop_158_);
v_res_162_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_155_, v_as_156_, v_i_boxed_160_, v_stop_boxed_161_, v_b_159_);
lean_dec_ref(v_as_156_);
return v_res_162_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(lean_object* v_env_167_, lean_object* v_s_168_, uint8_t v_x_169_){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; lean_object* v___x_174_; uint8_t v___x_175_; 
v___x_170_ = lean_unsigned_to_nat(0u);
v___x_171_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_172_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v___x_171_, v_s_168_);
v___x_173_ = lean_array_get_size(v___x_172_);
v___x_174_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_175_ = lean_nat_dec_lt(v___x_170_, v___x_173_);
if (v___x_175_ == 0)
{
lean_dec_ref(v___x_172_);
lean_dec_ref(v_env_167_);
return v___x_174_;
}
else
{
uint8_t v___x_176_; 
v___x_176_ = lean_nat_dec_le(v___x_173_, v___x_173_);
if (v___x_176_ == 0)
{
if (v___x_175_ == 0)
{
lean_dec_ref(v___x_172_);
lean_dec_ref(v_env_167_);
return v___x_174_;
}
else
{
size_t v___x_177_; size_t v___x_178_; lean_object* v___x_179_; 
v___x_177_ = ((size_t)0ULL);
v___x_178_ = lean_usize_of_nat(v___x_173_);
v___x_179_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_167_, v___x_172_, v___x_177_, v___x_178_, v___x_174_);
lean_dec_ref(v___x_172_);
return v___x_179_;
}
}
else
{
size_t v___x_180_; size_t v___x_181_; lean_object* v___x_182_; 
v___x_180_ = ((size_t)0ULL);
v___x_181_ = lean_usize_of_nat(v___x_173_);
v___x_182_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__1(v_env_167_, v___x_172_, v___x_180_, v___x_181_, v___x_174_);
lean_dec_ref(v___x_172_);
return v___x_182_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(lean_object* v_env_183_, lean_object* v_s_184_, lean_object* v_x_185_){
_start:
{
uint8_t v_x_409__boxed_186_; lean_object* v_res_187_; 
v_x_409__boxed_186_ = lean_unbox(v_x_185_);
v_res_187_ = l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(v_env_183_, v_s_184_, v_x_409__boxed_186_);
lean_dec(v_s_184_);
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_197_; lean_object* v___x_198_; lean_object* v___x_199_; lean_object* v___x_200_; 
v___f_197_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_198_ = ((lean_object*)(l_Lean_initFn___closed__3_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_199_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_200_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_198_, v___x_199_, v___f_197_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2____boxed(lean_object* v_a_201_){
_start:
{
lean_object* v_res_202_; 
v_res_202_ = l_Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_();
return v_res_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0(lean_object* v_init_203_, lean_object* v_t_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0_spec__0(v_init_203_, v_t_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_206_, lean_object* v_t_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2__spec__0(v_init_206_, v_t_207_);
lean_dec(v_t_207_);
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_Lean_addProjectionFnInfo(lean_object* v_env_209_, lean_object* v_projName_210_, lean_object* v_ctorName_211_, lean_object* v_numParams_212_, lean_object* v_i_213_, uint8_t v_fromClass_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_215_ = l_Lean_projectionFnInfoExt;
v___x_216_ = lean_alloc_ctor(0, 3, 1);
lean_ctor_set(v___x_216_, 0, v_ctorName_211_);
lean_ctor_set(v___x_216_, 1, v_numParams_212_);
lean_ctor_set(v___x_216_, 2, v_i_213_);
lean_ctor_set_uint8(v___x_216_, sizeof(void*)*3, v_fromClass_214_);
v___x_217_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_215_, v_env_209_, v_projName_210_, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_addProjectionFnInfo___boxed(lean_object* v_env_218_, lean_object* v_projName_219_, lean_object* v_ctorName_220_, lean_object* v_numParams_221_, lean_object* v_i_222_, lean_object* v_fromClass_223_){
_start:
{
uint8_t v_fromClass_boxed_224_; lean_object* v_res_225_; 
v_fromClass_boxed_224_ = lean_unbox(v_fromClass_223_);
v_res_225_ = l_Lean_addProjectionFnInfo(v_env_218_, v_projName_219_, v_ctorName_220_, v_numParams_221_, v_i_222_, v_fromClass_boxed_224_);
return v_res_225_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionFnInfo_x3f(lean_object* v_env_226_, lean_object* v_projName_227_){
_start:
{
lean_object* v___x_228_; lean_object* v_toEnvExtension_229_; lean_object* v_asyncMode_230_; lean_object* v___x_231_; uint8_t v___x_232_; lean_object* v___x_233_; 
v___x_228_ = l_Lean_projectionFnInfoExt;
v_toEnvExtension_229_ = lean_ctor_get(v___x_228_, 0);
lean_inc_ref(v_toEnvExtension_229_);
v_asyncMode_230_ = lean_ctor_get(v_toEnvExtension_229_, 2);
lean_inc(v_asyncMode_230_);
lean_dec_ref(v_toEnvExtension_229_);
v___x_231_ = ((lean_object*)(l_Lean_instInhabitedProjectionFunctionInfo_default));
v___x_232_ = 0;
v___x_233_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_231_, v___x_228_, v_env_226_, v_projName_227_, v_asyncMode_230_, v___x_232_);
lean_dec(v_asyncMode_230_);
return v___x_233_;
}
}
LEAN_EXPORT uint8_t l_Lean_Environment_isProjectionFn(lean_object* v_env_234_, lean_object* v_declName_235_){
_start:
{
lean_object* v___x_236_; lean_object* v___x_237_; uint8_t v___x_238_; 
v___x_236_ = ((lean_object*)(l_Lean_instInhabitedProjectionFunctionInfo_default));
v___x_237_ = l_Lean_projectionFnInfoExt;
v___x_238_ = l_Lean_MapDeclarationExtension_contains___redArg(v___x_236_, v___x_237_, v_env_234_, v_declName_235_);
return v___x_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_isProjectionFn___boxed(lean_object* v_env_239_, lean_object* v_declName_240_){
_start:
{
uint8_t v_res_241_; lean_object* v_r_242_; 
v_res_241_ = l_Lean_Environment_isProjectionFn(v_env_239_, v_declName_240_);
v_r_242_ = lean_box(v_res_241_);
return v_r_242_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getProjectionStructureName_x3f(lean_object* v_env_243_, lean_object* v_projName_244_){
_start:
{
lean_object* v___x_245_; 
lean_inc_ref(v_env_243_);
v___x_245_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_env_243_, v_projName_244_);
if (lean_obj_tag(v___x_245_) == 0)
{
lean_object* v___x_246_; 
lean_dec_ref(v_env_243_);
v___x_246_ = lean_box(0);
return v___x_246_;
}
else
{
lean_object* v_val_247_; lean_object* v_ctorName_248_; uint8_t v___x_249_; lean_object* v___x_250_; 
v_val_247_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_val_247_);
lean_dec_ref(v___x_245_);
v_ctorName_248_ = lean_ctor_get(v_val_247_, 0);
lean_inc(v_ctorName_248_);
lean_dec(v_val_247_);
v___x_249_ = 0;
v___x_250_ = l_Lean_Environment_find_x3f(v_env_243_, v_ctorName_248_, v___x_249_);
if (lean_obj_tag(v___x_250_) == 1)
{
lean_object* v_val_251_; lean_object* v___x_253_; uint8_t v_isShared_254_; uint8_t v_isSharedCheck_261_; 
v_val_251_ = lean_ctor_get(v___x_250_, 0);
v_isSharedCheck_261_ = !lean_is_exclusive(v___x_250_);
if (v_isSharedCheck_261_ == 0)
{
v___x_253_ = v___x_250_;
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
else
{
lean_inc(v_val_251_);
lean_dec(v___x_250_);
v___x_253_ = lean_box(0);
v_isShared_254_ = v_isSharedCheck_261_;
goto v_resetjp_252_;
}
v_resetjp_252_:
{
if (lean_obj_tag(v_val_251_) == 6)
{
lean_object* v_val_255_; lean_object* v_induct_256_; lean_object* v___x_258_; 
v_val_255_ = lean_ctor_get(v_val_251_, 0);
lean_inc_ref(v_val_255_);
lean_dec_ref(v_val_251_);
v_induct_256_ = lean_ctor_get(v_val_255_, 1);
lean_inc(v_induct_256_);
lean_dec_ref(v_val_255_);
if (v_isShared_254_ == 0)
{
lean_ctor_set(v___x_253_, 0, v_induct_256_);
v___x_258_ = v___x_253_;
goto v_reusejp_257_;
}
else
{
lean_object* v_reuseFailAlloc_259_; 
v_reuseFailAlloc_259_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_259_, 0, v_induct_256_);
v___x_258_ = v_reuseFailAlloc_259_;
goto v_reusejp_257_;
}
v_reusejp_257_:
{
return v___x_258_;
}
}
else
{
lean_object* v___x_260_; 
lean_del_object(v___x_253_);
lean_dec(v_val_251_);
v___x_260_ = lean_box(0);
return v___x_260_;
}
}
}
else
{
lean_object* v___x_262_; 
lean_dec(v___x_250_);
v___x_262_ = lean_box(0);
return v___x_262_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___redArg___lam__0(lean_object* v_declName_263_, lean_object* v_toPure_264_, lean_object* v_____do__lift_265_){
_start:
{
uint8_t v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; 
v___x_266_ = l_Lean_Environment_isProjectionFn(v_____do__lift_265_, v_declName_263_);
v___x_267_ = lean_box(v___x_266_);
v___x_268_ = lean_apply_2(v_toPure_264_, lean_box(0), v___x_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn___redArg(lean_object* v_inst_269_, lean_object* v_inst_270_, lean_object* v_declName_271_){
_start:
{
lean_object* v_toApplicative_272_; lean_object* v_toBind_273_; lean_object* v_getEnv_274_; lean_object* v_toPure_275_; lean_object* v___f_276_; lean_object* v___x_277_; 
v_toApplicative_272_ = lean_ctor_get(v_inst_270_, 0);
lean_inc_ref(v_toApplicative_272_);
v_toBind_273_ = lean_ctor_get(v_inst_270_, 1);
lean_inc(v_toBind_273_);
lean_dec_ref(v_inst_270_);
v_getEnv_274_ = lean_ctor_get(v_inst_269_, 0);
lean_inc(v_getEnv_274_);
lean_dec_ref(v_inst_269_);
v_toPure_275_ = lean_ctor_get(v_toApplicative_272_, 1);
lean_inc(v_toPure_275_);
lean_dec_ref(v_toApplicative_272_);
v___f_276_ = lean_alloc_closure((void*)(l_Lean_isProjectionFn___redArg___lam__0), 3, 2);
lean_closure_set(v___f_276_, 0, v_declName_271_);
lean_closure_set(v___f_276_, 1, v_toPure_275_);
v___x_277_ = lean_apply_4(v_toBind_273_, lean_box(0), lean_box(0), v_getEnv_274_, v___f_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Lean_isProjectionFn(lean_object* v_m_278_, lean_object* v_inst_279_, lean_object* v_inst_280_, lean_object* v_declName_281_){
_start:
{
lean_object* v___x_282_; 
v___x_282_ = l_Lean_isProjectionFn___redArg(v_inst_279_, v_inst_280_, v_declName_281_);
return v___x_282_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___redArg___lam__0(lean_object* v_declName_283_, lean_object* v_toPure_284_, lean_object* v_____do__lift_285_){
_start:
{
lean_object* v___x_286_; lean_object* v___x_287_; 
v___x_286_ = l_Lean_Environment_getProjectionFnInfo_x3f(v_____do__lift_285_, v_declName_283_);
v___x_287_ = lean_apply_2(v_toPure_284_, lean_box(0), v___x_286_);
return v___x_287_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f___redArg(lean_object* v_inst_288_, lean_object* v_inst_289_, lean_object* v_declName_290_){
_start:
{
lean_object* v_toApplicative_291_; lean_object* v_toBind_292_; lean_object* v_getEnv_293_; lean_object* v_toPure_294_; lean_object* v___f_295_; lean_object* v___x_296_; 
v_toApplicative_291_ = lean_ctor_get(v_inst_289_, 0);
lean_inc_ref(v_toApplicative_291_);
v_toBind_292_ = lean_ctor_get(v_inst_289_, 1);
lean_inc(v_toBind_292_);
lean_dec_ref(v_inst_289_);
v_getEnv_293_ = lean_ctor_get(v_inst_288_, 0);
lean_inc(v_getEnv_293_);
lean_dec_ref(v_inst_288_);
v_toPure_294_ = lean_ctor_get(v_toApplicative_291_, 1);
lean_inc(v_toPure_294_);
lean_dec_ref(v_toApplicative_291_);
v___f_295_ = lean_alloc_closure((void*)(l_Lean_getProjectionFnInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_295_, 0, v_declName_290_);
lean_closure_set(v___f_295_, 1, v_toPure_294_);
v___x_296_ = lean_apply_4(v_toBind_292_, lean_box(0), lean_box(0), v_getEnv_293_, v___f_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l_Lean_getProjectionFnInfo_x3f(lean_object* v_m_297_, lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_declName_300_){
_start:
{
lean_object* v___x_301_; 
v___x_301_ = l_Lean_getProjectionFnInfo_x3f___redArg(v_inst_298_, v_inst_299_, v_declName_300_);
return v___x_301_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___redArg(lean_object* v_x_313_){
_start:
{
lean_object* v_numParams_314_; uint8_t v_fromClass_315_; lean_object* v___x_317_; uint8_t v_isShared_318_; uint8_t v_isSharedCheck_348_; 
v_numParams_314_ = lean_ctor_get(v_x_313_, 0);
v_fromClass_315_ = lean_ctor_get_uint8(v_x_313_, sizeof(void*)*1);
v_isSharedCheck_348_ = !lean_is_exclusive(v_x_313_);
if (v_isSharedCheck_348_ == 0)
{
v___x_317_ = v_x_313_;
v_isShared_318_ = v_isSharedCheck_348_;
goto v_resetjp_316_;
}
else
{
lean_inc(v_numParams_314_);
lean_dec(v_x_313_);
v___x_317_ = lean_box(0);
v_isShared_318_ = v_isSharedCheck_348_;
goto v_resetjp_316_;
}
v_resetjp_316_:
{
lean_object* v___x_319_; lean_object* v___x_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; uint8_t v___x_325_; lean_object* v___x_327_; 
v___x_319_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__5));
v___x_320_ = ((lean_object*)(l_Lean_instReprAuxParentProjectionInfo_repr___redArg___closed__1));
v___x_321_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__12);
v___x_322_ = l_Nat_reprFast(v_numParams_314_);
v___x_323_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_323_, 0, v___x_322_);
v___x_324_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_324_, 0, v___x_321_);
lean_ctor_set(v___x_324_, 1, v___x_323_);
v___x_325_ = 0;
if (v_isShared_318_ == 0)
{
lean_ctor_set_tag(v___x_317_, 6);
lean_ctor_set(v___x_317_, 0, v___x_324_);
v___x_327_ = v___x_317_;
goto v_reusejp_326_;
}
else
{
lean_object* v_reuseFailAlloc_347_; 
v_reuseFailAlloc_347_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v_reuseFailAlloc_347_, 0, v___x_324_);
v___x_327_ = v_reuseFailAlloc_347_;
goto v_reusejp_326_;
}
v_reusejp_326_:
{
lean_object* v___x_328_; lean_object* v___x_329_; lean_object* v___x_330_; lean_object* v___x_331_; lean_object* v___x_332_; lean_object* v___x_333_; lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
lean_ctor_set_uint8(v___x_327_, sizeof(void*)*1, v___x_325_);
v___x_328_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_328_, 0, v___x_320_);
lean_ctor_set(v___x_328_, 1, v___x_327_);
v___x_329_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__9));
v___x_330_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_330_, 0, v___x_328_);
lean_ctor_set(v___x_330_, 1, v___x_329_);
v___x_331_ = lean_box(1);
v___x_332_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_332_, 0, v___x_330_);
lean_ctor_set(v___x_332_, 1, v___x_331_);
v___x_333_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__17));
v___x_334_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_334_, 0, v___x_332_);
lean_ctor_set(v___x_334_, 1, v___x_333_);
v___x_335_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_335_, 0, v___x_334_);
lean_ctor_set(v___x_335_, 1, v___x_319_);
v___x_336_ = l_Bool_repr___redArg(v_fromClass_315_);
v___x_337_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_337_, 0, v___x_321_);
lean_ctor_set(v___x_337_, 1, v___x_336_);
v___x_338_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_338_, 0, v___x_337_);
lean_ctor_set_uint8(v___x_338_, sizeof(void*)*1, v___x_325_);
v___x_339_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_339_, 0, v___x_335_);
lean_ctor_set(v___x_339_, 1, v___x_338_);
v___x_340_ = lean_obj_once(&l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20, &l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20_once, _init_l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__20);
v___x_341_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__21));
v___x_342_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_342_, 0, v___x_341_);
lean_ctor_set(v___x_342_, 1, v___x_339_);
v___x_343_ = ((lean_object*)(l_Lean_instReprProjectionFunctionInfo_repr___redArg___closed__22));
v___x_344_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v___x_344_, 0, v___x_342_);
lean_ctor_set(v___x_344_, 1, v___x_343_);
v___x_345_ = lean_alloc_ctor(4, 2, 0);
lean_ctor_set(v___x_345_, 0, v___x_340_);
lean_ctor_set(v___x_345_, 1, v___x_344_);
v___x_346_ = lean_alloc_ctor(6, 1, 1);
lean_ctor_set(v___x_346_, 0, v___x_345_);
lean_ctor_set_uint8(v___x_346_, sizeof(void*)*1, v___x_325_);
return v___x_346_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr(lean_object* v_x_349_, lean_object* v_prec_350_){
_start:
{
lean_object* v___x_351_; 
v___x_351_ = l_Lean_instReprAuxParentProjectionInfo_repr___redArg(v_x_349_);
return v___x_351_;
}
}
LEAN_EXPORT lean_object* l_Lean_instReprAuxParentProjectionInfo_repr___boxed(lean_object* v_x_352_, lean_object* v_prec_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l_Lean_instReprAuxParentProjectionInfo_repr(v_x_352_, v_prec_353_);
lean_dec(v_prec_353_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(lean_object* v_env_357_, lean_object* v_as_358_, size_t v_i_359_, size_t v_stop_360_, lean_object* v_b_361_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1___boxed(lean_object* v_env_372_, lean_object* v_as_373_, lean_object* v_i_374_, lean_object* v_stop_375_, lean_object* v_b_376_){
_start:
{
size_t v_i_boxed_377_; size_t v_stop_boxed_378_; lean_object* v_res_379_; 
v_i_boxed_377_ = lean_unbox_usize(v_i_374_);
lean_dec(v_i_374_);
v_stop_boxed_378_ = lean_unbox_usize(v_stop_375_);
lean_dec(v_stop_375_);
v_res_379_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_372_, v_as_373_, v_i_boxed_377_, v_stop_boxed_378_, v_b_376_);
lean_dec_ref(v_as_373_);
return v_res_379_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_init_380_, lean_object* v_x_381_){
_start:
{
if (lean_obj_tag(v_x_381_) == 0)
{
lean_object* v_k_382_; lean_object* v_v_383_; lean_object* v_l_384_; lean_object* v_r_385_; lean_object* v___x_386_; lean_object* v___x_387_; lean_object* v___x_388_; 
v_k_382_ = lean_ctor_get(v_x_381_, 1);
v_v_383_ = lean_ctor_get(v_x_381_, 2);
v_l_384_ = lean_ctor_get(v_x_381_, 3);
v_r_385_ = lean_ctor_get(v_x_381_, 4);
v___x_386_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_380_, v_l_384_);
lean_inc(v_v_383_);
lean_inc(v_k_382_);
v___x_387_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_387_, 0, v_k_382_);
lean_ctor_set(v___x_387_, 1, v_v_383_);
v___x_388_ = lean_array_push(v___x_386_, v___x_387_);
v_init_380_ = v___x_388_;
v_x_381_ = v_r_385_;
goto _start;
}
else
{
return v_init_380_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_init_390_, lean_object* v_x_391_){
_start:
{
lean_object* v_res_392_; 
v_res_392_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_390_, v_x_391_);
lean_dec(v_x_391_);
return v_res_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(lean_object* v_env_397_, lean_object* v_s_398_, uint8_t v_x_399_){
_start:
{
lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_403_; lean_object* v___x_404_; uint8_t v___x_405_; 
v___x_400_ = lean_unsigned_to_nat(0u);
v___x_401_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_));
v___x_402_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v___x_401_, v_s_398_);
v___x_403_ = lean_array_get_size(v___x_402_);
v___x_404_ = ((lean_object*)(l_Lean_initFn___lam__0___closed__1_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_));
v___x_405_ = lean_nat_dec_lt(v___x_400_, v___x_403_);
if (v___x_405_ == 0)
{
lean_dec_ref(v___x_402_);
lean_dec_ref(v_env_397_);
return v___x_404_;
}
else
{
uint8_t v___x_406_; 
v___x_406_ = lean_nat_dec_le(v___x_403_, v___x_403_);
if (v___x_406_ == 0)
{
if (v___x_405_ == 0)
{
lean_dec_ref(v___x_402_);
lean_dec_ref(v_env_397_);
return v___x_404_;
}
else
{
size_t v___x_407_; size_t v___x_408_; lean_object* v___x_409_; 
v___x_407_ = ((size_t)0ULL);
v___x_408_ = lean_usize_of_nat(v___x_403_);
v___x_409_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_397_, v___x_402_, v___x_407_, v___x_408_, v___x_404_);
lean_dec_ref(v___x_402_);
return v___x_409_;
}
}
else
{
size_t v___x_410_; size_t v___x_411_; lean_object* v___x_412_; 
v___x_410_ = ((size_t)0ULL);
v___x_411_ = lean_usize_of_nat(v___x_403_);
v___x_412_ = l___private_Init_Data_Array_Basic_0__Array_foldlMUnsafe_fold___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__1(v_env_397_, v___x_402_, v___x_410_, v___x_411_, v___x_404_);
lean_dec_ref(v___x_402_);
return v___x_412_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(lean_object* v_env_413_, lean_object* v_s_414_, lean_object* v_x_415_){
_start:
{
uint8_t v_x_409__boxed_416_; lean_object* v_res_417_; 
v_x_409__boxed_416_ = lean_unbox(v_x_415_);
v_res_417_ = l_Lean_initFn___lam__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(v_env_413_, v_s_414_, v_x_409__boxed_416_);
lean_dec(v_s_414_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_(){
_start:
{
lean_object* v___f_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; 
v___f_424_ = ((lean_object*)(l_Lean_initFn___closed__0_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_));
v___x_425_ = ((lean_object*)(l_Lean_initFn___closed__2_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_));
v___x_426_ = ((lean_object*)(l_Lean_initFn___closed__4_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_));
v___x_427_ = l_Lean_mkMapDeclarationExtension___redArg(v___x_425_, v___x_426_, v___f_424_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l_Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2____boxed(lean_object* v_a_428_){
_start:
{
lean_object* v_res_429_; 
v_res_429_ = l_Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_();
return v_res_429_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0(lean_object* v_init_430_, lean_object* v_t_431_){
_start:
{
lean_object* v___x_432_; 
v___x_432_ = l_Std_DTreeMap_Internal_Impl_foldlM___at___00Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0_spec__0(v_init_430_, v_t_431_);
return v___x_432_;
}
}
LEAN_EXPORT lean_object* l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0___boxed(lean_object* v_init_433_, lean_object* v_t_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_DTreeMap_Internal_Impl_foldl___at___00Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2__spec__0(v_init_433_, v_t_434_);
lean_dec(v_t_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAuxParentProjectionInfo(lean_object* v_env_436_, lean_object* v_projName_437_, lean_object* v_numParams_438_, uint8_t v_fromClass_439_){
_start:
{
lean_object* v___x_440_; lean_object* v___x_441_; lean_object* v___x_442_; 
v___x_440_ = l_Lean_auxParentProjInfoExt;
v___x_441_ = lean_alloc_ctor(0, 1, 1);
lean_ctor_set(v___x_441_, 0, v_numParams_438_);
lean_ctor_set_uint8(v___x_441_, sizeof(void*)*1, v_fromClass_439_);
v___x_442_ = l_Lean_MapDeclarationExtension_insert___redArg(v___x_440_, v_env_436_, v_projName_437_, v___x_441_);
return v___x_442_;
}
}
LEAN_EXPORT lean_object* l_Lean_addAuxParentProjectionInfo___boxed(lean_object* v_env_443_, lean_object* v_projName_444_, lean_object* v_numParams_445_, lean_object* v_fromClass_446_){
_start:
{
uint8_t v_fromClass_boxed_447_; lean_object* v_res_448_; 
v_fromClass_boxed_447_ = lean_unbox(v_fromClass_446_);
v_res_448_ = l_Lean_addAuxParentProjectionInfo(v_env_443_, v_projName_444_, v_numParams_445_, v_fromClass_boxed_447_);
return v_res_448_;
}
}
LEAN_EXPORT lean_object* l_Lean_Environment_getAuxParentProjectionInfo_x3f(lean_object* v_env_449_, lean_object* v_projName_450_){
_start:
{
lean_object* v___x_451_; lean_object* v_toEnvExtension_452_; lean_object* v_asyncMode_453_; lean_object* v___x_454_; uint8_t v___x_455_; lean_object* v___x_456_; 
v___x_451_ = l_Lean_auxParentProjInfoExt;
v_toEnvExtension_452_ = lean_ctor_get(v___x_451_, 0);
lean_inc_ref(v_toEnvExtension_452_);
v_asyncMode_453_ = lean_ctor_get(v_toEnvExtension_452_, 2);
lean_inc(v_asyncMode_453_);
lean_dec_ref(v_toEnvExtension_452_);
v___x_454_ = ((lean_object*)(l_Lean_instInhabitedAuxParentProjectionInfo_default));
v___x_455_ = 0;
v___x_456_ = l_Lean_MapDeclarationExtension_find_x3f___redArg(v___x_454_, v___x_451_, v_env_449_, v_projName_450_, v_asyncMode_453_, v___x_455_);
lean_dec(v_asyncMode_453_);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0(lean_object* v_declName_457_, lean_object* v_toPure_458_, lean_object* v_____do__lift_459_){
_start:
{
lean_object* v___x_460_; lean_object* v___x_461_; 
v___x_460_ = l_Lean_Environment_getAuxParentProjectionInfo_x3f(v_____do__lift_459_, v_declName_457_);
v___x_461_ = lean_apply_2(v_toPure_458_, lean_box(0), v___x_460_);
return v___x_461_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f___redArg(lean_object* v_inst_462_, lean_object* v_inst_463_, lean_object* v_declName_464_){
_start:
{
lean_object* v_toApplicative_465_; lean_object* v_toBind_466_; lean_object* v_getEnv_467_; lean_object* v_toPure_468_; lean_object* v___f_469_; lean_object* v___x_470_; 
v_toApplicative_465_ = lean_ctor_get(v_inst_463_, 0);
lean_inc_ref(v_toApplicative_465_);
v_toBind_466_ = lean_ctor_get(v_inst_463_, 1);
lean_inc(v_toBind_466_);
lean_dec_ref(v_inst_463_);
v_getEnv_467_ = lean_ctor_get(v_inst_462_, 0);
lean_inc(v_getEnv_467_);
lean_dec_ref(v_inst_462_);
v_toPure_468_ = lean_ctor_get(v_toApplicative_465_, 1);
lean_inc(v_toPure_468_);
lean_dec_ref(v_toApplicative_465_);
v___f_469_ = lean_alloc_closure((void*)(l_Lean_getAuxParentProjectionInfo_x3f___redArg___lam__0), 3, 2);
lean_closure_set(v___f_469_, 0, v_declName_464_);
lean_closure_set(v___f_469_, 1, v_toPure_468_);
v___x_470_ = lean_apply_4(v_toBind_466_, lean_box(0), lean_box(0), v_getEnv_467_, v___f_469_);
return v___x_470_;
}
}
LEAN_EXPORT lean_object* l_Lean_getAuxParentProjectionInfo_x3f(lean_object* v_m_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_declName_474_){
_start:
{
lean_object* v___x_475_; 
v___x_475_ = l_Lean_getAuxParentProjectionInfo_x3f___redArg(v_inst_472_, v_inst_473_, v_declName_474_);
return v___x_475_;
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
res = l_Lean_initFn_00___x40_Lean_ProjFns_2268652983____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_projectionFnInfoExt = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_projectionFnInfoExt);
lean_dec_ref(res);
res = l_Lean_initFn_00___x40_Lean_ProjFns_496916995____hygCtx___hyg_2_();
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
