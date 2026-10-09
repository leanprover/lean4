// Lean compiler output
// Module: Lean.Meta.Sym.DSimp.Variant
// Imports: public import Lean.Meta.Sym.DSimp.DSimpM import Lean.ScopedEnvExtension
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
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited___redArg();
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t);
static const lean_ctor_object l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 8, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),LEAN_SCALAR_PTR_LITERAL(0, 0, 0, 0, 0, 0, 0, 0)}};
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__1_value)}};
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__3_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 25, .m_capacity = 25, .m_length = 24, .m_data = "symDSimpVariantExtension"};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__3_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__3_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__4_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__3_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(160, 33, 169, 140, 255, 27, 4, 90)}};
static const lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__4_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__4_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object* v_x_14_, lean_object* v_a_15_){
_start:
{
lean_object* v___x_16_; lean_object* v___x_17_; 
v___x_16_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_16_, 0, v_a_15_);
lean_inc_ref_n(v___x_16_, 2);
v___x_17_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_17_, 0, v___x_16_);
lean_ctor_set(v___x_17_, 1, v___x_16_);
lean_ctor_set(v___x_17_, 2, v___x_16_);
return v___x_17_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object* v_x_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(v_x_18_, v_a_19_);
lean_dec_ref(v_x_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_21_, lean_object* v_x_22_){
_start:
{
if (lean_obj_tag(v_x_22_) == 0)
{
return v_x_21_;
}
else
{
lean_object* v_key_23_; lean_object* v_value_24_; lean_object* v_tail_25_; lean_object* v___x_27_; uint8_t v_isShared_28_; uint8_t v_isSharedCheck_51_; 
v_key_23_ = lean_ctor_get(v_x_22_, 0);
v_value_24_ = lean_ctor_get(v_x_22_, 1);
v_tail_25_ = lean_ctor_get(v_x_22_, 2);
v_isSharedCheck_51_ = !lean_is_exclusive(v_x_22_);
if (v_isSharedCheck_51_ == 0)
{
v___x_27_ = v_x_22_;
v_isShared_28_ = v_isSharedCheck_51_;
goto v_resetjp_26_;
}
else
{
lean_inc(v_tail_25_);
lean_inc(v_value_24_);
lean_inc(v_key_23_);
lean_dec(v_x_22_);
v___x_27_ = lean_box(0);
v_isShared_28_ = v_isSharedCheck_51_;
goto v_resetjp_26_;
}
v_resetjp_26_:
{
lean_object* v___x_29_; uint64_t v___y_31_; 
v___x_29_ = lean_array_get_size(v_x_21_);
if (lean_obj_tag(v_key_23_) == 0)
{
uint64_t v___x_49_; 
v___x_49_ = 1723ULL;
v___y_31_ = v___x_49_;
goto v___jp_30_;
}
else
{
uint64_t v_hash_50_; 
v_hash_50_ = lean_ctor_get_uint64(v_key_23_, sizeof(void*)*2);
v___y_31_ = v_hash_50_;
goto v___jp_30_;
}
v___jp_30_:
{
uint64_t v___x_32_; uint64_t v___x_33_; uint64_t v_fold_34_; uint64_t v___x_35_; uint64_t v___x_36_; uint64_t v___x_37_; size_t v___x_38_; size_t v___x_39_; size_t v___x_40_; size_t v___x_41_; size_t v___x_42_; lean_object* v___x_43_; lean_object* v___x_45_; 
v___x_32_ = 32ULL;
v___x_33_ = lean_uint64_shift_right(v___y_31_, v___x_32_);
v_fold_34_ = lean_uint64_xor(v___y_31_, v___x_33_);
v___x_35_ = 16ULL;
v___x_36_ = lean_uint64_shift_right(v_fold_34_, v___x_35_);
v___x_37_ = lean_uint64_xor(v_fold_34_, v___x_36_);
v___x_38_ = lean_uint64_to_usize(v___x_37_);
v___x_39_ = lean_usize_of_nat(v___x_29_);
v___x_40_ = ((size_t)1ULL);
v___x_41_ = lean_usize_sub(v___x_39_, v___x_40_);
v___x_42_ = lean_usize_land(v___x_38_, v___x_41_);
v___x_43_ = lean_array_uget_borrowed(v_x_21_, v___x_42_);
lean_inc(v___x_43_);
if (v_isShared_28_ == 0)
{
lean_ctor_set(v___x_27_, 2, v___x_43_);
v___x_45_ = v___x_27_;
goto v_reusejp_44_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_key_23_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v_value_24_);
lean_ctor_set(v_reuseFailAlloc_48_, 2, v___x_43_);
v___x_45_ = v_reuseFailAlloc_48_;
goto v_reusejp_44_;
}
v_reusejp_44_:
{
lean_object* v___x_46_; 
v___x_46_ = lean_array_uset(v_x_21_, v___x_42_, v___x_45_);
v_x_21_ = v___x_46_;
v_x_22_ = v_tail_25_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_52_, lean_object* v_source_53_, lean_object* v_target_54_){
_start:
{
lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_55_ = lean_array_get_size(v_source_53_);
v___x_56_ = lean_nat_dec_lt(v_i_52_, v___x_55_);
if (v___x_56_ == 0)
{
lean_dec_ref(v_source_53_);
lean_dec(v_i_52_);
return v_target_54_;
}
else
{
lean_object* v_es_57_; lean_object* v___x_58_; lean_object* v_source_59_; lean_object* v_target_60_; lean_object* v___x_61_; lean_object* v___x_62_; 
v_es_57_ = lean_array_fget(v_source_53_, v_i_52_);
v___x_58_ = lean_box(0);
v_source_59_ = lean_array_fset(v_source_53_, v_i_52_, v___x_58_);
v_target_60_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_target_54_, v_es_57_);
v___x_61_ = lean_unsigned_to_nat(1u);
v___x_62_ = lean_nat_add(v_i_52_, v___x_61_);
lean_dec(v_i_52_);
v_i_52_ = v___x_62_;
v_source_53_ = v_source_59_;
v_target_54_ = v_target_60_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_64_){
_start:
{
lean_object* v___x_65_; lean_object* v___x_66_; lean_object* v_nbuckets_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; lean_object* v___x_71_; lean_object* v___x_72_; 
v___x_65_ = lean_array_get_size(v_data_64_);
v___x_66_ = lean_unsigned_to_nat(2u);
v_nbuckets_67_ = lean_nat_mul(v___x_65_, v___x_66_);
v___x_68_ = lean_unsigned_to_nat(0u);
v___x_69_ = lean_box(0);
v___x_70_ = lean_mk_array(v_nbuckets_67_, v___x_69_);
v___x_71_ = lean_array_propagate_mark(v_data_64_, v___x_70_);
v___x_72_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_68_, v_data_64_, v___x_71_);
return v___x_72_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_73_, lean_object* v_x_74_){
_start:
{
if (lean_obj_tag(v_x_74_) == 0)
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
else
{
lean_object* v_key_76_; lean_object* v_tail_77_; uint8_t v___x_78_; 
v_key_76_ = lean_ctor_get(v_x_74_, 0);
v_tail_77_ = lean_ctor_get(v_x_74_, 2);
v___x_78_ = lean_name_eq(v_key_76_, v_a_73_);
if (v___x_78_ == 0)
{
v_x_74_ = v_tail_77_;
goto _start;
}
else
{
return v___x_78_;
}
}
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_73_ = stack[0].m_obj;
lean_object* v_x_74_ = stack[1].m_obj;
uint8_t v_res_80_;
v_res_80_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_73_, v_x_74_);
stack->m_num = v_res_80_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_81_, lean_object* v_x_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_81_, v_x_82_);
lean_dec(v_x_82_);
lean_dec(v_a_81_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_a_85_, lean_object* v_b_86_, lean_object* v_x_87_){
_start:
{
if (lean_obj_tag(v_x_87_) == 0)
{
lean_dec(v_b_86_);
lean_dec(v_a_85_);
return v_x_87_;
}
else
{
lean_object* v_key_88_; lean_object* v_value_89_; lean_object* v_tail_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_102_; 
v_key_88_ = lean_ctor_get(v_x_87_, 0);
v_value_89_ = lean_ctor_get(v_x_87_, 1);
v_tail_90_ = lean_ctor_get(v_x_87_, 2);
v_isSharedCheck_102_ = !lean_is_exclusive(v_x_87_);
if (v_isSharedCheck_102_ == 0)
{
v___x_92_ = v_x_87_;
v_isShared_93_ = v_isSharedCheck_102_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_tail_90_);
lean_inc(v_value_89_);
lean_inc(v_key_88_);
lean_dec(v_x_87_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_102_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
uint8_t v___x_94_; 
v___x_94_ = lean_name_eq(v_key_88_, v_a_85_);
if (v___x_94_ == 0)
{
lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_95_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_85_, v_b_86_, v_tail_90_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 2, v___x_95_);
v___x_97_ = v___x_92_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_key_88_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_value_89_);
lean_ctor_set(v_reuseFailAlloc_98_, 2, v___x_95_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
else
{
lean_object* v___x_100_; 
lean_dec(v_value_89_);
lean_dec(v_key_88_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 1, v_b_86_);
lean_ctor_set(v___x_92_, 0, v_a_85_);
v___x_100_ = v___x_92_;
goto v_reusejp_99_;
}
else
{
lean_object* v_reuseFailAlloc_101_; 
v_reuseFailAlloc_101_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_101_, 0, v_a_85_);
lean_ctor_set(v_reuseFailAlloc_101_, 1, v_b_86_);
lean_ctor_set(v_reuseFailAlloc_101_, 2, v_tail_90_);
v___x_100_ = v_reuseFailAlloc_101_;
goto v_reusejp_99_;
}
v_reusejp_99_:
{
return v___x_100_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_103_, lean_object* v_a_104_, lean_object* v_b_105_){
_start:
{
lean_object* v_size_106_; lean_object* v_buckets_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_153_; 
v_size_106_ = lean_ctor_get(v_m_103_, 0);
v_buckets_107_ = lean_ctor_get(v_m_103_, 1);
v_isSharedCheck_153_ = !lean_is_exclusive(v_m_103_);
if (v_isSharedCheck_153_ == 0)
{
v___x_109_ = v_m_103_;
v_isShared_110_ = v_isSharedCheck_153_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_buckets_107_);
lean_inc(v_size_106_);
lean_dec(v_m_103_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_153_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; uint64_t v___y_113_; 
v___x_111_ = lean_array_get_size(v_buckets_107_);
if (lean_obj_tag(v_a_104_) == 0)
{
uint64_t v___x_151_; 
v___x_151_ = 1723ULL;
v___y_113_ = v___x_151_;
goto v___jp_112_;
}
else
{
uint64_t v_hash_152_; 
v_hash_152_ = lean_ctor_get_uint64(v_a_104_, sizeof(void*)*2);
v___y_113_ = v_hash_152_;
goto v___jp_112_;
}
v___jp_112_:
{
uint64_t v___x_114_; uint64_t v___x_115_; uint64_t v_fold_116_; uint64_t v___x_117_; uint64_t v___x_118_; uint64_t v___x_119_; size_t v___x_120_; size_t v___x_121_; size_t v___x_122_; size_t v___x_123_; size_t v___x_124_; lean_object* v_bkt_125_; uint8_t v___x_126_; 
v___x_114_ = 32ULL;
v___x_115_ = lean_uint64_shift_right(v___y_113_, v___x_114_);
v_fold_116_ = lean_uint64_xor(v___y_113_, v___x_115_);
v___x_117_ = 16ULL;
v___x_118_ = lean_uint64_shift_right(v_fold_116_, v___x_117_);
v___x_119_ = lean_uint64_xor(v_fold_116_, v___x_118_);
v___x_120_ = lean_uint64_to_usize(v___x_119_);
v___x_121_ = lean_usize_of_nat(v___x_111_);
v___x_122_ = ((size_t)1ULL);
v___x_123_ = lean_usize_sub(v___x_121_, v___x_122_);
v___x_124_ = lean_usize_land(v___x_120_, v___x_123_);
v_bkt_125_ = lean_array_uget_borrowed(v_buckets_107_, v___x_124_);
v___x_126_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_104_, v_bkt_125_);
if (v___x_126_ == 0)
{
lean_object* v___x_127_; lean_object* v_size_x27_128_; lean_object* v___x_129_; lean_object* v_buckets_x27_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_135_; uint8_t v___x_136_; 
v___x_127_ = lean_unsigned_to_nat(1u);
v_size_x27_128_ = lean_nat_add(v_size_106_, v___x_127_);
lean_dec(v_size_106_);
lean_inc(v_bkt_125_);
v___x_129_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_129_, 0, v_a_104_);
lean_ctor_set(v___x_129_, 1, v_b_105_);
lean_ctor_set(v___x_129_, 2, v_bkt_125_);
v_buckets_x27_130_ = lean_array_uset(v_buckets_107_, v___x_124_, v___x_129_);
v___x_131_ = lean_unsigned_to_nat(4u);
v___x_132_ = lean_nat_mul(v_size_x27_128_, v___x_131_);
v___x_133_ = lean_unsigned_to_nat(3u);
v___x_134_ = lean_nat_div(v___x_132_, v___x_133_);
lean_dec(v___x_132_);
v___x_135_ = lean_array_get_size(v_buckets_x27_130_);
v___x_136_ = lean_nat_dec_le(v___x_134_, v___x_135_);
lean_dec(v___x_134_);
if (v___x_136_ == 0)
{
lean_object* v_val_137_; lean_object* v___x_139_; 
v_val_137_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_130_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v_val_137_);
lean_ctor_set(v___x_109_, 0, v_size_x27_128_);
v___x_139_ = v___x_109_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_size_x27_128_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_val_137_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
else
{
lean_object* v___x_142_; 
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v_buckets_x27_130_);
lean_ctor_set(v___x_109_, 0, v_size_x27_128_);
v___x_142_ = v___x_109_;
goto v_reusejp_141_;
}
else
{
lean_object* v_reuseFailAlloc_143_; 
v_reuseFailAlloc_143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_143_, 0, v_size_x27_128_);
lean_ctor_set(v_reuseFailAlloc_143_, 1, v_buckets_x27_130_);
v___x_142_ = v_reuseFailAlloc_143_;
goto v_reusejp_141_;
}
v_reusejp_141_:
{
return v___x_142_;
}
}
}
else
{
lean_object* v___x_144_; lean_object* v_buckets_x27_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
lean_inc(v_bkt_125_);
v___x_144_ = lean_box(0);
v_buckets_x27_145_ = lean_array_uset(v_buckets_107_, v___x_124_, v___x_144_);
v___x_146_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_104_, v_b_105_, v_bkt_125_);
v___x_147_ = lean_array_uset(v_buckets_x27_145_, v___x_124_, v___x_146_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 1, v___x_147_);
v___x_149_ = v___x_109_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_size_106_);
lean_ctor_set(v_reuseFailAlloc_150_, 1, v___x_147_);
v___x_149_ = v_reuseFailAlloc_150_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
return v___x_149_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object* v_map_154_, lean_object* v_entry_155_){
_start:
{
lean_object* v_name_156_; lean_object* v_variant_157_; lean_object* v___x_158_; 
v_name_156_ = lean_ctor_get(v_entry_155_, 0);
lean_inc(v_name_156_);
v_variant_157_ = lean_ctor_get(v_entry_155_, 1);
lean_inc_ref(v_variant_157_);
lean_dec_ref(v_entry_155_);
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_map_154_, v_name_156_, v_variant_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object* v___y_159_){
_start:
{
lean_inc_ref(v___y_159_);
return v___y_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(v___y_160_);
lean_dec_ref(v___y_160_);
return v_res_161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_box(0);
v___x_169_ = lean_unsigned_to_nat(16u);
v___x_170_ = lean_mk_array(v___x_169_, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_174_; uint8_t v___x_175_; lean_object* v___f_176_; lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___f_179_; lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_174_ = lean_box(0);
v___x_175_ = 0;
v___f_176_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___f_177_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_178_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___f_179_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_180_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__4_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_181_ = lean_alloc_ctor(0, 6, 2);
lean_ctor_set(v___x_181_, 0, v___x_180_);
lean_ctor_set(v___x_181_, 1, v___f_179_);
lean_ctor_set(v___x_181_, 2, v___x_178_);
lean_ctor_set(v___x_181_, 3, v___f_177_);
lean_ctor_set(v___x_181_, 4, v___f_176_);
lean_ctor_set(v___x_181_, 5, v___x_174_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*6, v___x_175_);
lean_ctor_set_uint8(v___x_181_, sizeof(void*)*6 + 1, v___x_175_);
return v___x_181_;
}
}
lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_183_; lean_object* v___x_184_; 
v___x_183_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___x_184_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_183_);
return v___x_184_;
}
}
LEAN_EXPORT void l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__0interp(lean_interpreter_value* stack)
{
lean_object* v_res_185_;
v_res_185_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_();
stack->m_obj
 = v_res_185_;
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object* v_a_186_){
_start:
{
lean_object* v_res_187_; 
v_res_187_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_();
return v_res_187_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_188_, lean_object* v_m_189_, lean_object* v_a_190_, lean_object* v_b_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_m_189_, v_a_190_, v_b_191_);
return v___x_192_;
}
}
uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_193_, lean_object* v_a_194_, lean_object* v_x_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_194_, v_x_195_);
return v___x_196_;
}
}
LEAN_EXPORT void l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_a_194_ = stack[1].m_obj;
lean_object* v_x_195_ = stack[2].m_obj;
uint8_t v_res_197_;
v_res_197_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(lean_box(0), v_a_194_, v_x_195_);
stack->m_num = v_res_197_;
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_198_, lean_object* v_a_199_, lean_object* v_x_200_){
_start:
{
uint8_t v_res_201_; lean_object* v_r_202_; 
v_res_201_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_198_, v_a_199_, v_x_200_);
lean_dec(v_x_200_);
lean_dec(v_a_199_);
v_r_202_ = lean_box(v_res_201_);
return v_r_202_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_203_, lean_object* v_data_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_206_, lean_object* v_a_207_, lean_object* v_b_208_, lean_object* v_x_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_207_, v_b_208_, v_x_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_211_, lean_object* v_i_212_, lean_object* v_source_213_, lean_object* v_target_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_212_, v_source_213_, v_target_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_216_, lean_object* v_x_217_, lean_object* v_x_218_){
_start:
{
lean_object* v___x_219_; 
v___x_219_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_217_, v_x_218_);
return v___x_219_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(lean_object* v_a_220_, lean_object* v_x_221_){
_start:
{
if (lean_obj_tag(v_x_221_) == 0)
{
lean_object* v___x_222_; 
v___x_222_ = lean_box(0);
return v___x_222_;
}
else
{
lean_object* v_key_223_; lean_object* v_value_224_; lean_object* v_tail_225_; uint8_t v___x_226_; 
v_key_223_ = lean_ctor_get(v_x_221_, 0);
v_value_224_ = lean_ctor_get(v_x_221_, 1);
v_tail_225_ = lean_ctor_get(v_x_221_, 2);
v___x_226_ = lean_name_eq(v_key_223_, v_a_220_);
if (v___x_226_ == 0)
{
v_x_221_ = v_tail_225_;
goto _start;
}
else
{
lean_object* v___x_228_; 
lean_inc(v_value_224_);
v___x_228_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_228_, 0, v_value_224_);
return v___x_228_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_229_, lean_object* v_x_230_){
_start:
{
lean_object* v_res_231_; 
v_res_231_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_229_, v_x_230_);
lean_dec(v_x_230_);
lean_dec(v_a_229_);
return v_res_231_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(lean_object* v_m_232_, lean_object* v_a_233_){
_start:
{
lean_object* v_buckets_234_; lean_object* v___x_235_; uint64_t v___y_237_; 
v_buckets_234_ = lean_ctor_get(v_m_232_, 1);
v___x_235_ = lean_array_get_size(v_buckets_234_);
if (lean_obj_tag(v_a_233_) == 0)
{
uint64_t v___x_251_; 
v___x_251_ = 1723ULL;
v___y_237_ = v___x_251_;
goto v___jp_236_;
}
else
{
uint64_t v_hash_252_; 
v_hash_252_ = lean_ctor_get_uint64(v_a_233_, sizeof(void*)*2);
v___y_237_ = v_hash_252_;
goto v___jp_236_;
}
v___jp_236_:
{
uint64_t v___x_238_; uint64_t v___x_239_; uint64_t v_fold_240_; uint64_t v___x_241_; uint64_t v___x_242_; uint64_t v___x_243_; size_t v___x_244_; size_t v___x_245_; size_t v___x_246_; size_t v___x_247_; size_t v___x_248_; lean_object* v___x_249_; lean_object* v___x_250_; 
v___x_238_ = 32ULL;
v___x_239_ = lean_uint64_shift_right(v___y_237_, v___x_238_);
v_fold_240_ = lean_uint64_xor(v___y_237_, v___x_239_);
v___x_241_ = 16ULL;
v___x_242_ = lean_uint64_shift_right(v_fold_240_, v___x_241_);
v___x_243_ = lean_uint64_xor(v_fold_240_, v___x_242_);
v___x_244_ = lean_uint64_to_usize(v___x_243_);
v___x_245_ = lean_usize_of_nat(v___x_235_);
v___x_246_ = ((size_t)1ULL);
v___x_247_ = lean_usize_sub(v___x_245_, v___x_246_);
v___x_248_ = lean_usize_land(v___x_244_, v___x_247_);
v___x_249_ = lean_array_uget_borrowed(v_buckets_234_, v___x_248_);
v___x_250_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_233_, v___x_249_);
return v___x_250_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg___boxed(lean_object* v_m_253_, lean_object* v_a_254_){
_start:
{
lean_object* v_res_255_; 
v_res_255_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v_m_253_, v_a_254_);
lean_dec(v_a_254_);
lean_dec_ref(v_m_253_);
return v_res_255_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0(void){
_start:
{
lean_object* v___x_256_; 
v___x_256_ = l_Std_HashMap_instInhabited___redArg();
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(lean_object* v_env_257_, lean_object* v_name_258_){
_start:
{
lean_object* v___x_259_; lean_object* v_ext_260_; lean_object* v_toEnvExtension_261_; lean_object* v_asyncMode_262_; lean_object* v___x_263_; uint8_t v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v___x_259_ = l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension;
v_ext_260_ = lean_ctor_get(v___x_259_, 1);
v_toEnvExtension_261_ = lean_ctor_get(v_ext_260_, 0);
v_asyncMode_262_ = lean_ctor_get(v_toEnvExtension_261_, 2);
v___x_263_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0, &l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0_once, _init_l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0);
v___x_264_ = 0;
v___x_265_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_263_, v___x_259_, v_env_257_, v_asyncMode_262_, v___x_264_);
v___x_266_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v___x_265_, v_name_258_);
lean_dec(v___x_265_);
return v___x_266_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___boxed(lean_object* v_env_267_, lean_object* v_name_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(v_env_267_, v_name_268_);
lean_dec(v_name_268_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0(lean_object* v_00_u03b2_270_, lean_object* v_m_271_, lean_object* v_a_272_){
_start:
{
lean_object* v___x_273_; 
v___x_273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v_m_271_, v_a_272_);
return v___x_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___boxed(lean_object* v_00_u03b2_274_, lean_object* v_m_275_, lean_object* v_a_276_){
_start:
{
lean_object* v_res_277_; 
v_res_277_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0(v_00_u03b2_274_, v_m_275_, v_a_276_);
lean_dec(v_a_276_);
lean_dec_ref(v_m_275_);
return v_res_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(lean_object* v_00_u03b2_278_, lean_object* v_a_279_, lean_object* v_x_280_){
_start:
{
lean_object* v___x_281_; 
v___x_281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_279_, v_x_280_);
return v___x_281_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_282_, lean_object* v_a_283_, lean_object* v_x_284_){
_start:
{
lean_object* v_res_285_; 
v_res_285_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(v_00_u03b2_282_, v_a_283_, v_x_284_);
lean_dec(v_x_284_);
lean_dec(v_a_283_);
return v_res_285_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Variant(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_DSimp_Variant(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_DSimp_Variant(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_DSimp_DSimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_DSimp_Variant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_DSimp_Variant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_DSimp_Variant(builtin);
}
#ifdef __cplusplus
}
#endif
