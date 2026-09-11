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
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_array_propagate_mark(lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
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
static const lean_closure_object l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2;
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
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_73_, lean_object* v_x_74_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_80_, lean_object* v_x_81_){
_start:
{
uint8_t v_res_82_; lean_object* v_r_83_; 
v_res_82_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_80_, v_x_81_);
lean_dec(v_x_81_);
lean_dec(v_a_80_);
v_r_83_ = lean_box(v_res_82_);
return v_r_83_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_a_84_, lean_object* v_b_85_, lean_object* v_x_86_){
_start:
{
if (lean_obj_tag(v_x_86_) == 0)
{
lean_dec(v_b_85_);
lean_dec(v_a_84_);
return v_x_86_;
}
else
{
lean_object* v_key_87_; lean_object* v_value_88_; lean_object* v_tail_89_; lean_object* v___x_91_; uint8_t v_isShared_92_; uint8_t v_isSharedCheck_101_; 
v_key_87_ = lean_ctor_get(v_x_86_, 0);
v_value_88_ = lean_ctor_get(v_x_86_, 1);
v_tail_89_ = lean_ctor_get(v_x_86_, 2);
v_isSharedCheck_101_ = !lean_is_exclusive(v_x_86_);
if (v_isSharedCheck_101_ == 0)
{
v___x_91_ = v_x_86_;
v_isShared_92_ = v_isSharedCheck_101_;
goto v_resetjp_90_;
}
else
{
lean_inc(v_tail_89_);
lean_inc(v_value_88_);
lean_inc(v_key_87_);
lean_dec(v_x_86_);
v___x_91_ = lean_box(0);
v_isShared_92_ = v_isSharedCheck_101_;
goto v_resetjp_90_;
}
v_resetjp_90_:
{
uint8_t v___x_93_; 
v___x_93_ = lean_name_eq(v_key_87_, v_a_84_);
if (v___x_93_ == 0)
{
lean_object* v___x_94_; lean_object* v___x_96_; 
v___x_94_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_84_, v_b_85_, v_tail_89_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 2, v___x_94_);
v___x_96_ = v___x_91_;
goto v_reusejp_95_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_key_87_);
lean_ctor_set(v_reuseFailAlloc_97_, 1, v_value_88_);
lean_ctor_set(v_reuseFailAlloc_97_, 2, v___x_94_);
v___x_96_ = v_reuseFailAlloc_97_;
goto v_reusejp_95_;
}
v_reusejp_95_:
{
return v___x_96_;
}
}
else
{
lean_object* v___x_99_; 
lean_dec(v_value_88_);
lean_dec(v_key_87_);
if (v_isShared_92_ == 0)
{
lean_ctor_set(v___x_91_, 1, v_b_85_);
lean_ctor_set(v___x_91_, 0, v_a_84_);
v___x_99_ = v___x_91_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_100_; 
v_reuseFailAlloc_100_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_100_, 0, v_a_84_);
lean_ctor_set(v_reuseFailAlloc_100_, 1, v_b_85_);
lean_ctor_set(v_reuseFailAlloc_100_, 2, v_tail_89_);
v___x_99_ = v_reuseFailAlloc_100_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
return v___x_99_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_102_, lean_object* v_a_103_, lean_object* v_b_104_){
_start:
{
lean_object* v_size_105_; lean_object* v_buckets_106_; lean_object* v___x_108_; uint8_t v_isShared_109_; uint8_t v_isSharedCheck_152_; 
v_size_105_ = lean_ctor_get(v_m_102_, 0);
v_buckets_106_ = lean_ctor_get(v_m_102_, 1);
v_isSharedCheck_152_ = !lean_is_exclusive(v_m_102_);
if (v_isSharedCheck_152_ == 0)
{
v___x_108_ = v_m_102_;
v_isShared_109_ = v_isSharedCheck_152_;
goto v_resetjp_107_;
}
else
{
lean_inc(v_buckets_106_);
lean_inc(v_size_105_);
lean_dec(v_m_102_);
v___x_108_ = lean_box(0);
v_isShared_109_ = v_isSharedCheck_152_;
goto v_resetjp_107_;
}
v_resetjp_107_:
{
lean_object* v___x_110_; uint64_t v___y_112_; 
v___x_110_ = lean_array_get_size(v_buckets_106_);
if (lean_obj_tag(v_a_103_) == 0)
{
uint64_t v___x_150_; 
v___x_150_ = 1723ULL;
v___y_112_ = v___x_150_;
goto v___jp_111_;
}
else
{
uint64_t v_hash_151_; 
v_hash_151_ = lean_ctor_get_uint64(v_a_103_, sizeof(void*)*2);
v___y_112_ = v_hash_151_;
goto v___jp_111_;
}
v___jp_111_:
{
uint64_t v___x_113_; uint64_t v___x_114_; uint64_t v_fold_115_; uint64_t v___x_116_; uint64_t v___x_117_; uint64_t v___x_118_; size_t v___x_119_; size_t v___x_120_; size_t v___x_121_; size_t v___x_122_; size_t v___x_123_; lean_object* v_bkt_124_; uint8_t v___x_125_; 
v___x_113_ = 32ULL;
v___x_114_ = lean_uint64_shift_right(v___y_112_, v___x_113_);
v_fold_115_ = lean_uint64_xor(v___y_112_, v___x_114_);
v___x_116_ = 16ULL;
v___x_117_ = lean_uint64_shift_right(v_fold_115_, v___x_116_);
v___x_118_ = lean_uint64_xor(v_fold_115_, v___x_117_);
v___x_119_ = lean_uint64_to_usize(v___x_118_);
v___x_120_ = lean_usize_of_nat(v___x_110_);
v___x_121_ = ((size_t)1ULL);
v___x_122_ = lean_usize_sub(v___x_120_, v___x_121_);
v___x_123_ = lean_usize_land(v___x_119_, v___x_122_);
v_bkt_124_ = lean_array_uget_borrowed(v_buckets_106_, v___x_123_);
v___x_125_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_103_, v_bkt_124_);
if (v___x_125_ == 0)
{
lean_object* v___x_126_; lean_object* v_size_x27_127_; lean_object* v___x_128_; lean_object* v_buckets_x27_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; uint8_t v___x_135_; 
v___x_126_ = lean_unsigned_to_nat(1u);
v_size_x27_127_ = lean_nat_add(v_size_105_, v___x_126_);
lean_dec(v_size_105_);
lean_inc(v_bkt_124_);
v___x_128_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_128_, 0, v_a_103_);
lean_ctor_set(v___x_128_, 1, v_b_104_);
lean_ctor_set(v___x_128_, 2, v_bkt_124_);
v_buckets_x27_129_ = lean_array_uset(v_buckets_106_, v___x_123_, v___x_128_);
v___x_130_ = lean_unsigned_to_nat(4u);
v___x_131_ = lean_nat_mul(v_size_x27_127_, v___x_130_);
v___x_132_ = lean_unsigned_to_nat(3u);
v___x_133_ = lean_nat_div(v___x_131_, v___x_132_);
lean_dec(v___x_131_);
v___x_134_ = lean_array_get_size(v_buckets_x27_129_);
v___x_135_ = lean_nat_dec_le(v___x_133_, v___x_134_);
lean_dec(v___x_133_);
if (v___x_135_ == 0)
{
lean_object* v_val_136_; lean_object* v___x_138_; 
v_val_136_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_129_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v_val_136_);
lean_ctor_set(v___x_108_, 0, v_size_x27_127_);
v___x_138_ = v___x_108_;
goto v_reusejp_137_;
}
else
{
lean_object* v_reuseFailAlloc_139_; 
v_reuseFailAlloc_139_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_139_, 0, v_size_x27_127_);
lean_ctor_set(v_reuseFailAlloc_139_, 1, v_val_136_);
v___x_138_ = v_reuseFailAlloc_139_;
goto v_reusejp_137_;
}
v_reusejp_137_:
{
return v___x_138_;
}
}
else
{
lean_object* v___x_141_; 
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v_buckets_x27_129_);
lean_ctor_set(v___x_108_, 0, v_size_x27_127_);
v___x_141_ = v___x_108_;
goto v_reusejp_140_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v_size_x27_127_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_buckets_x27_129_);
v___x_141_ = v_reuseFailAlloc_142_;
goto v_reusejp_140_;
}
v_reusejp_140_:
{
return v___x_141_;
}
}
}
else
{
lean_object* v___x_143_; lean_object* v_buckets_x27_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
lean_inc(v_bkt_124_);
v___x_143_ = lean_box(0);
v_buckets_x27_144_ = lean_array_uset(v_buckets_106_, v___x_123_, v___x_143_);
v___x_145_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_103_, v_b_104_, v_bkt_124_);
v___x_146_ = lean_array_uset(v_buckets_x27_144_, v___x_123_, v___x_145_);
if (v_isShared_109_ == 0)
{
lean_ctor_set(v___x_108_, 1, v___x_146_);
v___x_148_ = v___x_108_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v_size_105_);
lean_ctor_set(v_reuseFailAlloc_149_, 1, v___x_146_);
v___x_148_ = v_reuseFailAlloc_149_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
return v___x_148_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object* v_map_153_, lean_object* v_entry_154_){
_start:
{
lean_object* v_name_155_; lean_object* v_variant_156_; lean_object* v___x_157_; 
v_name_155_ = lean_ctor_get(v_entry_154_, 0);
lean_inc(v_name_155_);
v_variant_156_ = lean_ctor_get(v_entry_154_, 1);
lean_inc_ref(v_variant_156_);
lean_dec_ref(v_entry_154_);
v___x_157_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_map_153_, v_name_155_, v_variant_156_);
return v___x_157_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object* v___y_158_){
_start:
{
lean_inc_ref(v___y_158_);
return v___y_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object* v___y_159_){
_start:
{
lean_object* v_res_160_; 
v_res_160_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(v___y_159_);
lean_dec_ref(v___y_159_);
return v_res_160_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_167_; lean_object* v___x_168_; lean_object* v___x_169_; 
v___x_167_ = lean_box(0);
v___x_168_ = lean_unsigned_to_nat(16u);
v___x_169_ = lean_mk_array(v___x_168_, v___x_167_);
return v___x_169_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v___x_170_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___x_171_ = lean_unsigned_to_nat(0u);
v___x_172_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_172_, 0, v___x_171_);
lean_ctor_set(v___x_172_, 1, v___x_170_);
return v___x_172_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___f_176_; lean_object* v___x_177_; lean_object* v___x_178_; 
v___f_173_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___f_174_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_175_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___f_176_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_177_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__4_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_178_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_178_, 0, v___x_177_);
lean_ctor_set(v___x_178_, 1, v___f_176_);
lean_ctor_set(v___x_178_, 2, v___x_175_);
lean_ctor_set(v___x_178_, 3, v___f_174_);
lean_ctor_set(v___x_178_, 4, v___f_173_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___x_181_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_180_);
return v___x_181_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object* v_a_182_){
_start:
{
lean_object* v_res_183_; 
v_res_183_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_();
return v_res_183_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_184_, lean_object* v_m_185_, lean_object* v_a_186_, lean_object* v_b_187_){
_start:
{
lean_object* v___x_188_; 
v___x_188_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_m_185_, v_a_186_, v_b_187_);
return v___x_188_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_189_, lean_object* v_a_190_, lean_object* v_x_191_){
_start:
{
uint8_t v___x_192_; 
v___x_192_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_190_, v_x_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_193_, lean_object* v_a_194_, lean_object* v_x_195_){
_start:
{
uint8_t v_res_196_; lean_object* v_r_197_; 
v_res_196_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_193_, v_a_194_, v_x_195_);
lean_dec(v_x_195_);
lean_dec(v_a_194_);
v_r_197_ = lean_box(v_res_196_);
return v_r_197_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_198_, lean_object* v_data_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_199_);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_201_, lean_object* v_a_202_, lean_object* v_b_203_, lean_object* v_x_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_202_, v_b_203_, v_x_204_);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_206_, lean_object* v_i_207_, lean_object* v_source_208_, lean_object* v_target_209_){
_start:
{
lean_object* v___x_210_; 
v___x_210_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_207_, v_source_208_, v_target_209_);
return v___x_210_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_211_, lean_object* v_x_212_, lean_object* v_x_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_212_, v_x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(lean_object* v_a_215_, lean_object* v_x_216_){
_start:
{
if (lean_obj_tag(v_x_216_) == 0)
{
lean_object* v___x_217_; 
v___x_217_ = lean_box(0);
return v___x_217_;
}
else
{
lean_object* v_key_218_; lean_object* v_value_219_; lean_object* v_tail_220_; uint8_t v___x_221_; 
v_key_218_ = lean_ctor_get(v_x_216_, 0);
v_value_219_ = lean_ctor_get(v_x_216_, 1);
v_tail_220_ = lean_ctor_get(v_x_216_, 2);
v___x_221_ = lean_name_eq(v_key_218_, v_a_215_);
if (v___x_221_ == 0)
{
v_x_216_ = v_tail_220_;
goto _start;
}
else
{
lean_object* v___x_223_; 
lean_inc(v_value_219_);
v___x_223_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_223_, 0, v_value_219_);
return v___x_223_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_224_, lean_object* v_x_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_224_, v_x_225_);
lean_dec(v_x_225_);
lean_dec(v_a_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(lean_object* v_m_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_buckets_229_; lean_object* v___x_230_; uint64_t v___y_232_; 
v_buckets_229_ = lean_ctor_get(v_m_227_, 1);
v___x_230_ = lean_array_get_size(v_buckets_229_);
if (lean_obj_tag(v_a_228_) == 0)
{
uint64_t v___x_246_; 
v___x_246_ = 1723ULL;
v___y_232_ = v___x_246_;
goto v___jp_231_;
}
else
{
uint64_t v_hash_247_; 
v_hash_247_ = lean_ctor_get_uint64(v_a_228_, sizeof(void*)*2);
v___y_232_ = v_hash_247_;
goto v___jp_231_;
}
v___jp_231_:
{
uint64_t v___x_233_; uint64_t v___x_234_; uint64_t v_fold_235_; uint64_t v___x_236_; uint64_t v___x_237_; uint64_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; 
v___x_233_ = 32ULL;
v___x_234_ = lean_uint64_shift_right(v___y_232_, v___x_233_);
v_fold_235_ = lean_uint64_xor(v___y_232_, v___x_234_);
v___x_236_ = 16ULL;
v___x_237_ = lean_uint64_shift_right(v_fold_235_, v___x_236_);
v___x_238_ = lean_uint64_xor(v_fold_235_, v___x_237_);
v___x_239_ = lean_uint64_to_usize(v___x_238_);
v___x_240_ = lean_usize_of_nat(v___x_230_);
v___x_241_ = ((size_t)1ULL);
v___x_242_ = lean_usize_sub(v___x_240_, v___x_241_);
v___x_243_ = lean_usize_land(v___x_239_, v___x_242_);
v___x_244_ = lean_array_uget_borrowed(v_buckets_229_, v___x_243_);
v___x_245_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_228_, v___x_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg___boxed(lean_object* v_m_248_, lean_object* v_a_249_){
_start:
{
lean_object* v_res_250_; 
v_res_250_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v_m_248_, v_a_249_);
lean_dec(v_a_249_);
lean_dec_ref(v_m_248_);
return v_res_250_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2(void){
_start:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_253_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__1));
v___x_254_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0));
v___x_255_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_254_, v___x_253_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(lean_object* v_env_256_, lean_object* v_name_257_){
_start:
{
lean_object* v___x_258_; lean_object* v_ext_259_; lean_object* v_toEnvExtension_260_; lean_object* v_asyncMode_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_258_ = l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension;
v_ext_259_ = lean_ctor_get(v___x_258_, 1);
v_toEnvExtension_260_ = lean_ctor_get(v_ext_259_, 0);
v_asyncMode_261_ = lean_ctor_get(v_toEnvExtension_260_, 2);
v___x_262_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2, &l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2_once, _init_l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2);
v___x_263_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_262_, v___x_258_, v_env_256_, v_asyncMode_261_);
v___x_264_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v___x_263_, v_name_257_);
lean_dec(v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___boxed(lean_object* v_env_265_, lean_object* v_name_266_){
_start:
{
lean_object* v_res_267_; 
v_res_267_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(v_env_265_, v_name_266_);
lean_dec(v_name_266_);
return v_res_267_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0(lean_object* v_00_u03b2_268_, lean_object* v_m_269_, lean_object* v_a_270_){
_start:
{
lean_object* v___x_271_; 
v___x_271_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v_m_269_, v_a_270_);
return v___x_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___boxed(lean_object* v_00_u03b2_272_, lean_object* v_m_273_, lean_object* v_a_274_){
_start:
{
lean_object* v_res_275_; 
v_res_275_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0(v_00_u03b2_272_, v_m_273_, v_a_274_);
lean_dec(v_a_274_);
lean_dec_ref(v_m_273_);
return v_res_275_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(lean_object* v_00_u03b2_276_, lean_object* v_a_277_, lean_object* v_x_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_277_, v_x_278_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_280_, lean_object* v_a_281_, lean_object* v_x_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(v_00_u03b2_280_, v_a_281_, v_x_282_);
lean_dec(v_x_282_);
lean_dec(v_a_281_);
return v_res_283_;
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
