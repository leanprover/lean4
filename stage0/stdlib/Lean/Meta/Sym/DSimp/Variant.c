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
uint64_t lean_uint64_of_nat(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(100000) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariant_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry = (const lean_object*)&l_Lean_Meta_Sym_DSimp_instInhabitedSymDSimpVariantEntry_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0;
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object* v_x_11_, lean_object* v_a_12_){
_start:
{
lean_object* v___x_13_; lean_object* v___x_14_; 
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v_a_12_);
lean_inc_ref_n(v___x_13_, 2);
v___x_14_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_14_, 0, v___x_13_);
lean_ctor_set(v___x_14_, 1, v___x_13_);
lean_ctor_set(v___x_14_, 2, v___x_13_);
return v___x_14_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object* v_x_15_, lean_object* v_a_16_){
_start:
{
lean_object* v_res_17_; 
v_res_17_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(v_x_15_, v_a_16_);
lean_dec_ref(v_x_15_);
return v_res_17_;
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_18_; uint64_t v___x_19_; 
v___x_18_ = lean_unsigned_to_nat(1723u);
v___x_19_ = lean_uint64_of_nat(v___x_18_);
return v___x_19_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_20_, lean_object* v_x_21_){
_start:
{
if (lean_obj_tag(v_x_21_) == 0)
{
return v_x_20_;
}
else
{
lean_object* v_key_22_; lean_object* v_value_23_; lean_object* v_tail_24_; lean_object* v___x_26_; uint8_t v_isShared_27_; uint8_t v_isSharedCheck_50_; 
v_key_22_ = lean_ctor_get(v_x_21_, 0);
v_value_23_ = lean_ctor_get(v_x_21_, 1);
v_tail_24_ = lean_ctor_get(v_x_21_, 2);
v_isSharedCheck_50_ = !lean_is_exclusive(v_x_21_);
if (v_isSharedCheck_50_ == 0)
{
v___x_26_ = v_x_21_;
v_isShared_27_ = v_isSharedCheck_50_;
goto v_resetjp_25_;
}
else
{
lean_inc(v_tail_24_);
lean_inc(v_value_23_);
lean_inc(v_key_22_);
lean_dec(v_x_21_);
v___x_26_ = lean_box(0);
v_isShared_27_ = v_isSharedCheck_50_;
goto v_resetjp_25_;
}
v_resetjp_25_:
{
lean_object* v___x_28_; uint64_t v___y_30_; 
v___x_28_ = lean_array_get_size(v_x_20_);
if (lean_obj_tag(v_key_22_) == 0)
{
uint64_t v___x_48_; 
v___x_48_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_30_ = v___x_48_;
goto v___jp_29_;
}
else
{
uint64_t v_hash_49_; 
v_hash_49_ = lean_ctor_get_uint64(v_key_22_, sizeof(void*)*2);
v___y_30_ = v_hash_49_;
goto v___jp_29_;
}
v___jp_29_:
{
uint64_t v___x_31_; uint64_t v___x_32_; uint64_t v_fold_33_; uint64_t v___x_34_; uint64_t v___x_35_; uint64_t v___x_36_; size_t v___x_37_; size_t v___x_38_; size_t v___x_39_; size_t v___x_40_; size_t v___x_41_; lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_31_ = 32ULL;
v___x_32_ = lean_uint64_shift_right(v___y_30_, v___x_31_);
v_fold_33_ = lean_uint64_xor(v___y_30_, v___x_32_);
v___x_34_ = 16ULL;
v___x_35_ = lean_uint64_shift_right(v_fold_33_, v___x_34_);
v___x_36_ = lean_uint64_xor(v_fold_33_, v___x_35_);
v___x_37_ = lean_uint64_to_usize(v___x_36_);
v___x_38_ = lean_usize_of_nat(v___x_28_);
v___x_39_ = ((size_t)1ULL);
v___x_40_ = lean_usize_sub(v___x_38_, v___x_39_);
v___x_41_ = lean_usize_land(v___x_37_, v___x_40_);
v___x_42_ = lean_array_uget_borrowed(v_x_20_, v___x_41_);
lean_inc(v___x_42_);
if (v_isShared_27_ == 0)
{
lean_ctor_set(v___x_26_, 2, v___x_42_);
v___x_44_ = v___x_26_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_key_22_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v_value_23_);
lean_ctor_set(v_reuseFailAlloc_47_, 2, v___x_42_);
v___x_44_ = v_reuseFailAlloc_47_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; 
v___x_45_ = lean_array_uset(v_x_20_, v___x_41_, v___x_44_);
v_x_20_ = v___x_45_;
v_x_21_ = v_tail_24_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_51_, lean_object* v_source_52_, lean_object* v_target_53_){
_start:
{
lean_object* v___x_54_; uint8_t v___x_55_; 
v___x_54_ = lean_array_get_size(v_source_52_);
v___x_55_ = lean_nat_dec_lt(v_i_51_, v___x_54_);
if (v___x_55_ == 0)
{
lean_dec_ref(v_source_52_);
lean_dec(v_i_51_);
return v_target_53_;
}
else
{
lean_object* v_es_56_; lean_object* v___x_57_; lean_object* v_source_58_; lean_object* v_target_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_es_56_ = lean_array_fget(v_source_52_, v_i_51_);
v___x_57_ = lean_box(0);
v_source_58_ = lean_array_fset(v_source_52_, v_i_51_, v___x_57_);
v_target_59_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_target_53_, v_es_56_);
v___x_60_ = lean_unsigned_to_nat(1u);
v___x_61_ = lean_nat_add(v_i_51_, v___x_60_);
lean_dec(v_i_51_);
v_i_51_ = v___x_61_;
v_source_52_ = v_source_58_;
v_target_53_ = v_target_59_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_63_){
_start:
{
lean_object* v___x_64_; lean_object* v___x_65_; lean_object* v_nbuckets_66_; lean_object* v___x_67_; lean_object* v___x_68_; lean_object* v___x_69_; lean_object* v___x_70_; 
v___x_64_ = lean_array_get_size(v_data_63_);
v___x_65_ = lean_unsigned_to_nat(2u);
v_nbuckets_66_ = lean_nat_mul(v___x_64_, v___x_65_);
v___x_67_ = lean_unsigned_to_nat(0u);
v___x_68_ = lean_box(0);
v___x_69_ = lean_mk_array(v_nbuckets_66_, v___x_68_);
v___x_70_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_67_, v_data_63_, v___x_69_);
return v___x_70_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_71_, lean_object* v_x_72_){
_start:
{
if (lean_obj_tag(v_x_72_) == 0)
{
uint8_t v___x_73_; 
v___x_73_ = 0;
return v___x_73_;
}
else
{
lean_object* v_key_74_; lean_object* v_tail_75_; uint8_t v___x_76_; 
v_key_74_ = lean_ctor_get(v_x_72_, 0);
v_tail_75_ = lean_ctor_get(v_x_72_, 2);
v___x_76_ = lean_name_eq(v_key_74_, v_a_71_);
if (v___x_76_ == 0)
{
v_x_72_ = v_tail_75_;
goto _start;
}
else
{
return v___x_76_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_78_, lean_object* v_x_79_){
_start:
{
uint8_t v_res_80_; lean_object* v_r_81_; 
v_res_80_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_78_, v_x_79_);
lean_dec(v_x_79_);
lean_dec(v_a_78_);
v_r_81_ = lean_box(v_res_80_);
return v_r_81_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_a_82_, lean_object* v_b_83_, lean_object* v_x_84_){
_start:
{
if (lean_obj_tag(v_x_84_) == 0)
{
lean_dec(v_b_83_);
lean_dec(v_a_82_);
return v_x_84_;
}
else
{
lean_object* v_key_85_; lean_object* v_value_86_; lean_object* v_tail_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_99_; 
v_key_85_ = lean_ctor_get(v_x_84_, 0);
v_value_86_ = lean_ctor_get(v_x_84_, 1);
v_tail_87_ = lean_ctor_get(v_x_84_, 2);
v_isSharedCheck_99_ = !lean_is_exclusive(v_x_84_);
if (v_isSharedCheck_99_ == 0)
{
v___x_89_ = v_x_84_;
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_tail_87_);
lean_inc(v_value_86_);
lean_inc(v_key_85_);
lean_dec(v_x_84_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_99_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
uint8_t v___x_91_; 
v___x_91_ = lean_name_eq(v_key_85_, v_a_82_);
if (v___x_91_ == 0)
{
lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_92_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_82_, v_b_83_, v_tail_87_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 2, v___x_92_);
v___x_94_ = v___x_89_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_key_85_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v_value_86_);
lean_ctor_set(v_reuseFailAlloc_95_, 2, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
else
{
lean_object* v___x_97_; 
lean_dec(v_value_86_);
lean_dec(v_key_85_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v_b_83_);
lean_ctor_set(v___x_89_, 0, v_a_82_);
v___x_97_ = v___x_89_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_a_82_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v_b_83_);
lean_ctor_set(v_reuseFailAlloc_98_, 2, v_tail_87_);
v___x_97_ = v_reuseFailAlloc_98_;
goto v_reusejp_96_;
}
v_reusejp_96_:
{
return v___x_97_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_100_, lean_object* v_a_101_, lean_object* v_b_102_){
_start:
{
lean_object* v_size_103_; lean_object* v_buckets_104_; lean_object* v___x_106_; uint8_t v_isShared_107_; uint8_t v_isSharedCheck_150_; 
v_size_103_ = lean_ctor_get(v_m_100_, 0);
v_buckets_104_ = lean_ctor_get(v_m_100_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_m_100_);
if (v_isSharedCheck_150_ == 0)
{
v___x_106_ = v_m_100_;
v_isShared_107_ = v_isSharedCheck_150_;
goto v_resetjp_105_;
}
else
{
lean_inc(v_buckets_104_);
lean_inc(v_size_103_);
lean_dec(v_m_100_);
v___x_106_ = lean_box(0);
v_isShared_107_ = v_isSharedCheck_150_;
goto v_resetjp_105_;
}
v_resetjp_105_:
{
lean_object* v___x_108_; uint64_t v___y_110_; 
v___x_108_ = lean_array_get_size(v_buckets_104_);
if (lean_obj_tag(v_a_101_) == 0)
{
uint64_t v___x_148_; 
v___x_148_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_110_ = v___x_148_;
goto v___jp_109_;
}
else
{
uint64_t v_hash_149_; 
v_hash_149_ = lean_ctor_get_uint64(v_a_101_, sizeof(void*)*2);
v___y_110_ = v_hash_149_;
goto v___jp_109_;
}
v___jp_109_:
{
uint64_t v___x_111_; uint64_t v___x_112_; uint64_t v_fold_113_; uint64_t v___x_114_; uint64_t v___x_115_; uint64_t v___x_116_; size_t v___x_117_; size_t v___x_118_; size_t v___x_119_; size_t v___x_120_; size_t v___x_121_; lean_object* v_bkt_122_; uint8_t v___x_123_; 
v___x_111_ = 32ULL;
v___x_112_ = lean_uint64_shift_right(v___y_110_, v___x_111_);
v_fold_113_ = lean_uint64_xor(v___y_110_, v___x_112_);
v___x_114_ = 16ULL;
v___x_115_ = lean_uint64_shift_right(v_fold_113_, v___x_114_);
v___x_116_ = lean_uint64_xor(v_fold_113_, v___x_115_);
v___x_117_ = lean_uint64_to_usize(v___x_116_);
v___x_118_ = lean_usize_of_nat(v___x_108_);
v___x_119_ = ((size_t)1ULL);
v___x_120_ = lean_usize_sub(v___x_118_, v___x_119_);
v___x_121_ = lean_usize_land(v___x_117_, v___x_120_);
v_bkt_122_ = lean_array_uget_borrowed(v_buckets_104_, v___x_121_);
v___x_123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_101_, v_bkt_122_);
if (v___x_123_ == 0)
{
lean_object* v___x_124_; lean_object* v_size_x27_125_; lean_object* v___x_126_; lean_object* v_buckets_x27_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; lean_object* v___x_131_; lean_object* v___x_132_; uint8_t v___x_133_; 
v___x_124_ = lean_unsigned_to_nat(1u);
v_size_x27_125_ = lean_nat_add(v_size_103_, v___x_124_);
lean_dec(v_size_103_);
lean_inc(v_bkt_122_);
v___x_126_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v___x_126_, 0, v_a_101_);
lean_ctor_set(v___x_126_, 1, v_b_102_);
lean_ctor_set(v___x_126_, 2, v_bkt_122_);
v_buckets_x27_127_ = lean_array_uset(v_buckets_104_, v___x_121_, v___x_126_);
v___x_128_ = lean_unsigned_to_nat(4u);
v___x_129_ = lean_nat_mul(v_size_x27_125_, v___x_128_);
v___x_130_ = lean_unsigned_to_nat(3u);
v___x_131_ = lean_nat_div(v___x_129_, v___x_130_);
lean_dec(v___x_129_);
v___x_132_ = lean_array_get_size(v_buckets_x27_127_);
v___x_133_ = lean_nat_dec_le(v___x_131_, v___x_132_);
lean_dec(v___x_131_);
if (v___x_133_ == 0)
{
lean_object* v_val_134_; lean_object* v___x_136_; 
v_val_134_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_127_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v_val_134_);
lean_ctor_set(v___x_106_, 0, v_size_x27_125_);
v___x_136_ = v___x_106_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v_size_x27_125_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v_val_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
else
{
lean_object* v___x_139_; 
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v_buckets_x27_127_);
lean_ctor_set(v___x_106_, 0, v_size_x27_125_);
v___x_139_ = v___x_106_;
goto v_reusejp_138_;
}
else
{
lean_object* v_reuseFailAlloc_140_; 
v_reuseFailAlloc_140_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_140_, 0, v_size_x27_125_);
lean_ctor_set(v_reuseFailAlloc_140_, 1, v_buckets_x27_127_);
v___x_139_ = v_reuseFailAlloc_140_;
goto v_reusejp_138_;
}
v_reusejp_138_:
{
return v___x_139_;
}
}
}
else
{
lean_object* v___x_141_; lean_object* v_buckets_x27_142_; lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
lean_inc(v_bkt_122_);
v___x_141_ = lean_box(0);
v_buckets_x27_142_ = lean_array_uset(v_buckets_104_, v___x_121_, v___x_141_);
v___x_143_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_101_, v_b_102_, v_bkt_122_);
v___x_144_ = lean_array_uset(v_buckets_x27_142_, v___x_121_, v___x_143_);
if (v_isShared_107_ == 0)
{
lean_ctor_set(v___x_106_, 1, v___x_144_);
v___x_146_ = v___x_106_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v_size_103_);
lean_ctor_set(v_reuseFailAlloc_147_, 1, v___x_144_);
v___x_146_ = v_reuseFailAlloc_147_;
goto v_reusejp_145_;
}
v_reusejp_145_:
{
return v___x_146_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object* v_map_151_, lean_object* v_entry_152_){
_start:
{
lean_object* v_name_153_; lean_object* v_variant_154_; lean_object* v___x_155_; 
v_name_153_ = lean_ctor_get(v_entry_152_, 0);
lean_inc(v_name_153_);
v_variant_154_ = lean_ctor_get(v_entry_152_, 1);
lean_inc_ref(v_variant_154_);
lean_dec_ref(v_entry_152_);
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_map_151_, v_name_153_, v_variant_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object* v___y_156_){
_start:
{
lean_inc_ref(v___y_156_);
return v___y_156_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(v___y_157_);
lean_dec_ref(v___y_157_);
return v_res_158_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_box(0);
v___x_166_ = lean_unsigned_to_nat(16u);
v___x_167_ = lean_mk_array(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___f_171_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___f_172_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_173_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___f_174_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_175_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__4_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___f_174_);
lean_ctor_set(v___x_176_, 2, v___x_173_);
lean_ctor_set(v___x_176_, 3, v___f_172_);
lean_ctor_set(v___x_176_, 4, v___f_171_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___x_179_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_();
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_182_, lean_object* v_m_183_, lean_object* v_a_184_, lean_object* v_b_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_m_183_, v_a_184_, v_b_185_);
return v___x_186_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_187_, lean_object* v_a_188_, lean_object* v_x_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_188_, v_x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_191_, lean_object* v_a_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_191_, v_a_192_, v_x_193_);
lean_dec(v_x_193_);
lean_dec(v_a_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_196_, lean_object* v_data_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_199_, lean_object* v_a_200_, lean_object* v_b_201_, lean_object* v_x_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_200_, v_b_201_, v_x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_204_, lean_object* v_i_205_, lean_object* v_source_206_, lean_object* v_target_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_205_, v_source_206_, v_target_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_209_, lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_210_, v_x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(lean_object* v_a_213_, lean_object* v_x_214_){
_start:
{
if (lean_obj_tag(v_x_214_) == 0)
{
lean_object* v___x_215_; 
v___x_215_ = lean_box(0);
return v___x_215_;
}
else
{
lean_object* v_key_216_; lean_object* v_value_217_; lean_object* v_tail_218_; uint8_t v___x_219_; 
v_key_216_ = lean_ctor_get(v_x_214_, 0);
v_value_217_ = lean_ctor_get(v_x_214_, 1);
v_tail_218_ = lean_ctor_get(v_x_214_, 2);
v___x_219_ = lean_name_eq(v_key_216_, v_a_213_);
if (v___x_219_ == 0)
{
v_x_214_ = v_tail_218_;
goto _start;
}
else
{
lean_object* v___x_221_; 
lean_inc(v_value_217_);
v___x_221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_221_, 0, v_value_217_);
return v___x_221_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_222_, v_x_223_);
lean_dec(v_x_223_);
lean_dec(v_a_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(lean_object* v_m_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_buckets_227_; lean_object* v___x_228_; uint64_t v___y_230_; 
v_buckets_227_ = lean_ctor_get(v_m_225_, 1);
v___x_228_ = lean_array_get_size(v_buckets_227_);
if (lean_obj_tag(v_a_226_) == 0)
{
uint64_t v___x_244_; 
v___x_244_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_230_ = v___x_244_;
goto v___jp_229_;
}
else
{
uint64_t v_hash_245_; 
v_hash_245_ = lean_ctor_get_uint64(v_a_226_, sizeof(void*)*2);
v___y_230_ = v_hash_245_;
goto v___jp_229_;
}
v___jp_229_:
{
uint64_t v___x_231_; uint64_t v___x_232_; uint64_t v_fold_233_; uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v___x_236_; size_t v___x_237_; size_t v___x_238_; size_t v___x_239_; size_t v___x_240_; size_t v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_231_ = 32ULL;
v___x_232_ = lean_uint64_shift_right(v___y_230_, v___x_231_);
v_fold_233_ = lean_uint64_xor(v___y_230_, v___x_232_);
v___x_234_ = 16ULL;
v___x_235_ = lean_uint64_shift_right(v_fold_233_, v___x_234_);
v___x_236_ = lean_uint64_xor(v_fold_233_, v___x_235_);
v___x_237_ = lean_uint64_to_usize(v___x_236_);
v___x_238_ = lean_usize_of_nat(v___x_228_);
v___x_239_ = ((size_t)1ULL);
v___x_240_ = lean_usize_sub(v___x_238_, v___x_239_);
v___x_241_ = lean_usize_land(v___x_237_, v___x_240_);
v___x_242_ = lean_array_uget_borrowed(v_buckets_227_, v___x_241_);
v___x_243_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_226_, v___x_242_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg___boxed(lean_object* v_m_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v_m_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_m_246_);
return v_res_248_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__1));
v___x_252_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0));
v___x_253_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_252_, v___x_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(lean_object* v_env_254_, lean_object* v_name_255_){
_start:
{
lean_object* v___x_256_; lean_object* v_ext_257_; lean_object* v_toEnvExtension_258_; lean_object* v_asyncMode_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_256_ = l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension;
v_ext_257_ = lean_ctor_get(v___x_256_, 1);
v_toEnvExtension_258_ = lean_ctor_get(v_ext_257_, 0);
v_asyncMode_259_ = lean_ctor_get(v_toEnvExtension_258_, 2);
v___x_260_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2, &l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2_once, _init_l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2);
v___x_261_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_260_, v___x_256_, v_env_254_, v_asyncMode_259_);
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v___x_261_, v_name_255_);
lean_dec(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___boxed(lean_object* v_env_263_, lean_object* v_name_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(v_env_263_, v_name_264_);
lean_dec(v_name_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0(lean_object* v_00_u03b2_266_, lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v_m_267_, v_a_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___boxed(lean_object* v_00_u03b2_270_, lean_object* v_m_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0(v_00_u03b2_270_, v_m_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_m_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(lean_object* v_00_u03b2_274_, lean_object* v_a_275_, lean_object* v_x_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_a_275_, v_x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_278_, lean_object* v_a_279_, lean_object* v_x_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(v_00_u03b2_278_, v_a_279_, v_x_280_);
lean_dec(v_x_280_);
lean_dec(v_a_279_);
return v_res_281_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_DSimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_DSimp_Variant(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
