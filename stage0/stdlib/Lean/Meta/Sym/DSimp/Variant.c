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
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_usize_to_nat(size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_noption_get(lean_object*);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Raw_setEntry___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(lean_object*, lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object*);
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
static lean_once_cell_t l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__8_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__8_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_m_21_, lean_object* v_query_22_, lean_object* v_x_23_, lean_object* v_x_24_, lean_object* v_x_25_){
_start:
{
lean_object* v_zero_26_; uint8_t v_isZero_27_; 
v_zero_26_ = lean_unsigned_to_nat(0u);
v_isZero_27_ = lean_nat_dec_eq(v_x_24_, v_zero_26_);
if (v_isZero_27_ == 1)
{
lean_dec(v_x_25_);
lean_dec(v_x_24_);
if (lean_obj_tag(v_x_23_) == 0)
{
lean_object* v___x_28_; 
v___x_28_ = lean_box(2);
return v___x_28_;
}
else
{
lean_object* v_val_29_; lean_object* v___x_31_; uint8_t v_isShared_32_; uint8_t v_isSharedCheck_36_; 
v_val_29_ = lean_ctor_get(v_x_23_, 0);
v_isSharedCheck_36_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_36_ == 0)
{
v___x_31_ = v_x_23_;
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
else
{
lean_inc(v_val_29_);
lean_dec(v_x_23_);
v___x_31_ = lean_box(0);
v_isShared_32_ = v_isSharedCheck_36_;
goto v_resetjp_30_;
}
v_resetjp_30_:
{
lean_object* v___x_34_; 
if (v_isShared_32_ == 0)
{
v___x_34_ = v___x_31_;
goto v_reusejp_33_;
}
else
{
lean_object* v_reuseFailAlloc_35_; 
v_reuseFailAlloc_35_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_35_, 0, v_val_29_);
v___x_34_ = v_reuseFailAlloc_35_;
goto v_reusejp_33_;
}
v_reusejp_33_:
{
return v___x_34_;
}
}
}
}
else
{
lean_object* v_keyArray_37_; lean_object* v_valueArray_38_; lean_object* v___x_39_; uint8_t v_isSome_40_; 
v_keyArray_37_ = lean_ctor_get(v_m_21_, 1);
v_valueArray_38_ = lean_ctor_get(v_m_21_, 2);
v___x_39_ = lean_array_fget_borrowed(v_keyArray_37_, v_x_25_);
v_isSome_40_ = lean_noption_is_some(v___x_39_);
if (v_isSome_40_ == 0)
{
lean_dec(v_x_24_);
if (lean_obj_tag(v_x_23_) == 0)
{
lean_object* v___x_41_; 
v___x_41_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_41_, 0, v_x_25_);
return v___x_41_;
}
else
{
lean_object* v_val_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_49_; 
lean_dec(v_x_25_);
v_val_42_ = lean_ctor_get(v_x_23_, 0);
v_isSharedCheck_49_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_49_ == 0)
{
v___x_44_ = v_x_23_;
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_val_42_);
lean_dec(v_x_23_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_49_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_47_; 
if (v_isShared_45_ == 0)
{
v___x_47_ = v___x_44_;
goto v_reusejp_46_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_val_42_);
v___x_47_ = v_reuseFailAlloc_48_;
goto v_reusejp_46_;
}
v_reusejp_46_:
{
return v___x_47_;
}
}
}
}
else
{
lean_object* v_one_50_; lean_object* v_n_51_; lean_object* v___y_53_; 
v_one_50_ = lean_unsigned_to_nat(1u);
v_n_51_ = lean_nat_sub(v_x_24_, v_one_50_);
lean_dec(v_x_24_);
if (v_isSome_40_ == 0)
{
goto v___jp_59_;
}
else
{
lean_object* v___x_61_; uint8_t v_isSome_62_; 
v___x_61_ = lean_array_fget_borrowed(v_valueArray_38_, v_x_25_);
v_isSome_62_ = lean_noption_is_some(v___x_61_);
if (v_isSome_62_ == 0)
{
goto v___jp_59_;
}
else
{
lean_object* v_val_63_; uint8_t v___x_64_; 
lean_inc(v___x_39_);
v_val_63_ = lean_noption_get(v___x_39_);
v___x_64_ = lean_name_eq(v_val_63_, v_query_22_);
if (v___x_64_ == 0)
{
lean_object* v___x_65_; lean_object* v___x_66_; uint8_t v___x_67_; 
lean_dec(v_val_63_);
v___x_65_ = lean_array_get_size(v_keyArray_37_);
v___x_66_ = lean_nat_add(v_x_25_, v_one_50_);
lean_dec(v_x_25_);
v___x_67_ = lean_nat_dec_lt(v___x_66_, v___x_65_);
if (v___x_67_ == 0)
{
lean_dec(v___x_66_);
v_x_24_ = v_n_51_;
v_x_25_ = v_zero_26_;
goto _start;
}
else
{
v_x_24_ = v_n_51_;
v_x_25_ = v___x_66_;
goto _start;
}
}
else
{
lean_object* v_val_70_; lean_object* v___x_71_; 
lean_dec(v_n_51_);
lean_dec(v_x_23_);
lean_inc(v___x_61_);
v_val_70_ = lean_noption_get(v___x_61_);
v___x_71_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_71_, 0, v_x_25_);
lean_ctor_set(v___x_71_, 1, v_val_63_);
lean_ctor_set(v___x_71_, 2, v_val_70_);
return v___x_71_;
}
}
}
v___jp_52_:
{
lean_object* v___x_54_; lean_object* v___x_55_; uint8_t v___x_56_; 
v___x_54_ = lean_array_get_size(v_keyArray_37_);
v___x_55_ = lean_nat_add(v_x_25_, v_one_50_);
lean_dec(v_x_25_);
v___x_56_ = lean_nat_dec_lt(v___x_55_, v___x_54_);
if (v___x_56_ == 0)
{
lean_dec(v___x_55_);
v_x_23_ = v___y_53_;
v_x_24_ = v_n_51_;
v_x_25_ = v_zero_26_;
goto _start;
}
else
{
v_x_23_ = v___y_53_;
v_x_24_ = v_n_51_;
v_x_25_ = v___x_55_;
goto _start;
}
}
v___jp_59_:
{
if (lean_obj_tag(v_x_23_) == 0)
{
lean_object* v___x_60_; 
lean_inc(v_x_25_);
v___x_60_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_60_, 0, v_x_25_);
v___y_53_ = v___x_60_;
goto v___jp_52_;
}
else
{
v___y_53_ = v_x_23_;
goto v___jp_52_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_m_72_, lean_object* v_query_73_, lean_object* v_x_74_, lean_object* v_x_75_, lean_object* v_x_76_){
_start:
{
lean_object* v_res_77_; 
v_res_77_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_72_, v_query_73_, v_x_74_, v_x_75_, v_x_76_);
lean_dec(v_query_73_);
lean_dec_ref(v_m_72_);
return v_res_77_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_78_, lean_object* v_query_79_){
_start:
{
lean_object* v_keyArray_80_; lean_object* v___x_81_; uint64_t v___y_83_; 
v_keyArray_80_ = lean_ctor_get(v_m_78_, 1);
v___x_81_ = lean_array_get_size(v_keyArray_80_);
if (lean_obj_tag(v_query_79_) == 0)
{
uint64_t v___x_98_; 
v___x_98_ = 1723ULL;
v___y_83_ = v___x_98_;
goto v___jp_82_;
}
else
{
uint64_t v_hash_99_; 
v_hash_99_ = lean_ctor_get_uint64(v_query_79_, sizeof(void*)*2);
v___y_83_ = v_hash_99_;
goto v___jp_82_;
}
v___jp_82_:
{
uint64_t v___x_84_; uint64_t v___x_85_; uint64_t v_fold_86_; uint64_t v___x_87_; uint64_t v___x_88_; uint64_t v___x_89_; size_t v___x_90_; size_t v___x_91_; size_t v___x_92_; size_t v___x_93_; size_t v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; 
v___x_84_ = 32ULL;
v___x_85_ = lean_uint64_shift_right(v___y_83_, v___x_84_);
v_fold_86_ = lean_uint64_xor(v___y_83_, v___x_85_);
v___x_87_ = 16ULL;
v___x_88_ = lean_uint64_shift_right(v_fold_86_, v___x_87_);
v___x_89_ = lean_uint64_xor(v_fold_86_, v___x_88_);
v___x_90_ = lean_uint64_to_usize(v___x_89_);
v___x_91_ = lean_usize_of_nat(v___x_81_);
v___x_92_ = ((size_t)1ULL);
v___x_93_ = lean_usize_sub(v___x_91_, v___x_92_);
v___x_94_ = lean_usize_land(v___x_90_, v___x_93_);
v___x_95_ = lean_usize_to_nat(v___x_94_);
v___x_96_ = lean_box(0);
v___x_97_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_78_, v_query_79_, v___x_96_, v___x_81_, v___x_95_);
return v___x_97_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg___boxed(lean_object* v_m_100_, lean_object* v_query_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_m_100_, v_query_101_);
lean_dec(v_query_101_);
lean_dec_ref(v_m_100_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(lean_object* v_b_103_, lean_object* v_acc_104_, lean_object* v_i_105_){
_start:
{
lean_object* v___y_107_; lean_object* v_keyArray_115_; lean_object* v_valueArray_116_; lean_object* v___x_117_; uint8_t v___x_118_; 
v_keyArray_115_ = lean_ctor_get(v_b_103_, 1);
v_valueArray_116_ = lean_ctor_get(v_b_103_, 2);
v___x_117_ = lean_array_get_size(v_keyArray_115_);
v___x_118_ = lean_nat_dec_lt(v_i_105_, v___x_117_);
if (v___x_118_ == 0)
{
lean_dec(v_i_105_);
return v_acc_104_;
}
else
{
lean_object* v___x_119_; uint8_t v_isSome_120_; 
v___x_119_ = lean_array_fget_borrowed(v_keyArray_115_, v_i_105_);
v_isSome_120_ = lean_noption_is_some(v___x_119_);
if (v_isSome_120_ == 0)
{
goto v___jp_111_;
}
else
{
lean_object* v___x_121_; uint8_t v_isSome_122_; 
v___x_121_ = lean_array_fget_borrowed(v_valueArray_116_, v_i_105_);
v_isSome_122_ = lean_noption_is_some(v___x_121_);
if (v_isSome_122_ == 0)
{
goto v___jp_111_;
}
else
{
lean_object* v_val_123_; lean_object* v_val_124_; lean_object* v_i_126_; lean_object* v___x_131_; 
lean_inc(v___x_119_);
v_val_123_ = lean_noption_get(v___x_119_);
lean_inc(v___x_121_);
v_val_124_ = lean_noption_get(v___x_121_);
v___x_131_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_acc_104_, v_val_123_);
switch(lean_obj_tag(v___x_131_))
{
case 0:
{
lean_object* v_index_132_; lean_object* v_size_133_; lean_object* v___x_134_; 
v_index_132_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_index_132_);
lean_dec_ref_known(v___x_131_, 3);
v_size_133_ = lean_ctor_get(v_acc_104_, 0);
lean_inc(v_size_133_);
v___x_134_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_104_, v_size_133_, v_index_132_, v_val_123_, v_val_124_);
lean_dec(v_index_132_);
v___y_107_ = v___x_134_;
goto v___jp_106_;
}
case 1:
{
lean_object* v_index_135_; 
v_index_135_ = lean_ctor_get(v___x_131_, 0);
lean_inc(v_index_135_);
lean_dec_ref_known(v___x_131_, 1);
v_i_126_ = v_index_135_;
goto v___jp_125_;
}
default: 
{
lean_object* v___x_136_; lean_object* v___x_137_; 
v___x_136_ = lean_unsigned_to_nat(0u);
v___x_137_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v_acc_104_, v___x_136_);
if (lean_obj_tag(v___x_137_) == 0)
{
lean_object* v_index_138_; 
v_index_138_ = lean_ctor_get(v___x_137_, 0);
lean_inc(v_index_138_);
lean_dec_ref_known(v___x_137_, 1);
v_i_126_ = v_index_138_;
goto v___jp_125_;
}
else
{
lean_dec(v_val_124_);
lean_dec(v_val_123_);
v___y_107_ = v_acc_104_;
goto v___jp_106_;
}
}
}
v___jp_125_:
{
lean_object* v_size_127_; lean_object* v___x_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
v_size_127_ = lean_ctor_get(v_acc_104_, 0);
v___x_128_ = lean_unsigned_to_nat(1u);
v___x_129_ = lean_nat_add(v_size_127_, v___x_128_);
v___x_130_ = l_Std_DHashMap_Raw_setEntry___redArg(v_acc_104_, v___x_129_, v_i_126_, v_val_123_, v_val_124_);
lean_dec(v_i_126_);
v___y_107_ = v___x_130_;
goto v___jp_106_;
}
}
}
}
v___jp_106_:
{
lean_object* v___x_108_; lean_object* v___x_109_; 
v___x_108_ = lean_unsigned_to_nat(1u);
v___x_109_ = lean_nat_add(v_i_105_, v___x_108_);
lean_dec(v_i_105_);
v_acc_104_ = v___y_107_;
v_i_105_ = v___x_109_;
goto _start;
}
v___jp_111_:
{
lean_object* v___x_112_; lean_object* v___x_113_; 
v___x_112_ = lean_unsigned_to_nat(1u);
v___x_113_ = lean_nat_add(v_i_105_, v___x_112_);
lean_dec(v_i_105_);
v_i_105_ = v___x_113_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg___boxed(lean_object* v_b_139_, lean_object* v_acc_140_, lean_object* v_i_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_b_139_, v_acc_140_, v_i_141_);
lean_dec_ref(v_b_139_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2___redArg(lean_object* v_init_143_, lean_object* v_b_144_){
_start:
{
lean_object* v___x_145_; lean_object* v___x_146_; 
v___x_145_ = lean_unsigned_to_nat(0u);
v___x_146_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_b_144_, v_init_143_, v___x_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2___redArg___boxed(lean_object* v_init_147_, lean_object* v_b_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2___redArg(v_init_147_, v_b_148_);
lean_dec_ref(v_b_148_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1___redArg(lean_object* v_m_150_){
_start:
{
lean_object* v_keyArray_151_; lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v_cellCount_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_157_; lean_object* v_target_158_; lean_object* v___x_159_; 
v_keyArray_151_ = lean_ctor_get(v_m_150_, 1);
v___x_152_ = lean_array_get_size(v_keyArray_151_);
v___x_153_ = lean_unsigned_to_nat(2u);
v_cellCount_154_ = lean_nat_mul(v___x_152_, v___x_153_);
v___x_155_ = lean_unsigned_to_nat(0u);
lean_inc(v_cellCount_154_);
v___x_156_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_154_);
v___x_157_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_154_);
v_target_158_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_target_158_, 0, v___x_155_);
lean_ctor_set(v_target_158_, 1, v___x_156_);
lean_ctor_set(v_target_158_, 2, v___x_157_);
v___x_159_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2___redArg(v_target_158_, v_m_150_);
return v___x_159_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1___redArg___boxed(lean_object* v_m_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1___redArg(v_m_160_);
lean_dec_ref(v_m_160_);
return v_res_161_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object* v_map_162_, lean_object* v_entry_163_){
_start:
{
lean_object* v_name_164_; lean_object* v_variant_165_; lean_object* v___y_167_; lean_object* v_i_168_; lean_object* v___y_174_; lean_object* v___y_184_; lean_object* v_i_185_; lean_object* v___x_200_; 
v_name_164_ = lean_ctor_get(v_entry_163_, 0);
lean_inc(v_name_164_);
v_variant_165_ = lean_ctor_get(v_entry_163_, 1);
lean_inc_ref(v_variant_165_);
lean_dec_ref(v_entry_163_);
v___x_200_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_map_162_, v_name_164_);
switch(lean_obj_tag(v___x_200_))
{
case 0:
{
lean_object* v_index_201_; lean_object* v_size_202_; lean_object* v___x_203_; 
v_index_201_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_index_201_);
lean_dec_ref_known(v___x_200_, 3);
v_size_202_ = lean_ctor_get(v_map_162_, 0);
lean_inc(v_size_202_);
v___x_203_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_162_, v_size_202_, v_index_201_, v_name_164_, v_variant_165_);
lean_dec(v_index_201_);
return v___x_203_;
}
case 1:
{
lean_object* v_index_204_; lean_object* v_size_205_; lean_object* v_keyArray_206_; lean_object* v___x_207_; lean_object* v___x_208_; lean_object* v___x_209_; uint8_t v___x_210_; 
v_index_204_ = lean_ctor_get(v___x_200_, 0);
lean_inc(v_index_204_);
lean_dec_ref_known(v___x_200_, 1);
v_size_205_ = lean_ctor_get(v_map_162_, 0);
v_keyArray_206_ = lean_ctor_get(v_map_162_, 1);
v___x_207_ = lean_unsigned_to_nat(1u);
v___x_208_ = lean_nat_add(v_size_205_, v___x_207_);
v___x_209_ = lean_array_get_size(v_keyArray_206_);
v___x_210_ = lean_nat_dec_lt(v___x_208_, v___x_209_);
if (v___x_210_ == 0)
{
lean_dec(v___x_208_);
lean_dec(v_index_204_);
goto v___jp_190_;
}
else
{
lean_object* v___x_211_; lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; uint8_t v___x_215_; 
v___x_211_ = lean_unsigned_to_nat(4u);
v___x_212_ = lean_nat_mul(v___x_208_, v___x_211_);
v___x_213_ = lean_unsigned_to_nat(3u);
v___x_214_ = lean_nat_mul(v___x_209_, v___x_213_);
v___x_215_ = lean_nat_dec_le(v___x_212_, v___x_214_);
lean_dec(v___x_214_);
lean_dec(v___x_212_);
if (v___x_215_ == 0)
{
lean_dec(v___x_208_);
lean_dec(v_index_204_);
goto v___jp_190_;
}
else
{
lean_object* v___x_216_; 
v___x_216_ = l_Std_DHashMap_Raw_setEntry___redArg(v_map_162_, v___x_208_, v_index_204_, v_name_164_, v_variant_165_);
lean_dec(v_index_204_);
return v___x_216_;
}
}
}
default: 
{
lean_object* v_size_217_; lean_object* v_keyArray_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; uint8_t v___x_222_; 
v_size_217_ = lean_ctor_get(v_map_162_, 0);
v_keyArray_218_ = lean_ctor_get(v_map_162_, 1);
v___x_219_ = lean_unsigned_to_nat(1u);
v___x_220_ = lean_nat_add(v_size_217_, v___x_219_);
v___x_221_ = lean_array_get_size(v_keyArray_218_);
v___x_222_ = lean_nat_dec_lt(v___x_220_, v___x_221_);
if (v___x_222_ == 0)
{
lean_object* v___x_223_; 
lean_dec(v___x_220_);
v___x_223_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1___redArg(v_map_162_);
lean_dec_ref(v_map_162_);
v___y_174_ = v___x_223_;
goto v___jp_173_;
}
else
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; uint8_t v___x_228_; 
v___x_224_ = lean_unsigned_to_nat(4u);
v___x_225_ = lean_nat_mul(v___x_220_, v___x_224_);
lean_dec(v___x_220_);
v___x_226_ = lean_unsigned_to_nat(3u);
v___x_227_ = lean_nat_mul(v___x_221_, v___x_226_);
v___x_228_ = lean_nat_dec_le(v___x_225_, v___x_227_);
lean_dec(v___x_227_);
lean_dec(v___x_225_);
if (v___x_228_ == 0)
{
lean_object* v___x_229_; 
v___x_229_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1___redArg(v_map_162_);
lean_dec_ref(v_map_162_);
v___y_174_ = v___x_229_;
goto v___jp_173_;
}
else
{
v___y_174_ = v_map_162_;
goto v___jp_173_;
}
}
}
}
v___jp_166_:
{
lean_object* v_size_169_; lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_172_; 
v_size_169_ = lean_ctor_get(v___y_167_, 0);
v___x_170_ = lean_unsigned_to_nat(1u);
v___x_171_ = lean_nat_add(v_size_169_, v___x_170_);
v___x_172_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_167_, v___x_171_, v_i_168_, v_name_164_, v_variant_165_);
lean_dec(v_i_168_);
return v___x_172_;
}
v___jp_173_:
{
lean_object* v___x_175_; 
v___x_175_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v___y_174_, v_name_164_);
switch(lean_obj_tag(v___x_175_))
{
case 0:
{
lean_object* v_index_176_; lean_object* v_size_177_; lean_object* v___x_178_; 
v_index_176_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_index_176_);
lean_dec_ref_known(v___x_175_, 3);
v_size_177_ = lean_ctor_get(v___y_174_, 0);
lean_inc(v_size_177_);
v___x_178_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_174_, v_size_177_, v_index_176_, v_name_164_, v_variant_165_);
lean_dec(v_index_176_);
return v___x_178_;
}
case 1:
{
lean_object* v_index_179_; 
v_index_179_ = lean_ctor_get(v___x_175_, 0);
lean_inc(v_index_179_);
lean_dec_ref_known(v___x_175_, 1);
v___y_167_ = v___y_174_;
v_i_168_ = v_index_179_;
goto v___jp_166_;
}
default: 
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_unsigned_to_nat(0u);
v___x_181_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___y_174_, v___x_180_);
if (lean_obj_tag(v___x_181_) == 0)
{
lean_object* v_index_182_; 
v_index_182_ = lean_ctor_get(v___x_181_, 0);
lean_inc(v_index_182_);
lean_dec_ref_known(v___x_181_, 1);
v___y_167_ = v___y_174_;
v_i_168_ = v_index_182_;
goto v___jp_166_;
}
else
{
lean_dec_ref(v_variant_165_);
lean_dec(v_name_164_);
return v___y_174_;
}
}
}
}
v___jp_183_:
{
lean_object* v_size_186_; lean_object* v___x_187_; lean_object* v___x_188_; lean_object* v___x_189_; 
v_size_186_ = lean_ctor_get(v___y_184_, 0);
v___x_187_ = lean_unsigned_to_nat(1u);
v___x_188_ = lean_nat_add(v_size_186_, v___x_187_);
v___x_189_ = l_Std_DHashMap_Raw_setEntry___redArg(v___y_184_, v___x_188_, v_i_185_, v_name_164_, v_variant_165_);
lean_dec(v_i_185_);
return v___x_189_;
}
v___jp_190_:
{
lean_object* v___x_191_; lean_object* v___x_192_; 
v___x_191_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1___redArg(v_map_162_);
lean_dec_ref(v_map_162_);
v___x_192_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v___x_191_, v_name_164_);
switch(lean_obj_tag(v___x_192_))
{
case 0:
{
lean_object* v_index_193_; lean_object* v_size_194_; lean_object* v___x_195_; 
v_index_193_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_index_193_);
lean_dec_ref_known(v___x_192_, 3);
v_size_194_ = lean_ctor_get(v___x_191_, 0);
lean_inc(v_size_194_);
v___x_195_ = l_Std_DHashMap_Raw_setEntry___redArg(v___x_191_, v_size_194_, v_index_193_, v_name_164_, v_variant_165_);
lean_dec(v_index_193_);
return v___x_195_;
}
case 1:
{
lean_object* v_index_196_; 
v_index_196_ = lean_ctor_get(v___x_192_, 0);
lean_inc(v_index_196_);
lean_dec_ref_known(v___x_192_, 1);
v___y_184_ = v___x_191_;
v_i_185_ = v_index_196_;
goto v___jp_183_;
}
default: 
{
lean_object* v___x_197_; lean_object* v___x_198_; 
v___x_197_ = lean_unsigned_to_nat(0u);
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_findEmptyFrom___redArg(v___x_191_, v___x_197_);
if (lean_obj_tag(v___x_198_) == 0)
{
lean_object* v_index_199_; 
v_index_199_ = lean_ctor_get(v___x_198_, 0);
lean_inc(v_index_199_);
lean_dec_ref_known(v___x_198_, 1);
v___y_184_ = v___x_191_;
v_i_185_ = v_index_199_;
goto v___jp_183_;
}
else
{
lean_dec_ref(v_variant_165_);
lean_dec(v_name_164_);
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(lean_object* v___y_230_){
_start:
{
lean_inc_ref(v___y_230_);
return v___y_230_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object* v___y_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___lam__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(v___y_231_);
lean_dec_ref(v___y_231_);
return v_res_232_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_239_; lean_object* v___x_240_; 
v_cellCount_239_ = lean_unsigned_to_nat(16u);
v___x_240_ = l_Std_DHashMap_Internal_Raw_u2080_emptyKeyArray___redArg(v_cellCount_239_);
return v___x_240_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v_cellCount_241_; lean_object* v___x_242_; 
v_cellCount_241_ = lean_unsigned_to_nat(16u);
v___x_242_ = l_Std_DHashMap_Internal_Raw_u2080_emptyValueArray___redArg(v_cellCount_241_);
return v___x_242_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_243_; lean_object* v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_243_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__6_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___x_244_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__5_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___x_245_ = lean_unsigned_to_nat(0u);
v___x_246_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_246_, 0, v___x_245_);
lean_ctor_set(v___x_246_, 1, v___x_244_);
lean_ctor_set(v___x_246_, 2, v___x_243_);
return v___x_246_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__8_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_247_; lean_object* v___f_248_; lean_object* v___x_249_; lean_object* v___f_250_; lean_object* v___x_251_; lean_object* v___x_252_; 
v___f_247_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__0_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___f_248_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__2_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_249_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__7_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___f_250_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__1_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_251_ = ((lean_object*)(l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__4_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_));
v___x_252_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_252_, 0, v___x_251_);
lean_ctor_set(v___x_252_, 1, v___f_250_);
lean_ctor_set(v___x_252_, 2, v___x_249_);
lean_ctor_set(v___x_252_, 3, v___f_248_);
lean_ctor_set(v___x_252_, 4, v___f_247_);
return v___x_252_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; 
v___x_254_ = lean_obj_once(&l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__8_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__8_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn___closed__8_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_);
v___x_255_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_254_);
return v___x_255_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2____boxed(lean_object* v_a_256_){
_start:
{
lean_object* v_res_257_; 
v_res_257_ = l___private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2_();
return v_res_257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_258_, lean_object* v_m_259_, lean_object* v_query_260_){
_start:
{
lean_object* v___x_261_; 
v___x_261_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_m_259_, v_query_260_);
return v___x_261_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___boxed(lean_object* v_00_u03b2_262_, lean_object* v_m_263_, lean_object* v_query_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0(v_00_u03b2_262_, v_m_263_, v_query_264_);
lean_dec(v_query_264_);
lean_dec_ref(v_m_263_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1(lean_object* v_00_u03b2_266_, lean_object* v_m_267_){
_start:
{
lean_object* v___x_268_; 
v___x_268_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1___redArg(v_m_267_);
return v___x_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1___boxed(lean_object* v_00_u03b2_269_, lean_object* v_m_270_){
_start:
{
lean_object* v_res_271_; 
v_res_271_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1(v_00_u03b2_269_, v_m_270_);
lean_dec_ref(v_m_270_);
return v_res_271_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_272_, lean_object* v_m_273_, lean_object* v_query_274_, lean_object* v_x_275_, lean_object* v_x_276_, lean_object* v_x_277_, lean_object* v_x_278_){
_start:
{
lean_object* v___x_279_; 
v___x_279_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___redArg(v_m_273_, v_query_274_, v_x_275_, v_x_276_, v_x_277_);
return v___x_279_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_280_, lean_object* v_m_281_, lean_object* v_query_282_, lean_object* v_x_283_, lean_object* v_x_284_, lean_object* v_x_285_, lean_object* v_x_286_){
_start:
{
lean_object* v_res_287_; 
v_res_287_ = l_Std_DHashMap_Internal_Raw_u2080_probeFromAux___at___00Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_280_, v_m_281_, v_query_282_, v_x_283_, v_x_284_, v_x_285_, v_x_286_);
lean_dec(v_query_282_);
lean_dec_ref(v_m_281_);
return v_res_287_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2(lean_object* v_00_u03b2_288_, lean_object* v_init_289_, lean_object* v_b_290_){
_start:
{
lean_object* v___x_291_; 
v___x_291_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2___redArg(v_init_289_, v_b_290_);
return v___x_291_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2___boxed(lean_object* v_00_u03b2_292_, lean_object* v_init_293_, lean_object* v_b_294_){
_start:
{
lean_object* v_res_295_; 
v_res_295_ = l_Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2(v_00_u03b2_292_, v_init_293_, v_b_294_);
lean_dec_ref(v_b_294_);
return v_res_295_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3(lean_object* v_00_u03b2_296_, lean_object* v_b_297_, lean_object* v_acc_298_, lean_object* v_i_299_){
_start:
{
lean_object* v___x_300_; 
v___x_300_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3___redArg(v_b_297_, v_acc_298_, v_i_299_);
return v___x_300_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3___boxed(lean_object* v_00_u03b2_301_, lean_object* v_b_302_, lean_object* v_acc_303_, lean_object* v_i_304_){
_start:
{
lean_object* v_res_305_; 
v_res_305_ = l_Std_DHashMap_Raw_foldMFrom___at___00Std_DHashMap_Raw_foldM___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__1_spec__2_spec__3(v_00_u03b2_301_, v_b_302_, v_acc_303_, v_i_304_);
lean_dec_ref(v_b_302_);
return v_res_305_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(lean_object* v_m_306_, lean_object* v_query_307_){
_start:
{
lean_object* v___x_308_; 
v___x_308_ = l_Std_DHashMap_Internal_Raw_u2080_probe___at___00__private_Lean_Meta_Sym_DSimp_Variant_0__Lean_Meta_Sym_DSimp_initFn_00___x40_Lean_Meta_Sym_DSimp_Variant_3815569538____hygCtx___hyg_2__spec__0___redArg(v_m_306_, v_query_307_);
if (lean_obj_tag(v___x_308_) == 0)
{
lean_object* v_index_309_; lean_object* v_key_310_; lean_object* v_value_311_; lean_object* v___x_313_; uint8_t v_isShared_314_; uint8_t v_isSharedCheck_318_; 
v_index_309_ = lean_ctor_get(v___x_308_, 0);
v_key_310_ = lean_ctor_get(v___x_308_, 1);
v_value_311_ = lean_ctor_get(v___x_308_, 2);
v_isSharedCheck_318_ = !lean_is_exclusive(v___x_308_);
if (v_isSharedCheck_318_ == 0)
{
v___x_313_ = v___x_308_;
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
else
{
lean_inc(v_value_311_);
lean_inc(v_key_310_);
lean_inc(v_index_309_);
lean_dec(v___x_308_);
v___x_313_ = lean_box(0);
v_isShared_314_ = v_isSharedCheck_318_;
goto v_resetjp_312_;
}
v_resetjp_312_:
{
lean_object* v___x_316_; 
if (v_isShared_314_ == 0)
{
v___x_316_ = v___x_313_;
goto v_reusejp_315_;
}
else
{
lean_object* v_reuseFailAlloc_317_; 
v_reuseFailAlloc_317_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_317_, 0, v_index_309_);
lean_ctor_set(v_reuseFailAlloc_317_, 1, v_key_310_);
lean_ctor_set(v_reuseFailAlloc_317_, 2, v_value_311_);
v___x_316_ = v_reuseFailAlloc_317_;
goto v_reusejp_315_;
}
v_reusejp_315_:
{
return v___x_316_;
}
}
}
else
{
lean_object* v___x_319_; 
lean_dec(v___x_308_);
v___x_319_ = lean_box(1);
return v___x_319_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_m_320_, lean_object* v_query_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_m_320_, v_query_321_);
lean_dec(v_query_321_);
lean_dec_ref(v_m_320_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(lean_object* v_m_323_, lean_object* v_a_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_m_323_, v_a_324_);
if (lean_obj_tag(v___x_325_) == 0)
{
lean_object* v_value_326_; lean_object* v___x_327_; 
v_value_326_ = lean_ctor_get(v___x_325_, 2);
lean_inc(v_value_326_);
lean_dec_ref_known(v___x_325_, 3);
v___x_327_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_327_, 0, v_value_326_);
return v___x_327_;
}
else
{
lean_object* v___x_328_; 
v___x_328_ = lean_box(0);
return v___x_328_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg___boxed(lean_object* v_m_329_, lean_object* v_a_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v_m_329_, v_a_330_);
lean_dec(v_a_330_);
lean_dec_ref(v_m_329_);
return v_res_331_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2(void){
_start:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; 
v___x_334_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__1));
v___x_335_ = ((lean_object*)(l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__0));
v___x_336_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_335_, v___x_334_);
return v___x_336_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(lean_object* v_env_337_, lean_object* v_name_338_){
_start:
{
lean_object* v___x_339_; lean_object* v_ext_340_; lean_object* v_toEnvExtension_341_; lean_object* v_asyncMode_342_; lean_object* v___x_343_; lean_object* v___x_344_; lean_object* v___x_345_; 
v___x_339_ = l_Lean_Meta_Sym_DSimp_symDSimpVariantExtension;
v_ext_340_ = lean_ctor_get(v___x_339_, 1);
v_toEnvExtension_341_ = lean_ctor_get(v_ext_340_, 0);
v_asyncMode_342_ = lean_ctor_get(v_toEnvExtension_341_, 2);
v___x_343_ = lean_obj_once(&l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2, &l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2_once, _init_l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___closed__2);
v___x_344_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_343_, v___x_339_, v_env_337_, v_asyncMode_342_);
v___x_345_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v___x_344_, v_name_338_);
lean_dec(v___x_344_);
return v___x_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f___boxed(lean_object* v_env_346_, lean_object* v_name_347_){
_start:
{
lean_object* v_res_348_; 
v_res_348_ = l_Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f(v_env_346_, v_name_347_);
lean_dec(v_name_347_);
return v_res_348_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0(lean_object* v_00_u03b2_349_, lean_object* v_m_350_, lean_object* v_a_351_){
_start:
{
lean_object* v___x_352_; 
v___x_352_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___redArg(v_m_350_, v_a_351_);
return v___x_352_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0___boxed(lean_object* v_00_u03b2_353_, lean_object* v_m_354_, lean_object* v_a_355_){
_start:
{
lean_object* v_res_356_; 
v_res_356_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0(v_00_u03b2_353_, v_m_354_, v_a_355_);
lean_dec(v_a_355_);
lean_dec_ref(v_m_354_);
return v_res_356_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(lean_object* v_00_u03b2_357_, lean_object* v_m_358_, lean_object* v_query_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___redArg(v_m_358_, v_query_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_361_, lean_object* v_m_362_, lean_object* v_query_363_){
_start:
{
lean_object* v_res_364_; 
v_res_364_ = l_Std_DHashMap_Internal_Raw_u2080_scan___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_DSimp_getSymDSimpVariant_x3f_spec__0_spec__0(v_00_u03b2_361_, v_m_362_, v_query_363_);
lean_dec(v_query_363_);
lean_dec_ref(v_m_362_);
return v_res_364_;
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
