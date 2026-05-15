// Lean compiler output
// Module: Lean.Meta.Sym.Simp.Variant
// Imports: public import Lean.Meta.Sym.Simp.SimpM import Lean.ScopedEnvExtension
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
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(100000) << 1) | 1)),((lean_object*)(((size_t)(2) << 1) | 1))}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*3 + 0, .m_other = 3, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0_value)}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1_value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__1_value)}};
static const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry = (const lean_object*)&l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0_value;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value;
static const lean_closure_object l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value;
static const lean_string_object l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "symSimpVariantExtension"};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value;
static const lean_ctor_object l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 101, 167, 211, 231, 20, 82, 40)}};
static const lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_ = (const lean_object*)&l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_;
static lean_once_cell_t l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_symSimpVariantExtension;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__0 = (const lean_object*)&l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__0_value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Name_hash___override___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__1 = (const lean_object*)&l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__1_value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(lean_object* v_x_14_, lean_object* v_a_15_){
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object* v_x_18_, lean_object* v_a_19_){
_start:
{
lean_object* v_res_20_; 
v_res_20_ = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(v_x_18_, v_a_19_);
lean_dec_ref(v_x_18_);
return v_res_20_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_a_21_, lean_object* v_b_22_, lean_object* v_x_23_){
_start:
{
if (lean_obj_tag(v_x_23_) == 0)
{
lean_dec(v_b_22_);
lean_dec(v_a_21_);
return v_x_23_;
}
else
{
lean_object* v_key_24_; lean_object* v_value_25_; lean_object* v_tail_26_; lean_object* v___x_28_; uint8_t v_isShared_29_; uint8_t v_isSharedCheck_38_; 
v_key_24_ = lean_ctor_get(v_x_23_, 0);
v_value_25_ = lean_ctor_get(v_x_23_, 1);
v_tail_26_ = lean_ctor_get(v_x_23_, 2);
v_isSharedCheck_38_ = !lean_is_exclusive(v_x_23_);
if (v_isSharedCheck_38_ == 0)
{
v___x_28_ = v_x_23_;
v_isShared_29_ = v_isSharedCheck_38_;
goto v_resetjp_27_;
}
else
{
lean_inc(v_tail_26_);
lean_inc(v_value_25_);
lean_inc(v_key_24_);
lean_dec(v_x_23_);
v___x_28_ = lean_box(0);
v_isShared_29_ = v_isSharedCheck_38_;
goto v_resetjp_27_;
}
v_resetjp_27_:
{
uint8_t v___x_30_; 
v___x_30_ = lean_name_eq(v_key_24_, v_a_21_);
if (v___x_30_ == 0)
{
lean_object* v___x_31_; lean_object* v___x_33_; 
v___x_31_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_21_, v_b_22_, v_tail_26_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 2, v___x_31_);
v___x_33_ = v___x_28_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_key_24_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_value_25_);
lean_ctor_set(v_reuseFailAlloc_34_, 2, v___x_31_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
else
{
lean_object* v___x_36_; 
lean_dec(v_value_25_);
lean_dec(v_key_24_);
if (v_isShared_29_ == 0)
{
lean_ctor_set(v___x_28_, 1, v_b_22_);
lean_ctor_set(v___x_28_, 0, v_a_21_);
v___x_36_ = v___x_28_;
goto v_reusejp_35_;
}
else
{
lean_object* v_reuseFailAlloc_37_; 
v_reuseFailAlloc_37_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_37_, 0, v_a_21_);
lean_ctor_set(v_reuseFailAlloc_37_, 1, v_b_22_);
lean_ctor_set(v_reuseFailAlloc_37_, 2, v_tail_26_);
v___x_36_ = v_reuseFailAlloc_37_;
goto v_reusejp_35_;
}
v_reusejp_35_:
{
return v___x_36_;
}
}
}
}
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_39_; uint64_t v___x_40_; 
v___x_39_ = lean_unsigned_to_nat(1723u);
v___x_40_ = lean_uint64_of_nat(v___x_39_);
return v___x_40_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_41_, lean_object* v_x_42_){
_start:
{
if (lean_obj_tag(v_x_42_) == 0)
{
return v_x_41_;
}
else
{
lean_object* v_key_43_; lean_object* v_value_44_; lean_object* v_tail_45_; lean_object* v___x_47_; uint8_t v_isShared_48_; uint8_t v_isSharedCheck_71_; 
v_key_43_ = lean_ctor_get(v_x_42_, 0);
v_value_44_ = lean_ctor_get(v_x_42_, 1);
v_tail_45_ = lean_ctor_get(v_x_42_, 2);
v_isSharedCheck_71_ = !lean_is_exclusive(v_x_42_);
if (v_isSharedCheck_71_ == 0)
{
v___x_47_ = v_x_42_;
v_isShared_48_ = v_isSharedCheck_71_;
goto v_resetjp_46_;
}
else
{
lean_inc(v_tail_45_);
lean_inc(v_value_44_);
lean_inc(v_key_43_);
lean_dec(v_x_42_);
v___x_47_ = lean_box(0);
v_isShared_48_ = v_isSharedCheck_71_;
goto v_resetjp_46_;
}
v_resetjp_46_:
{
lean_object* v___x_49_; uint64_t v___y_51_; 
v___x_49_ = lean_array_get_size(v_x_41_);
if (lean_obj_tag(v_key_43_) == 0)
{
uint64_t v___x_69_; 
v___x_69_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_51_ = v___x_69_;
goto v___jp_50_;
}
else
{
uint64_t v_hash_70_; 
v_hash_70_ = lean_ctor_get_uint64(v_key_43_, sizeof(void*)*2);
v___y_51_ = v_hash_70_;
goto v___jp_50_;
}
v___jp_50_:
{
uint64_t v___x_52_; uint64_t v___x_53_; uint64_t v_fold_54_; uint64_t v___x_55_; uint64_t v___x_56_; uint64_t v___x_57_; size_t v___x_58_; size_t v___x_59_; size_t v___x_60_; size_t v___x_61_; size_t v___x_62_; lean_object* v___x_63_; lean_object* v___x_65_; 
v___x_52_ = 32ULL;
v___x_53_ = lean_uint64_shift_right(v___y_51_, v___x_52_);
v_fold_54_ = lean_uint64_xor(v___y_51_, v___x_53_);
v___x_55_ = 16ULL;
v___x_56_ = lean_uint64_shift_right(v_fold_54_, v___x_55_);
v___x_57_ = lean_uint64_xor(v_fold_54_, v___x_56_);
v___x_58_ = lean_uint64_to_usize(v___x_57_);
v___x_59_ = lean_usize_of_nat(v___x_49_);
v___x_60_ = ((size_t)1ULL);
v___x_61_ = lean_usize_sub(v___x_59_, v___x_60_);
v___x_62_ = lean_usize_land(v___x_58_, v___x_61_);
v___x_63_ = lean_array_uget_borrowed(v_x_41_, v___x_62_);
lean_inc(v___x_63_);
if (v_isShared_48_ == 0)
{
lean_ctor_set(v___x_47_, 2, v___x_63_);
v___x_65_ = v___x_47_;
goto v_reusejp_64_;
}
else
{
lean_object* v_reuseFailAlloc_68_; 
v_reuseFailAlloc_68_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_68_, 0, v_key_43_);
lean_ctor_set(v_reuseFailAlloc_68_, 1, v_value_44_);
lean_ctor_set(v_reuseFailAlloc_68_, 2, v___x_63_);
v___x_65_ = v_reuseFailAlloc_68_;
goto v_reusejp_64_;
}
v_reusejp_64_:
{
lean_object* v___x_66_; 
v___x_66_ = lean_array_uset(v_x_41_, v___x_62_, v___x_65_);
v_x_41_ = v___x_66_;
v_x_42_ = v_tail_45_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_72_, lean_object* v_source_73_, lean_object* v_target_74_){
_start:
{
lean_object* v___x_75_; uint8_t v___x_76_; 
v___x_75_ = lean_array_get_size(v_source_73_);
v___x_76_ = lean_nat_dec_lt(v_i_72_, v___x_75_);
if (v___x_76_ == 0)
{
lean_dec_ref(v_source_73_);
lean_dec(v_i_72_);
return v_target_74_;
}
else
{
lean_object* v_es_77_; lean_object* v___x_78_; lean_object* v_source_79_; lean_object* v_target_80_; lean_object* v___x_81_; lean_object* v___x_82_; 
v_es_77_ = lean_array_fget(v_source_73_, v_i_72_);
v___x_78_ = lean_box(0);
v_source_79_ = lean_array_fset(v_source_73_, v_i_72_, v___x_78_);
v_target_80_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_target_74_, v_es_77_);
v___x_81_ = lean_unsigned_to_nat(1u);
v___x_82_ = lean_nat_add(v_i_72_, v___x_81_);
lean_dec(v_i_72_);
v_i_72_ = v___x_82_;
v_source_73_ = v_source_79_;
v_target_74_ = v_target_80_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_84_){
_start:
{
lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v_nbuckets_87_; lean_object* v___x_88_; lean_object* v___x_89_; lean_object* v___x_90_; lean_object* v___x_91_; 
v___x_85_ = lean_array_get_size(v_data_84_);
v___x_86_ = lean_unsigned_to_nat(2u);
v_nbuckets_87_ = lean_nat_mul(v___x_85_, v___x_86_);
v___x_88_ = lean_unsigned_to_nat(0u);
v___x_89_ = lean_box(0);
v___x_90_ = lean_mk_array(v_nbuckets_87_, v___x_89_);
v___x_91_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_88_, v_data_84_, v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_92_, lean_object* v_x_93_){
_start:
{
if (lean_obj_tag(v_x_93_) == 0)
{
uint8_t v___x_94_; 
v___x_94_ = 0;
return v___x_94_;
}
else
{
lean_object* v_key_95_; lean_object* v_tail_96_; uint8_t v___x_97_; 
v_key_95_ = lean_ctor_get(v_x_93_, 0);
v_tail_96_ = lean_ctor_get(v_x_93_, 2);
v___x_97_ = lean_name_eq(v_key_95_, v_a_92_);
if (v___x_97_ == 0)
{
v_x_93_ = v_tail_96_;
goto _start;
}
else
{
return v___x_97_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_99_, lean_object* v_x_100_){
_start:
{
uint8_t v_res_101_; lean_object* v_r_102_; 
v_res_101_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_99_, v_x_100_);
lean_dec(v_x_100_);
lean_dec(v_a_99_);
v_r_102_ = lean_box(v_res_101_);
return v_r_102_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_103_, lean_object* v_a_104_, lean_object* v_b_105_){
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
v___x_151_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
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
v___x_126_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_104_, v_bkt_125_);
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
v_val_137_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_130_);
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
v___x_146_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_104_, v_b_105_, v_bkt_125_);
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
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(lean_object* v_map_154_, lean_object* v_entry_155_){
_start:
{
lean_object* v_name_156_; lean_object* v_variant_157_; lean_object* v___x_158_; 
v_name_156_ = lean_ctor_get(v_entry_155_, 0);
lean_inc(v_name_156_);
v_variant_157_ = lean_ctor_get(v_entry_155_, 1);
lean_inc_ref(v_variant_157_);
lean_dec_ref(v_entry_155_);
v___x_158_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0___redArg(v_map_154_, v_name_156_, v_variant_157_);
return v___x_158_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(lean_object* v___y_159_){
_start:
{
lean_inc_ref(v___y_159_);
return v___y_159_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object* v___y_160_){
_start:
{
lean_object* v_res_161_; 
v_res_161_ = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(v___y_160_);
lean_dec_ref(v___y_160_);
return v_res_161_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_box(0);
v___x_169_ = lean_unsigned_to_nat(16u);
v___x_170_ = lean_mk_array(v___x_169_, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_171_; lean_object* v___x_172_; lean_object* v___x_173_; 
v___x_171_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_);
v___x_172_ = lean_unsigned_to_nat(0u);
v___x_173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_173_, 0, v___x_172_);
lean_ctor_set(v___x_173_, 1, v___x_171_);
return v___x_173_;
}
}
static lean_object* _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_174_; lean_object* v___f_175_; lean_object* v___x_176_; lean_object* v___f_177_; lean_object* v___x_178_; lean_object* v___x_179_; 
v___f_174_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_));
v___f_175_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_));
v___x_176_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_);
v___f_177_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_));
v___x_178_ = ((lean_object*)(l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_));
v___x_179_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_179_, 0, v___x_178_);
lean_ctor_set(v___x_179_, 1, v___f_177_);
lean_ctor_set(v___x_179_, 2, v___x_176_);
lean_ctor_set(v___x_179_, 3, v___f_175_);
lean_ctor_set(v___x_179_, 4, v___f_174_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_181_; lean_object* v___x_182_; 
v___x_181_ = lean_obj_once(&l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_, &l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once, _init_l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_);
v___x_182_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_181_);
return v___x_182_;
}
}
LEAN_EXPORT lean_object* l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object* v_a_183_){
_start:
{
lean_object* v_res_184_; 
v_res_184_ = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_();
return v_res_184_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_185_, lean_object* v_m_186_, lean_object* v_a_187_, lean_object* v_b_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0___redArg(v_m_186_, v_a_187_, v_b_188_);
return v___x_189_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_190_, lean_object* v_a_191_, lean_object* v_x_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_191_, v_x_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_194_, lean_object* v_a_195_, lean_object* v_x_196_){
_start:
{
uint8_t v_res_197_; lean_object* v_r_198_; 
v_res_197_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_194_, v_a_195_, v_x_196_);
lean_dec(v_x_196_);
lean_dec(v_a_195_);
v_r_198_ = lean_box(v_res_197_);
return v_r_198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_199_, lean_object* v_data_200_){
_start:
{
lean_object* v___x_201_; 
v___x_201_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_202_, lean_object* v_a_203_, lean_object* v_b_204_, lean_object* v_x_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_203_, v_b_204_, v_x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_207_, lean_object* v_i_208_, lean_object* v_source_209_, lean_object* v_target_210_){
_start:
{
lean_object* v___x_211_; 
v___x_211_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_208_, v_source_209_, v_target_210_);
return v___x_211_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_212_, lean_object* v_x_213_, lean_object* v_x_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_213_, v_x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(lean_object* v_a_216_, lean_object* v_x_217_){
_start:
{
if (lean_obj_tag(v_x_217_) == 0)
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
else
{
lean_object* v_key_219_; lean_object* v_value_220_; lean_object* v_tail_221_; uint8_t v___x_222_; 
v_key_219_ = lean_ctor_get(v_x_217_, 0);
v_value_220_ = lean_ctor_get(v_x_217_, 1);
v_tail_221_ = lean_ctor_get(v_x_217_, 2);
v___x_222_ = lean_name_eq(v_key_219_, v_a_216_);
if (v___x_222_ == 0)
{
v_x_217_ = v_tail_221_;
goto _start;
}
else
{
lean_object* v___x_224_; 
lean_inc(v_value_220_);
v___x_224_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_224_, 0, v_value_220_);
return v___x_224_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_225_, lean_object* v_x_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(v_a_225_, v_x_226_);
lean_dec(v_x_226_);
lean_dec(v_a_225_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(lean_object* v_m_228_, lean_object* v_a_229_){
_start:
{
lean_object* v_buckets_230_; lean_object* v___x_231_; uint64_t v___y_233_; 
v_buckets_230_ = lean_ctor_get(v_m_228_, 1);
v___x_231_ = lean_array_get_size(v_buckets_230_);
if (lean_obj_tag(v_a_229_) == 0)
{
uint64_t v___x_247_; 
v___x_247_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00__private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_233_ = v___x_247_;
goto v___jp_232_;
}
else
{
uint64_t v_hash_248_; 
v_hash_248_ = lean_ctor_get_uint64(v_a_229_, sizeof(void*)*2);
v___y_233_ = v_hash_248_;
goto v___jp_232_;
}
v___jp_232_:
{
uint64_t v___x_234_; uint64_t v___x_235_; uint64_t v_fold_236_; uint64_t v___x_237_; uint64_t v___x_238_; uint64_t v___x_239_; size_t v___x_240_; size_t v___x_241_; size_t v___x_242_; size_t v___x_243_; size_t v___x_244_; lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_234_ = 32ULL;
v___x_235_ = lean_uint64_shift_right(v___y_233_, v___x_234_);
v_fold_236_ = lean_uint64_xor(v___y_233_, v___x_235_);
v___x_237_ = 16ULL;
v___x_238_ = lean_uint64_shift_right(v_fold_236_, v___x_237_);
v___x_239_ = lean_uint64_xor(v_fold_236_, v___x_238_);
v___x_240_ = lean_uint64_to_usize(v___x_239_);
v___x_241_ = lean_usize_of_nat(v___x_231_);
v___x_242_ = ((size_t)1ULL);
v___x_243_ = lean_usize_sub(v___x_241_, v___x_242_);
v___x_244_ = lean_usize_land(v___x_240_, v___x_243_);
v___x_245_ = lean_array_uget_borrowed(v_buckets_230_, v___x_244_);
v___x_246_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(v_a_229_, v___x_245_);
return v___x_246_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg___boxed(lean_object* v_m_249_, lean_object* v_a_250_){
_start:
{
lean_object* v_res_251_; 
v_res_251_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(v_m_249_, v_a_250_);
lean_dec(v_a_250_);
lean_dec_ref(v_m_249_);
return v_res_251_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2(void){
_start:
{
lean_object* v___x_254_; lean_object* v___x_255_; lean_object* v___x_256_; 
v___x_254_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__1));
v___x_255_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__0));
v___x_256_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_255_, v___x_254_);
return v___x_256_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(lean_object* v_env_257_, lean_object* v_name_258_){
_start:
{
lean_object* v___x_259_; lean_object* v_ext_260_; lean_object* v_toEnvExtension_261_; lean_object* v_asyncMode_262_; lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v___x_259_ = l_Lean_Meta_Sym_Simp_symSimpVariantExtension;
v_ext_260_ = lean_ctor_get(v___x_259_, 1);
v_toEnvExtension_261_ = lean_ctor_get(v_ext_260_, 0);
v_asyncMode_262_ = lean_ctor_get(v_toEnvExtension_261_, 2);
v___x_263_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2, &l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2_once, _init_l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2);
v___x_264_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_263_, v___x_259_, v_env_257_, v_asyncMode_262_);
v___x_265_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(v___x_264_, v_name_258_);
lean_dec(v___x_264_);
return v___x_265_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___boxed(lean_object* v_env_266_, lean_object* v_name_267_){
_start:
{
lean_object* v_res_268_; 
v_res_268_ = l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(v_env_266_, v_name_267_);
lean_dec(v_name_267_);
return v_res_268_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0(lean_object* v_00_u03b2_269_, lean_object* v_m_270_, lean_object* v_a_271_){
_start:
{
lean_object* v___x_272_; 
v___x_272_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(v_m_270_, v_a_271_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___boxed(lean_object* v_00_u03b2_273_, lean_object* v_m_274_, lean_object* v_a_275_){
_start:
{
lean_object* v_res_276_; 
v_res_276_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0(v_00_u03b2_273_, v_m_274_, v_a_275_);
lean_dec(v_a_275_);
lean_dec_ref(v_m_274_);
return v_res_276_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0(lean_object* v_00_u03b2_277_, lean_object* v_a_278_, lean_object* v_x_279_){
_start:
{
lean_object* v___x_280_; 
v___x_280_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(v_a_278_, v_x_279_);
return v___x_280_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_281_, lean_object* v_a_282_, lean_object* v_x_283_){
_start:
{
lean_object* v_res_284_; 
v_res_284_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0(v_00_u03b2_281_, v_a_282_, v_x_283_);
lean_dec(v_x_283_);
lean_dec(v_a_282_);
return v_res_284_;
}
}
lean_object* runtime_initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* runtime_initialize_Lean_ScopedEnvExtension(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Simp_Variant(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = l___private_Lean_Meta_Sym_Simp_Variant_0__Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_();
if (lean_io_result_is_error(res)) return res;
l_Lean_Meta_Sym_Simp_symSimpVariantExtension = lean_io_result_get_value(res);
lean_mark_persistent(l_Lean_Meta_Sym_Simp_symSimpVariantExtension);
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Simp_Variant(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Lean_Meta_Sym_Simp_SimpM(uint8_t builtin);
lean_object* initialize_Lean_ScopedEnvExtension(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Simp_Variant(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Lean_Meta_Sym_Simp_SimpM(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_ScopedEnvExtension(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Simp_Variant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Simp_Variant(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Simp_Variant(builtin);
}
#ifdef __cplusplus
}
#endif
