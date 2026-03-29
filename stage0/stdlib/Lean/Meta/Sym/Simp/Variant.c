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
lean_object* l_Lean_Name_mkStr1(lean_object*);
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_name_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_uset(lean_object*, size_t, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_nat_div(lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_fset(lean_object*, lean_object*, lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
lean_object* l_Lean_registerSimpleScopedEnvExtension___redArg(lean_object*);
lean_object* l_Lean_Name_hash___override___boxed(lean_object*);
lean_object* l_Lean_Name_beq___boxed(lean_object*, lean_object*);
lean_object* l_Std_HashMap_instInhabited(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_Lean_ScopedEnvExtension_getState___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
extern lean_object* l_Lean_Meta_Sym_Simp_instInhabitedConfig_default;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(uint8_t, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static uint64_t l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0;
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn___lam__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object*);
static const lean_closure_object l_Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_initFn___lam__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value;
static const lean_closure_object l_Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value;
static const lean_string_object l_Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 24, .m_capacity = 24, .m_length = 23, .m_data = "symSimpVariantExtension"};
static const lean_object* l_Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value;
static const lean_ctor_object l_Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 8, .m_other = 2, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Meta_Sym_Simp_initFn___closed__3_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value),LEAN_SCALAR_PTR_LITERAL(94, 101, 167, 211, 231, 20, 82, 40)}};
static const lean_object* l_Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_ = (const lean_object*)&l_Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__value;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_;
static lean_once_cell_t l_Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_;
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_();
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object*, lean_object*, lean_object*);
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
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0(void){
_start:
{
lean_object* v___x_1_; lean_object* v___x_2_; lean_object* v___x_3_; 
v___x_1_ = l_Lean_Meta_Sym_Simp_instInhabitedConfig_default;
v___x_2_ = lean_box(0);
v___x_3_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3_, 0, v___x_2_);
lean_ctor_set(v___x_3_, 1, v___x_2_);
lean_ctor_set(v___x_3_, 2, v___x_1_);
return v___x_3_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default(void){
_start:
{
lean_object* v___x_4_; 
v___x_4_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0, &l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default___closed__0);
return v___x_4_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant(void){
_start:
{
lean_object* v___x_5_; 
v___x_5_ = l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default;
return v___x_5_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0(void){
_start:
{
lean_object* v___x_6_; lean_object* v___x_7_; lean_object* v___x_8_; 
v___x_6_ = l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default;
v___x_7_ = lean_box(0);
v___x_8_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_8_, 0, v___x_7_);
lean_ctor_set(v___x_8_, 1, v___x_6_);
return v___x_8_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default(void){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0, &l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0_once, _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default___closed__0);
return v___x_9_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry(void){
_start:
{
lean_object* v___x_10_; 
v___x_10_ = l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default;
return v___x_10_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(uint8_t v_x_11_, lean_object* v___y_12_){
_start:
{
lean_object* v___x_13_; 
v___x_13_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_13_, 0, v___y_12_);
return v___x_13_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object* v_x_14_, lean_object* v___y_15_){
_start:
{
uint8_t v_x_435__boxed_16_; lean_object* v_res_17_; 
v_x_435__boxed_16_ = lean_unbox(v_x_14_);
v_res_17_ = l_Lean_Meta_Sym_Simp_initFn___lam__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(v_x_435__boxed_16_, v___y_15_);
return v_res_17_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(lean_object* v_a_18_, lean_object* v_b_19_, lean_object* v_x_20_){
_start:
{
if (lean_obj_tag(v_x_20_) == 0)
{
lean_dec(v_b_19_);
lean_dec(v_a_18_);
return v_x_20_;
}
else
{
lean_object* v_key_21_; lean_object* v_value_22_; lean_object* v_tail_23_; lean_object* v___x_25_; uint8_t v_isShared_26_; uint8_t v_isSharedCheck_35_; 
v_key_21_ = lean_ctor_get(v_x_20_, 0);
v_value_22_ = lean_ctor_get(v_x_20_, 1);
v_tail_23_ = lean_ctor_get(v_x_20_, 2);
v_isSharedCheck_35_ = !lean_is_exclusive(v_x_20_);
if (v_isSharedCheck_35_ == 0)
{
v___x_25_ = v_x_20_;
v_isShared_26_ = v_isSharedCheck_35_;
goto v_resetjp_24_;
}
else
{
lean_inc(v_tail_23_);
lean_inc(v_value_22_);
lean_inc(v_key_21_);
lean_dec(v_x_20_);
v___x_25_ = lean_box(0);
v_isShared_26_ = v_isSharedCheck_35_;
goto v_resetjp_24_;
}
v_resetjp_24_:
{
uint8_t v___x_27_; 
v___x_27_ = lean_name_eq(v_key_21_, v_a_18_);
if (v___x_27_ == 0)
{
lean_object* v___x_28_; lean_object* v___x_30_; 
v___x_28_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_18_, v_b_19_, v_tail_23_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 2, v___x_28_);
v___x_30_ = v___x_25_;
goto v_reusejp_29_;
}
else
{
lean_object* v_reuseFailAlloc_31_; 
v_reuseFailAlloc_31_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_31_, 0, v_key_21_);
lean_ctor_set(v_reuseFailAlloc_31_, 1, v_value_22_);
lean_ctor_set(v_reuseFailAlloc_31_, 2, v___x_28_);
v___x_30_ = v_reuseFailAlloc_31_;
goto v_reusejp_29_;
}
v_reusejp_29_:
{
return v___x_30_;
}
}
else
{
lean_object* v___x_33_; 
lean_dec(v_value_22_);
lean_dec(v_key_21_);
if (v_isShared_26_ == 0)
{
lean_ctor_set(v___x_25_, 1, v_b_19_);
lean_ctor_set(v___x_25_, 0, v_a_18_);
v___x_33_ = v___x_25_;
goto v_reusejp_32_;
}
else
{
lean_object* v_reuseFailAlloc_34_; 
v_reuseFailAlloc_34_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_34_, 0, v_a_18_);
lean_ctor_set(v_reuseFailAlloc_34_, 1, v_b_19_);
lean_ctor_set(v_reuseFailAlloc_34_, 2, v_tail_23_);
v___x_33_ = v_reuseFailAlloc_34_;
goto v_reusejp_32_;
}
v_reusejp_32_:
{
return v___x_33_;
}
}
}
}
}
}
static uint64_t _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0(void){
_start:
{
lean_object* v___x_36_; uint64_t v___x_37_; 
v___x_36_ = lean_unsigned_to_nat(1723u);
v___x_37_ = lean_uint64_of_nat(v___x_36_);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(lean_object* v_x_38_, lean_object* v_x_39_){
_start:
{
if (lean_obj_tag(v_x_39_) == 0)
{
return v_x_38_;
}
else
{
lean_object* v_key_40_; lean_object* v_value_41_; lean_object* v_tail_42_; lean_object* v___x_44_; uint8_t v_isShared_45_; uint8_t v_isSharedCheck_68_; 
v_key_40_ = lean_ctor_get(v_x_39_, 0);
v_value_41_ = lean_ctor_get(v_x_39_, 1);
v_tail_42_ = lean_ctor_get(v_x_39_, 2);
v_isSharedCheck_68_ = !lean_is_exclusive(v_x_39_);
if (v_isSharedCheck_68_ == 0)
{
v___x_44_ = v_x_39_;
v_isShared_45_ = v_isSharedCheck_68_;
goto v_resetjp_43_;
}
else
{
lean_inc(v_tail_42_);
lean_inc(v_value_41_);
lean_inc(v_key_40_);
lean_dec(v_x_39_);
v___x_44_ = lean_box(0);
v_isShared_45_ = v_isSharedCheck_68_;
goto v_resetjp_43_;
}
v_resetjp_43_:
{
lean_object* v___x_46_; uint64_t v___y_48_; 
v___x_46_ = lean_array_get_size(v_x_38_);
if (lean_obj_tag(v_key_40_) == 0)
{
uint64_t v___x_66_; 
v___x_66_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
v___y_48_ = v___x_66_;
goto v___jp_47_;
}
else
{
uint64_t v_hash_67_; 
v_hash_67_ = lean_ctor_get_uint64(v_key_40_, sizeof(void*)*2);
v___y_48_ = v_hash_67_;
goto v___jp_47_;
}
v___jp_47_:
{
uint64_t v___x_49_; uint64_t v___x_50_; uint64_t v_fold_51_; uint64_t v___x_52_; uint64_t v___x_53_; uint64_t v___x_54_; size_t v___x_55_; size_t v___x_56_; size_t v___x_57_; size_t v___x_58_; size_t v___x_59_; lean_object* v___x_60_; lean_object* v___x_62_; 
v___x_49_ = 32ULL;
v___x_50_ = lean_uint64_shift_right(v___y_48_, v___x_49_);
v_fold_51_ = lean_uint64_xor(v___y_48_, v___x_50_);
v___x_52_ = 16ULL;
v___x_53_ = lean_uint64_shift_right(v_fold_51_, v___x_52_);
v___x_54_ = lean_uint64_xor(v_fold_51_, v___x_53_);
v___x_55_ = lean_uint64_to_usize(v___x_54_);
v___x_56_ = lean_usize_of_nat(v___x_46_);
v___x_57_ = ((size_t)1ULL);
v___x_58_ = lean_usize_sub(v___x_56_, v___x_57_);
v___x_59_ = lean_usize_land(v___x_55_, v___x_58_);
v___x_60_ = lean_array_uget_borrowed(v_x_38_, v___x_59_);
lean_inc(v___x_60_);
if (v_isShared_45_ == 0)
{
lean_ctor_set(v___x_44_, 2, v___x_60_);
v___x_62_ = v___x_44_;
goto v_reusejp_61_;
}
else
{
lean_object* v_reuseFailAlloc_65_; 
v_reuseFailAlloc_65_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_65_, 0, v_key_40_);
lean_ctor_set(v_reuseFailAlloc_65_, 1, v_value_41_);
lean_ctor_set(v_reuseFailAlloc_65_, 2, v___x_60_);
v___x_62_ = v_reuseFailAlloc_65_;
goto v_reusejp_61_;
}
v_reusejp_61_:
{
lean_object* v___x_63_; 
v___x_63_ = lean_array_uset(v_x_38_, v___x_59_, v___x_62_);
v_x_38_ = v___x_63_;
v_x_39_ = v_tail_42_;
goto _start;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(lean_object* v_i_69_, lean_object* v_source_70_, lean_object* v_target_71_){
_start:
{
lean_object* v___x_72_; uint8_t v___x_73_; 
v___x_72_ = lean_array_get_size(v_source_70_);
v___x_73_ = lean_nat_dec_lt(v_i_69_, v___x_72_);
if (v___x_73_ == 0)
{
lean_dec_ref(v_source_70_);
lean_dec(v_i_69_);
return v_target_71_;
}
else
{
lean_object* v_es_74_; lean_object* v___x_75_; lean_object* v_source_76_; lean_object* v_target_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_es_74_ = lean_array_fget(v_source_70_, v_i_69_);
v___x_75_ = lean_box(0);
v_source_76_ = lean_array_fset(v_source_70_, v_i_69_, v___x_75_);
v_target_77_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_target_71_, v_es_74_);
v___x_78_ = lean_unsigned_to_nat(1u);
v___x_79_ = lean_nat_add(v_i_69_, v___x_78_);
lean_dec(v_i_69_);
v_i_69_ = v___x_79_;
v_source_70_ = v_source_76_;
v_target_71_ = v_target_77_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1___redArg(lean_object* v_data_81_){
_start:
{
lean_object* v___x_82_; lean_object* v___x_83_; lean_object* v_nbuckets_84_; lean_object* v___x_85_; lean_object* v___x_86_; lean_object* v___x_87_; lean_object* v___x_88_; 
v___x_82_ = lean_array_get_size(v_data_81_);
v___x_83_ = lean_unsigned_to_nat(2u);
v_nbuckets_84_ = lean_nat_mul(v___x_82_, v___x_83_);
v___x_85_ = lean_unsigned_to_nat(0u);
v___x_86_ = lean_box(0);
v___x_87_ = lean_mk_array(v_nbuckets_84_, v___x_86_);
v___x_88_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v___x_85_, v_data_81_, v___x_87_);
return v___x_88_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(lean_object* v_a_89_, lean_object* v_x_90_){
_start:
{
if (lean_obj_tag(v_x_90_) == 0)
{
uint8_t v___x_91_; 
v___x_91_ = 0;
return v___x_91_;
}
else
{
lean_object* v_key_92_; lean_object* v_tail_93_; uint8_t v___x_94_; 
v_key_92_ = lean_ctor_get(v_x_90_, 0);
v_tail_93_ = lean_ctor_get(v_x_90_, 2);
v___x_94_ = lean_name_eq(v_key_92_, v_a_89_);
if (v___x_94_ == 0)
{
v_x_90_ = v_tail_93_;
goto _start;
}
else
{
return v___x_94_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg___boxed(lean_object* v_a_96_, lean_object* v_x_97_){
_start:
{
uint8_t v_res_98_; lean_object* v_r_99_; 
v_res_98_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_96_, v_x_97_);
lean_dec(v_x_97_);
lean_dec(v_a_96_);
v_r_99_ = lean_box(v_res_98_);
return v_r_99_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0___redArg(lean_object* v_m_100_, lean_object* v_a_101_, lean_object* v_b_102_){
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
v___x_148_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
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
v___x_123_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_101_, v_bkt_122_);
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
v_val_134_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1___redArg(v_buckets_x27_127_);
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
v___x_143_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_101_, v_b_102_, v_bkt_122_);
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
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn___lam__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(lean_object* v_map_151_, lean_object* v_entry_152_){
_start:
{
lean_object* v_name_153_; lean_object* v_variant_154_; lean_object* v___x_155_; 
v_name_153_ = lean_ctor_get(v_entry_152_, 0);
lean_inc(v_name_153_);
v_variant_154_ = lean_ctor_get(v_entry_152_, 1);
lean_inc_ref(v_variant_154_);
lean_dec_ref(v_entry_152_);
v___x_155_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0___redArg(v_map_151_, v_name_153_, v_variant_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(lean_object* v___y_156_){
_start:
{
lean_inc_ref(v___y_156_);
return v___y_156_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object* v___y_157_){
_start:
{
lean_object* v_res_158_; 
v_res_158_ = l_Lean_Meta_Sym_Simp_initFn___lam__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(v___y_157_);
lean_dec_ref(v___y_157_);
return v_res_158_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_165_ = lean_box(0);
v___x_166_ = lean_unsigned_to_nat(16u);
v___x_167_ = lean_mk_array(v___x_166_, v___x_165_);
return v___x_167_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_, &l_Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once, _init_l_Lean_Meta_Sym_Simp_initFn___closed__5_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_);
v___x_169_ = lean_unsigned_to_nat(0u);
v___x_170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_170_, 0, v___x_169_);
lean_ctor_set(v___x_170_, 1, v___x_168_);
return v___x_170_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(void){
_start:
{
lean_object* v___f_171_; lean_object* v___f_172_; lean_object* v___x_173_; lean_object* v___f_174_; lean_object* v___x_175_; lean_object* v___x_176_; 
v___f_171_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_initFn___closed__0_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_));
v___f_172_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_initFn___closed__2_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_));
v___x_173_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_, &l_Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once, _init_l_Lean_Meta_Sym_Simp_initFn___closed__6_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_);
v___f_174_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_initFn___closed__1_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_));
v___x_175_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_initFn___closed__4_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_));
v___x_176_ = lean_alloc_ctor(0, 5, 0);
lean_ctor_set(v___x_176_, 0, v___x_175_);
lean_ctor_set(v___x_176_, 1, v___f_174_);
lean_ctor_set(v___x_176_, 2, v___x_173_);
lean_ctor_set(v___x_176_, 3, v___f_172_);
lean_ctor_set(v___x_176_, 4, v___f_171_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_(){
_start:
{
lean_object* v___x_178_; lean_object* v___x_179_; 
v___x_178_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_, &l_Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__once, _init_l_Lean_Meta_Sym_Simp_initFn___closed__7_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_);
v___x_179_ = l_Lean_registerSimpleScopedEnvExtension___redArg(v___x_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2____boxed(lean_object* v_a_180_){
_start:
{
lean_object* v_res_181_; 
v_res_181_ = l_Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_();
return v_res_181_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0(lean_object* v_00_u03b2_182_, lean_object* v_m_183_, lean_object* v_a_184_, lean_object* v_b_185_){
_start:
{
lean_object* v___x_186_; 
v___x_186_ = l_Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0___redArg(v_m_183_, v_a_184_, v_b_185_);
return v___x_186_;
}
}
LEAN_EXPORT uint8_t l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0(lean_object* v_00_u03b2_187_, lean_object* v_a_188_, lean_object* v_x_189_){
_start:
{
uint8_t v___x_190_; 
v___x_190_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___redArg(v_a_188_, v_x_189_);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0___boxed(lean_object* v_00_u03b2_191_, lean_object* v_a_192_, lean_object* v_x_193_){
_start:
{
uint8_t v_res_194_; lean_object* v_r_195_; 
v_res_194_ = l_Std_DHashMap_Internal_AssocList_contains___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__0(v_00_u03b2_191_, v_a_192_, v_x_193_);
lean_dec(v_x_193_);
lean_dec(v_a_192_);
v_r_195_ = lean_box(v_res_194_);
return v_r_195_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1(lean_object* v_00_u03b2_196_, lean_object* v_data_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = l_Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1___redArg(v_data_197_);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2(lean_object* v_00_u03b2_199_, lean_object* v_a_200_, lean_object* v_b_201_, lean_object* v_x_202_){
_start:
{
lean_object* v___x_203_; 
v___x_203_ = l_Std_DHashMap_Internal_AssocList_replace___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__2___redArg(v_a_200_, v_b_201_, v_x_202_);
return v___x_203_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2(lean_object* v_00_u03b2_204_, lean_object* v_i_205_, lean_object* v_source_206_, lean_object* v_target_207_){
_start:
{
lean_object* v___x_208_; 
v___x_208_ = l___private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2___redArg(v_i_205_, v_source_206_, v_target_207_);
return v___x_208_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3(lean_object* v_00_u03b2_209_, lean_object* v_x_210_, lean_object* v_x_211_){
_start:
{
lean_object* v___x_212_; 
v___x_212_ = l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg(v_x_210_, v_x_211_);
return v___x_212_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(lean_object* v_a_213_, lean_object* v_x_214_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg___boxed(lean_object* v_a_222_, lean_object* v_x_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(v_a_222_, v_x_223_);
lean_dec(v_x_223_);
lean_dec(v_a_222_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(lean_object* v_m_225_, lean_object* v_a_226_){
_start:
{
lean_object* v_buckets_227_; lean_object* v___x_228_; uint64_t v___y_230_; 
v_buckets_227_ = lean_ctor_get(v_m_225_, 1);
v___x_228_ = lean_array_get_size(v_buckets_227_);
if (lean_obj_tag(v_a_226_) == 0)
{
uint64_t v___x_244_; 
v___x_244_ = lean_uint64_once(&l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0, &l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0_once, _init_l_Std_DHashMap_Internal_AssocList_foldlM___at___00__private_Std_Data_DHashMap_Internal_Defs_0__Std_DHashMap_Internal_Raw_u2080_expand_go___at___00Std_DHashMap_Internal_Raw_u2080_expand___at___00Std_DHashMap_Internal_Raw_u2080_insert___at___00Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2__spec__0_spec__1_spec__2_spec__3___redArg___closed__0);
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
v___x_243_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(v_a_226_, v___x_242_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg___boxed(lean_object* v_m_246_, lean_object* v_a_247_){
_start:
{
lean_object* v_res_248_; 
v_res_248_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(v_m_246_, v_a_247_);
lean_dec(v_a_247_);
lean_dec_ref(v_m_246_);
return v_res_248_;
}
}
static lean_object* _init_l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2(void){
_start:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; 
v___x_251_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__1));
v___x_252_ = ((lean_object*)(l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__0));
v___x_253_ = l_Std_HashMap_instInhabited(lean_box(0), lean_box(0), v___x_252_, v___x_251_);
return v___x_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(lean_object* v_env_254_, lean_object* v_name_255_){
_start:
{
lean_object* v___x_256_; lean_object* v_ext_257_; lean_object* v_toEnvExtension_258_; lean_object* v_asyncMode_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___x_262_; 
v___x_256_ = l_Lean_Meta_Sym_Simp_symSimpVariantExtension;
v_ext_257_ = lean_ctor_get(v___x_256_, 1);
v_toEnvExtension_258_ = lean_ctor_get(v_ext_257_, 0);
v_asyncMode_259_ = lean_ctor_get(v_toEnvExtension_258_, 2);
v___x_260_ = lean_obj_once(&l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2, &l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2_once, _init_l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___closed__2);
v___x_261_ = l_Lean_ScopedEnvExtension_getState___redArg(v___x_260_, v___x_256_, v_env_254_, v_asyncMode_259_);
v___x_262_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(v___x_261_, v_name_255_);
lean_dec(v___x_261_);
return v___x_262_;
}
}
LEAN_EXPORT lean_object* l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f___boxed(lean_object* v_env_263_, lean_object* v_name_264_){
_start:
{
lean_object* v_res_265_; 
v_res_265_ = l_Lean_Meta_Sym_Simp_getSymSimpVariant_x3f(v_env_263_, v_name_264_);
lean_dec(v_name_264_);
return v_res_265_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0(lean_object* v_00_u03b2_266_, lean_object* v_m_267_, lean_object* v_a_268_){
_start:
{
lean_object* v___x_269_; 
v___x_269_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___redArg(v_m_267_, v_a_268_);
return v___x_269_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0___boxed(lean_object* v_00_u03b2_270_, lean_object* v_m_271_, lean_object* v_a_272_){
_start:
{
lean_object* v_res_273_; 
v_res_273_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0(v_00_u03b2_270_, v_m_271_, v_a_272_);
lean_dec(v_a_272_);
lean_dec_ref(v_m_271_);
return v_res_273_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0(lean_object* v_00_u03b2_274_, lean_object* v_a_275_, lean_object* v_x_276_){
_start:
{
lean_object* v___x_277_; 
v___x_277_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___redArg(v_a_275_, v_x_276_);
return v___x_277_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0___boxed(lean_object* v_00_u03b2_278_, lean_object* v_a_279_, lean_object* v_x_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Meta_Sym_Simp_getSymSimpVariant_x3f_spec__0_spec__0(v_00_u03b2_278_, v_a_279_, v_x_280_);
lean_dec(v_x_280_);
lean_dec(v_a_279_);
return v_res_281_;
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
l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default = _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant_default);
l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant = _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariant);
l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default = _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry_default);
l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry = _init_l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry();
lean_mark_persistent(l_Lean_Meta_Sym_Simp_instInhabitedSymSimpVariantEntry);
res = l_Lean_Meta_Sym_Simp_initFn_00___x40_Lean_Meta_Sym_Simp_Variant_3569157790____hygCtx___hyg_2_();
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
