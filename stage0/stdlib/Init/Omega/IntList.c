// Lean compiler output
// Module: Init.Omega.IntList
// Imports: public import Init.Data.Int.DivMod.Bootstrap public import Init.Data.Nat.Gcd import Init.Data.Int.Lemmas import Init.Data.Int.Order import Init.Data.Nat.Dvd import Init.PropLemmas import Init.RCases
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
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_List_zipWithAll___redArg(lean_object*, lean_object*, lean_object*);
lean_object* l_Int_bmod(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
lean_object* l_List_find_x3f___redArg(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWithAll_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWith_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWith_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_Lean_Omega_IntList_get___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_Lean_Omega_IntList_get___closed__0;
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_get(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_get___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_set(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_set___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_Lean_Omega_IntList_leading___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading___lam__0___boxed(lean_object*);
static const lean_closure_object l_Lean_Omega_IntList_leading___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_leading___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_IntList_leading___closed__0 = (const lean_object*)&l_Lean_Omega_IntList_leading___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_IntList_add___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_add___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_IntList_add___closed__0 = (const lean_object*)&l_Lean_Omega_IntList_add___closed__0_value;
static const lean_closure_object l_Lean_Omega_IntList_add___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_add___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Omega_IntList_add___closed__0_value)} };
static const lean_object* l_Lean_Omega_IntList_add___closed__1 = (const lean_object*)&l_Lean_Omega_IntList_add___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_IntList_instAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_IntList_instAdd___closed__0 = (const lean_object*)&l_Lean_Omega_IntList_instAdd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_IntList_instAdd = (const lean_object*)&l_Lean_Omega_IntList_instAdd___closed__0_value;
LEAN_EXPORT lean_object* l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mul___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_IntList_instMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_mul___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_IntList_instMul___closed__0 = (const lean_object*)&l_Lean_Omega_IntList_instMul___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_IntList_instMul = (const lean_object*)&l_Lean_Omega_IntList_instMul___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_neg(lean_object*);
static const lean_closure_object l_Lean_Omega_IntList_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_neg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_IntList_instNeg___closed__0 = (const lean_object*)&l_Lean_Omega_IntList_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_IntList_instNeg = (const lean_object*)&l_Lean_Omega_IntList_instNeg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sub___lam__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sub___lam__1___boxed(lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_IntList_sub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_sub___lam__1___boxed, .m_arity = 3, .m_num_fixed = 1, .m_objs = {((lean_object*)&l_Lean_Omega_IntList_add___closed__0_value)} };
static const lean_object* l_Lean_Omega_IntList_sub___closed__0 = (const lean_object*)&l_Lean_Omega_IntList_sub___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sub(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_IntList_instSub___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_sub, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_IntList_instSub___closed__0 = (const lean_object*)&l_Lean_Omega_IntList_instSub___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_IntList_instSub = (const lean_object*)&l_Lean_Omega_IntList_instSub___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_IntList_instHMulInt___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_instHMulInt___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_IntList_instHMulInt___closed__0 = (const lean_object*)&l_Lean_Omega_IntList_instHMulInt___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_IntList_instHMulInt = (const lean_object*)&l_Lean_Omega_IntList_instHMulInt___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sum(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sum___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcd(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod__dot__sub__dot__bmod(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWithAll_match__1_splitter___redArg(lean_object* v_x_1_, lean_object* v_x_2_, lean_object* v_h__1_3_, lean_object* v_h__2_4_){
_start:
{
if (lean_obj_tag(v_x_1_) == 0)
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_5_; lean_object* v___x_6_; 
lean_dec(v_h__2_4_);
v___x_5_ = lean_box(0);
v___x_6_ = lean_apply_1(v_h__1_3_, v___x_5_);
return v___x_6_;
}
else
{
lean_object* v___x_7_; 
lean_dec(v_h__1_3_);
v___x_7_ = lean_apply_3(v_h__2_4_, v_x_1_, v_x_2_, lean_box(0));
return v___x_7_;
}
}
else
{
lean_object* v___x_8_; 
lean_dec(v_h__1_3_);
v___x_8_ = lean_apply_3(v_h__2_4_, v_x_1_, v_x_2_, lean_box(0));
return v___x_8_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWithAll_match__1_splitter(lean_object* v_00_u03b1_9_, lean_object* v_00_u03b2_10_, lean_object* v_motive_11_, lean_object* v_x_12_, lean_object* v_x_13_, lean_object* v_h__1_14_, lean_object* v_h__2_15_){
_start:
{
if (lean_obj_tag(v_x_12_) == 0)
{
if (lean_obj_tag(v_x_13_) == 0)
{
lean_object* v___x_16_; lean_object* v___x_17_; 
lean_dec(v_h__2_15_);
v___x_16_ = lean_box(0);
v___x_17_ = lean_apply_1(v_h__1_14_, v___x_16_);
return v___x_17_;
}
else
{
lean_object* v___x_18_; 
lean_dec(v_h__1_14_);
v___x_18_ = lean_apply_3(v_h__2_15_, v_x_12_, v_x_13_, lean_box(0));
return v___x_18_;
}
}
else
{
lean_object* v___x_19_; 
lean_dec(v_h__1_14_);
v___x_19_ = lean_apply_3(v_h__2_15_, v_x_12_, v_x_13_, lean_box(0));
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWith_match__1_splitter___redArg(lean_object* v_x_20_, lean_object* v_x_21_, lean_object* v_h__1_22_, lean_object* v_h__2_23_){
_start:
{
if (lean_obj_tag(v_x_20_) == 1)
{
if (lean_obj_tag(v_x_21_) == 1)
{
lean_object* v_val_24_; lean_object* v_val_25_; lean_object* v___x_26_; 
lean_dec(v_h__2_23_);
v_val_24_ = lean_ctor_get(v_x_20_, 0);
lean_inc(v_val_24_);
lean_dec_ref(v_x_20_);
v_val_25_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_val_25_);
lean_dec_ref(v_x_21_);
v___x_26_ = lean_apply_2(v_h__1_22_, v_val_24_, v_val_25_);
return v___x_26_;
}
else
{
lean_object* v___x_27_; 
lean_dec(v_h__1_22_);
v___x_27_ = lean_apply_3(v_h__2_23_, v_x_20_, v_x_21_, lean_box(0));
return v___x_27_;
}
}
else
{
lean_object* v___x_28_; 
lean_dec(v_h__1_22_);
v___x_28_ = lean_apply_3(v_h__2_23_, v_x_20_, v_x_21_, lean_box(0));
return v___x_28_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__List_getElem_x3f__zipWith_match__1_splitter(lean_object* v_00_u03b1_29_, lean_object* v_00_u03b2_30_, lean_object* v_motive_31_, lean_object* v_x_32_, lean_object* v_x_33_, lean_object* v_h__1_34_, lean_object* v_h__2_35_){
_start:
{
if (lean_obj_tag(v_x_32_) == 1)
{
if (lean_obj_tag(v_x_33_) == 1)
{
lean_object* v_val_36_; lean_object* v_val_37_; lean_object* v___x_38_; 
lean_dec(v_h__2_35_);
v_val_36_ = lean_ctor_get(v_x_32_, 0);
lean_inc(v_val_36_);
lean_dec_ref(v_x_32_);
v_val_37_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_val_37_);
lean_dec_ref(v_x_33_);
v___x_38_ = lean_apply_2(v_h__1_34_, v_val_36_, v_val_37_);
return v___x_38_;
}
else
{
lean_object* v___x_39_; 
lean_dec(v_h__1_34_);
v___x_39_ = lean_apply_3(v_h__2_35_, v_x_32_, v_x_33_, lean_box(0));
return v___x_39_;
}
}
else
{
lean_object* v___x_40_; 
lean_dec(v_h__1_34_);
v___x_40_ = lean_apply_3(v_h__2_35_, v_x_32_, v_x_33_, lean_box(0));
return v___x_40_;
}
}
}
static lean_object* _init_l_Lean_Omega_IntList_get___closed__0(void){
_start:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
v___x_41_ = lean_unsigned_to_nat(0u);
v___x_42_ = lean_nat_to_int(v___x_41_);
return v___x_42_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_get(lean_object* v_xs_43_, lean_object* v_i_44_){
_start:
{
lean_object* v___x_45_; 
v___x_45_ = l_List_get_x3fInternal___redArg(v_xs_43_, v_i_44_);
if (lean_obj_tag(v___x_45_) == 0)
{
lean_object* v___x_46_; 
v___x_46_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
return v___x_46_;
}
else
{
lean_object* v_val_47_; 
v_val_47_ = lean_ctor_get(v___x_45_, 0);
lean_inc(v_val_47_);
lean_dec_ref(v___x_45_);
return v_val_47_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_get___boxed(lean_object* v_xs_48_, lean_object* v_i_49_){
_start:
{
lean_object* v_res_50_; 
v_res_50_ = l_Lean_Omega_IntList_get(v_xs_48_, v_i_49_);
lean_dec(v_xs_48_);
return v_res_50_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_set(lean_object* v_xs_51_, lean_object* v_i_52_, lean_object* v_y_53_){
_start:
{
if (lean_obj_tag(v_xs_51_) == 0)
{
lean_object* v_zero_54_; uint8_t v_isZero_55_; 
v_zero_54_ = lean_unsigned_to_nat(0u);
v_isZero_55_ = lean_nat_dec_eq(v_i_52_, v_zero_54_);
if (v_isZero_55_ == 1)
{
lean_object* v___x_56_; 
v___x_56_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_56_, 0, v_y_53_);
lean_ctor_set(v___x_56_, 1, v_xs_51_);
return v___x_56_;
}
else
{
lean_object* v_one_57_; lean_object* v_n_58_; lean_object* v___x_59_; lean_object* v___x_60_; lean_object* v___x_61_; 
v_one_57_ = lean_unsigned_to_nat(1u);
v_n_58_ = lean_nat_sub(v_i_52_, v_one_57_);
v___x_59_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_60_ = l_Lean_Omega_IntList_set(v_xs_51_, v_n_58_, v_y_53_);
lean_dec(v_n_58_);
v___x_61_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_61_, 0, v___x_59_);
lean_ctor_set(v___x_61_, 1, v___x_60_);
return v___x_61_;
}
}
else
{
lean_object* v_head_62_; lean_object* v_tail_63_; lean_object* v___x_65_; uint8_t v_isShared_66_; uint8_t v_isSharedCheck_78_; 
v_head_62_ = lean_ctor_get(v_xs_51_, 0);
v_tail_63_ = lean_ctor_get(v_xs_51_, 1);
v_isSharedCheck_78_ = !lean_is_exclusive(v_xs_51_);
if (v_isSharedCheck_78_ == 0)
{
v___x_65_ = v_xs_51_;
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
else
{
lean_inc(v_tail_63_);
lean_inc(v_head_62_);
lean_dec(v_xs_51_);
v___x_65_ = lean_box(0);
v_isShared_66_ = v_isSharedCheck_78_;
goto v_resetjp_64_;
}
v_resetjp_64_:
{
lean_object* v_zero_67_; uint8_t v_isZero_68_; 
v_zero_67_ = lean_unsigned_to_nat(0u);
v_isZero_68_ = lean_nat_dec_eq(v_i_52_, v_zero_67_);
if (v_isZero_68_ == 1)
{
lean_object* v___x_70_; 
lean_dec(v_head_62_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 0, v_y_53_);
v___x_70_ = v___x_65_;
goto v_reusejp_69_;
}
else
{
lean_object* v_reuseFailAlloc_71_; 
v_reuseFailAlloc_71_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_71_, 0, v_y_53_);
lean_ctor_set(v_reuseFailAlloc_71_, 1, v_tail_63_);
v___x_70_ = v_reuseFailAlloc_71_;
goto v_reusejp_69_;
}
v_reusejp_69_:
{
return v___x_70_;
}
}
else
{
lean_object* v_one_72_; lean_object* v_n_73_; lean_object* v___x_74_; lean_object* v___x_76_; 
v_one_72_ = lean_unsigned_to_nat(1u);
v_n_73_ = lean_nat_sub(v_i_52_, v_one_72_);
v___x_74_ = l_Lean_Omega_IntList_set(v_tail_63_, v_n_73_, v_y_53_);
lean_dec(v_n_73_);
if (v_isShared_66_ == 0)
{
lean_ctor_set(v___x_65_, 1, v___x_74_);
v___x_76_ = v___x_65_;
goto v_reusejp_75_;
}
else
{
lean_object* v_reuseFailAlloc_77_; 
v_reuseFailAlloc_77_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_77_, 0, v_head_62_);
lean_ctor_set(v_reuseFailAlloc_77_, 1, v___x_74_);
v___x_76_ = v_reuseFailAlloc_77_;
goto v_reusejp_75_;
}
v_reusejp_75_:
{
return v___x_76_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_set___boxed(lean_object* v_xs_79_, lean_object* v_i_80_, lean_object* v_y_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Lean_Omega_IntList_set(v_xs_79_, v_i_80_, v_y_81_);
lean_dec(v_i_80_);
return v_res_82_;
}
}
LEAN_EXPORT uint8_t l_Lean_Omega_IntList_leading___lam__0(lean_object* v_x_83_){
_start:
{
lean_object* v___x_84_; uint8_t v___x_85_; 
v___x_84_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_85_ = lean_int_dec_eq(v_x_83_, v___x_84_);
if (v___x_85_ == 0)
{
uint8_t v___x_86_; 
v___x_86_ = 1;
return v___x_86_;
}
else
{
uint8_t v___x_87_; 
v___x_87_ = 0;
return v___x_87_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading___lam__0___boxed(lean_object* v_x_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_Lean_Omega_IntList_leading___lam__0(v_x_88_);
lean_dec(v_x_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading(lean_object* v_xs_92_){
_start:
{
lean_object* v___f_93_; lean_object* v___x_94_; 
v___f_93_ = ((lean_object*)(l_Lean_Omega_IntList_leading___closed__0));
v___x_94_ = l_List_find_x3f___redArg(v___f_93_, v_xs_92_);
if (lean_obj_tag(v___x_94_) == 0)
{
lean_object* v___x_95_; 
v___x_95_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
return v___x_95_;
}
else
{
lean_object* v_val_96_; 
v_val_96_ = lean_ctor_get(v___x_94_, 0);
lean_inc(v_val_96_);
lean_dec_ref(v___x_94_);
return v_val_96_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add___lam__0(lean_object* v_00___97_){
_start:
{
lean_object* v___x_98_; 
v___x_98_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
return v___x_98_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add___lam__1(lean_object* v___f_99_, lean_object* v_x_100_, lean_object* v_y_101_){
_start:
{
lean_object* v___y_103_; 
if (lean_obj_tag(v_x_100_) == 0)
{
lean_object* v___x_109_; lean_object* v___x_110_; 
v___x_109_ = lean_box(0);
lean_inc_ref(v___f_99_);
v___x_110_ = lean_apply_1(v___f_99_, v___x_109_);
v___y_103_ = v___x_110_;
goto v___jp_102_;
}
else
{
lean_object* v_val_111_; 
v_val_111_ = lean_ctor_get(v_x_100_, 0);
lean_inc(v_val_111_);
lean_dec_ref(v_x_100_);
v___y_103_ = v_val_111_;
goto v___jp_102_;
}
v___jp_102_:
{
if (lean_obj_tag(v_y_101_) == 0)
{
lean_object* v___x_104_; lean_object* v___x_105_; lean_object* v___x_106_; 
v___x_104_ = lean_box(0);
v___x_105_ = lean_apply_1(v___f_99_, v___x_104_);
v___x_106_ = lean_int_add(v___y_103_, v___x_105_);
lean_dec(v___x_105_);
lean_dec(v___y_103_);
return v___x_106_;
}
else
{
lean_object* v_val_107_; lean_object* v___x_108_; 
lean_dec_ref(v___f_99_);
v_val_107_ = lean_ctor_get(v_y_101_, 0);
v___x_108_ = lean_int_add(v___y_103_, v_val_107_);
lean_dec(v___y_103_);
return v___x_108_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add___lam__1___boxed(lean_object* v___f_112_, lean_object* v_x_113_, lean_object* v_y_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_Lean_Omega_IntList_add___lam__1(v___f_112_, v_x_113_, v_y_114_);
lean_dec(v_y_114_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add(lean_object* v_xs_119_, lean_object* v_ys_120_){
_start:
{
lean_object* v___f_121_; lean_object* v___x_122_; 
v___f_121_ = ((lean_object*)(l_Lean_Omega_IntList_add___closed__1));
v___x_122_ = l_List_zipWithAll___redArg(v___f_121_, v_xs_119_, v_ys_120_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(lean_object* v_x_125_, lean_object* v_x_126_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
lean_dec(v_x_126_);
return v_x_125_;
}
else
{
if (lean_obj_tag(v_x_126_) == 0)
{
return v_x_126_;
}
else
{
lean_object* v_head_127_; lean_object* v_tail_128_; lean_object* v_head_129_; lean_object* v_tail_130_; lean_object* v___x_132_; uint8_t v_isShared_133_; uint8_t v_isSharedCheck_139_; 
v_head_127_ = lean_ctor_get(v_x_125_, 0);
v_tail_128_ = lean_ctor_get(v_x_125_, 1);
v_head_129_ = lean_ctor_get(v_x_126_, 0);
v_tail_130_ = lean_ctor_get(v_x_126_, 1);
v_isSharedCheck_139_ = !lean_is_exclusive(v_x_126_);
if (v_isSharedCheck_139_ == 0)
{
v___x_132_ = v_x_126_;
v_isShared_133_ = v_isSharedCheck_139_;
goto v_resetjp_131_;
}
else
{
lean_inc(v_tail_130_);
lean_inc(v_head_129_);
lean_dec(v_x_126_);
v___x_132_ = lean_box(0);
v_isShared_133_ = v_isSharedCheck_139_;
goto v_resetjp_131_;
}
v_resetjp_131_:
{
lean_object* v___x_134_; lean_object* v___x_135_; lean_object* v___x_137_; 
v___x_134_ = lean_int_mul(v_head_127_, v_head_129_);
lean_dec(v_head_129_);
v___x_135_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_tail_128_, v_tail_130_);
if (v_isShared_133_ == 0)
{
lean_ctor_set(v___x_132_, 1, v___x_135_);
lean_ctor_set(v___x_132_, 0, v___x_134_);
v___x_137_ = v___x_132_;
goto v_reusejp_136_;
}
else
{
lean_object* v_reuseFailAlloc_138_; 
v_reuseFailAlloc_138_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_138_, 0, v___x_134_);
lean_ctor_set(v_reuseFailAlloc_138_, 1, v___x_135_);
v___x_137_ = v_reuseFailAlloc_138_;
goto v_reusejp_136_;
}
v_reusejp_136_:
{
return v___x_137_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0___boxed(lean_object* v_x_140_, lean_object* v_x_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_x_140_, v_x_141_);
lean_dec(v_x_140_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mul(lean_object* v_xs_143_, lean_object* v_ys_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_xs_143_, v_ys_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mul___boxed(lean_object* v_xs_146_, lean_object* v_ys_147_){
_start:
{
lean_object* v_res_148_; 
v_res_148_ = l_Lean_Omega_IntList_mul(v_xs_146_, v_ys_147_);
lean_dec(v_xs_146_);
return v_res_148_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(lean_object* v_a_151_, lean_object* v_a_152_){
_start:
{
if (lean_obj_tag(v_a_151_) == 0)
{
lean_object* v___x_153_; 
v___x_153_ = l_List_reverse___redArg(v_a_152_);
return v___x_153_;
}
else
{
lean_object* v_head_154_; lean_object* v_tail_155_; lean_object* v___x_157_; uint8_t v_isShared_158_; uint8_t v_isSharedCheck_164_; 
v_head_154_ = lean_ctor_get(v_a_151_, 0);
v_tail_155_ = lean_ctor_get(v_a_151_, 1);
v_isSharedCheck_164_ = !lean_is_exclusive(v_a_151_);
if (v_isSharedCheck_164_ == 0)
{
v___x_157_ = v_a_151_;
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
else
{
lean_inc(v_tail_155_);
lean_inc(v_head_154_);
lean_dec(v_a_151_);
v___x_157_ = lean_box(0);
v_isShared_158_ = v_isSharedCheck_164_;
goto v_resetjp_156_;
}
v_resetjp_156_:
{
lean_object* v___x_159_; lean_object* v___x_161_; 
v___x_159_ = lean_int_neg(v_head_154_);
lean_dec(v_head_154_);
if (v_isShared_158_ == 0)
{
lean_ctor_set(v___x_157_, 1, v_a_152_);
lean_ctor_set(v___x_157_, 0, v___x_159_);
v___x_161_ = v___x_157_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_163_; 
v_reuseFailAlloc_163_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_163_, 0, v___x_159_);
lean_ctor_set(v_reuseFailAlloc_163_, 1, v_a_152_);
v___x_161_ = v_reuseFailAlloc_163_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
v_a_151_ = v_tail_155_;
v_a_152_ = v___x_161_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_neg(lean_object* v_xs_165_){
_start:
{
lean_object* v___x_166_; lean_object* v___x_167_; 
v___x_166_ = lean_box(0);
v___x_167_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(v_xs_165_, v___x_166_);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sub___lam__1(lean_object* v___f_170_, lean_object* v_x_171_, lean_object* v_y_172_){
_start:
{
lean_object* v___y_174_; 
if (lean_obj_tag(v_x_171_) == 0)
{
lean_object* v___x_180_; lean_object* v___x_181_; 
v___x_180_ = lean_box(0);
lean_inc_ref(v___f_170_);
v___x_181_ = lean_apply_1(v___f_170_, v___x_180_);
v___y_174_ = v___x_181_;
goto v___jp_173_;
}
else
{
lean_object* v_val_182_; 
v_val_182_ = lean_ctor_get(v_x_171_, 0);
lean_inc(v_val_182_);
lean_dec_ref(v_x_171_);
v___y_174_ = v_val_182_;
goto v___jp_173_;
}
v___jp_173_:
{
if (lean_obj_tag(v_y_172_) == 0)
{
lean_object* v___x_175_; lean_object* v___x_176_; lean_object* v___x_177_; 
v___x_175_ = lean_box(0);
v___x_176_ = lean_apply_1(v___f_170_, v___x_175_);
v___x_177_ = lean_int_sub(v___y_174_, v___x_176_);
lean_dec(v___x_176_);
lean_dec(v___y_174_);
return v___x_177_;
}
else
{
lean_object* v_val_178_; lean_object* v___x_179_; 
lean_dec_ref(v___f_170_);
v_val_178_ = lean_ctor_get(v_y_172_, 0);
v___x_179_ = lean_int_sub(v___y_174_, v_val_178_);
lean_dec(v___y_174_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sub___lam__1___boxed(lean_object* v___f_183_, lean_object* v_x_184_, lean_object* v_y_185_){
_start:
{
lean_object* v_res_186_; 
v_res_186_ = l_Lean_Omega_IntList_sub___lam__1(v___f_183_, v_x_184_, v_y_185_);
lean_dec(v_y_185_);
return v_res_186_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sub(lean_object* v_xs_189_, lean_object* v_ys_190_){
_start:
{
lean_object* v___f_191_; lean_object* v___x_192_; 
v___f_191_ = ((lean_object*)(l_Lean_Omega_IntList_sub___closed__0));
v___x_192_ = l_List_zipWithAll___redArg(v___f_191_, v_xs_189_, v_ys_190_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(lean_object* v_i_195_, lean_object* v_a_196_, lean_object* v_a_197_){
_start:
{
if (lean_obj_tag(v_a_196_) == 0)
{
lean_object* v___x_198_; 
v___x_198_ = l_List_reverse___redArg(v_a_197_);
return v___x_198_;
}
else
{
lean_object* v_head_199_; lean_object* v_tail_200_; lean_object* v___x_202_; uint8_t v_isShared_203_; uint8_t v_isSharedCheck_209_; 
v_head_199_ = lean_ctor_get(v_a_196_, 0);
v_tail_200_ = lean_ctor_get(v_a_196_, 1);
v_isSharedCheck_209_ = !lean_is_exclusive(v_a_196_);
if (v_isSharedCheck_209_ == 0)
{
v___x_202_ = v_a_196_;
v_isShared_203_ = v_isSharedCheck_209_;
goto v_resetjp_201_;
}
else
{
lean_inc(v_tail_200_);
lean_inc(v_head_199_);
lean_dec(v_a_196_);
v___x_202_ = lean_box(0);
v_isShared_203_ = v_isSharedCheck_209_;
goto v_resetjp_201_;
}
v_resetjp_201_:
{
lean_object* v___x_204_; lean_object* v___x_206_; 
v___x_204_ = lean_int_mul(v_i_195_, v_head_199_);
lean_dec(v_head_199_);
if (v_isShared_203_ == 0)
{
lean_ctor_set(v___x_202_, 1, v_a_197_);
lean_ctor_set(v___x_202_, 0, v___x_204_);
v___x_206_ = v___x_202_;
goto v_reusejp_205_;
}
else
{
lean_object* v_reuseFailAlloc_208_; 
v_reuseFailAlloc_208_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_208_, 0, v___x_204_);
lean_ctor_set(v_reuseFailAlloc_208_, 1, v_a_197_);
v___x_206_ = v_reuseFailAlloc_208_;
goto v_reusejp_205_;
}
v_reusejp_205_:
{
v_a_196_ = v_tail_200_;
v_a_197_ = v___x_206_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0___boxed(lean_object* v_i_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_210_, v_a_211_, v_a_212_);
lean_dec(v_i_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul(lean_object* v_xs_214_, lean_object* v_i_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_box(0);
v___x_217_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_215_, v_xs_214_, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul___boxed(lean_object* v_xs_218_, lean_object* v_i_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_Lean_Omega_IntList_smul(v_xs_218_, v_i_219_);
lean_dec(v_i_219_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0(lean_object* v_i_221_, lean_object* v_xs_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l_Lean_Omega_IntList_smul(v_xs_222_, v_i_221_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0___boxed(lean_object* v_i_224_, lean_object* v_xs_225_){
_start:
{
lean_object* v_res_226_; 
v_res_226_ = l_Lean_Omega_IntList_instHMulInt___lam__0(v_i_224_, v_xs_225_);
lean_dec(v_i_224_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo___lam__1(lean_object* v_b_229_, lean_object* v_a_230_, lean_object* v___f_231_, lean_object* v_x_232_, lean_object* v_y_233_){
_start:
{
lean_object* v___y_235_; lean_object* v___y_236_; lean_object* v___y_240_; 
if (lean_obj_tag(v_x_232_) == 0)
{
lean_object* v___x_245_; lean_object* v___x_246_; 
v___x_245_ = lean_box(0);
lean_inc_ref(v___f_231_);
v___x_246_ = lean_apply_1(v___f_231_, v___x_245_);
v___y_240_ = v___x_246_;
goto v___jp_239_;
}
else
{
lean_object* v_val_247_; 
v_val_247_ = lean_ctor_get(v_x_232_, 0);
lean_inc(v_val_247_);
lean_dec_ref(v_x_232_);
v___y_240_ = v_val_247_;
goto v___jp_239_;
}
v___jp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; 
v___x_237_ = lean_int_mul(v_b_229_, v___y_236_);
lean_dec(v___y_236_);
v___x_238_ = lean_int_add(v___y_235_, v___x_237_);
lean_dec(v___x_237_);
lean_dec(v___y_235_);
return v___x_238_;
}
v___jp_239_:
{
lean_object* v___x_241_; 
v___x_241_ = lean_int_mul(v_a_230_, v___y_240_);
lean_dec(v___y_240_);
if (lean_obj_tag(v_y_233_) == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
v___x_242_ = lean_box(0);
v___x_243_ = lean_apply_1(v___f_231_, v___x_242_);
v___y_235_ = v___x_241_;
v___y_236_ = v___x_243_;
goto v___jp_234_;
}
else
{
lean_object* v_val_244_; 
lean_dec_ref(v___f_231_);
v_val_244_ = lean_ctor_get(v_y_233_, 0);
lean_inc(v_val_244_);
lean_dec_ref(v_y_233_);
v___y_235_ = v___x_241_;
v___y_236_ = v_val_244_;
goto v___jp_234_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo___lam__1___boxed(lean_object* v_b_248_, lean_object* v_a_249_, lean_object* v___f_250_, lean_object* v_x_251_, lean_object* v_y_252_){
_start:
{
lean_object* v_res_253_; 
v_res_253_ = l_Lean_Omega_IntList_combo___lam__1(v_b_248_, v_a_249_, v___f_250_, v_x_251_, v_y_252_);
lean_dec(v_a_249_);
lean_dec(v_b_248_);
return v_res_253_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo(lean_object* v_a_254_, lean_object* v_xs_255_, lean_object* v_b_256_, lean_object* v_ys_257_){
_start:
{
lean_object* v___f_258_; lean_object* v___f_259_; lean_object* v___x_260_; 
v___f_258_ = ((lean_object*)(l_Lean_Omega_IntList_add___closed__0));
v___f_259_ = lean_alloc_closure((void*)(l_Lean_Omega_IntList_combo___lam__1___boxed), 5, 3);
lean_closure_set(v___f_259_, 0, v_b_256_);
lean_closure_set(v___f_259_, 1, v_a_254_);
lean_closure_set(v___f_259_, 2, v___f_258_);
v___x_260_ = l_List_zipWithAll___redArg(v___f_259_, v_xs_255_, v_ys_257_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(lean_object* v_init_261_, lean_object* v_x_262_){
_start:
{
if (lean_obj_tag(v_x_262_) == 0)
{
lean_inc(v_init_261_);
return v_init_261_;
}
else
{
lean_object* v_head_263_; lean_object* v_tail_264_; lean_object* v___x_265_; lean_object* v___x_266_; 
v_head_263_ = lean_ctor_get(v_x_262_, 0);
v_tail_264_ = lean_ctor_get(v_x_262_, 1);
v___x_265_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v_init_261_, v_tail_264_);
v___x_266_ = lean_int_add(v_head_263_, v___x_265_);
lean_dec(v___x_265_);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0___boxed(lean_object* v_init_267_, lean_object* v_x_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v_init_267_, v_x_268_);
lean_dec(v_x_268_);
lean_dec(v_init_267_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sum(lean_object* v_xs_270_){
_start:
{
lean_object* v___x_271_; lean_object* v___x_272_; 
v___x_271_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_272_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v___x_271_, v_xs_270_);
return v___x_272_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sum___boxed(lean_object* v_xs_273_){
_start:
{
lean_object* v_res_274_; 
v_res_274_ = l_Lean_Omega_IntList_sum(v_xs_273_);
lean_dec(v_xs_273_);
return v_res_274_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot(lean_object* v_xs_275_, lean_object* v_ys_276_){
_start:
{
lean_object* v___x_277_; lean_object* v___x_278_; 
v___x_277_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_xs_275_, v_ys_276_);
v___x_278_ = l_Lean_Omega_IntList_sum(v___x_277_);
lean_dec(v___x_277_);
return v___x_278_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot___boxed(lean_object* v_xs_279_, lean_object* v_ys_280_){
_start:
{
lean_object* v_res_281_; 
v_res_281_ = l_Lean_Omega_IntList_dot(v_xs_279_, v_ys_280_);
lean_dec(v_xs_279_);
return v_res_281_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(lean_object* v_g_282_, lean_object* v_a_283_, lean_object* v_a_284_){
_start:
{
if (lean_obj_tag(v_a_283_) == 0)
{
lean_object* v___x_285_; 
v___x_285_ = l_List_reverse___redArg(v_a_284_);
return v___x_285_;
}
else
{
lean_object* v_head_286_; lean_object* v_tail_287_; lean_object* v___x_289_; uint8_t v_isShared_290_; uint8_t v_isSharedCheck_296_; 
v_head_286_ = lean_ctor_get(v_a_283_, 0);
v_tail_287_ = lean_ctor_get(v_a_283_, 1);
v_isSharedCheck_296_ = !lean_is_exclusive(v_a_283_);
if (v_isSharedCheck_296_ == 0)
{
v___x_289_ = v_a_283_;
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
else
{
lean_inc(v_tail_287_);
lean_inc(v_head_286_);
lean_dec(v_a_283_);
v___x_289_ = lean_box(0);
v_isShared_290_ = v_isSharedCheck_296_;
goto v_resetjp_288_;
}
v_resetjp_288_:
{
lean_object* v___x_291_; lean_object* v___x_293_; 
v___x_291_ = lean_int_ediv(v_head_286_, v_g_282_);
lean_dec(v_head_286_);
if (v_isShared_290_ == 0)
{
lean_ctor_set(v___x_289_, 1, v_a_284_);
lean_ctor_set(v___x_289_, 0, v___x_291_);
v___x_293_ = v___x_289_;
goto v_reusejp_292_;
}
else
{
lean_object* v_reuseFailAlloc_295_; 
v_reuseFailAlloc_295_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_295_, 0, v___x_291_);
lean_ctor_set(v_reuseFailAlloc_295_, 1, v_a_284_);
v___x_293_ = v_reuseFailAlloc_295_;
goto v_reusejp_292_;
}
v_reusejp_292_:
{
v_a_283_ = v_tail_287_;
v_a_284_ = v___x_293_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0___boxed(lean_object* v_g_297_, lean_object* v_a_298_, lean_object* v_a_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(v_g_297_, v_a_298_, v_a_299_);
lean_dec(v_g_297_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv(lean_object* v_xs_301_, lean_object* v_g_302_){
_start:
{
lean_object* v___x_303_; lean_object* v___x_304_; 
v___x_303_ = lean_box(0);
v___x_304_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(v_g_302_, v_xs_301_, v___x_303_);
return v___x_304_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv___boxed(lean_object* v_xs_305_, lean_object* v_g_306_){
_start:
{
lean_object* v_res_307_; 
v_res_307_ = l_Lean_Omega_IntList_sdiv(v_xs_305_, v_g_306_);
lean_dec(v_g_306_);
return v_res_307_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(lean_object* v_init_308_, lean_object* v_x_309_){
_start:
{
if (lean_obj_tag(v_x_309_) == 0)
{
lean_inc(v_init_308_);
return v_init_308_;
}
else
{
lean_object* v_head_310_; lean_object* v_tail_311_; lean_object* v___x_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
v_head_310_ = lean_ctor_get(v_x_309_, 0);
v_tail_311_ = lean_ctor_get(v_x_309_, 1);
v___x_312_ = l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v_init_308_, v_tail_311_);
v___x_313_ = lean_nat_abs(v_head_310_);
v___x_314_ = lean_nat_gcd(v___x_313_, v___x_312_);
lean_dec(v___x_312_);
lean_dec(v___x_313_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0___boxed(lean_object* v_init_315_, lean_object* v_x_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v_init_315_, v_x_316_);
lean_dec(v_x_316_);
lean_dec(v_init_315_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcd(lean_object* v_xs_318_){
_start:
{
lean_object* v___x_319_; lean_object* v___x_320_; 
v___x_319_ = lean_unsigned_to_nat(0u);
v___x_320_ = l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v___x_319_, v_xs_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcd___boxed(lean_object* v_xs_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l_Lean_Omega_IntList_gcd(v_xs_321_);
lean_dec(v_xs_321_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0(lean_object* v_m_323_, lean_object* v_x_324_){
_start:
{
lean_object* v___x_325_; 
v___x_325_ = l_Int_bmod(v_x_324_, v_m_323_);
return v___x_325_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0___boxed(lean_object* v_m_326_, lean_object* v_x_327_){
_start:
{
lean_object* v_res_328_; 
v_res_328_ = l_Lean_Omega_IntList_bmod___lam__0(v_m_326_, v_x_327_);
lean_dec(v_x_327_);
return v_res_328_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod(lean_object* v_x_329_, lean_object* v_m_330_){
_start:
{
lean_object* v___f_331_; lean_object* v___x_332_; lean_object* v___x_333_; 
v___f_331_ = lean_alloc_closure((void*)(l_Lean_Omega_IntList_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_331_, 0, v_m_330_);
v___x_332_ = lean_box(0);
v___x_333_ = l_List_mapTR_loop___redArg(v___f_331_, v_x_329_, v___x_332_);
return v___x_333_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod__dot__sub__dot__bmod(lean_object* v_m_334_, lean_object* v_a_335_, lean_object* v_b_336_){
_start:
{
lean_object* v___f_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_340_; lean_object* v___x_341_; lean_object* v___x_342_; lean_object* v___x_343_; 
lean_inc(v_m_334_);
v___f_337_ = lean_alloc_closure((void*)(l_Lean_Omega_IntList_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_337_, 0, v_m_334_);
lean_inc(v_b_336_);
v___x_338_ = l_Lean_Omega_IntList_dot(v_a_335_, v_b_336_);
v___x_339_ = l_Int_bmod(v___x_338_, v_m_334_);
lean_dec(v___x_338_);
v___x_340_ = lean_box(0);
v___x_341_ = l_List_mapTR_loop___redArg(v___f_337_, v_a_335_, v___x_340_);
v___x_342_ = l_Lean_Omega_IntList_dot(v___x_341_, v_b_336_);
lean_dec(v___x_341_);
v___x_343_ = lean_int_sub(v___x_339_, v___x_342_);
lean_dec(v___x_342_);
lean_dec(v___x_339_);
return v___x_343_;
}
}
lean_object* runtime_initialize_Init_Data_Int_DivMod_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Omega_IntList(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Omega_IntList(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Int_DivMod_Bootstrap(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
lean_object* initialize_Init_RCases(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Omega_IntList(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Int_DivMod_Bootstrap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Gcd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Int_Order(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Nat_Dvd(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_RCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega_IntList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Omega_IntList(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Omega_IntList(builtin);
}
#ifdef __cplusplus
}
#endif
