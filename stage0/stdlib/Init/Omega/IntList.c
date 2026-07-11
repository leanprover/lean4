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
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* lean_int_mul(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* l_Int_bmod(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
uint8_t lean_bool_not(uint8_t);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading___boxed(lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_x_20_, 1);
v_val_25_ = lean_ctor_get(v_x_21_, 0);
lean_inc(v_val_25_);
lean_dec_ref_known(v_x_21_, 1);
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
lean_dec_ref_known(v_x_32_, 1);
v_val_37_ = lean_ctor_get(v_x_33_, 0);
lean_inc(v_val_37_);
lean_dec_ref_known(v_x_33_, 1);
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
lean_dec_ref_known(v___x_45_, 1);
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
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(lean_object* v_x_83_){
_start:
{
if (lean_obj_tag(v_x_83_) == 0)
{
lean_object* v___x_84_; 
v___x_84_ = lean_box(0);
return v___x_84_;
}
else
{
lean_object* v_head_85_; lean_object* v_tail_86_; lean_object* v___x_87_; uint8_t v___x_88_; uint8_t v___x_89_; 
v_head_85_ = lean_ctor_get(v_x_83_, 0);
v_tail_86_ = lean_ctor_get(v_x_83_, 1);
v___x_87_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_88_ = lean_int_dec_eq(v_head_85_, v___x_87_);
v___x_89_ = lean_bool_not(v___x_88_);
if (v___x_89_ == 0)
{
v_x_83_ = v_tail_86_;
goto _start;
}
else
{
lean_object* v___x_91_; 
lean_inc(v_head_85_);
v___x_91_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_91_, 0, v_head_85_);
return v___x_91_;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0___boxed(lean_object* v_x_92_){
_start:
{
lean_object* v_res_93_; 
v_res_93_ = l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(v_x_92_);
lean_dec(v_x_92_);
return v_res_93_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading(lean_object* v_xs_94_){
_start:
{
lean_object* v___x_95_; 
v___x_95_ = l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(v_xs_94_);
if (lean_obj_tag(v___x_95_) == 0)
{
lean_object* v___x_96_; 
v___x_96_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
return v___x_96_;
}
else
{
lean_object* v_val_97_; 
v_val_97_ = lean_ctor_get(v___x_95_, 0);
lean_inc(v_val_97_);
lean_dec_ref_known(v___x_95_, 1);
return v_val_97_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading___boxed(lean_object* v_xs_98_){
_start:
{
lean_object* v_res_99_; 
v_res_99_ = l_Lean_Omega_IntList_leading(v_xs_98_);
lean_dec(v_xs_98_);
return v_res_99_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(lean_object* v_x_100_){
_start:
{
if (lean_obj_tag(v_x_100_) == 0)
{
return v_x_100_;
}
else
{
lean_object* v_head_101_; lean_object* v_tail_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_112_; 
v_head_101_ = lean_ctor_get(v_x_100_, 0);
v_tail_102_ = lean_ctor_get(v_x_100_, 1);
v_isSharedCheck_112_ = !lean_is_exclusive(v_x_100_);
if (v_isSharedCheck_112_ == 0)
{
v___x_104_ = v_x_100_;
v_isShared_105_ = v_isSharedCheck_112_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_tail_102_);
lean_inc(v_head_101_);
lean_dec(v_x_100_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_112_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_106_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_107_ = lean_int_add(v___x_106_, v_head_101_);
lean_dec(v_head_101_);
v___x_108_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(v_tail_102_);
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v___x_108_);
lean_ctor_set(v___x_104_, 0, v___x_107_);
v___x_110_ = v___x_104_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_107_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v___x_108_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(lean_object* v_x_113_){
_start:
{
if (lean_obj_tag(v_x_113_) == 0)
{
return v_x_113_;
}
else
{
lean_object* v_head_114_; lean_object* v_tail_115_; lean_object* v___x_117_; uint8_t v_isShared_118_; uint8_t v_isSharedCheck_125_; 
v_head_114_ = lean_ctor_get(v_x_113_, 0);
v_tail_115_ = lean_ctor_get(v_x_113_, 1);
v_isSharedCheck_125_ = !lean_is_exclusive(v_x_113_);
if (v_isSharedCheck_125_ == 0)
{
v___x_117_ = v_x_113_;
v_isShared_118_ = v_isSharedCheck_125_;
goto v_resetjp_116_;
}
else
{
lean_inc(v_tail_115_);
lean_inc(v_head_114_);
lean_dec(v_x_113_);
v___x_117_ = lean_box(0);
v_isShared_118_ = v_isSharedCheck_125_;
goto v_resetjp_116_;
}
v_resetjp_116_:
{
lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_121_; lean_object* v___x_123_; 
v___x_119_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_120_ = lean_int_add(v___x_119_, v_head_114_);
lean_dec(v_head_114_);
v___x_121_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(v_tail_115_);
if (v_isShared_118_ == 0)
{
lean_ctor_set(v___x_117_, 1, v___x_121_);
lean_ctor_set(v___x_117_, 0, v___x_120_);
v___x_123_ = v___x_117_;
goto v_reusejp_122_;
}
else
{
lean_object* v_reuseFailAlloc_124_; 
v_reuseFailAlloc_124_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_124_, 0, v___x_120_);
lean_ctor_set(v_reuseFailAlloc_124_, 1, v___x_121_);
v___x_123_ = v_reuseFailAlloc_124_;
goto v_reusejp_122_;
}
v_reusejp_122_:
{
return v___x_123_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(lean_object* v_x_126_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
return v_x_126_;
}
else
{
lean_object* v_head_127_; lean_object* v_tail_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_138_; 
v_head_127_ = lean_ctor_get(v_x_126_, 0);
v_tail_128_ = lean_ctor_get(v_x_126_, 1);
v_isSharedCheck_138_ = !lean_is_exclusive(v_x_126_);
if (v_isSharedCheck_138_ == 0)
{
v___x_130_ = v_x_126_;
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_tail_128_);
lean_inc(v_head_127_);
lean_dec(v_x_126_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_138_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_134_; lean_object* v___x_136_; 
v___x_132_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_133_ = lean_int_add(v_head_127_, v___x_132_);
lean_dec(v_head_127_);
v___x_134_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(v_tail_128_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_134_);
lean_ctor_set(v___x_130_, 0, v___x_133_);
v___x_136_ = v___x_130_;
goto v_reusejp_135_;
}
else
{
lean_object* v_reuseFailAlloc_137_; 
v_reuseFailAlloc_137_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_137_, 0, v___x_133_);
lean_ctor_set(v_reuseFailAlloc_137_, 1, v___x_134_);
v___x_136_ = v_reuseFailAlloc_137_;
goto v_reusejp_135_;
}
v_reusejp_135_:
{
return v___x_136_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(lean_object* v_x_139_){
_start:
{
if (lean_obj_tag(v_x_139_) == 0)
{
return v_x_139_;
}
else
{
lean_object* v_head_140_; lean_object* v_tail_141_; lean_object* v___x_143_; uint8_t v_isShared_144_; uint8_t v_isSharedCheck_151_; 
v_head_140_ = lean_ctor_get(v_x_139_, 0);
v_tail_141_ = lean_ctor_get(v_x_139_, 1);
v_isSharedCheck_151_ = !lean_is_exclusive(v_x_139_);
if (v_isSharedCheck_151_ == 0)
{
v___x_143_ = v_x_139_;
v_isShared_144_ = v_isSharedCheck_151_;
goto v_resetjp_142_;
}
else
{
lean_inc(v_tail_141_);
lean_inc(v_head_140_);
lean_dec(v_x_139_);
v___x_143_ = lean_box(0);
v_isShared_144_ = v_isSharedCheck_151_;
goto v_resetjp_142_;
}
v_resetjp_142_:
{
lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_147_; lean_object* v___x_149_; 
v___x_145_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_146_ = lean_int_add(v_head_140_, v___x_145_);
lean_dec(v_head_140_);
v___x_147_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(v_tail_141_);
if (v_isShared_144_ == 0)
{
lean_ctor_set(v___x_143_, 1, v___x_147_);
lean_ctor_set(v___x_143_, 0, v___x_146_);
v___x_149_ = v___x_143_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v___x_146_);
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
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(lean_object* v_x_152_, lean_object* v_x_153_){
_start:
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v___x_154_; 
v___x_154_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(v_x_153_);
return v___x_154_;
}
else
{
if (lean_obj_tag(v_x_153_) == 0)
{
lean_object* v___x_155_; 
v___x_155_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(v_x_152_);
return v___x_155_;
}
else
{
lean_object* v_head_156_; lean_object* v_tail_157_; lean_object* v_head_158_; lean_object* v_tail_159_; lean_object* v___x_161_; uint8_t v_isShared_162_; uint8_t v_isSharedCheck_168_; 
v_head_156_ = lean_ctor_get(v_x_152_, 0);
lean_inc(v_head_156_);
v_tail_157_ = lean_ctor_get(v_x_152_, 1);
lean_inc(v_tail_157_);
lean_dec_ref_known(v_x_152_, 2);
v_head_158_ = lean_ctor_get(v_x_153_, 0);
v_tail_159_ = lean_ctor_get(v_x_153_, 1);
v_isSharedCheck_168_ = !lean_is_exclusive(v_x_153_);
if (v_isSharedCheck_168_ == 0)
{
v___x_161_ = v_x_153_;
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
else
{
lean_inc(v_tail_159_);
lean_inc(v_head_158_);
lean_dec(v_x_153_);
v___x_161_ = lean_box(0);
v_isShared_162_ = v_isSharedCheck_168_;
goto v_resetjp_160_;
}
v_resetjp_160_:
{
lean_object* v___x_163_; lean_object* v___x_164_; lean_object* v___x_166_; 
v___x_163_ = lean_int_add(v_head_156_, v_head_158_);
lean_dec(v_head_158_);
lean_dec(v_head_156_);
v___x_164_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_tail_157_, v_tail_159_);
if (v_isShared_162_ == 0)
{
lean_ctor_set(v___x_161_, 1, v___x_164_);
lean_ctor_set(v___x_161_, 0, v___x_163_);
v___x_166_ = v___x_161_;
goto v_reusejp_165_;
}
else
{
lean_object* v_reuseFailAlloc_167_; 
v_reuseFailAlloc_167_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_167_, 0, v___x_163_);
lean_ctor_set(v_reuseFailAlloc_167_, 1, v___x_164_);
v___x_166_ = v_reuseFailAlloc_167_;
goto v_reusejp_165_;
}
v_reusejp_165_:
{
return v___x_166_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add(lean_object* v_xs_169_, lean_object* v_ys_170_){
_start:
{
lean_object* v___x_171_; 
v___x_171_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_xs_169_, v_ys_170_);
return v___x_171_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(lean_object* v_x_174_, lean_object* v_x_175_){
_start:
{
if (lean_obj_tag(v_x_174_) == 0)
{
lean_dec(v_x_175_);
return v_x_174_;
}
else
{
if (lean_obj_tag(v_x_175_) == 0)
{
return v_x_175_;
}
else
{
lean_object* v_head_176_; lean_object* v_tail_177_; lean_object* v_head_178_; lean_object* v_tail_179_; lean_object* v___x_181_; uint8_t v_isShared_182_; uint8_t v_isSharedCheck_188_; 
v_head_176_ = lean_ctor_get(v_x_174_, 0);
v_tail_177_ = lean_ctor_get(v_x_174_, 1);
v_head_178_ = lean_ctor_get(v_x_175_, 0);
v_tail_179_ = lean_ctor_get(v_x_175_, 1);
v_isSharedCheck_188_ = !lean_is_exclusive(v_x_175_);
if (v_isSharedCheck_188_ == 0)
{
v___x_181_ = v_x_175_;
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
else
{
lean_inc(v_tail_179_);
lean_inc(v_head_178_);
lean_dec(v_x_175_);
v___x_181_ = lean_box(0);
v_isShared_182_ = v_isSharedCheck_188_;
goto v_resetjp_180_;
}
v_resetjp_180_:
{
lean_object* v___x_183_; lean_object* v___x_184_; lean_object* v___x_186_; 
v___x_183_ = lean_int_mul(v_head_176_, v_head_178_);
lean_dec(v_head_178_);
v___x_184_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_tail_177_, v_tail_179_);
if (v_isShared_182_ == 0)
{
lean_ctor_set(v___x_181_, 1, v___x_184_);
lean_ctor_set(v___x_181_, 0, v___x_183_);
v___x_186_ = v___x_181_;
goto v_reusejp_185_;
}
else
{
lean_object* v_reuseFailAlloc_187_; 
v_reuseFailAlloc_187_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_187_, 0, v___x_183_);
lean_ctor_set(v_reuseFailAlloc_187_, 1, v___x_184_);
v___x_186_ = v_reuseFailAlloc_187_;
goto v_reusejp_185_;
}
v_reusejp_185_:
{
return v___x_186_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0___boxed(lean_object* v_x_189_, lean_object* v_x_190_){
_start:
{
lean_object* v_res_191_; 
v_res_191_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_x_189_, v_x_190_);
lean_dec(v_x_189_);
return v_res_191_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mul(lean_object* v_xs_192_, lean_object* v_ys_193_){
_start:
{
lean_object* v___x_194_; 
v___x_194_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_xs_192_, v_ys_193_);
return v___x_194_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mul___boxed(lean_object* v_xs_195_, lean_object* v_ys_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l_Lean_Omega_IntList_mul(v_xs_195_, v_ys_196_);
lean_dec(v_xs_195_);
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(lean_object* v_a_200_, lean_object* v_a_201_){
_start:
{
if (lean_obj_tag(v_a_200_) == 0)
{
lean_object* v___x_202_; 
v___x_202_ = l_List_reverse___redArg(v_a_201_);
return v___x_202_;
}
else
{
lean_object* v_head_203_; lean_object* v_tail_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_213_; 
v_head_203_ = lean_ctor_get(v_a_200_, 0);
v_tail_204_ = lean_ctor_get(v_a_200_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_a_200_);
if (v_isSharedCheck_213_ == 0)
{
v___x_206_ = v_a_200_;
v_isShared_207_ = v_isSharedCheck_213_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_tail_204_);
lean_inc(v_head_203_);
lean_dec(v_a_200_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_213_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_210_; 
v___x_208_ = lean_int_neg(v_head_203_);
lean_dec(v_head_203_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v_a_201_);
lean_ctor_set(v___x_206_, 0, v___x_208_);
v___x_210_ = v___x_206_;
goto v_reusejp_209_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v_a_201_);
v___x_210_ = v_reuseFailAlloc_212_;
goto v_reusejp_209_;
}
v_reusejp_209_:
{
v_a_200_ = v_tail_204_;
v_a_201_ = v___x_210_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_neg(lean_object* v_xs_214_){
_start:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_box(0);
v___x_216_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(v_xs_214_, v___x_215_);
return v___x_216_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(lean_object* v_x_219_){
_start:
{
if (lean_obj_tag(v_x_219_) == 0)
{
return v_x_219_;
}
else
{
lean_object* v_head_220_; lean_object* v_tail_221_; lean_object* v___x_223_; uint8_t v_isShared_224_; uint8_t v_isSharedCheck_231_; 
v_head_220_ = lean_ctor_get(v_x_219_, 0);
v_tail_221_ = lean_ctor_get(v_x_219_, 1);
v_isSharedCheck_231_ = !lean_is_exclusive(v_x_219_);
if (v_isSharedCheck_231_ == 0)
{
v___x_223_ = v_x_219_;
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
else
{
lean_inc(v_tail_221_);
lean_inc(v_head_220_);
lean_dec(v_x_219_);
v___x_223_ = lean_box(0);
v_isShared_224_ = v_isSharedCheck_231_;
goto v_resetjp_222_;
}
v_resetjp_222_:
{
lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_227_; lean_object* v___x_229_; 
v___x_225_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_226_ = lean_int_sub(v___x_225_, v_head_220_);
lean_dec(v_head_220_);
v___x_227_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(v_tail_221_);
if (v_isShared_224_ == 0)
{
lean_ctor_set(v___x_223_, 1, v___x_227_);
lean_ctor_set(v___x_223_, 0, v___x_226_);
v___x_229_ = v___x_223_;
goto v_reusejp_228_;
}
else
{
lean_object* v_reuseFailAlloc_230_; 
v_reuseFailAlloc_230_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_230_, 0, v___x_226_);
lean_ctor_set(v_reuseFailAlloc_230_, 1, v___x_227_);
v___x_229_ = v_reuseFailAlloc_230_;
goto v_reusejp_228_;
}
v_reusejp_228_:
{
return v___x_229_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(lean_object* v_x_232_){
_start:
{
if (lean_obj_tag(v_x_232_) == 0)
{
return v_x_232_;
}
else
{
lean_object* v_head_233_; lean_object* v_tail_234_; lean_object* v___x_236_; uint8_t v_isShared_237_; uint8_t v_isSharedCheck_244_; 
v_head_233_ = lean_ctor_get(v_x_232_, 0);
v_tail_234_ = lean_ctor_get(v_x_232_, 1);
v_isSharedCheck_244_ = !lean_is_exclusive(v_x_232_);
if (v_isSharedCheck_244_ == 0)
{
v___x_236_ = v_x_232_;
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
else
{
lean_inc(v_tail_234_);
lean_inc(v_head_233_);
lean_dec(v_x_232_);
v___x_236_ = lean_box(0);
v_isShared_237_ = v_isSharedCheck_244_;
goto v_resetjp_235_;
}
v_resetjp_235_:
{
lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_240_; lean_object* v___x_242_; 
v___x_238_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_239_ = lean_int_sub(v___x_238_, v_head_233_);
lean_dec(v_head_233_);
v___x_240_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(v_tail_234_);
if (v_isShared_237_ == 0)
{
lean_ctor_set(v___x_236_, 1, v___x_240_);
lean_ctor_set(v___x_236_, 0, v___x_239_);
v___x_242_ = v___x_236_;
goto v_reusejp_241_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v___x_239_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v___x_240_);
v___x_242_ = v_reuseFailAlloc_243_;
goto v_reusejp_241_;
}
v_reusejp_241_:
{
return v___x_242_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(lean_object* v_x_245_){
_start:
{
if (lean_obj_tag(v_x_245_) == 0)
{
return v_x_245_;
}
else
{
lean_object* v_head_246_; lean_object* v_tail_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_257_; 
v_head_246_ = lean_ctor_get(v_x_245_, 0);
v_tail_247_ = lean_ctor_get(v_x_245_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_x_245_);
if (v_isSharedCheck_257_ == 0)
{
v___x_249_ = v_x_245_;
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_tail_247_);
lean_inc(v_head_246_);
lean_dec(v_x_245_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_257_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_253_; lean_object* v___x_255_; 
v___x_251_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_252_ = lean_int_sub(v_head_246_, v___x_251_);
lean_dec(v_head_246_);
v___x_253_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(v_tail_247_);
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v___x_253_);
lean_ctor_set(v___x_249_, 0, v___x_252_);
v___x_255_ = v___x_249_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(lean_object* v_x_258_){
_start:
{
if (lean_obj_tag(v_x_258_) == 0)
{
return v_x_258_;
}
else
{
lean_object* v_head_259_; lean_object* v_tail_260_; lean_object* v___x_262_; uint8_t v_isShared_263_; uint8_t v_isSharedCheck_270_; 
v_head_259_ = lean_ctor_get(v_x_258_, 0);
v_tail_260_ = lean_ctor_get(v_x_258_, 1);
v_isSharedCheck_270_ = !lean_is_exclusive(v_x_258_);
if (v_isSharedCheck_270_ == 0)
{
v___x_262_ = v_x_258_;
v_isShared_263_ = v_isSharedCheck_270_;
goto v_resetjp_261_;
}
else
{
lean_inc(v_tail_260_);
lean_inc(v_head_259_);
lean_dec(v_x_258_);
v___x_262_ = lean_box(0);
v_isShared_263_ = v_isSharedCheck_270_;
goto v_resetjp_261_;
}
v_resetjp_261_:
{
lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_266_; lean_object* v___x_268_; 
v___x_264_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_265_ = lean_int_sub(v_head_259_, v___x_264_);
lean_dec(v_head_259_);
v___x_266_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(v_tail_260_);
if (v_isShared_263_ == 0)
{
lean_ctor_set(v___x_262_, 1, v___x_266_);
lean_ctor_set(v___x_262_, 0, v___x_265_);
v___x_268_ = v___x_262_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_269_; 
v_reuseFailAlloc_269_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_269_, 0, v___x_265_);
lean_ctor_set(v_reuseFailAlloc_269_, 1, v___x_266_);
v___x_268_ = v_reuseFailAlloc_269_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
return v___x_268_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(lean_object* v_x_271_, lean_object* v_x_272_){
_start:
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v___x_273_; 
v___x_273_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(v_x_272_);
return v___x_273_;
}
else
{
if (lean_obj_tag(v_x_272_) == 0)
{
lean_object* v___x_274_; 
v___x_274_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(v_x_271_);
return v___x_274_;
}
else
{
lean_object* v_head_275_; lean_object* v_tail_276_; lean_object* v_head_277_; lean_object* v_tail_278_; lean_object* v___x_280_; uint8_t v_isShared_281_; uint8_t v_isSharedCheck_287_; 
v_head_275_ = lean_ctor_get(v_x_271_, 0);
lean_inc(v_head_275_);
v_tail_276_ = lean_ctor_get(v_x_271_, 1);
lean_inc(v_tail_276_);
lean_dec_ref_known(v_x_271_, 2);
v_head_277_ = lean_ctor_get(v_x_272_, 0);
v_tail_278_ = lean_ctor_get(v_x_272_, 1);
v_isSharedCheck_287_ = !lean_is_exclusive(v_x_272_);
if (v_isSharedCheck_287_ == 0)
{
v___x_280_ = v_x_272_;
v_isShared_281_ = v_isSharedCheck_287_;
goto v_resetjp_279_;
}
else
{
lean_inc(v_tail_278_);
lean_inc(v_head_277_);
lean_dec(v_x_272_);
v___x_280_ = lean_box(0);
v_isShared_281_ = v_isSharedCheck_287_;
goto v_resetjp_279_;
}
v_resetjp_279_:
{
lean_object* v___x_282_; lean_object* v___x_283_; lean_object* v___x_285_; 
v___x_282_ = lean_int_sub(v_head_275_, v_head_277_);
lean_dec(v_head_277_);
lean_dec(v_head_275_);
v___x_283_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_tail_276_, v_tail_278_);
if (v_isShared_281_ == 0)
{
lean_ctor_set(v___x_280_, 1, v___x_283_);
lean_ctor_set(v___x_280_, 0, v___x_282_);
v___x_285_ = v___x_280_;
goto v_reusejp_284_;
}
else
{
lean_object* v_reuseFailAlloc_286_; 
v_reuseFailAlloc_286_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_286_, 0, v___x_282_);
lean_ctor_set(v_reuseFailAlloc_286_, 1, v___x_283_);
v___x_285_ = v_reuseFailAlloc_286_;
goto v_reusejp_284_;
}
v_reusejp_284_:
{
return v___x_285_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sub(lean_object* v_xs_288_, lean_object* v_ys_289_){
_start:
{
lean_object* v___x_290_; 
v___x_290_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_xs_288_, v_ys_289_);
return v___x_290_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(lean_object* v_i_293_, lean_object* v_a_294_, lean_object* v_a_295_){
_start:
{
if (lean_obj_tag(v_a_294_) == 0)
{
lean_object* v___x_296_; 
v___x_296_ = l_List_reverse___redArg(v_a_295_);
return v___x_296_;
}
else
{
lean_object* v_head_297_; lean_object* v_tail_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_307_; 
v_head_297_ = lean_ctor_get(v_a_294_, 0);
v_tail_298_ = lean_ctor_get(v_a_294_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_a_294_);
if (v_isSharedCheck_307_ == 0)
{
v___x_300_ = v_a_294_;
v_isShared_301_ = v_isSharedCheck_307_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_tail_298_);
lean_inc(v_head_297_);
lean_dec(v_a_294_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_307_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_302_ = lean_int_mul(v_i_293_, v_head_297_);
lean_dec(v_head_297_);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v_a_295_);
lean_ctor_set(v___x_300_, 0, v___x_302_);
v___x_304_ = v___x_300_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_a_295_);
v___x_304_ = v_reuseFailAlloc_306_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
v_a_294_ = v_tail_298_;
v_a_295_ = v___x_304_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0___boxed(lean_object* v_i_308_, lean_object* v_a_309_, lean_object* v_a_310_){
_start:
{
lean_object* v_res_311_; 
v_res_311_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_308_, v_a_309_, v_a_310_);
lean_dec(v_i_308_);
return v_res_311_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul(lean_object* v_xs_312_, lean_object* v_i_313_){
_start:
{
lean_object* v___x_314_; lean_object* v___x_315_; 
v___x_314_ = lean_box(0);
v___x_315_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_313_, v_xs_312_, v___x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul___boxed(lean_object* v_xs_316_, lean_object* v_i_317_){
_start:
{
lean_object* v_res_318_; 
v_res_318_ = l_Lean_Omega_IntList_smul(v_xs_316_, v_i_317_);
lean_dec(v_i_317_);
return v_res_318_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0(lean_object* v_i_319_, lean_object* v_xs_320_){
_start:
{
lean_object* v___x_321_; 
v___x_321_ = l_Lean_Omega_IntList_smul(v_xs_320_, v_i_319_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0___boxed(lean_object* v_i_322_, lean_object* v_xs_323_){
_start:
{
lean_object* v_res_324_; 
v_res_324_ = l_Lean_Omega_IntList_instHMulInt___lam__0(v_i_322_, v_xs_323_);
lean_dec(v_i_322_);
return v_res_324_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(lean_object* v_a_327_, lean_object* v_b_328_, lean_object* v_x_329_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
return v_x_329_;
}
else
{
lean_object* v_head_330_; lean_object* v_tail_331_; lean_object* v___x_333_; uint8_t v_isShared_334_; uint8_t v_isSharedCheck_343_; 
v_head_330_ = lean_ctor_get(v_x_329_, 0);
v_tail_331_ = lean_ctor_get(v_x_329_, 1);
v_isSharedCheck_343_ = !lean_is_exclusive(v_x_329_);
if (v_isSharedCheck_343_ == 0)
{
v___x_333_ = v_x_329_;
v_isShared_334_ = v_isSharedCheck_343_;
goto v_resetjp_332_;
}
else
{
lean_inc(v_tail_331_);
lean_inc(v_head_330_);
lean_dec(v_x_329_);
v___x_333_ = lean_box(0);
v_isShared_334_ = v_isSharedCheck_343_;
goto v_resetjp_332_;
}
v_resetjp_332_:
{
lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_339_; lean_object* v___x_341_; 
v___x_335_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_336_ = lean_int_mul(v_a_327_, v___x_335_);
v___x_337_ = lean_int_mul(v_b_328_, v_head_330_);
lean_dec(v_head_330_);
v___x_338_ = lean_int_add(v___x_336_, v___x_337_);
lean_dec(v___x_337_);
lean_dec(v___x_336_);
v___x_339_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_327_, v_b_328_, v_tail_331_);
if (v_isShared_334_ == 0)
{
lean_ctor_set(v___x_333_, 1, v___x_339_);
lean_ctor_set(v___x_333_, 0, v___x_338_);
v___x_341_ = v___x_333_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v___x_338_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v___x_339_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1___boxed(lean_object* v_a_344_, lean_object* v_b_345_, lean_object* v_x_346_){
_start:
{
lean_object* v_res_347_; 
v_res_347_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_344_, v_b_345_, v_x_346_);
lean_dec(v_b_345_);
lean_dec(v_a_344_);
return v_res_347_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(lean_object* v_a_348_, lean_object* v_b_349_, lean_object* v_x_350_){
_start:
{
if (lean_obj_tag(v_x_350_) == 0)
{
return v_x_350_;
}
else
{
lean_object* v_head_351_; lean_object* v_tail_352_; lean_object* v___x_354_; uint8_t v_isShared_355_; uint8_t v_isSharedCheck_364_; 
v_head_351_ = lean_ctor_get(v_x_350_, 0);
v_tail_352_ = lean_ctor_get(v_x_350_, 1);
v_isSharedCheck_364_ = !lean_is_exclusive(v_x_350_);
if (v_isSharedCheck_364_ == 0)
{
v___x_354_ = v_x_350_;
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
else
{
lean_inc(v_tail_352_);
lean_inc(v_head_351_);
lean_dec(v_x_350_);
v___x_354_ = lean_box(0);
v_isShared_355_ = v_isSharedCheck_364_;
goto v_resetjp_353_;
}
v_resetjp_353_:
{
lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_360_; lean_object* v___x_362_; 
v___x_356_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_357_ = lean_int_mul(v_a_348_, v___x_356_);
v___x_358_ = lean_int_mul(v_b_349_, v_head_351_);
lean_dec(v_head_351_);
v___x_359_ = lean_int_add(v___x_357_, v___x_358_);
lean_dec(v___x_358_);
lean_dec(v___x_357_);
v___x_360_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_348_, v_b_349_, v_tail_352_);
if (v_isShared_355_ == 0)
{
lean_ctor_set(v___x_354_, 1, v___x_360_);
lean_ctor_set(v___x_354_, 0, v___x_359_);
v___x_362_ = v___x_354_;
goto v_reusejp_361_;
}
else
{
lean_object* v_reuseFailAlloc_363_; 
v_reuseFailAlloc_363_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_363_, 0, v___x_359_);
lean_ctor_set(v_reuseFailAlloc_363_, 1, v___x_360_);
v___x_362_ = v_reuseFailAlloc_363_;
goto v_reusejp_361_;
}
v_reusejp_361_:
{
return v___x_362_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0___boxed(lean_object* v_a_365_, lean_object* v_b_366_, lean_object* v_x_367_){
_start:
{
lean_object* v_res_368_; 
v_res_368_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(v_a_365_, v_b_366_, v_x_367_);
lean_dec(v_b_366_);
lean_dec(v_a_365_);
return v_res_368_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(lean_object* v_a_369_, lean_object* v_b_370_, lean_object* v_x_371_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
return v_x_371_;
}
else
{
lean_object* v_head_372_; lean_object* v_tail_373_; lean_object* v___x_375_; uint8_t v_isShared_376_; uint8_t v_isSharedCheck_385_; 
v_head_372_ = lean_ctor_get(v_x_371_, 0);
v_tail_373_ = lean_ctor_get(v_x_371_, 1);
v_isSharedCheck_385_ = !lean_is_exclusive(v_x_371_);
if (v_isSharedCheck_385_ == 0)
{
v___x_375_ = v_x_371_;
v_isShared_376_ = v_isSharedCheck_385_;
goto v_resetjp_374_;
}
else
{
lean_inc(v_tail_373_);
lean_inc(v_head_372_);
lean_dec(v_x_371_);
v___x_375_ = lean_box(0);
v_isShared_376_ = v_isSharedCheck_385_;
goto v_resetjp_374_;
}
v_resetjp_374_:
{
lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; lean_object* v___x_383_; 
v___x_377_ = lean_int_mul(v_a_369_, v_head_372_);
lean_dec(v_head_372_);
v___x_378_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_379_ = lean_int_mul(v_b_370_, v___x_378_);
v___x_380_ = lean_int_add(v___x_377_, v___x_379_);
lean_dec(v___x_379_);
lean_dec(v___x_377_);
v___x_381_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_369_, v_b_370_, v_tail_373_);
if (v_isShared_376_ == 0)
{
lean_ctor_set(v___x_375_, 1, v___x_381_);
lean_ctor_set(v___x_375_, 0, v___x_380_);
v___x_383_ = v___x_375_;
goto v_reusejp_382_;
}
else
{
lean_object* v_reuseFailAlloc_384_; 
v_reuseFailAlloc_384_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_384_, 0, v___x_380_);
lean_ctor_set(v_reuseFailAlloc_384_, 1, v___x_381_);
v___x_383_ = v_reuseFailAlloc_384_;
goto v_reusejp_382_;
}
v_reusejp_382_:
{
return v___x_383_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3___boxed(lean_object* v_a_386_, lean_object* v_b_387_, lean_object* v_x_388_){
_start:
{
lean_object* v_res_389_; 
v_res_389_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_386_, v_b_387_, v_x_388_);
lean_dec(v_b_387_);
lean_dec(v_a_386_);
return v_res_389_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(lean_object* v_a_390_, lean_object* v_b_391_, lean_object* v_x_392_){
_start:
{
if (lean_obj_tag(v_x_392_) == 0)
{
return v_x_392_;
}
else
{
lean_object* v_head_393_; lean_object* v_tail_394_; lean_object* v___x_396_; uint8_t v_isShared_397_; uint8_t v_isSharedCheck_406_; 
v_head_393_ = lean_ctor_get(v_x_392_, 0);
v_tail_394_ = lean_ctor_get(v_x_392_, 1);
v_isSharedCheck_406_ = !lean_is_exclusive(v_x_392_);
if (v_isSharedCheck_406_ == 0)
{
v___x_396_ = v_x_392_;
v_isShared_397_ = v_isSharedCheck_406_;
goto v_resetjp_395_;
}
else
{
lean_inc(v_tail_394_);
lean_inc(v_head_393_);
lean_dec(v_x_392_);
v___x_396_ = lean_box(0);
v_isShared_397_ = v_isSharedCheck_406_;
goto v_resetjp_395_;
}
v_resetjp_395_:
{
lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_402_; lean_object* v___x_404_; 
v___x_398_ = lean_int_mul(v_a_390_, v_head_393_);
lean_dec(v_head_393_);
v___x_399_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_400_ = lean_int_mul(v_b_391_, v___x_399_);
v___x_401_ = lean_int_add(v___x_398_, v___x_400_);
lean_dec(v___x_400_);
lean_dec(v___x_398_);
v___x_402_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_390_, v_b_391_, v_tail_394_);
if (v_isShared_397_ == 0)
{
lean_ctor_set(v___x_396_, 1, v___x_402_);
lean_ctor_set(v___x_396_, 0, v___x_401_);
v___x_404_ = v___x_396_;
goto v_reusejp_403_;
}
else
{
lean_object* v_reuseFailAlloc_405_; 
v_reuseFailAlloc_405_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_405_, 0, v___x_401_);
lean_ctor_set(v_reuseFailAlloc_405_, 1, v___x_402_);
v___x_404_ = v_reuseFailAlloc_405_;
goto v_reusejp_403_;
}
v_reusejp_403_:
{
return v___x_404_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1___boxed(lean_object* v_a_407_, lean_object* v_b_408_, lean_object* v_x_409_){
_start:
{
lean_object* v_res_410_; 
v_res_410_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(v_a_407_, v_b_408_, v_x_409_);
lean_dec(v_b_408_);
lean_dec(v_a_407_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(lean_object* v_a_411_, lean_object* v_b_412_, lean_object* v_x_413_, lean_object* v_x_414_){
_start:
{
if (lean_obj_tag(v_x_413_) == 0)
{
lean_object* v___x_415_; 
v___x_415_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(v_a_411_, v_b_412_, v_x_414_);
return v___x_415_;
}
else
{
if (lean_obj_tag(v_x_414_) == 0)
{
lean_object* v___x_416_; 
v___x_416_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(v_a_411_, v_b_412_, v_x_413_);
return v___x_416_;
}
else
{
lean_object* v_head_417_; lean_object* v_tail_418_; lean_object* v_head_419_; lean_object* v_tail_420_; lean_object* v___x_422_; uint8_t v_isShared_423_; uint8_t v_isSharedCheck_431_; 
v_head_417_ = lean_ctor_get(v_x_413_, 0);
lean_inc(v_head_417_);
v_tail_418_ = lean_ctor_get(v_x_413_, 1);
lean_inc(v_tail_418_);
lean_dec_ref_known(v_x_413_, 2);
v_head_419_ = lean_ctor_get(v_x_414_, 0);
v_tail_420_ = lean_ctor_get(v_x_414_, 1);
v_isSharedCheck_431_ = !lean_is_exclusive(v_x_414_);
if (v_isSharedCheck_431_ == 0)
{
v___x_422_ = v_x_414_;
v_isShared_423_ = v_isSharedCheck_431_;
goto v_resetjp_421_;
}
else
{
lean_inc(v_tail_420_);
lean_inc(v_head_419_);
lean_dec(v_x_414_);
v___x_422_ = lean_box(0);
v_isShared_423_ = v_isSharedCheck_431_;
goto v_resetjp_421_;
}
v_resetjp_421_:
{
lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_427_; lean_object* v___x_429_; 
v___x_424_ = lean_int_mul(v_a_411_, v_head_417_);
lean_dec(v_head_417_);
v___x_425_ = lean_int_mul(v_b_412_, v_head_419_);
lean_dec(v_head_419_);
v___x_426_ = lean_int_add(v___x_424_, v___x_425_);
lean_dec(v___x_425_);
lean_dec(v___x_424_);
v___x_427_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_411_, v_b_412_, v_tail_418_, v_tail_420_);
if (v_isShared_423_ == 0)
{
lean_ctor_set(v___x_422_, 1, v___x_427_);
lean_ctor_set(v___x_422_, 0, v___x_426_);
v___x_429_ = v___x_422_;
goto v_reusejp_428_;
}
else
{
lean_object* v_reuseFailAlloc_430_; 
v_reuseFailAlloc_430_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_430_, 0, v___x_426_);
lean_ctor_set(v_reuseFailAlloc_430_, 1, v___x_427_);
v___x_429_ = v_reuseFailAlloc_430_;
goto v_reusejp_428_;
}
v_reusejp_428_:
{
return v___x_429_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0___boxed(lean_object* v_a_432_, lean_object* v_b_433_, lean_object* v_x_434_, lean_object* v_x_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_432_, v_b_433_, v_x_434_, v_x_435_);
lean_dec(v_b_433_);
lean_dec(v_a_432_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo(lean_object* v_a_437_, lean_object* v_xs_438_, lean_object* v_b_439_, lean_object* v_ys_440_){
_start:
{
lean_object* v___x_441_; 
v___x_441_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_437_, v_b_439_, v_xs_438_, v_ys_440_);
return v___x_441_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo___boxed(lean_object* v_a_442_, lean_object* v_xs_443_, lean_object* v_b_444_, lean_object* v_ys_445_){
_start:
{
lean_object* v_res_446_; 
v_res_446_ = l_Lean_Omega_IntList_combo(v_a_442_, v_xs_443_, v_b_444_, v_ys_445_);
lean_dec(v_b_444_);
lean_dec(v_a_442_);
return v_res_446_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(lean_object* v_init_447_, lean_object* v_x_448_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
lean_inc(v_init_447_);
return v_init_447_;
}
else
{
lean_object* v_head_449_; lean_object* v_tail_450_; lean_object* v___x_451_; lean_object* v___x_452_; 
v_head_449_ = lean_ctor_get(v_x_448_, 0);
v_tail_450_ = lean_ctor_get(v_x_448_, 1);
v___x_451_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v_init_447_, v_tail_450_);
v___x_452_ = lean_int_add(v_head_449_, v___x_451_);
lean_dec(v___x_451_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0___boxed(lean_object* v_init_453_, lean_object* v_x_454_){
_start:
{
lean_object* v_res_455_; 
v_res_455_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v_init_453_, v_x_454_);
lean_dec(v_x_454_);
lean_dec(v_init_453_);
return v_res_455_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sum(lean_object* v_xs_456_){
_start:
{
lean_object* v___x_457_; lean_object* v___x_458_; 
v___x_457_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_458_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v___x_457_, v_xs_456_);
return v___x_458_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sum___boxed(lean_object* v_xs_459_){
_start:
{
lean_object* v_res_460_; 
v_res_460_ = l_Lean_Omega_IntList_sum(v_xs_459_);
lean_dec(v_xs_459_);
return v_res_460_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot(lean_object* v_xs_461_, lean_object* v_ys_462_){
_start:
{
lean_object* v___x_463_; lean_object* v___x_464_; 
v___x_463_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_xs_461_, v_ys_462_);
v___x_464_ = l_Lean_Omega_IntList_sum(v___x_463_);
lean_dec(v___x_463_);
return v___x_464_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot___boxed(lean_object* v_xs_465_, lean_object* v_ys_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Lean_Omega_IntList_dot(v_xs_465_, v_ys_466_);
lean_dec(v_xs_465_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(lean_object* v_g_468_, lean_object* v_a_469_, lean_object* v_a_470_){
_start:
{
if (lean_obj_tag(v_a_469_) == 0)
{
lean_object* v___x_471_; 
v___x_471_ = l_List_reverse___redArg(v_a_470_);
return v___x_471_;
}
else
{
lean_object* v_head_472_; lean_object* v_tail_473_; lean_object* v___x_475_; uint8_t v_isShared_476_; uint8_t v_isSharedCheck_482_; 
v_head_472_ = lean_ctor_get(v_a_469_, 0);
v_tail_473_ = lean_ctor_get(v_a_469_, 1);
v_isSharedCheck_482_ = !lean_is_exclusive(v_a_469_);
if (v_isSharedCheck_482_ == 0)
{
v___x_475_ = v_a_469_;
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
else
{
lean_inc(v_tail_473_);
lean_inc(v_head_472_);
lean_dec(v_a_469_);
v___x_475_ = lean_box(0);
v_isShared_476_ = v_isSharedCheck_482_;
goto v_resetjp_474_;
}
v_resetjp_474_:
{
lean_object* v___x_477_; lean_object* v___x_479_; 
v___x_477_ = lean_int_ediv(v_head_472_, v_g_468_);
lean_dec(v_head_472_);
if (v_isShared_476_ == 0)
{
lean_ctor_set(v___x_475_, 1, v_a_470_);
lean_ctor_set(v___x_475_, 0, v___x_477_);
v___x_479_ = v___x_475_;
goto v_reusejp_478_;
}
else
{
lean_object* v_reuseFailAlloc_481_; 
v_reuseFailAlloc_481_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_481_, 0, v___x_477_);
lean_ctor_set(v_reuseFailAlloc_481_, 1, v_a_470_);
v___x_479_ = v_reuseFailAlloc_481_;
goto v_reusejp_478_;
}
v_reusejp_478_:
{
v_a_469_ = v_tail_473_;
v_a_470_ = v___x_479_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0___boxed(lean_object* v_g_483_, lean_object* v_a_484_, lean_object* v_a_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(v_g_483_, v_a_484_, v_a_485_);
lean_dec(v_g_483_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv(lean_object* v_xs_487_, lean_object* v_g_488_){
_start:
{
lean_object* v___x_489_; lean_object* v___x_490_; 
v___x_489_ = lean_box(0);
v___x_490_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(v_g_488_, v_xs_487_, v___x_489_);
return v___x_490_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv___boxed(lean_object* v_xs_491_, lean_object* v_g_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Lean_Omega_IntList_sdiv(v_xs_491_, v_g_492_);
lean_dec(v_g_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(lean_object* v_init_494_, lean_object* v_x_495_){
_start:
{
if (lean_obj_tag(v_x_495_) == 0)
{
lean_inc(v_init_494_);
return v_init_494_;
}
else
{
lean_object* v_head_496_; lean_object* v_tail_497_; lean_object* v___x_498_; lean_object* v___x_499_; lean_object* v___x_500_; 
v_head_496_ = lean_ctor_get(v_x_495_, 0);
v_tail_497_ = lean_ctor_get(v_x_495_, 1);
v___x_498_ = l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v_init_494_, v_tail_497_);
v___x_499_ = lean_nat_abs(v_head_496_);
v___x_500_ = lean_nat_gcd(v___x_499_, v___x_498_);
lean_dec(v___x_498_);
lean_dec(v___x_499_);
return v___x_500_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0___boxed(lean_object* v_init_501_, lean_object* v_x_502_){
_start:
{
lean_object* v_res_503_; 
v_res_503_ = l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v_init_501_, v_x_502_);
lean_dec(v_x_502_);
lean_dec(v_init_501_);
return v_res_503_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcd(lean_object* v_xs_504_){
_start:
{
lean_object* v___x_505_; lean_object* v___x_506_; 
v___x_505_ = lean_unsigned_to_nat(0u);
v___x_506_ = l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v___x_505_, v_xs_504_);
return v___x_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcd___boxed(lean_object* v_xs_507_){
_start:
{
lean_object* v_res_508_; 
v_res_508_ = l_Lean_Omega_IntList_gcd(v_xs_507_);
lean_dec(v_xs_507_);
return v_res_508_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0(lean_object* v_m_509_, lean_object* v_x_510_){
_start:
{
lean_object* v___x_511_; 
v___x_511_ = l_Int_bmod(v_x_510_, v_m_509_);
return v___x_511_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0___boxed(lean_object* v_m_512_, lean_object* v_x_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Lean_Omega_IntList_bmod___lam__0(v_m_512_, v_x_513_);
lean_dec(v_x_513_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod(lean_object* v_x_515_, lean_object* v_m_516_){
_start:
{
lean_object* v___f_517_; lean_object* v___x_518_; lean_object* v___x_519_; 
v___f_517_ = lean_alloc_closure((void*)(l_Lean_Omega_IntList_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_517_, 0, v_m_516_);
v___x_518_ = lean_box(0);
v___x_519_ = l_List_mapTR_loop___redArg(v___f_517_, v_x_515_, v___x_518_);
return v___x_519_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod__dot__sub__dot__bmod(lean_object* v_m_520_, lean_object* v_a_521_, lean_object* v_b_522_){
_start:
{
lean_object* v___f_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; lean_object* v___x_529_; 
lean_inc(v_m_520_);
v___f_523_ = lean_alloc_closure((void*)(l_Lean_Omega_IntList_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_523_, 0, v_m_520_);
lean_inc(v_b_522_);
v___x_524_ = l_Lean_Omega_IntList_dot(v_a_521_, v_b_522_);
v___x_525_ = l_Int_bmod(v___x_524_, v_m_520_);
lean_dec(v___x_524_);
v___x_526_ = lean_box(0);
v___x_527_ = l_List_mapTR_loop___redArg(v___f_523_, v_a_521_, v___x_526_);
v___x_528_ = l_Lean_Omega_IntList_dot(v___x_527_, v_b_522_);
lean_dec(v___x_527_);
v___x_529_ = lean_int_sub(v___x_525_, v___x_528_);
lean_dec(v___x_528_);
lean_dec(v___x_525_);
return v___x_529_;
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
