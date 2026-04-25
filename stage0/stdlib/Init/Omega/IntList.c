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
lean_object* v_head_85_; lean_object* v_tail_86_; lean_object* v___x_87_; uint8_t v___x_88_; 
v_head_85_ = lean_ctor_get(v_x_83_, 0);
v_tail_86_ = lean_ctor_get(v_x_83_, 1);
v___x_87_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_88_ = lean_int_dec_eq(v_head_85_, v___x_87_);
if (v___x_88_ == 0)
{
lean_object* v___x_89_; 
lean_inc(v_head_85_);
v___x_89_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_89_, 0, v_head_85_);
return v___x_89_;
}
else
{
v_x_83_ = v_tail_86_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0___boxed(lean_object* v_x_91_){
_start:
{
lean_object* v_res_92_; 
v_res_92_ = l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(v_x_91_);
lean_dec(v_x_91_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading(lean_object* v_xs_93_){
_start:
{
lean_object* v___x_94_; 
v___x_94_ = l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(v_xs_93_);
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
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading___boxed(lean_object* v_xs_97_){
_start:
{
lean_object* v_res_98_; 
v_res_98_ = l_Lean_Omega_IntList_leading(v_xs_97_);
lean_dec(v_xs_97_);
return v_res_98_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(lean_object* v_x_99_){
_start:
{
if (lean_obj_tag(v_x_99_) == 0)
{
return v_x_99_;
}
else
{
lean_object* v_head_100_; lean_object* v_tail_101_; lean_object* v___x_103_; uint8_t v_isShared_104_; uint8_t v_isSharedCheck_111_; 
v_head_100_ = lean_ctor_get(v_x_99_, 0);
v_tail_101_ = lean_ctor_get(v_x_99_, 1);
v_isSharedCheck_111_ = !lean_is_exclusive(v_x_99_);
if (v_isSharedCheck_111_ == 0)
{
v___x_103_ = v_x_99_;
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
else
{
lean_inc(v_tail_101_);
lean_inc(v_head_100_);
lean_dec(v_x_99_);
v___x_103_ = lean_box(0);
v_isShared_104_ = v_isSharedCheck_111_;
goto v_resetjp_102_;
}
v_resetjp_102_:
{
lean_object* v___x_105_; lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_109_; 
v___x_105_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_106_ = lean_int_add(v___x_105_, v_head_100_);
lean_dec(v_head_100_);
v___x_107_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(v_tail_101_);
if (v_isShared_104_ == 0)
{
lean_ctor_set(v___x_103_, 1, v___x_107_);
lean_ctor_set(v___x_103_, 0, v___x_106_);
v___x_109_ = v___x_103_;
goto v_reusejp_108_;
}
else
{
lean_object* v_reuseFailAlloc_110_; 
v_reuseFailAlloc_110_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_110_, 0, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_110_, 1, v___x_107_);
v___x_109_ = v_reuseFailAlloc_110_;
goto v_reusejp_108_;
}
v_reusejp_108_:
{
return v___x_109_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(lean_object* v_x_112_){
_start:
{
if (lean_obj_tag(v_x_112_) == 0)
{
return v_x_112_;
}
else
{
lean_object* v_head_113_; lean_object* v_tail_114_; lean_object* v___x_116_; uint8_t v_isShared_117_; uint8_t v_isSharedCheck_124_; 
v_head_113_ = lean_ctor_get(v_x_112_, 0);
v_tail_114_ = lean_ctor_get(v_x_112_, 1);
v_isSharedCheck_124_ = !lean_is_exclusive(v_x_112_);
if (v_isSharedCheck_124_ == 0)
{
v___x_116_ = v_x_112_;
v_isShared_117_ = v_isSharedCheck_124_;
goto v_resetjp_115_;
}
else
{
lean_inc(v_tail_114_);
lean_inc(v_head_113_);
lean_dec(v_x_112_);
v___x_116_ = lean_box(0);
v_isShared_117_ = v_isSharedCheck_124_;
goto v_resetjp_115_;
}
v_resetjp_115_:
{
lean_object* v___x_118_; lean_object* v___x_119_; lean_object* v___x_120_; lean_object* v___x_122_; 
v___x_118_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_119_ = lean_int_add(v___x_118_, v_head_113_);
lean_dec(v_head_113_);
v___x_120_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(v_tail_114_);
if (v_isShared_117_ == 0)
{
lean_ctor_set(v___x_116_, 1, v___x_120_);
lean_ctor_set(v___x_116_, 0, v___x_119_);
v___x_122_ = v___x_116_;
goto v_reusejp_121_;
}
else
{
lean_object* v_reuseFailAlloc_123_; 
v_reuseFailAlloc_123_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_123_, 0, v___x_119_);
lean_ctor_set(v_reuseFailAlloc_123_, 1, v___x_120_);
v___x_122_ = v_reuseFailAlloc_123_;
goto v_reusejp_121_;
}
v_reusejp_121_:
{
return v___x_122_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(lean_object* v_x_125_){
_start:
{
if (lean_obj_tag(v_x_125_) == 0)
{
return v_x_125_;
}
else
{
lean_object* v_head_126_; lean_object* v_tail_127_; lean_object* v___x_129_; uint8_t v_isShared_130_; uint8_t v_isSharedCheck_137_; 
v_head_126_ = lean_ctor_get(v_x_125_, 0);
v_tail_127_ = lean_ctor_get(v_x_125_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_x_125_);
if (v_isSharedCheck_137_ == 0)
{
v___x_129_ = v_x_125_;
v_isShared_130_ = v_isSharedCheck_137_;
goto v_resetjp_128_;
}
else
{
lean_inc(v_tail_127_);
lean_inc(v_head_126_);
lean_dec(v_x_125_);
v___x_129_ = lean_box(0);
v_isShared_130_ = v_isSharedCheck_137_;
goto v_resetjp_128_;
}
v_resetjp_128_:
{
lean_object* v___x_131_; lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_131_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_132_ = lean_int_add(v_head_126_, v___x_131_);
lean_dec(v_head_126_);
v___x_133_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(v_tail_127_);
if (v_isShared_130_ == 0)
{
lean_ctor_set(v___x_129_, 1, v___x_133_);
lean_ctor_set(v___x_129_, 0, v___x_132_);
v___x_135_ = v___x_129_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_136_, 0, v___x_132_);
lean_ctor_set(v_reuseFailAlloc_136_, 1, v___x_133_);
v___x_135_ = v_reuseFailAlloc_136_;
goto v_reusejp_134_;
}
v_reusejp_134_:
{
return v___x_135_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(lean_object* v_x_138_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
return v_x_138_;
}
else
{
lean_object* v_head_139_; lean_object* v_tail_140_; lean_object* v___x_142_; uint8_t v_isShared_143_; uint8_t v_isSharedCheck_150_; 
v_head_139_ = lean_ctor_get(v_x_138_, 0);
v_tail_140_ = lean_ctor_get(v_x_138_, 1);
v_isSharedCheck_150_ = !lean_is_exclusive(v_x_138_);
if (v_isSharedCheck_150_ == 0)
{
v___x_142_ = v_x_138_;
v_isShared_143_ = v_isSharedCheck_150_;
goto v_resetjp_141_;
}
else
{
lean_inc(v_tail_140_);
lean_inc(v_head_139_);
lean_dec(v_x_138_);
v___x_142_ = lean_box(0);
v_isShared_143_ = v_isSharedCheck_150_;
goto v_resetjp_141_;
}
v_resetjp_141_:
{
lean_object* v___x_144_; lean_object* v___x_145_; lean_object* v___x_146_; lean_object* v___x_148_; 
v___x_144_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_145_ = lean_int_add(v_head_139_, v___x_144_);
lean_dec(v_head_139_);
v___x_146_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(v_tail_140_);
if (v_isShared_143_ == 0)
{
lean_ctor_set(v___x_142_, 1, v___x_146_);
lean_ctor_set(v___x_142_, 0, v___x_145_);
v___x_148_ = v___x_142_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_149_; 
v_reuseFailAlloc_149_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_149_, 0, v___x_145_);
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
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(lean_object* v_x_151_, lean_object* v_x_152_){
_start:
{
if (lean_obj_tag(v_x_151_) == 0)
{
lean_object* v___x_153_; 
v___x_153_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(v_x_152_);
return v___x_153_;
}
else
{
if (lean_obj_tag(v_x_152_) == 0)
{
lean_object* v___x_154_; 
v___x_154_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(v_x_151_);
return v___x_154_;
}
else
{
lean_object* v_head_155_; lean_object* v_tail_156_; lean_object* v_head_157_; lean_object* v_tail_158_; lean_object* v___x_160_; uint8_t v_isShared_161_; uint8_t v_isSharedCheck_167_; 
v_head_155_ = lean_ctor_get(v_x_151_, 0);
lean_inc(v_head_155_);
v_tail_156_ = lean_ctor_get(v_x_151_, 1);
lean_inc(v_tail_156_);
lean_dec_ref(v_x_151_);
v_head_157_ = lean_ctor_get(v_x_152_, 0);
v_tail_158_ = lean_ctor_get(v_x_152_, 1);
v_isSharedCheck_167_ = !lean_is_exclusive(v_x_152_);
if (v_isSharedCheck_167_ == 0)
{
v___x_160_ = v_x_152_;
v_isShared_161_ = v_isSharedCheck_167_;
goto v_resetjp_159_;
}
else
{
lean_inc(v_tail_158_);
lean_inc(v_head_157_);
lean_dec(v_x_152_);
v___x_160_ = lean_box(0);
v_isShared_161_ = v_isSharedCheck_167_;
goto v_resetjp_159_;
}
v_resetjp_159_:
{
lean_object* v___x_162_; lean_object* v___x_163_; lean_object* v___x_165_; 
v___x_162_ = lean_int_add(v_head_155_, v_head_157_);
lean_dec(v_head_157_);
lean_dec(v_head_155_);
v___x_163_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_tail_156_, v_tail_158_);
if (v_isShared_161_ == 0)
{
lean_ctor_set(v___x_160_, 1, v___x_163_);
lean_ctor_set(v___x_160_, 0, v___x_162_);
v___x_165_ = v___x_160_;
goto v_reusejp_164_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v___x_162_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v___x_163_);
v___x_165_ = v_reuseFailAlloc_166_;
goto v_reusejp_164_;
}
v_reusejp_164_:
{
return v___x_165_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add(lean_object* v_xs_168_, lean_object* v_ys_169_){
_start:
{
lean_object* v___x_170_; 
v___x_170_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_xs_168_, v_ys_169_);
return v___x_170_;
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(lean_object* v_x_173_, lean_object* v_x_174_){
_start:
{
if (lean_obj_tag(v_x_173_) == 0)
{
lean_dec(v_x_174_);
return v_x_173_;
}
else
{
if (lean_obj_tag(v_x_174_) == 0)
{
return v_x_174_;
}
else
{
lean_object* v_head_175_; lean_object* v_tail_176_; lean_object* v_head_177_; lean_object* v_tail_178_; lean_object* v___x_180_; uint8_t v_isShared_181_; uint8_t v_isSharedCheck_187_; 
v_head_175_ = lean_ctor_get(v_x_173_, 0);
v_tail_176_ = lean_ctor_get(v_x_173_, 1);
v_head_177_ = lean_ctor_get(v_x_174_, 0);
v_tail_178_ = lean_ctor_get(v_x_174_, 1);
v_isSharedCheck_187_ = !lean_is_exclusive(v_x_174_);
if (v_isSharedCheck_187_ == 0)
{
v___x_180_ = v_x_174_;
v_isShared_181_ = v_isSharedCheck_187_;
goto v_resetjp_179_;
}
else
{
lean_inc(v_tail_178_);
lean_inc(v_head_177_);
lean_dec(v_x_174_);
v___x_180_ = lean_box(0);
v_isShared_181_ = v_isSharedCheck_187_;
goto v_resetjp_179_;
}
v_resetjp_179_:
{
lean_object* v___x_182_; lean_object* v___x_183_; lean_object* v___x_185_; 
v___x_182_ = lean_int_mul(v_head_175_, v_head_177_);
lean_dec(v_head_177_);
v___x_183_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_tail_176_, v_tail_178_);
if (v_isShared_181_ == 0)
{
lean_ctor_set(v___x_180_, 1, v___x_183_);
lean_ctor_set(v___x_180_, 0, v___x_182_);
v___x_185_ = v___x_180_;
goto v_reusejp_184_;
}
else
{
lean_object* v_reuseFailAlloc_186_; 
v_reuseFailAlloc_186_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_186_, 0, v___x_182_);
lean_ctor_set(v_reuseFailAlloc_186_, 1, v___x_183_);
v___x_185_ = v_reuseFailAlloc_186_;
goto v_reusejp_184_;
}
v_reusejp_184_:
{
return v___x_185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0___boxed(lean_object* v_x_188_, lean_object* v_x_189_){
_start:
{
lean_object* v_res_190_; 
v_res_190_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_x_188_, v_x_189_);
lean_dec(v_x_188_);
return v_res_190_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mul(lean_object* v_xs_191_, lean_object* v_ys_192_){
_start:
{
lean_object* v___x_193_; 
v___x_193_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_xs_191_, v_ys_192_);
return v___x_193_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mul___boxed(lean_object* v_xs_194_, lean_object* v_ys_195_){
_start:
{
lean_object* v_res_196_; 
v_res_196_ = l_Lean_Omega_IntList_mul(v_xs_194_, v_ys_195_);
lean_dec(v_xs_194_);
return v_res_196_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
if (lean_obj_tag(v_a_199_) == 0)
{
lean_object* v___x_201_; 
v___x_201_ = l_List_reverse___redArg(v_a_200_);
return v___x_201_;
}
else
{
lean_object* v_head_202_; lean_object* v_tail_203_; lean_object* v___x_205_; uint8_t v_isShared_206_; uint8_t v_isSharedCheck_212_; 
v_head_202_ = lean_ctor_get(v_a_199_, 0);
v_tail_203_ = lean_ctor_get(v_a_199_, 1);
v_isSharedCheck_212_ = !lean_is_exclusive(v_a_199_);
if (v_isSharedCheck_212_ == 0)
{
v___x_205_ = v_a_199_;
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
else
{
lean_inc(v_tail_203_);
lean_inc(v_head_202_);
lean_dec(v_a_199_);
v___x_205_ = lean_box(0);
v_isShared_206_ = v_isSharedCheck_212_;
goto v_resetjp_204_;
}
v_resetjp_204_:
{
lean_object* v___x_207_; lean_object* v___x_209_; 
v___x_207_ = lean_int_neg(v_head_202_);
lean_dec(v_head_202_);
if (v_isShared_206_ == 0)
{
lean_ctor_set(v___x_205_, 1, v_a_200_);
lean_ctor_set(v___x_205_, 0, v___x_207_);
v___x_209_ = v___x_205_;
goto v_reusejp_208_;
}
else
{
lean_object* v_reuseFailAlloc_211_; 
v_reuseFailAlloc_211_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_211_, 0, v___x_207_);
lean_ctor_set(v_reuseFailAlloc_211_, 1, v_a_200_);
v___x_209_ = v_reuseFailAlloc_211_;
goto v_reusejp_208_;
}
v_reusejp_208_:
{
v_a_199_ = v_tail_203_;
v_a_200_ = v___x_209_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_neg(lean_object* v_xs_213_){
_start:
{
lean_object* v___x_214_; lean_object* v___x_215_; 
v___x_214_ = lean_box(0);
v___x_215_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(v_xs_213_, v___x_214_);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
return v_x_218_;
}
else
{
lean_object* v_head_219_; lean_object* v_tail_220_; lean_object* v___x_222_; uint8_t v_isShared_223_; uint8_t v_isSharedCheck_230_; 
v_head_219_ = lean_ctor_get(v_x_218_, 0);
v_tail_220_ = lean_ctor_get(v_x_218_, 1);
v_isSharedCheck_230_ = !lean_is_exclusive(v_x_218_);
if (v_isSharedCheck_230_ == 0)
{
v___x_222_ = v_x_218_;
v_isShared_223_ = v_isSharedCheck_230_;
goto v_resetjp_221_;
}
else
{
lean_inc(v_tail_220_);
lean_inc(v_head_219_);
lean_dec(v_x_218_);
v___x_222_ = lean_box(0);
v_isShared_223_ = v_isSharedCheck_230_;
goto v_resetjp_221_;
}
v_resetjp_221_:
{
lean_object* v___x_224_; lean_object* v___x_225_; lean_object* v___x_226_; lean_object* v___x_228_; 
v___x_224_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_225_ = lean_int_sub(v___x_224_, v_head_219_);
lean_dec(v_head_219_);
v___x_226_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(v_tail_220_);
if (v_isShared_223_ == 0)
{
lean_ctor_set(v___x_222_, 1, v___x_226_);
lean_ctor_set(v___x_222_, 0, v___x_225_);
v___x_228_ = v___x_222_;
goto v_reusejp_227_;
}
else
{
lean_object* v_reuseFailAlloc_229_; 
v_reuseFailAlloc_229_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_229_, 0, v___x_225_);
lean_ctor_set(v_reuseFailAlloc_229_, 1, v___x_226_);
v___x_228_ = v_reuseFailAlloc_229_;
goto v_reusejp_227_;
}
v_reusejp_227_:
{
return v___x_228_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
return v_x_231_;
}
else
{
lean_object* v_head_232_; lean_object* v_tail_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_243_; 
v_head_232_ = lean_ctor_get(v_x_231_, 0);
v_tail_233_ = lean_ctor_get(v_x_231_, 1);
v_isSharedCheck_243_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_243_ == 0)
{
v___x_235_ = v_x_231_;
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_tail_233_);
lean_inc(v_head_232_);
lean_dec(v_x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_243_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; lean_object* v___x_238_; lean_object* v___x_239_; lean_object* v___x_241_; 
v___x_237_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_238_ = lean_int_sub(v___x_237_, v_head_232_);
lean_dec(v_head_232_);
v___x_239_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(v_tail_233_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v___x_239_);
lean_ctor_set(v___x_235_, 0, v___x_238_);
v___x_241_ = v___x_235_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_242_; 
v_reuseFailAlloc_242_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_242_, 0, v___x_238_);
lean_ctor_set(v_reuseFailAlloc_242_, 1, v___x_239_);
v___x_241_ = v_reuseFailAlloc_242_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
return v___x_241_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(lean_object* v_x_244_){
_start:
{
if (lean_obj_tag(v_x_244_) == 0)
{
return v_x_244_;
}
else
{
lean_object* v_head_245_; lean_object* v_tail_246_; lean_object* v___x_248_; uint8_t v_isShared_249_; uint8_t v_isSharedCheck_256_; 
v_head_245_ = lean_ctor_get(v_x_244_, 0);
v_tail_246_ = lean_ctor_get(v_x_244_, 1);
v_isSharedCheck_256_ = !lean_is_exclusive(v_x_244_);
if (v_isSharedCheck_256_ == 0)
{
v___x_248_ = v_x_244_;
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
else
{
lean_inc(v_tail_246_);
lean_inc(v_head_245_);
lean_dec(v_x_244_);
v___x_248_ = lean_box(0);
v_isShared_249_ = v_isSharedCheck_256_;
goto v_resetjp_247_;
}
v_resetjp_247_:
{
lean_object* v___x_250_; lean_object* v___x_251_; lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_250_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_251_ = lean_int_sub(v_head_245_, v___x_250_);
lean_dec(v_head_245_);
v___x_252_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(v_tail_246_);
if (v_isShared_249_ == 0)
{
lean_ctor_set(v___x_248_, 1, v___x_252_);
lean_ctor_set(v___x_248_, 0, v___x_251_);
v___x_254_ = v___x_248_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v___x_251_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v___x_252_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(lean_object* v_x_257_){
_start:
{
if (lean_obj_tag(v_x_257_) == 0)
{
return v_x_257_;
}
else
{
lean_object* v_head_258_; lean_object* v_tail_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_269_; 
v_head_258_ = lean_ctor_get(v_x_257_, 0);
v_tail_259_ = lean_ctor_get(v_x_257_, 1);
v_isSharedCheck_269_ = !lean_is_exclusive(v_x_257_);
if (v_isSharedCheck_269_ == 0)
{
v___x_261_ = v_x_257_;
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_tail_259_);
lean_inc(v_head_258_);
lean_dec(v_x_257_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_263_; lean_object* v___x_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
v___x_263_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_264_ = lean_int_sub(v_head_258_, v___x_263_);
lean_dec(v_head_258_);
v___x_265_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(v_tail_259_);
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 1, v___x_265_);
lean_ctor_set(v___x_261_, 0, v___x_264_);
v___x_267_ = v___x_261_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v___x_264_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v___x_265_);
v___x_267_ = v_reuseFailAlloc_268_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
return v___x_267_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(lean_object* v_x_270_, lean_object* v_x_271_){
_start:
{
if (lean_obj_tag(v_x_270_) == 0)
{
lean_object* v___x_272_; 
v___x_272_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(v_x_271_);
return v___x_272_;
}
else
{
if (lean_obj_tag(v_x_271_) == 0)
{
lean_object* v___x_273_; 
v___x_273_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(v_x_270_);
return v___x_273_;
}
else
{
lean_object* v_head_274_; lean_object* v_tail_275_; lean_object* v_head_276_; lean_object* v_tail_277_; lean_object* v___x_279_; uint8_t v_isShared_280_; uint8_t v_isSharedCheck_286_; 
v_head_274_ = lean_ctor_get(v_x_270_, 0);
lean_inc(v_head_274_);
v_tail_275_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_tail_275_);
lean_dec_ref(v_x_270_);
v_head_276_ = lean_ctor_get(v_x_271_, 0);
v_tail_277_ = lean_ctor_get(v_x_271_, 1);
v_isSharedCheck_286_ = !lean_is_exclusive(v_x_271_);
if (v_isSharedCheck_286_ == 0)
{
v___x_279_ = v_x_271_;
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
else
{
lean_inc(v_tail_277_);
lean_inc(v_head_276_);
lean_dec(v_x_271_);
v___x_279_ = lean_box(0);
v_isShared_280_ = v_isSharedCheck_286_;
goto v_resetjp_278_;
}
v_resetjp_278_:
{
lean_object* v___x_281_; lean_object* v___x_282_; lean_object* v___x_284_; 
v___x_281_ = lean_int_sub(v_head_274_, v_head_276_);
lean_dec(v_head_276_);
lean_dec(v_head_274_);
v___x_282_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_tail_275_, v_tail_277_);
if (v_isShared_280_ == 0)
{
lean_ctor_set(v___x_279_, 1, v___x_282_);
lean_ctor_set(v___x_279_, 0, v___x_281_);
v___x_284_ = v___x_279_;
goto v_reusejp_283_;
}
else
{
lean_object* v_reuseFailAlloc_285_; 
v_reuseFailAlloc_285_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_285_, 0, v___x_281_);
lean_ctor_set(v_reuseFailAlloc_285_, 1, v___x_282_);
v___x_284_ = v_reuseFailAlloc_285_;
goto v_reusejp_283_;
}
v_reusejp_283_:
{
return v___x_284_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sub(lean_object* v_xs_287_, lean_object* v_ys_288_){
_start:
{
lean_object* v___x_289_; 
v___x_289_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_xs_287_, v_ys_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(lean_object* v_i_292_, lean_object* v_a_293_, lean_object* v_a_294_){
_start:
{
if (lean_obj_tag(v_a_293_) == 0)
{
lean_object* v___x_295_; 
v___x_295_ = l_List_reverse___redArg(v_a_294_);
return v___x_295_;
}
else
{
lean_object* v_head_296_; lean_object* v_tail_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_306_; 
v_head_296_ = lean_ctor_get(v_a_293_, 0);
v_tail_297_ = lean_ctor_get(v_a_293_, 1);
v_isSharedCheck_306_ = !lean_is_exclusive(v_a_293_);
if (v_isSharedCheck_306_ == 0)
{
v___x_299_ = v_a_293_;
v_isShared_300_ = v_isSharedCheck_306_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_tail_297_);
lean_inc(v_head_296_);
lean_dec(v_a_293_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_306_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_303_; 
v___x_301_ = lean_int_mul(v_i_292_, v_head_296_);
lean_dec(v_head_296_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_a_294_);
lean_ctor_set(v___x_299_, 0, v___x_301_);
v___x_303_ = v___x_299_;
goto v_reusejp_302_;
}
else
{
lean_object* v_reuseFailAlloc_305_; 
v_reuseFailAlloc_305_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_305_, 0, v___x_301_);
lean_ctor_set(v_reuseFailAlloc_305_, 1, v_a_294_);
v___x_303_ = v_reuseFailAlloc_305_;
goto v_reusejp_302_;
}
v_reusejp_302_:
{
v_a_293_ = v_tail_297_;
v_a_294_ = v___x_303_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0___boxed(lean_object* v_i_307_, lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
lean_object* v_res_310_; 
v_res_310_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_307_, v_a_308_, v_a_309_);
lean_dec(v_i_307_);
return v_res_310_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul(lean_object* v_xs_311_, lean_object* v_i_312_){
_start:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = lean_box(0);
v___x_314_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_312_, v_xs_311_, v___x_313_);
return v___x_314_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul___boxed(lean_object* v_xs_315_, lean_object* v_i_316_){
_start:
{
lean_object* v_res_317_; 
v_res_317_ = l_Lean_Omega_IntList_smul(v_xs_315_, v_i_316_);
lean_dec(v_i_316_);
return v_res_317_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0(lean_object* v_i_318_, lean_object* v_xs_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Omega_IntList_smul(v_xs_319_, v_i_318_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0___boxed(lean_object* v_i_321_, lean_object* v_xs_322_){
_start:
{
lean_object* v_res_323_; 
v_res_323_ = l_Lean_Omega_IntList_instHMulInt___lam__0(v_i_321_, v_xs_322_);
lean_dec(v_i_321_);
return v_res_323_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(lean_object* v_a_326_, lean_object* v_b_327_, lean_object* v_x_328_){
_start:
{
if (lean_obj_tag(v_x_328_) == 0)
{
return v_x_328_;
}
else
{
lean_object* v_head_329_; lean_object* v_tail_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_342_; 
v_head_329_ = lean_ctor_get(v_x_328_, 0);
v_tail_330_ = lean_ctor_get(v_x_328_, 1);
v_isSharedCheck_342_ = !lean_is_exclusive(v_x_328_);
if (v_isSharedCheck_342_ == 0)
{
v___x_332_ = v_x_328_;
v_isShared_333_ = v_isSharedCheck_342_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_tail_330_);
lean_inc(v_head_329_);
lean_dec(v_x_328_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_342_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_336_; lean_object* v___x_337_; lean_object* v___x_338_; lean_object* v___x_340_; 
v___x_334_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_335_ = lean_int_mul(v_a_326_, v___x_334_);
v___x_336_ = lean_int_mul(v_b_327_, v_head_329_);
lean_dec(v_head_329_);
v___x_337_ = lean_int_add(v___x_335_, v___x_336_);
lean_dec(v___x_336_);
lean_dec(v___x_335_);
v___x_338_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_326_, v_b_327_, v_tail_330_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_338_);
lean_ctor_set(v___x_332_, 0, v___x_337_);
v___x_340_ = v___x_332_;
goto v_reusejp_339_;
}
else
{
lean_object* v_reuseFailAlloc_341_; 
v_reuseFailAlloc_341_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_341_, 0, v___x_337_);
lean_ctor_set(v_reuseFailAlloc_341_, 1, v___x_338_);
v___x_340_ = v_reuseFailAlloc_341_;
goto v_reusejp_339_;
}
v_reusejp_339_:
{
return v___x_340_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1___boxed(lean_object* v_a_343_, lean_object* v_b_344_, lean_object* v_x_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_343_, v_b_344_, v_x_345_);
lean_dec(v_b_344_);
lean_dec(v_a_343_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(lean_object* v_a_347_, lean_object* v_b_348_, lean_object* v_x_349_){
_start:
{
if (lean_obj_tag(v_x_349_) == 0)
{
return v_x_349_;
}
else
{
lean_object* v_head_350_; lean_object* v_tail_351_; lean_object* v___x_353_; uint8_t v_isShared_354_; uint8_t v_isSharedCheck_363_; 
v_head_350_ = lean_ctor_get(v_x_349_, 0);
v_tail_351_ = lean_ctor_get(v_x_349_, 1);
v_isSharedCheck_363_ = !lean_is_exclusive(v_x_349_);
if (v_isSharedCheck_363_ == 0)
{
v___x_353_ = v_x_349_;
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
else
{
lean_inc(v_tail_351_);
lean_inc(v_head_350_);
lean_dec(v_x_349_);
v___x_353_ = lean_box(0);
v_isShared_354_ = v_isSharedCheck_363_;
goto v_resetjp_352_;
}
v_resetjp_352_:
{
lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_357_; lean_object* v___x_358_; lean_object* v___x_359_; lean_object* v___x_361_; 
v___x_355_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_356_ = lean_int_mul(v_a_347_, v___x_355_);
v___x_357_ = lean_int_mul(v_b_348_, v_head_350_);
lean_dec(v_head_350_);
v___x_358_ = lean_int_add(v___x_356_, v___x_357_);
lean_dec(v___x_357_);
lean_dec(v___x_356_);
v___x_359_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_347_, v_b_348_, v_tail_351_);
if (v_isShared_354_ == 0)
{
lean_ctor_set(v___x_353_, 1, v___x_359_);
lean_ctor_set(v___x_353_, 0, v___x_358_);
v___x_361_ = v___x_353_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_359_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
return v___x_361_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0___boxed(lean_object* v_a_364_, lean_object* v_b_365_, lean_object* v_x_366_){
_start:
{
lean_object* v_res_367_; 
v_res_367_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(v_a_364_, v_b_365_, v_x_366_);
lean_dec(v_b_365_);
lean_dec(v_a_364_);
return v_res_367_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(lean_object* v_a_368_, lean_object* v_b_369_, lean_object* v_x_370_){
_start:
{
if (lean_obj_tag(v_x_370_) == 0)
{
return v_x_370_;
}
else
{
lean_object* v_head_371_; lean_object* v_tail_372_; lean_object* v___x_374_; uint8_t v_isShared_375_; uint8_t v_isSharedCheck_384_; 
v_head_371_ = lean_ctor_get(v_x_370_, 0);
v_tail_372_ = lean_ctor_get(v_x_370_, 1);
v_isSharedCheck_384_ = !lean_is_exclusive(v_x_370_);
if (v_isSharedCheck_384_ == 0)
{
v___x_374_ = v_x_370_;
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
else
{
lean_inc(v_tail_372_);
lean_inc(v_head_371_);
lean_dec(v_x_370_);
v___x_374_ = lean_box(0);
v_isShared_375_ = v_isSharedCheck_384_;
goto v_resetjp_373_;
}
v_resetjp_373_:
{
lean_object* v___x_376_; lean_object* v___x_377_; lean_object* v___x_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_382_; 
v___x_376_ = lean_int_mul(v_a_368_, v_head_371_);
lean_dec(v_head_371_);
v___x_377_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_378_ = lean_int_mul(v_b_369_, v___x_377_);
v___x_379_ = lean_int_add(v___x_376_, v___x_378_);
lean_dec(v___x_378_);
lean_dec(v___x_376_);
v___x_380_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_368_, v_b_369_, v_tail_372_);
if (v_isShared_375_ == 0)
{
lean_ctor_set(v___x_374_, 1, v___x_380_);
lean_ctor_set(v___x_374_, 0, v___x_379_);
v___x_382_ = v___x_374_;
goto v_reusejp_381_;
}
else
{
lean_object* v_reuseFailAlloc_383_; 
v_reuseFailAlloc_383_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_383_, 0, v___x_379_);
lean_ctor_set(v_reuseFailAlloc_383_, 1, v___x_380_);
v___x_382_ = v_reuseFailAlloc_383_;
goto v_reusejp_381_;
}
v_reusejp_381_:
{
return v___x_382_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3___boxed(lean_object* v_a_385_, lean_object* v_b_386_, lean_object* v_x_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_385_, v_b_386_, v_x_387_);
lean_dec(v_b_386_);
lean_dec(v_a_385_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(lean_object* v_a_389_, lean_object* v_b_390_, lean_object* v_x_391_){
_start:
{
if (lean_obj_tag(v_x_391_) == 0)
{
return v_x_391_;
}
else
{
lean_object* v_head_392_; lean_object* v_tail_393_; lean_object* v___x_395_; uint8_t v_isShared_396_; uint8_t v_isSharedCheck_405_; 
v_head_392_ = lean_ctor_get(v_x_391_, 0);
v_tail_393_ = lean_ctor_get(v_x_391_, 1);
v_isSharedCheck_405_ = !lean_is_exclusive(v_x_391_);
if (v_isSharedCheck_405_ == 0)
{
v___x_395_ = v_x_391_;
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
else
{
lean_inc(v_tail_393_);
lean_inc(v_head_392_);
lean_dec(v_x_391_);
v___x_395_ = lean_box(0);
v_isShared_396_ = v_isSharedCheck_405_;
goto v_resetjp_394_;
}
v_resetjp_394_:
{
lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_399_; lean_object* v___x_400_; lean_object* v___x_401_; lean_object* v___x_403_; 
v___x_397_ = lean_int_mul(v_a_389_, v_head_392_);
lean_dec(v_head_392_);
v___x_398_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_399_ = lean_int_mul(v_b_390_, v___x_398_);
v___x_400_ = lean_int_add(v___x_397_, v___x_399_);
lean_dec(v___x_399_);
lean_dec(v___x_397_);
v___x_401_ = l_List_map___at___00List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_389_, v_b_390_, v_tail_393_);
if (v_isShared_396_ == 0)
{
lean_ctor_set(v___x_395_, 1, v___x_401_);
lean_ctor_set(v___x_395_, 0, v___x_400_);
v___x_403_ = v___x_395_;
goto v_reusejp_402_;
}
else
{
lean_object* v_reuseFailAlloc_404_; 
v_reuseFailAlloc_404_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_404_, 0, v___x_400_);
lean_ctor_set(v_reuseFailAlloc_404_, 1, v___x_401_);
v___x_403_ = v_reuseFailAlloc_404_;
goto v_reusejp_402_;
}
v_reusejp_402_:
{
return v___x_403_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1___boxed(lean_object* v_a_406_, lean_object* v_b_407_, lean_object* v_x_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(v_a_406_, v_b_407_, v_x_408_);
lean_dec(v_b_407_);
lean_dec(v_a_406_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(lean_object* v_a_410_, lean_object* v_b_411_, lean_object* v_x_412_, lean_object* v_x_413_){
_start:
{
if (lean_obj_tag(v_x_412_) == 0)
{
lean_object* v___x_414_; 
v___x_414_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(v_a_410_, v_b_411_, v_x_413_);
return v___x_414_;
}
else
{
if (lean_obj_tag(v_x_413_) == 0)
{
lean_object* v___x_415_; 
v___x_415_ = l_List_map___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(v_a_410_, v_b_411_, v_x_412_);
return v___x_415_;
}
else
{
lean_object* v_head_416_; lean_object* v_tail_417_; lean_object* v_head_418_; lean_object* v_tail_419_; lean_object* v___x_421_; uint8_t v_isShared_422_; uint8_t v_isSharedCheck_430_; 
v_head_416_ = lean_ctor_get(v_x_412_, 0);
lean_inc(v_head_416_);
v_tail_417_ = lean_ctor_get(v_x_412_, 1);
lean_inc(v_tail_417_);
lean_dec_ref(v_x_412_);
v_head_418_ = lean_ctor_get(v_x_413_, 0);
v_tail_419_ = lean_ctor_get(v_x_413_, 1);
v_isSharedCheck_430_ = !lean_is_exclusive(v_x_413_);
if (v_isSharedCheck_430_ == 0)
{
v___x_421_ = v_x_413_;
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
else
{
lean_inc(v_tail_419_);
lean_inc(v_head_418_);
lean_dec(v_x_413_);
v___x_421_ = lean_box(0);
v_isShared_422_ = v_isSharedCheck_430_;
goto v_resetjp_420_;
}
v_resetjp_420_:
{
lean_object* v___x_423_; lean_object* v___x_424_; lean_object* v___x_425_; lean_object* v___x_426_; lean_object* v___x_428_; 
v___x_423_ = lean_int_mul(v_a_410_, v_head_416_);
lean_dec(v_head_416_);
v___x_424_ = lean_int_mul(v_b_411_, v_head_418_);
lean_dec(v_head_418_);
v___x_425_ = lean_int_add(v___x_423_, v___x_424_);
lean_dec(v___x_424_);
lean_dec(v___x_423_);
v___x_426_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_410_, v_b_411_, v_tail_417_, v_tail_419_);
if (v_isShared_422_ == 0)
{
lean_ctor_set(v___x_421_, 1, v___x_426_);
lean_ctor_set(v___x_421_, 0, v___x_425_);
v___x_428_ = v___x_421_;
goto v_reusejp_427_;
}
else
{
lean_object* v_reuseFailAlloc_429_; 
v_reuseFailAlloc_429_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_429_, 0, v___x_425_);
lean_ctor_set(v_reuseFailAlloc_429_, 1, v___x_426_);
v___x_428_ = v_reuseFailAlloc_429_;
goto v_reusejp_427_;
}
v_reusejp_427_:
{
return v___x_428_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0___boxed(lean_object* v_a_431_, lean_object* v_b_432_, lean_object* v_x_433_, lean_object* v_x_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_431_, v_b_432_, v_x_433_, v_x_434_);
lean_dec(v_b_432_);
lean_dec(v_a_431_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo(lean_object* v_a_436_, lean_object* v_xs_437_, lean_object* v_b_438_, lean_object* v_ys_439_){
_start:
{
lean_object* v___x_440_; 
v___x_440_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_436_, v_b_438_, v_xs_437_, v_ys_439_);
return v___x_440_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo___boxed(lean_object* v_a_441_, lean_object* v_xs_442_, lean_object* v_b_443_, lean_object* v_ys_444_){
_start:
{
lean_object* v_res_445_; 
v_res_445_ = l_Lean_Omega_IntList_combo(v_a_441_, v_xs_442_, v_b_443_, v_ys_444_);
lean_dec(v_b_443_);
lean_dec(v_a_441_);
return v_res_445_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(lean_object* v_init_446_, lean_object* v_x_447_){
_start:
{
if (lean_obj_tag(v_x_447_) == 0)
{
lean_inc(v_init_446_);
return v_init_446_;
}
else
{
lean_object* v_head_448_; lean_object* v_tail_449_; lean_object* v___x_450_; lean_object* v___x_451_; 
v_head_448_ = lean_ctor_get(v_x_447_, 0);
v_tail_449_ = lean_ctor_get(v_x_447_, 1);
v___x_450_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v_init_446_, v_tail_449_);
v___x_451_ = lean_int_add(v_head_448_, v___x_450_);
lean_dec(v___x_450_);
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0___boxed(lean_object* v_init_452_, lean_object* v_x_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v_init_452_, v_x_453_);
lean_dec(v_x_453_);
lean_dec(v_init_452_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sum(lean_object* v_xs_455_){
_start:
{
lean_object* v___x_456_; lean_object* v___x_457_; 
v___x_456_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_457_ = l_List_foldr___at___00Lean_Omega_IntList_sum_spec__0(v___x_456_, v_xs_455_);
return v___x_457_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sum___boxed(lean_object* v_xs_458_){
_start:
{
lean_object* v_res_459_; 
v_res_459_ = l_Lean_Omega_IntList_sum(v_xs_458_);
lean_dec(v_xs_458_);
return v_res_459_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot(lean_object* v_xs_460_, lean_object* v_ys_461_){
_start:
{
lean_object* v___x_462_; lean_object* v___x_463_; 
v___x_462_ = l_List_zipWith___at___00Lean_Omega_IntList_mul_spec__0(v_xs_460_, v_ys_461_);
v___x_463_ = l_Lean_Omega_IntList_sum(v___x_462_);
lean_dec(v___x_462_);
return v___x_463_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot___boxed(lean_object* v_xs_464_, lean_object* v_ys_465_){
_start:
{
lean_object* v_res_466_; 
v_res_466_ = l_Lean_Omega_IntList_dot(v_xs_464_, v_ys_465_);
lean_dec(v_xs_464_);
return v_res_466_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(lean_object* v_g_467_, lean_object* v_a_468_, lean_object* v_a_469_){
_start:
{
if (lean_obj_tag(v_a_468_) == 0)
{
lean_object* v___x_470_; 
v___x_470_ = l_List_reverse___redArg(v_a_469_);
return v___x_470_;
}
else
{
lean_object* v_head_471_; lean_object* v_tail_472_; lean_object* v___x_474_; uint8_t v_isShared_475_; uint8_t v_isSharedCheck_481_; 
v_head_471_ = lean_ctor_get(v_a_468_, 0);
v_tail_472_ = lean_ctor_get(v_a_468_, 1);
v_isSharedCheck_481_ = !lean_is_exclusive(v_a_468_);
if (v_isSharedCheck_481_ == 0)
{
v___x_474_ = v_a_468_;
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
else
{
lean_inc(v_tail_472_);
lean_inc(v_head_471_);
lean_dec(v_a_468_);
v___x_474_ = lean_box(0);
v_isShared_475_ = v_isSharedCheck_481_;
goto v_resetjp_473_;
}
v_resetjp_473_:
{
lean_object* v___x_476_; lean_object* v___x_478_; 
v___x_476_ = lean_int_ediv(v_head_471_, v_g_467_);
lean_dec(v_head_471_);
if (v_isShared_475_ == 0)
{
lean_ctor_set(v___x_474_, 1, v_a_469_);
lean_ctor_set(v___x_474_, 0, v___x_476_);
v___x_478_ = v___x_474_;
goto v_reusejp_477_;
}
else
{
lean_object* v_reuseFailAlloc_480_; 
v_reuseFailAlloc_480_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_480_, 0, v___x_476_);
lean_ctor_set(v_reuseFailAlloc_480_, 1, v_a_469_);
v___x_478_ = v_reuseFailAlloc_480_;
goto v_reusejp_477_;
}
v_reusejp_477_:
{
v_a_468_ = v_tail_472_;
v_a_469_ = v___x_478_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0___boxed(lean_object* v_g_482_, lean_object* v_a_483_, lean_object* v_a_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(v_g_482_, v_a_483_, v_a_484_);
lean_dec(v_g_482_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv(lean_object* v_xs_486_, lean_object* v_g_487_){
_start:
{
lean_object* v___x_488_; lean_object* v___x_489_; 
v___x_488_ = lean_box(0);
v___x_489_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(v_g_487_, v_xs_486_, v___x_488_);
return v___x_489_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv___boxed(lean_object* v_xs_490_, lean_object* v_g_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Omega_IntList_sdiv(v_xs_490_, v_g_491_);
lean_dec(v_g_491_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(lean_object* v_init_493_, lean_object* v_x_494_){
_start:
{
if (lean_obj_tag(v_x_494_) == 0)
{
lean_inc(v_init_493_);
return v_init_493_;
}
else
{
lean_object* v_head_495_; lean_object* v_tail_496_; lean_object* v___x_497_; lean_object* v___x_498_; lean_object* v___x_499_; 
v_head_495_ = lean_ctor_get(v_x_494_, 0);
v_tail_496_ = lean_ctor_get(v_x_494_, 1);
v___x_497_ = l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v_init_493_, v_tail_496_);
v___x_498_ = lean_nat_abs(v_head_495_);
v___x_499_ = lean_nat_gcd(v___x_498_, v___x_497_);
lean_dec(v___x_497_);
lean_dec(v___x_498_);
return v___x_499_;
}
}
}
LEAN_EXPORT lean_object* l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0___boxed(lean_object* v_init_500_, lean_object* v_x_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v_init_500_, v_x_501_);
lean_dec(v_x_501_);
lean_dec(v_init_500_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcd(lean_object* v_xs_503_){
_start:
{
lean_object* v___x_504_; lean_object* v___x_505_; 
v___x_504_ = lean_unsigned_to_nat(0u);
v___x_505_ = l_List_foldr___at___00Lean_Omega_IntList_gcd_spec__0(v___x_504_, v_xs_503_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcd___boxed(lean_object* v_xs_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Lean_Omega_IntList_gcd(v_xs_506_);
lean_dec(v_xs_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0(lean_object* v_m_508_, lean_object* v_x_509_){
_start:
{
lean_object* v___x_510_; 
v___x_510_ = l_Int_bmod(v_x_509_, v_m_508_);
return v___x_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0___boxed(lean_object* v_m_511_, lean_object* v_x_512_){
_start:
{
lean_object* v_res_513_; 
v_res_513_ = l_Lean_Omega_IntList_bmod___lam__0(v_m_511_, v_x_512_);
lean_dec(v_x_512_);
return v_res_513_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod(lean_object* v_x_514_, lean_object* v_m_515_){
_start:
{
lean_object* v___f_516_; lean_object* v___x_517_; lean_object* v___x_518_; 
v___f_516_ = lean_alloc_closure((void*)(l_Lean_Omega_IntList_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_516_, 0, v_m_515_);
v___x_517_ = lean_box(0);
v___x_518_ = l_List_mapTR_loop___redArg(v___f_516_, v_x_514_, v___x_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod__dot__sub__dot__bmod(lean_object* v_m_519_, lean_object* v_a_520_, lean_object* v_b_521_){
_start:
{
lean_object* v___f_522_; lean_object* v___x_523_; lean_object* v___x_524_; lean_object* v___x_525_; lean_object* v___x_526_; lean_object* v___x_527_; lean_object* v___x_528_; 
lean_inc(v_m_519_);
v___f_522_ = lean_alloc_closure((void*)(l_Lean_Omega_IntList_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_522_, 0, v_m_519_);
lean_inc(v_b_521_);
v___x_523_ = l_Lean_Omega_IntList_dot(v_a_520_, v_b_521_);
v___x_524_ = l_Int_bmod(v___x_523_, v_m_519_);
lean_dec(v___x_523_);
v___x_525_ = lean_box(0);
v___x_526_ = l_List_mapTR_loop___redArg(v___f_522_, v_a_520_, v___x_525_);
v___x_527_ = l_Lean_Omega_IntList_dot(v___x_526_, v_b_521_);
lean_dec(v___x_526_);
v___x_528_ = lean_int_sub(v___x_524_, v___x_527_);
lean_dec(v___x_527_);
lean_dec(v___x_524_);
return v___x_528_;
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
