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
lean_object* lean_int_mul(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_List_reverse___redArg(lean_object*);
lean_object* lean_int_sub(lean_object*, lean_object*);
lean_object* lean_int_add(lean_object*, lean_object*);
lean_object* l_Int_bmod(lean_object*, lean_object*);
lean_object* l_List_mapTR_loop___redArg(lean_object*, lean_object*, lean_object*);
uint8_t lean_int_dec_eq(lean_object*, lean_object*);
lean_object* lean_int_ediv(lean_object*, lean_object*);
lean_object* l_List_get_x3fInternal___redArg(lean_object*, lean_object*);
lean_object* lean_int_neg(lean_object*);
lean_object* lean_nat_abs(lean_object*);
lean_object* lean_nat_gcd(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add(lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_IntList_instAdd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_add, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_IntList_instAdd___closed__0 = (const lean_object*)&l_Lean_Omega_IntList_instAdd___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_IntList_instAdd = (const lean_object*)&l_Lean_Omega_IntList_instAdd___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mulImpl(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mulImpl___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_mulImpl_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_mulImpl_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Lean_Omega_IntList_instMul___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_mulImpl___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_IntList_instMul___closed__0 = (const lean_object*)&l_Lean_Omega_IntList_instMul___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_IntList_instMul = (const lean_object*)&l_Lean_Omega_IntList_instMul___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_neg(lean_object*);
static const lean_closure_object l_Lean_Omega_IntList_instNeg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Lean_Omega_IntList_neg, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Lean_Omega_IntList_instNeg___closed__0 = (const lean_object*)&l_Lean_Omega_IntList_instNeg___closed__0_value;
LEAN_EXPORT const lean_object* l_Lean_Omega_IntList_instNeg = (const lean_object*)&l_Lean_Omega_IntList_instNeg___closed__0_value;
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sumImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sumImpl___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_sumImpl_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_sumImpl_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcdImpl(lean_object*);
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcdImpl___boxed(lean_object*);
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
lean_dec_ref_known(v___x_94_, 1);
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
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(lean_object* v_a_99_, lean_object* v_a_100_){
_start:
{
if (lean_obj_tag(v_a_99_) == 0)
{
lean_object* v___x_101_; 
v___x_101_ = l_List_reverse___redArg(v_a_100_);
return v___x_101_;
}
else
{
lean_object* v_head_102_; lean_object* v_tail_103_; lean_object* v___x_105_; uint8_t v_isShared_106_; uint8_t v_isSharedCheck_113_; 
v_head_102_ = lean_ctor_get(v_a_99_, 0);
v_tail_103_ = lean_ctor_get(v_a_99_, 1);
v_isSharedCheck_113_ = !lean_is_exclusive(v_a_99_);
if (v_isSharedCheck_113_ == 0)
{
v___x_105_ = v_a_99_;
v_isShared_106_ = v_isSharedCheck_113_;
goto v_resetjp_104_;
}
else
{
lean_inc(v_tail_103_);
lean_inc(v_head_102_);
lean_dec(v_a_99_);
v___x_105_ = lean_box(0);
v_isShared_106_ = v_isSharedCheck_113_;
goto v_resetjp_104_;
}
v_resetjp_104_:
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_110_; 
v___x_107_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_108_ = lean_int_add(v___x_107_, v_head_102_);
lean_dec(v_head_102_);
if (v_isShared_106_ == 0)
{
lean_ctor_set(v___x_105_, 1, v_a_100_);
lean_ctor_set(v___x_105_, 0, v___x_108_);
v___x_110_ = v___x_105_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_a_100_);
v___x_110_ = v_reuseFailAlloc_112_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
v_a_99_ = v_tail_103_;
v_a_100_ = v___x_110_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(lean_object* v_a_114_, lean_object* v_a_115_){
_start:
{
if (lean_obj_tag(v_a_114_) == 0)
{
lean_object* v___x_116_; 
v___x_116_ = l_List_reverse___redArg(v_a_115_);
return v___x_116_;
}
else
{
lean_object* v_head_117_; lean_object* v_tail_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_128_; 
v_head_117_ = lean_ctor_get(v_a_114_, 0);
v_tail_118_ = lean_ctor_get(v_a_114_, 1);
v_isSharedCheck_128_ = !lean_is_exclusive(v_a_114_);
if (v_isSharedCheck_128_ == 0)
{
v___x_120_ = v_a_114_;
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_tail_118_);
lean_inc(v_head_117_);
lean_dec(v_a_114_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_128_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_123_; lean_object* v___x_125_; 
v___x_122_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_123_ = lean_int_add(v___x_122_, v_head_117_);
lean_dec(v_head_117_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v_a_115_);
lean_ctor_set(v___x_120_, 0, v___x_123_);
v___x_125_ = v___x_120_;
goto v_reusejp_124_;
}
else
{
lean_object* v_reuseFailAlloc_127_; 
v_reuseFailAlloc_127_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_127_, 0, v___x_123_);
lean_ctor_set(v_reuseFailAlloc_127_, 1, v_a_115_);
v___x_125_ = v_reuseFailAlloc_127_;
goto v_reusejp_124_;
}
v_reusejp_124_:
{
lean_object* v___x_126_; 
v___x_126_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(v_tail_118_, v___x_125_);
return v___x_126_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(lean_object* v_a_129_, lean_object* v_a_130_){
_start:
{
if (lean_obj_tag(v_a_129_) == 0)
{
lean_object* v___x_131_; 
v___x_131_ = l_List_reverse___redArg(v_a_130_);
return v___x_131_;
}
else
{
lean_object* v_head_132_; lean_object* v_tail_133_; lean_object* v___x_135_; uint8_t v_isShared_136_; uint8_t v_isSharedCheck_143_; 
v_head_132_ = lean_ctor_get(v_a_129_, 0);
v_tail_133_ = lean_ctor_get(v_a_129_, 1);
v_isSharedCheck_143_ = !lean_is_exclusive(v_a_129_);
if (v_isSharedCheck_143_ == 0)
{
v___x_135_ = v_a_129_;
v_isShared_136_ = v_isSharedCheck_143_;
goto v_resetjp_134_;
}
else
{
lean_inc(v_tail_133_);
lean_inc(v_head_132_);
lean_dec(v_a_129_);
v___x_135_ = lean_box(0);
v_isShared_136_ = v_isSharedCheck_143_;
goto v_resetjp_134_;
}
v_resetjp_134_:
{
lean_object* v___x_137_; lean_object* v___x_138_; lean_object* v___x_140_; 
v___x_137_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_138_ = lean_int_add(v_head_132_, v___x_137_);
lean_dec(v_head_132_);
if (v_isShared_136_ == 0)
{
lean_ctor_set(v___x_135_, 1, v_a_130_);
lean_ctor_set(v___x_135_, 0, v___x_138_);
v___x_140_ = v___x_135_;
goto v_reusejp_139_;
}
else
{
lean_object* v_reuseFailAlloc_142_; 
v_reuseFailAlloc_142_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_142_, 0, v___x_138_);
lean_ctor_set(v_reuseFailAlloc_142_, 1, v_a_130_);
v___x_140_ = v_reuseFailAlloc_142_;
goto v_reusejp_139_;
}
v_reusejp_139_:
{
v_a_129_ = v_tail_133_;
v_a_130_ = v___x_140_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(lean_object* v_a_144_, lean_object* v_a_145_){
_start:
{
if (lean_obj_tag(v_a_144_) == 0)
{
lean_object* v___x_146_; 
v___x_146_ = l_List_reverse___redArg(v_a_145_);
return v___x_146_;
}
else
{
lean_object* v_head_147_; lean_object* v_tail_148_; lean_object* v___x_150_; uint8_t v_isShared_151_; uint8_t v_isSharedCheck_158_; 
v_head_147_ = lean_ctor_get(v_a_144_, 0);
v_tail_148_ = lean_ctor_get(v_a_144_, 1);
v_isSharedCheck_158_ = !lean_is_exclusive(v_a_144_);
if (v_isSharedCheck_158_ == 0)
{
v___x_150_ = v_a_144_;
v_isShared_151_ = v_isSharedCheck_158_;
goto v_resetjp_149_;
}
else
{
lean_inc(v_tail_148_);
lean_inc(v_head_147_);
lean_dec(v_a_144_);
v___x_150_ = lean_box(0);
v_isShared_151_ = v_isSharedCheck_158_;
goto v_resetjp_149_;
}
v_resetjp_149_:
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_155_; 
v___x_152_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_153_ = lean_int_add(v_head_147_, v___x_152_);
lean_dec(v_head_147_);
if (v_isShared_151_ == 0)
{
lean_ctor_set(v___x_150_, 1, v_a_145_);
lean_ctor_set(v___x_150_, 0, v___x_153_);
v___x_155_ = v___x_150_;
goto v_reusejp_154_;
}
else
{
lean_object* v_reuseFailAlloc_157_; 
v_reuseFailAlloc_157_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_157_, 0, v___x_153_);
lean_ctor_set(v_reuseFailAlloc_157_, 1, v_a_145_);
v___x_155_ = v_reuseFailAlloc_157_;
goto v_reusejp_154_;
}
v_reusejp_154_:
{
lean_object* v___x_156_; 
v___x_156_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(v_tail_148_, v___x_155_);
return v___x_156_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(lean_object* v_x_159_, lean_object* v_x_160_){
_start:
{
if (lean_obj_tag(v_x_159_) == 0)
{
lean_object* v___x_161_; 
v___x_161_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(v_x_160_, v_x_159_);
return v___x_161_;
}
else
{
if (lean_obj_tag(v_x_160_) == 0)
{
lean_object* v___x_162_; 
v___x_162_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(v_x_159_, v_x_160_);
return v___x_162_;
}
else
{
lean_object* v_head_163_; lean_object* v_tail_164_; lean_object* v_head_165_; lean_object* v_tail_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_175_; 
v_head_163_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_head_163_);
v_tail_164_ = lean_ctor_get(v_x_159_, 1);
lean_inc(v_tail_164_);
lean_dec_ref_known(v_x_159_, 2);
v_head_165_ = lean_ctor_get(v_x_160_, 0);
v_tail_166_ = lean_ctor_get(v_x_160_, 1);
v_isSharedCheck_175_ = !lean_is_exclusive(v_x_160_);
if (v_isSharedCheck_175_ == 0)
{
v___x_168_ = v_x_160_;
v_isShared_169_ = v_isSharedCheck_175_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_tail_166_);
lean_inc(v_head_165_);
lean_dec(v_x_160_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_175_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_170_ = lean_int_add(v_head_163_, v_head_165_);
lean_dec(v_head_165_);
lean_dec(v_head_163_);
v___x_171_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_tail_164_, v_tail_166_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v___x_171_);
lean_ctor_set(v___x_168_, 0, v___x_170_);
v___x_173_ = v___x_168_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_174_; 
v_reuseFailAlloc_174_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_174_, 0, v___x_170_);
lean_ctor_set(v_reuseFailAlloc_174_, 1, v___x_171_);
v___x_173_ = v_reuseFailAlloc_174_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
return v___x_173_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add(lean_object* v_xs_176_, lean_object* v_ys_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_xs_176_, v_ys_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mulImpl(lean_object* v_x_181_, lean_object* v_x_182_){
_start:
{
if (lean_obj_tag(v_x_181_) == 1)
{
if (lean_obj_tag(v_x_182_) == 1)
{
lean_object* v_head_183_; lean_object* v_tail_184_; lean_object* v_head_185_; lean_object* v_tail_186_; lean_object* v___x_188_; uint8_t v_isShared_189_; uint8_t v_isSharedCheck_195_; 
v_head_183_ = lean_ctor_get(v_x_181_, 0);
v_tail_184_ = lean_ctor_get(v_x_181_, 1);
v_head_185_ = lean_ctor_get(v_x_182_, 0);
v_tail_186_ = lean_ctor_get(v_x_182_, 1);
v_isSharedCheck_195_ = !lean_is_exclusive(v_x_182_);
if (v_isSharedCheck_195_ == 0)
{
v___x_188_ = v_x_182_;
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
else
{
lean_inc(v_tail_186_);
lean_inc(v_head_185_);
lean_dec(v_x_182_);
v___x_188_ = lean_box(0);
v_isShared_189_ = v_isSharedCheck_195_;
goto v_resetjp_187_;
}
v_resetjp_187_:
{
lean_object* v___x_190_; lean_object* v___x_191_; lean_object* v___x_193_; 
v___x_190_ = lean_int_mul(v_head_183_, v_head_185_);
lean_dec(v_head_185_);
v___x_191_ = l_Lean_Omega_IntList_mulImpl(v_tail_184_, v_tail_186_);
if (v_isShared_189_ == 0)
{
lean_ctor_set(v___x_188_, 1, v___x_191_);
lean_ctor_set(v___x_188_, 0, v___x_190_);
v___x_193_ = v___x_188_;
goto v_reusejp_192_;
}
else
{
lean_object* v_reuseFailAlloc_194_; 
v_reuseFailAlloc_194_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_194_, 0, v___x_190_);
lean_ctor_set(v_reuseFailAlloc_194_, 1, v___x_191_);
v___x_193_ = v_reuseFailAlloc_194_;
goto v_reusejp_192_;
}
v_reusejp_192_:
{
return v___x_193_;
}
}
}
else
{
lean_object* v___x_196_; 
lean_dec(v_x_182_);
v___x_196_ = lean_box(0);
return v___x_196_;
}
}
else
{
lean_object* v___x_197_; 
lean_dec(v_x_182_);
v___x_197_ = lean_box(0);
return v___x_197_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mulImpl___boxed(lean_object* v_x_198_, lean_object* v_x_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_Lean_Omega_IntList_mulImpl(v_x_198_, v_x_199_);
lean_dec(v_x_198_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_mulImpl_match__1_splitter___redArg(lean_object* v_x_201_, lean_object* v_x_202_, lean_object* v_h__1_203_, lean_object* v_h__2_204_){
_start:
{
if (lean_obj_tag(v_x_201_) == 1)
{
if (lean_obj_tag(v_x_202_) == 1)
{
lean_object* v_head_205_; lean_object* v_tail_206_; lean_object* v_head_207_; lean_object* v_tail_208_; lean_object* v___x_209_; 
lean_dec(v_h__2_204_);
v_head_205_ = lean_ctor_get(v_x_201_, 0);
lean_inc(v_head_205_);
v_tail_206_ = lean_ctor_get(v_x_201_, 1);
lean_inc(v_tail_206_);
lean_dec_ref_known(v_x_201_, 2);
v_head_207_ = lean_ctor_get(v_x_202_, 0);
lean_inc(v_head_207_);
v_tail_208_ = lean_ctor_get(v_x_202_, 1);
lean_inc(v_tail_208_);
lean_dec_ref_known(v_x_202_, 2);
v___x_209_ = lean_apply_4(v_h__1_203_, v_head_205_, v_tail_206_, v_head_207_, v_tail_208_);
return v___x_209_;
}
else
{
lean_object* v___x_210_; 
lean_dec(v_h__1_203_);
v___x_210_ = lean_apply_3(v_h__2_204_, v_x_201_, v_x_202_, lean_box(0));
return v___x_210_;
}
}
else
{
lean_object* v___x_211_; 
lean_dec(v_h__1_203_);
v___x_211_ = lean_apply_3(v_h__2_204_, v_x_201_, v_x_202_, lean_box(0));
return v___x_211_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_mulImpl_match__1_splitter(lean_object* v_motive_212_, lean_object* v_x_213_, lean_object* v_x_214_, lean_object* v_h__1_215_, lean_object* v_h__2_216_){
_start:
{
if (lean_obj_tag(v_x_213_) == 1)
{
if (lean_obj_tag(v_x_214_) == 1)
{
lean_object* v_head_217_; lean_object* v_tail_218_; lean_object* v_head_219_; lean_object* v_tail_220_; lean_object* v___x_221_; 
lean_dec(v_h__2_216_);
v_head_217_ = lean_ctor_get(v_x_213_, 0);
lean_inc(v_head_217_);
v_tail_218_ = lean_ctor_get(v_x_213_, 1);
lean_inc(v_tail_218_);
lean_dec_ref_known(v_x_213_, 2);
v_head_219_ = lean_ctor_get(v_x_214_, 0);
lean_inc(v_head_219_);
v_tail_220_ = lean_ctor_get(v_x_214_, 1);
lean_inc(v_tail_220_);
lean_dec_ref_known(v_x_214_, 2);
v___x_221_ = lean_apply_4(v_h__1_215_, v_head_217_, v_tail_218_, v_head_219_, v_tail_220_);
return v___x_221_;
}
else
{
lean_object* v___x_222_; 
lean_dec(v_h__1_215_);
v___x_222_ = lean_apply_3(v_h__2_216_, v_x_213_, v_x_214_, lean_box(0));
return v___x_222_;
}
}
else
{
lean_object* v___x_223_; 
lean_dec(v_h__1_215_);
v___x_223_ = lean_apply_3(v_h__2_216_, v_x_213_, v_x_214_, lean_box(0));
return v___x_223_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(lean_object* v_a_226_, lean_object* v_a_227_){
_start:
{
if (lean_obj_tag(v_a_226_) == 0)
{
lean_object* v___x_228_; 
v___x_228_ = l_List_reverse___redArg(v_a_227_);
return v___x_228_;
}
else
{
lean_object* v_head_229_; lean_object* v_tail_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_239_; 
v_head_229_ = lean_ctor_get(v_a_226_, 0);
v_tail_230_ = lean_ctor_get(v_a_226_, 1);
v_isSharedCheck_239_ = !lean_is_exclusive(v_a_226_);
if (v_isSharedCheck_239_ == 0)
{
v___x_232_ = v_a_226_;
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_tail_230_);
lean_inc(v_head_229_);
lean_dec(v_a_226_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_239_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v___x_234_; lean_object* v___x_236_; 
v___x_234_ = lean_int_neg(v_head_229_);
lean_dec(v_head_229_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 1, v_a_227_);
lean_ctor_set(v___x_232_, 0, v___x_234_);
v___x_236_ = v___x_232_;
goto v_reusejp_235_;
}
else
{
lean_object* v_reuseFailAlloc_238_; 
v_reuseFailAlloc_238_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_238_, 0, v___x_234_);
lean_ctor_set(v_reuseFailAlloc_238_, 1, v_a_227_);
v___x_236_ = v_reuseFailAlloc_238_;
goto v_reusejp_235_;
}
v_reusejp_235_:
{
v_a_226_ = v_tail_230_;
v_a_227_ = v___x_236_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_neg(lean_object* v_xs_240_){
_start:
{
lean_object* v___x_241_; lean_object* v___x_242_; 
v___x_241_ = lean_box(0);
v___x_242_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(v_xs_240_, v___x_241_);
return v___x_242_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(lean_object* v_a_245_, lean_object* v_a_246_){
_start:
{
if (lean_obj_tag(v_a_245_) == 0)
{
lean_object* v___x_247_; 
v___x_247_ = l_List_reverse___redArg(v_a_246_);
return v___x_247_;
}
else
{
lean_object* v_head_248_; lean_object* v_tail_249_; lean_object* v___x_251_; uint8_t v_isShared_252_; uint8_t v_isSharedCheck_259_; 
v_head_248_ = lean_ctor_get(v_a_245_, 0);
v_tail_249_ = lean_ctor_get(v_a_245_, 1);
v_isSharedCheck_259_ = !lean_is_exclusive(v_a_245_);
if (v_isSharedCheck_259_ == 0)
{
v___x_251_ = v_a_245_;
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
else
{
lean_inc(v_tail_249_);
lean_inc(v_head_248_);
lean_dec(v_a_245_);
v___x_251_ = lean_box(0);
v_isShared_252_ = v_isSharedCheck_259_;
goto v_resetjp_250_;
}
v_resetjp_250_:
{
lean_object* v___x_253_; lean_object* v___x_254_; lean_object* v___x_256_; 
v___x_253_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_254_ = lean_int_sub(v_head_248_, v___x_253_);
lean_dec(v_head_248_);
if (v_isShared_252_ == 0)
{
lean_ctor_set(v___x_251_, 1, v_a_246_);
lean_ctor_set(v___x_251_, 0, v___x_254_);
v___x_256_ = v___x_251_;
goto v_reusejp_255_;
}
else
{
lean_object* v_reuseFailAlloc_258_; 
v_reuseFailAlloc_258_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_258_, 0, v___x_254_);
lean_ctor_set(v_reuseFailAlloc_258_, 1, v_a_246_);
v___x_256_ = v_reuseFailAlloc_258_;
goto v_reusejp_255_;
}
v_reusejp_255_:
{
v_a_245_ = v_tail_249_;
v_a_246_ = v___x_256_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(lean_object* v_a_260_, lean_object* v_a_261_){
_start:
{
if (lean_obj_tag(v_a_260_) == 0)
{
lean_object* v___x_262_; 
v___x_262_ = l_List_reverse___redArg(v_a_261_);
return v___x_262_;
}
else
{
lean_object* v_head_263_; lean_object* v_tail_264_; lean_object* v___x_266_; uint8_t v_isShared_267_; uint8_t v_isSharedCheck_274_; 
v_head_263_ = lean_ctor_get(v_a_260_, 0);
v_tail_264_ = lean_ctor_get(v_a_260_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_a_260_);
if (v_isSharedCheck_274_ == 0)
{
v___x_266_ = v_a_260_;
v_isShared_267_ = v_isSharedCheck_274_;
goto v_resetjp_265_;
}
else
{
lean_inc(v_tail_264_);
lean_inc(v_head_263_);
lean_dec(v_a_260_);
v___x_266_ = lean_box(0);
v_isShared_267_ = v_isSharedCheck_274_;
goto v_resetjp_265_;
}
v_resetjp_265_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
v___x_268_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_269_ = lean_int_sub(v_head_263_, v___x_268_);
lean_dec(v_head_263_);
if (v_isShared_267_ == 0)
{
lean_ctor_set(v___x_266_, 1, v_a_261_);
lean_ctor_set(v___x_266_, 0, v___x_269_);
v___x_271_ = v___x_266_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_269_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_a_261_);
v___x_271_ = v_reuseFailAlloc_273_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; 
v___x_272_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(v_tail_264_, v___x_271_);
return v___x_272_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(lean_object* v_a_275_, lean_object* v_a_276_){
_start:
{
if (lean_obj_tag(v_a_275_) == 0)
{
lean_object* v___x_277_; 
v___x_277_ = l_List_reverse___redArg(v_a_276_);
return v___x_277_;
}
else
{
lean_object* v_head_278_; lean_object* v_tail_279_; lean_object* v___x_281_; uint8_t v_isShared_282_; uint8_t v_isSharedCheck_289_; 
v_head_278_ = lean_ctor_get(v_a_275_, 0);
v_tail_279_ = lean_ctor_get(v_a_275_, 1);
v_isSharedCheck_289_ = !lean_is_exclusive(v_a_275_);
if (v_isSharedCheck_289_ == 0)
{
v___x_281_ = v_a_275_;
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
else
{
lean_inc(v_tail_279_);
lean_inc(v_head_278_);
lean_dec(v_a_275_);
v___x_281_ = lean_box(0);
v_isShared_282_ = v_isSharedCheck_289_;
goto v_resetjp_280_;
}
v_resetjp_280_:
{
lean_object* v___x_283_; lean_object* v___x_284_; lean_object* v___x_286_; 
v___x_283_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_284_ = lean_int_sub(v___x_283_, v_head_278_);
lean_dec(v_head_278_);
if (v_isShared_282_ == 0)
{
lean_ctor_set(v___x_281_, 1, v_a_276_);
lean_ctor_set(v___x_281_, 0, v___x_284_);
v___x_286_ = v___x_281_;
goto v_reusejp_285_;
}
else
{
lean_object* v_reuseFailAlloc_288_; 
v_reuseFailAlloc_288_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_288_, 0, v___x_284_);
lean_ctor_set(v_reuseFailAlloc_288_, 1, v_a_276_);
v___x_286_ = v_reuseFailAlloc_288_;
goto v_reusejp_285_;
}
v_reusejp_285_:
{
v_a_275_ = v_tail_279_;
v_a_276_ = v___x_286_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(lean_object* v_a_290_, lean_object* v_a_291_){
_start:
{
if (lean_obj_tag(v_a_290_) == 0)
{
lean_object* v___x_292_; 
v___x_292_ = l_List_reverse___redArg(v_a_291_);
return v___x_292_;
}
else
{
lean_object* v_head_293_; lean_object* v_tail_294_; lean_object* v___x_296_; uint8_t v_isShared_297_; uint8_t v_isSharedCheck_304_; 
v_head_293_ = lean_ctor_get(v_a_290_, 0);
v_tail_294_ = lean_ctor_get(v_a_290_, 1);
v_isSharedCheck_304_ = !lean_is_exclusive(v_a_290_);
if (v_isSharedCheck_304_ == 0)
{
v___x_296_ = v_a_290_;
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
else
{
lean_inc(v_tail_294_);
lean_inc(v_head_293_);
lean_dec(v_a_290_);
v___x_296_ = lean_box(0);
v_isShared_297_ = v_isSharedCheck_304_;
goto v_resetjp_295_;
}
v_resetjp_295_:
{
lean_object* v___x_298_; lean_object* v___x_299_; lean_object* v___x_301_; 
v___x_298_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_299_ = lean_int_sub(v___x_298_, v_head_293_);
lean_dec(v_head_293_);
if (v_isShared_297_ == 0)
{
lean_ctor_set(v___x_296_, 1, v_a_291_);
lean_ctor_set(v___x_296_, 0, v___x_299_);
v___x_301_ = v___x_296_;
goto v_reusejp_300_;
}
else
{
lean_object* v_reuseFailAlloc_303_; 
v_reuseFailAlloc_303_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_303_, 0, v___x_299_);
lean_ctor_set(v_reuseFailAlloc_303_, 1, v_a_291_);
v___x_301_ = v_reuseFailAlloc_303_;
goto v_reusejp_300_;
}
v_reusejp_300_:
{
lean_object* v___x_302_; 
v___x_302_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(v_tail_294_, v___x_301_);
return v___x_302_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(lean_object* v_x_305_, lean_object* v_x_306_){
_start:
{
if (lean_obj_tag(v_x_305_) == 0)
{
lean_object* v___x_307_; 
v___x_307_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(v_x_306_, v_x_305_);
return v___x_307_;
}
else
{
if (lean_obj_tag(v_x_306_) == 0)
{
lean_object* v___x_308_; 
v___x_308_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(v_x_305_, v_x_306_);
return v___x_308_;
}
else
{
lean_object* v_head_309_; lean_object* v_tail_310_; lean_object* v_head_311_; lean_object* v_tail_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_321_; 
v_head_309_ = lean_ctor_get(v_x_305_, 0);
lean_inc(v_head_309_);
v_tail_310_ = lean_ctor_get(v_x_305_, 1);
lean_inc(v_tail_310_);
lean_dec_ref_known(v_x_305_, 2);
v_head_311_ = lean_ctor_get(v_x_306_, 0);
v_tail_312_ = lean_ctor_get(v_x_306_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_x_306_);
if (v_isSharedCheck_321_ == 0)
{
v___x_314_ = v_x_306_;
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_tail_312_);
lean_inc(v_head_311_);
lean_dec(v_x_306_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_321_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_316_ = lean_int_sub(v_head_309_, v_head_311_);
lean_dec(v_head_311_);
lean_dec(v_head_309_);
v___x_317_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_tail_310_, v_tail_312_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v___x_317_);
lean_ctor_set(v___x_314_, 0, v___x_316_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v___x_316_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___x_317_);
v___x_319_ = v_reuseFailAlloc_320_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
return v___x_319_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sub(lean_object* v_xs_322_, lean_object* v_ys_323_){
_start:
{
lean_object* v___x_324_; 
v___x_324_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_xs_322_, v_ys_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(lean_object* v_i_327_, lean_object* v_a_328_, lean_object* v_a_329_){
_start:
{
if (lean_obj_tag(v_a_328_) == 0)
{
lean_object* v___x_330_; 
v___x_330_ = l_List_reverse___redArg(v_a_329_);
return v___x_330_;
}
else
{
lean_object* v_head_331_; lean_object* v_tail_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_341_; 
v_head_331_ = lean_ctor_get(v_a_328_, 0);
v_tail_332_ = lean_ctor_get(v_a_328_, 1);
v_isSharedCheck_341_ = !lean_is_exclusive(v_a_328_);
if (v_isSharedCheck_341_ == 0)
{
v___x_334_ = v_a_328_;
v_isShared_335_ = v_isSharedCheck_341_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_tail_332_);
lean_inc(v_head_331_);
lean_dec(v_a_328_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_341_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v___x_336_; lean_object* v___x_338_; 
v___x_336_ = lean_int_mul(v_i_327_, v_head_331_);
lean_dec(v_head_331_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 1, v_a_329_);
lean_ctor_set(v___x_334_, 0, v___x_336_);
v___x_338_ = v___x_334_;
goto v_reusejp_337_;
}
else
{
lean_object* v_reuseFailAlloc_340_; 
v_reuseFailAlloc_340_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_340_, 0, v___x_336_);
lean_ctor_set(v_reuseFailAlloc_340_, 1, v_a_329_);
v___x_338_ = v_reuseFailAlloc_340_;
goto v_reusejp_337_;
}
v_reusejp_337_:
{
v_a_328_ = v_tail_332_;
v_a_329_ = v___x_338_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0___boxed(lean_object* v_i_342_, lean_object* v_a_343_, lean_object* v_a_344_){
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_342_, v_a_343_, v_a_344_);
lean_dec(v_i_342_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul(lean_object* v_xs_346_, lean_object* v_i_347_){
_start:
{
lean_object* v___x_348_; lean_object* v___x_349_; 
v___x_348_ = lean_box(0);
v___x_349_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_347_, v_xs_346_, v___x_348_);
return v___x_349_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul___boxed(lean_object* v_xs_350_, lean_object* v_i_351_){
_start:
{
lean_object* v_res_352_; 
v_res_352_ = l_Lean_Omega_IntList_smul(v_xs_350_, v_i_351_);
lean_dec(v_i_351_);
return v_res_352_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0(lean_object* v_i_353_, lean_object* v_xs_354_){
_start:
{
lean_object* v___x_355_; 
v___x_355_ = l_Lean_Omega_IntList_smul(v_xs_354_, v_i_353_);
return v___x_355_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0___boxed(lean_object* v_i_356_, lean_object* v_xs_357_){
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Lean_Omega_IntList_instHMulInt___lam__0(v_i_356_, v_xs_357_);
lean_dec(v_i_356_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(lean_object* v_a_361_, lean_object* v_b_362_, lean_object* v_a_363_, lean_object* v_a_364_){
_start:
{
if (lean_obj_tag(v_a_363_) == 0)
{
lean_object* v___x_365_; 
v___x_365_ = l_List_reverse___redArg(v_a_364_);
return v___x_365_;
}
else
{
lean_object* v_head_366_; lean_object* v_tail_367_; lean_object* v___x_369_; uint8_t v_isShared_370_; uint8_t v_isSharedCheck_379_; 
v_head_366_ = lean_ctor_get(v_a_363_, 0);
v_tail_367_ = lean_ctor_get(v_a_363_, 1);
v_isSharedCheck_379_ = !lean_is_exclusive(v_a_363_);
if (v_isSharedCheck_379_ == 0)
{
v___x_369_ = v_a_363_;
v_isShared_370_ = v_isSharedCheck_379_;
goto v_resetjp_368_;
}
else
{
lean_inc(v_tail_367_);
lean_inc(v_head_366_);
lean_dec(v_a_363_);
v___x_369_ = lean_box(0);
v_isShared_370_ = v_isSharedCheck_379_;
goto v_resetjp_368_;
}
v_resetjp_368_:
{
lean_object* v___x_371_; lean_object* v___x_372_; lean_object* v___x_373_; lean_object* v___x_374_; lean_object* v___x_376_; 
v___x_371_ = lean_int_mul(v_a_361_, v_head_366_);
lean_dec(v_head_366_);
v___x_372_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_373_ = lean_int_mul(v_b_362_, v___x_372_);
v___x_374_ = lean_int_add(v___x_371_, v___x_373_);
lean_dec(v___x_373_);
lean_dec(v___x_371_);
if (v_isShared_370_ == 0)
{
lean_ctor_set(v___x_369_, 1, v_a_364_);
lean_ctor_set(v___x_369_, 0, v___x_374_);
v___x_376_ = v___x_369_;
goto v_reusejp_375_;
}
else
{
lean_object* v_reuseFailAlloc_378_; 
v_reuseFailAlloc_378_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_378_, 0, v___x_374_);
lean_ctor_set(v_reuseFailAlloc_378_, 1, v_a_364_);
v___x_376_ = v_reuseFailAlloc_378_;
goto v_reusejp_375_;
}
v_reusejp_375_:
{
v_a_363_ = v_tail_367_;
v_a_364_ = v___x_376_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3___boxed(lean_object* v_a_380_, lean_object* v_b_381_, lean_object* v_a_382_, lean_object* v_a_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_380_, v_b_381_, v_a_382_, v_a_383_);
lean_dec(v_b_381_);
lean_dec(v_a_380_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(lean_object* v_a_385_, lean_object* v_b_386_, lean_object* v_a_387_, lean_object* v_a_388_){
_start:
{
if (lean_obj_tag(v_a_387_) == 0)
{
lean_object* v___x_389_; 
v___x_389_ = l_List_reverse___redArg(v_a_388_);
return v___x_389_;
}
else
{
lean_object* v_head_390_; lean_object* v_tail_391_; lean_object* v___x_393_; uint8_t v_isShared_394_; uint8_t v_isSharedCheck_403_; 
v_head_390_ = lean_ctor_get(v_a_387_, 0);
v_tail_391_ = lean_ctor_get(v_a_387_, 1);
v_isSharedCheck_403_ = !lean_is_exclusive(v_a_387_);
if (v_isSharedCheck_403_ == 0)
{
v___x_393_ = v_a_387_;
v_isShared_394_ = v_isSharedCheck_403_;
goto v_resetjp_392_;
}
else
{
lean_inc(v_tail_391_);
lean_inc(v_head_390_);
lean_dec(v_a_387_);
v___x_393_ = lean_box(0);
v_isShared_394_ = v_isSharedCheck_403_;
goto v_resetjp_392_;
}
v_resetjp_392_:
{
lean_object* v___x_395_; lean_object* v___x_396_; lean_object* v___x_397_; lean_object* v___x_398_; lean_object* v___x_400_; 
v___x_395_ = lean_int_mul(v_a_385_, v_head_390_);
lean_dec(v_head_390_);
v___x_396_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_397_ = lean_int_mul(v_b_386_, v___x_396_);
v___x_398_ = lean_int_add(v___x_395_, v___x_397_);
lean_dec(v___x_397_);
lean_dec(v___x_395_);
if (v_isShared_394_ == 0)
{
lean_ctor_set(v___x_393_, 1, v_a_388_);
lean_ctor_set(v___x_393_, 0, v___x_398_);
v___x_400_ = v___x_393_;
goto v_reusejp_399_;
}
else
{
lean_object* v_reuseFailAlloc_402_; 
v_reuseFailAlloc_402_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_402_, 0, v___x_398_);
lean_ctor_set(v_reuseFailAlloc_402_, 1, v_a_388_);
v___x_400_ = v_reuseFailAlloc_402_;
goto v_reusejp_399_;
}
v_reusejp_399_:
{
lean_object* v___x_401_; 
v___x_401_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_385_, v_b_386_, v_tail_391_, v___x_400_);
return v___x_401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1___boxed(lean_object* v_a_404_, lean_object* v_b_405_, lean_object* v_a_406_, lean_object* v_a_407_){
_start:
{
lean_object* v_res_408_; 
v_res_408_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(v_a_404_, v_b_405_, v_a_406_, v_a_407_);
lean_dec(v_b_405_);
lean_dec(v_a_404_);
return v_res_408_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(lean_object* v_a_409_, lean_object* v_b_410_, lean_object* v_a_411_, lean_object* v_a_412_){
_start:
{
if (lean_obj_tag(v_a_411_) == 0)
{
lean_object* v___x_413_; 
v___x_413_ = l_List_reverse___redArg(v_a_412_);
return v___x_413_;
}
else
{
lean_object* v_head_414_; lean_object* v_tail_415_; lean_object* v___x_417_; uint8_t v_isShared_418_; uint8_t v_isSharedCheck_427_; 
v_head_414_ = lean_ctor_get(v_a_411_, 0);
v_tail_415_ = lean_ctor_get(v_a_411_, 1);
v_isSharedCheck_427_ = !lean_is_exclusive(v_a_411_);
if (v_isSharedCheck_427_ == 0)
{
v___x_417_ = v_a_411_;
v_isShared_418_ = v_isSharedCheck_427_;
goto v_resetjp_416_;
}
else
{
lean_inc(v_tail_415_);
lean_inc(v_head_414_);
lean_dec(v_a_411_);
v___x_417_ = lean_box(0);
v_isShared_418_ = v_isSharedCheck_427_;
goto v_resetjp_416_;
}
v_resetjp_416_:
{
lean_object* v___x_419_; lean_object* v___x_420_; lean_object* v___x_421_; lean_object* v___x_422_; lean_object* v___x_424_; 
v___x_419_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_420_ = lean_int_mul(v_a_409_, v___x_419_);
v___x_421_ = lean_int_mul(v_b_410_, v_head_414_);
lean_dec(v_head_414_);
v___x_422_ = lean_int_add(v___x_420_, v___x_421_);
lean_dec(v___x_421_);
lean_dec(v___x_420_);
if (v_isShared_418_ == 0)
{
lean_ctor_set(v___x_417_, 1, v_a_412_);
lean_ctor_set(v___x_417_, 0, v___x_422_);
v___x_424_ = v___x_417_;
goto v_reusejp_423_;
}
else
{
lean_object* v_reuseFailAlloc_426_; 
v_reuseFailAlloc_426_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_426_, 0, v___x_422_);
lean_ctor_set(v_reuseFailAlloc_426_, 1, v_a_412_);
v___x_424_ = v_reuseFailAlloc_426_;
goto v_reusejp_423_;
}
v_reusejp_423_:
{
v_a_411_ = v_tail_415_;
v_a_412_ = v___x_424_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1___boxed(lean_object* v_a_428_, lean_object* v_b_429_, lean_object* v_a_430_, lean_object* v_a_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_428_, v_b_429_, v_a_430_, v_a_431_);
lean_dec(v_b_429_);
lean_dec(v_a_428_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(lean_object* v_a_433_, lean_object* v_b_434_, lean_object* v_a_435_, lean_object* v_a_436_){
_start:
{
if (lean_obj_tag(v_a_435_) == 0)
{
lean_object* v___x_437_; 
v___x_437_ = l_List_reverse___redArg(v_a_436_);
return v___x_437_;
}
else
{
lean_object* v_head_438_; lean_object* v_tail_439_; lean_object* v___x_441_; uint8_t v_isShared_442_; uint8_t v_isSharedCheck_451_; 
v_head_438_ = lean_ctor_get(v_a_435_, 0);
v_tail_439_ = lean_ctor_get(v_a_435_, 1);
v_isSharedCheck_451_ = !lean_is_exclusive(v_a_435_);
if (v_isSharedCheck_451_ == 0)
{
v___x_441_ = v_a_435_;
v_isShared_442_ = v_isSharedCheck_451_;
goto v_resetjp_440_;
}
else
{
lean_inc(v_tail_439_);
lean_inc(v_head_438_);
lean_dec(v_a_435_);
v___x_441_ = lean_box(0);
v_isShared_442_ = v_isSharedCheck_451_;
goto v_resetjp_440_;
}
v_resetjp_440_:
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_443_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_444_ = lean_int_mul(v_a_433_, v___x_443_);
v___x_445_ = lean_int_mul(v_b_434_, v_head_438_);
lean_dec(v_head_438_);
v___x_446_ = lean_int_add(v___x_444_, v___x_445_);
lean_dec(v___x_445_);
lean_dec(v___x_444_);
if (v_isShared_442_ == 0)
{
lean_ctor_set(v___x_441_, 1, v_a_436_);
lean_ctor_set(v___x_441_, 0, v___x_446_);
v___x_448_ = v___x_441_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v_a_436_);
v___x_448_ = v_reuseFailAlloc_450_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_449_; 
v___x_449_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_433_, v_b_434_, v_tail_439_, v___x_448_);
return v___x_449_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0___boxed(lean_object* v_a_452_, lean_object* v_b_453_, lean_object* v_a_454_, lean_object* v_a_455_){
_start:
{
lean_object* v_res_456_; 
v_res_456_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(v_a_452_, v_b_453_, v_a_454_, v_a_455_);
lean_dec(v_b_453_);
lean_dec(v_a_452_);
return v_res_456_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(lean_object* v_a_457_, lean_object* v_b_458_, lean_object* v_x_459_, lean_object* v_x_460_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_object* v___x_461_; 
v___x_461_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(v_a_457_, v_b_458_, v_x_460_, v_x_459_);
return v___x_461_;
}
else
{
if (lean_obj_tag(v_x_460_) == 0)
{
lean_object* v___x_462_; 
v___x_462_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(v_a_457_, v_b_458_, v_x_459_, v_x_460_);
return v___x_462_;
}
else
{
lean_object* v_head_463_; lean_object* v_tail_464_; lean_object* v_head_465_; lean_object* v_tail_466_; lean_object* v___x_468_; uint8_t v_isShared_469_; uint8_t v_isSharedCheck_477_; 
v_head_463_ = lean_ctor_get(v_x_459_, 0);
lean_inc(v_head_463_);
v_tail_464_ = lean_ctor_get(v_x_459_, 1);
lean_inc(v_tail_464_);
lean_dec_ref_known(v_x_459_, 2);
v_head_465_ = lean_ctor_get(v_x_460_, 0);
v_tail_466_ = lean_ctor_get(v_x_460_, 1);
v_isSharedCheck_477_ = !lean_is_exclusive(v_x_460_);
if (v_isSharedCheck_477_ == 0)
{
v___x_468_ = v_x_460_;
v_isShared_469_ = v_isSharedCheck_477_;
goto v_resetjp_467_;
}
else
{
lean_inc(v_tail_466_);
lean_inc(v_head_465_);
lean_dec(v_x_460_);
v___x_468_ = lean_box(0);
v_isShared_469_ = v_isSharedCheck_477_;
goto v_resetjp_467_;
}
v_resetjp_467_:
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_470_ = lean_int_mul(v_a_457_, v_head_463_);
lean_dec(v_head_463_);
v___x_471_ = lean_int_mul(v_b_458_, v_head_465_);
lean_dec(v_head_465_);
v___x_472_ = lean_int_add(v___x_470_, v___x_471_);
lean_dec(v___x_471_);
lean_dec(v___x_470_);
v___x_473_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_457_, v_b_458_, v_tail_464_, v_tail_466_);
if (v_isShared_469_ == 0)
{
lean_ctor_set(v___x_468_, 1, v___x_473_);
lean_ctor_set(v___x_468_, 0, v___x_472_);
v___x_475_ = v___x_468_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_476_; 
v_reuseFailAlloc_476_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_476_, 0, v___x_472_);
lean_ctor_set(v_reuseFailAlloc_476_, 1, v___x_473_);
v___x_475_ = v_reuseFailAlloc_476_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
return v___x_475_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0___boxed(lean_object* v_a_478_, lean_object* v_b_479_, lean_object* v_x_480_, lean_object* v_x_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_478_, v_b_479_, v_x_480_, v_x_481_);
lean_dec(v_b_479_);
lean_dec(v_a_478_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo(lean_object* v_a_483_, lean_object* v_xs_484_, lean_object* v_b_485_, lean_object* v_ys_486_){
_start:
{
lean_object* v___x_487_; 
v___x_487_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_483_, v_b_485_, v_xs_484_, v_ys_486_);
return v___x_487_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo___boxed(lean_object* v_a_488_, lean_object* v_xs_489_, lean_object* v_b_490_, lean_object* v_ys_491_){
_start:
{
lean_object* v_res_492_; 
v_res_492_ = l_Lean_Omega_IntList_combo(v_a_488_, v_xs_489_, v_b_490_, v_ys_491_);
lean_dec(v_b_490_);
lean_dec(v_a_488_);
return v_res_492_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sumImpl(lean_object* v_x_493_){
_start:
{
if (lean_obj_tag(v_x_493_) == 0)
{
lean_object* v___x_494_; 
v___x_494_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
return v___x_494_;
}
else
{
lean_object* v_head_495_; lean_object* v_tail_496_; lean_object* v___x_497_; lean_object* v___x_498_; 
v_head_495_ = lean_ctor_get(v_x_493_, 0);
v_tail_496_ = lean_ctor_get(v_x_493_, 1);
v___x_497_ = l_Lean_Omega_IntList_sumImpl(v_tail_496_);
v___x_498_ = lean_int_add(v_head_495_, v___x_497_);
lean_dec(v___x_497_);
return v___x_498_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sumImpl___boxed(lean_object* v_x_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Omega_IntList_sumImpl(v_x_499_);
lean_dec(v_x_499_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_sumImpl_match__1_splitter___redArg(lean_object* v_x_501_, lean_object* v_h__1_502_, lean_object* v_h__2_503_){
_start:
{
if (lean_obj_tag(v_x_501_) == 0)
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v_h__2_503_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_apply_1(v_h__1_502_, v___x_504_);
return v___x_505_;
}
else
{
lean_object* v_head_506_; lean_object* v_tail_507_; lean_object* v___x_508_; 
lean_dec(v_h__1_502_);
v_head_506_ = lean_ctor_get(v_x_501_, 0);
lean_inc(v_head_506_);
v_tail_507_ = lean_ctor_get(v_x_501_, 1);
lean_inc(v_tail_507_);
lean_dec_ref_known(v_x_501_, 2);
v___x_508_ = lean_apply_2(v_h__2_503_, v_head_506_, v_tail_507_);
return v___x_508_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_sumImpl_match__1_splitter(lean_object* v_motive_509_, lean_object* v_x_510_, lean_object* v_h__1_511_, lean_object* v_h__2_512_){
_start:
{
if (lean_obj_tag(v_x_510_) == 0)
{
lean_object* v___x_513_; lean_object* v___x_514_; 
lean_dec(v_h__2_512_);
v___x_513_ = lean_box(0);
v___x_514_ = lean_apply_1(v_h__1_511_, v___x_513_);
return v___x_514_;
}
else
{
lean_object* v_head_515_; lean_object* v_tail_516_; lean_object* v___x_517_; 
lean_dec(v_h__1_511_);
v_head_515_ = lean_ctor_get(v_x_510_, 0);
lean_inc(v_head_515_);
v_tail_516_ = lean_ctor_get(v_x_510_, 1);
lean_inc(v_tail_516_);
lean_dec_ref_known(v_x_510_, 2);
v___x_517_ = lean_apply_2(v_h__2_512_, v_head_515_, v_tail_516_);
return v___x_517_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot(lean_object* v_xs_518_, lean_object* v_ys_519_){
_start:
{
lean_object* v___x_520_; lean_object* v___x_521_; 
v___x_520_ = l_Lean_Omega_IntList_mulImpl(v_xs_518_, v_ys_519_);
v___x_521_ = l_Lean_Omega_IntList_sumImpl(v___x_520_);
lean_dec(v___x_520_);
return v___x_521_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot___boxed(lean_object* v_xs_522_, lean_object* v_ys_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Lean_Omega_IntList_dot(v_xs_522_, v_ys_523_);
lean_dec(v_xs_522_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(lean_object* v_g_525_, lean_object* v_a_526_, lean_object* v_a_527_){
_start:
{
if (lean_obj_tag(v_a_526_) == 0)
{
lean_object* v___x_528_; 
v___x_528_ = l_List_reverse___redArg(v_a_527_);
return v___x_528_;
}
else
{
lean_object* v_head_529_; lean_object* v_tail_530_; lean_object* v___x_532_; uint8_t v_isShared_533_; uint8_t v_isSharedCheck_539_; 
v_head_529_ = lean_ctor_get(v_a_526_, 0);
v_tail_530_ = lean_ctor_get(v_a_526_, 1);
v_isSharedCheck_539_ = !lean_is_exclusive(v_a_526_);
if (v_isSharedCheck_539_ == 0)
{
v___x_532_ = v_a_526_;
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
else
{
lean_inc(v_tail_530_);
lean_inc(v_head_529_);
lean_dec(v_a_526_);
v___x_532_ = lean_box(0);
v_isShared_533_ = v_isSharedCheck_539_;
goto v_resetjp_531_;
}
v_resetjp_531_:
{
lean_object* v___x_534_; lean_object* v___x_536_; 
v___x_534_ = lean_int_ediv(v_head_529_, v_g_525_);
lean_dec(v_head_529_);
if (v_isShared_533_ == 0)
{
lean_ctor_set(v___x_532_, 1, v_a_527_);
lean_ctor_set(v___x_532_, 0, v___x_534_);
v___x_536_ = v___x_532_;
goto v_reusejp_535_;
}
else
{
lean_object* v_reuseFailAlloc_538_; 
v_reuseFailAlloc_538_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_538_, 0, v___x_534_);
lean_ctor_set(v_reuseFailAlloc_538_, 1, v_a_527_);
v___x_536_ = v_reuseFailAlloc_538_;
goto v_reusejp_535_;
}
v_reusejp_535_:
{
v_a_526_ = v_tail_530_;
v_a_527_ = v___x_536_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0___boxed(lean_object* v_g_540_, lean_object* v_a_541_, lean_object* v_a_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(v_g_540_, v_a_541_, v_a_542_);
lean_dec(v_g_540_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv(lean_object* v_xs_544_, lean_object* v_g_545_){
_start:
{
lean_object* v___x_546_; lean_object* v___x_547_; 
v___x_546_ = lean_box(0);
v___x_547_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(v_g_545_, v_xs_544_, v___x_546_);
return v___x_547_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv___boxed(lean_object* v_xs_548_, lean_object* v_g_549_){
_start:
{
lean_object* v_res_550_; 
v_res_550_ = l_Lean_Omega_IntList_sdiv(v_xs_548_, v_g_549_);
lean_dec(v_g_549_);
return v_res_550_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcdImpl(lean_object* v_x_551_){
_start:
{
if (lean_obj_tag(v_x_551_) == 0)
{
lean_object* v___x_552_; 
v___x_552_ = lean_unsigned_to_nat(0u);
return v___x_552_;
}
else
{
lean_object* v_head_553_; lean_object* v_tail_554_; lean_object* v___x_555_; lean_object* v___x_556_; lean_object* v___x_557_; 
v_head_553_ = lean_ctor_get(v_x_551_, 0);
v_tail_554_ = lean_ctor_get(v_x_551_, 1);
v___x_555_ = lean_nat_abs(v_head_553_);
v___x_556_ = l_Lean_Omega_IntList_gcdImpl(v_tail_554_);
v___x_557_ = lean_nat_gcd(v___x_555_, v___x_556_);
lean_dec(v___x_556_);
lean_dec(v___x_555_);
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcdImpl___boxed(lean_object* v_x_558_){
_start:
{
lean_object* v_res_559_; 
v_res_559_ = l_Lean_Omega_IntList_gcdImpl(v_x_558_);
lean_dec(v_x_558_);
return v_res_559_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0(lean_object* v_m_560_, lean_object* v_x_561_){
_start:
{
lean_object* v___x_562_; 
v___x_562_ = l_Int_bmod(v_x_561_, v_m_560_);
return v___x_562_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0___boxed(lean_object* v_m_563_, lean_object* v_x_564_){
_start:
{
lean_object* v_res_565_; 
v_res_565_ = l_Lean_Omega_IntList_bmod___lam__0(v_m_563_, v_x_564_);
lean_dec(v_x_564_);
return v_res_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod(lean_object* v_x_566_, lean_object* v_m_567_){
_start:
{
lean_object* v___f_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v___f_568_ = lean_alloc_closure((void*)(l_Lean_Omega_IntList_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_568_, 0, v_m_567_);
v___x_569_ = lean_box(0);
v___x_570_ = l_List_mapTR_loop___redArg(v___f_568_, v_x_566_, v___x_569_);
return v___x_570_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod__dot__sub__dot__bmod(lean_object* v_m_571_, lean_object* v_a_572_, lean_object* v_b_573_){
_start:
{
lean_object* v___f_574_; lean_object* v___x_575_; lean_object* v___x_576_; lean_object* v___x_577_; lean_object* v___x_578_; lean_object* v___x_579_; lean_object* v___x_580_; 
lean_inc(v_m_571_);
v___f_574_ = lean_alloc_closure((void*)(l_Lean_Omega_IntList_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_574_, 0, v_m_571_);
lean_inc(v_b_573_);
v___x_575_ = l_Lean_Omega_IntList_dot(v_a_572_, v_b_573_);
v___x_576_ = l_Int_bmod(v___x_575_, v_m_571_);
lean_dec(v___x_575_);
v___x_577_ = lean_box(0);
v___x_578_ = l_List_mapTR_loop___redArg(v___f_574_, v_a_572_, v___x_577_);
v___x_579_ = l_Lean_Omega_IntList_dot(v___x_578_, v_b_573_);
lean_dec(v___x_578_);
v___x_580_ = lean_int_sub(v___x_576_, v___x_579_);
lean_dec(v___x_579_);
lean_dec(v___x_576_);
return v___x_580_;
}
}
lean_object* runtime_initialize_Init_Data_Int_DivMod_Bootstrap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Gcd(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Int_Order(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Nat_Dvd(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_RCases(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Omega_IntList(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
