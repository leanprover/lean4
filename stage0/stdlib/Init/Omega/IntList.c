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
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__instDecidableEqList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__instDecidableEqList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__instDecidableEqList_match__1_splitter___redArg(lean_object* v_ys_41_, lean_object* v_h__1_42_, lean_object* v_h__2_43_){
_start:
{
if (lean_obj_tag(v_ys_41_) == 0)
{
lean_object* v___x_44_; lean_object* v___x_45_; 
lean_dec(v_h__2_43_);
v___x_44_ = lean_box(0);
v___x_45_ = lean_apply_1(v_h__1_42_, v___x_44_);
return v___x_45_;
}
else
{
lean_object* v_head_46_; lean_object* v_tail_47_; lean_object* v___x_48_; 
lean_dec(v_h__1_42_);
v_head_46_ = lean_ctor_get(v_ys_41_, 0);
lean_inc(v_head_46_);
v_tail_47_ = lean_ctor_get(v_ys_41_, 1);
lean_inc(v_tail_47_);
lean_dec_ref_known(v_ys_41_, 2);
v___x_48_ = lean_apply_2(v_h__2_43_, v_head_46_, v_tail_47_);
return v___x_48_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__instDecidableEqList_match__1_splitter(lean_object* v_00_u03b1_49_, lean_object* v_motive_50_, lean_object* v_ys_51_, lean_object* v_h__1_52_, lean_object* v_h__2_53_){
_start:
{
if (lean_obj_tag(v_ys_51_) == 0)
{
lean_object* v___x_54_; lean_object* v___x_55_; 
lean_dec(v_h__2_53_);
v___x_54_ = lean_box(0);
v___x_55_ = lean_apply_1(v_h__1_52_, v___x_54_);
return v___x_55_;
}
else
{
lean_object* v_head_56_; lean_object* v_tail_57_; lean_object* v___x_58_; 
lean_dec(v_h__1_52_);
v_head_56_ = lean_ctor_get(v_ys_51_, 0);
lean_inc(v_head_56_);
v_tail_57_ = lean_ctor_get(v_ys_51_, 1);
lean_inc(v_tail_57_);
lean_dec_ref_known(v_ys_51_, 2);
v___x_58_ = lean_apply_2(v_h__2_53_, v_head_56_, v_tail_57_);
return v___x_58_;
}
}
}
static lean_object* _init_l_Lean_Omega_IntList_get___closed__0(void){
_start:
{
lean_object* v___x_59_; lean_object* v___x_60_; 
v___x_59_ = lean_unsigned_to_nat(0u);
v___x_60_ = lean_nat_to_int(v___x_59_);
return v___x_60_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_get(lean_object* v_xs_61_, lean_object* v_i_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = l_List_get_x3fInternal___redArg(v_xs_61_, v_i_62_);
if (lean_obj_tag(v___x_63_) == 0)
{
lean_object* v___x_64_; 
v___x_64_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
return v___x_64_;
}
else
{
lean_object* v_val_65_; 
v_val_65_ = lean_ctor_get(v___x_63_, 0);
lean_inc(v_val_65_);
lean_dec_ref_known(v___x_63_, 1);
return v_val_65_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_get___boxed(lean_object* v_xs_66_, lean_object* v_i_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Lean_Omega_IntList_get(v_xs_66_, v_i_67_);
lean_dec(v_xs_66_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_set(lean_object* v_xs_69_, lean_object* v_i_70_, lean_object* v_y_71_){
_start:
{
if (lean_obj_tag(v_xs_69_) == 0)
{
lean_object* v_zero_72_; uint8_t v_isZero_73_; 
v_zero_72_ = lean_unsigned_to_nat(0u);
v_isZero_73_ = lean_nat_dec_eq(v_i_70_, v_zero_72_);
if (v_isZero_73_ == 1)
{
lean_object* v___x_74_; 
v___x_74_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_74_, 0, v_y_71_);
lean_ctor_set(v___x_74_, 1, v_xs_69_);
return v___x_74_;
}
else
{
lean_object* v_one_75_; lean_object* v_n_76_; lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_79_; 
v_one_75_ = lean_unsigned_to_nat(1u);
v_n_76_ = lean_nat_sub(v_i_70_, v_one_75_);
v___x_77_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_78_ = l_Lean_Omega_IntList_set(v_xs_69_, v_n_76_, v_y_71_);
lean_dec(v_n_76_);
v___x_79_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v___x_79_, 0, v___x_77_);
lean_ctor_set(v___x_79_, 1, v___x_78_);
return v___x_79_;
}
}
else
{
lean_object* v_head_80_; lean_object* v_tail_81_; lean_object* v___x_83_; uint8_t v_isShared_84_; uint8_t v_isSharedCheck_96_; 
v_head_80_ = lean_ctor_get(v_xs_69_, 0);
v_tail_81_ = lean_ctor_get(v_xs_69_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v_xs_69_);
if (v_isSharedCheck_96_ == 0)
{
v___x_83_ = v_xs_69_;
v_isShared_84_ = v_isSharedCheck_96_;
goto v_resetjp_82_;
}
else
{
lean_inc(v_tail_81_);
lean_inc(v_head_80_);
lean_dec(v_xs_69_);
v___x_83_ = lean_box(0);
v_isShared_84_ = v_isSharedCheck_96_;
goto v_resetjp_82_;
}
v_resetjp_82_:
{
lean_object* v_zero_85_; uint8_t v_isZero_86_; 
v_zero_85_ = lean_unsigned_to_nat(0u);
v_isZero_86_ = lean_nat_dec_eq(v_i_70_, v_zero_85_);
if (v_isZero_86_ == 1)
{
lean_object* v___x_88_; 
lean_dec(v_head_80_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 0, v_y_71_);
v___x_88_ = v___x_83_;
goto v_reusejp_87_;
}
else
{
lean_object* v_reuseFailAlloc_89_; 
v_reuseFailAlloc_89_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_89_, 0, v_y_71_);
lean_ctor_set(v_reuseFailAlloc_89_, 1, v_tail_81_);
v___x_88_ = v_reuseFailAlloc_89_;
goto v_reusejp_87_;
}
v_reusejp_87_:
{
return v___x_88_;
}
}
else
{
lean_object* v_one_90_; lean_object* v_n_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v_one_90_ = lean_unsigned_to_nat(1u);
v_n_91_ = lean_nat_sub(v_i_70_, v_one_90_);
v___x_92_ = l_Lean_Omega_IntList_set(v_tail_81_, v_n_91_, v_y_71_);
lean_dec(v_n_91_);
if (v_isShared_84_ == 0)
{
lean_ctor_set(v___x_83_, 1, v___x_92_);
v___x_94_ = v___x_83_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v_head_80_);
lean_ctor_set(v_reuseFailAlloc_95_, 1, v___x_92_);
v___x_94_ = v_reuseFailAlloc_95_;
goto v_reusejp_93_;
}
v_reusejp_93_:
{
return v___x_94_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_set___boxed(lean_object* v_xs_97_, lean_object* v_i_98_, lean_object* v_y_99_){
_start:
{
lean_object* v_res_100_; 
v_res_100_ = l_Lean_Omega_IntList_set(v_xs_97_, v_i_98_, v_y_99_);
lean_dec(v_i_98_);
return v_res_100_;
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(lean_object* v_x_101_){
_start:
{
if (lean_obj_tag(v_x_101_) == 0)
{
lean_object* v___x_102_; 
v___x_102_ = lean_box(0);
return v___x_102_;
}
else
{
lean_object* v_head_103_; lean_object* v_tail_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v_head_103_ = lean_ctor_get(v_x_101_, 0);
v_tail_104_ = lean_ctor_get(v_x_101_, 1);
v___x_105_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_106_ = lean_int_dec_eq(v_head_103_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; 
lean_inc(v_head_103_);
v___x_107_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_107_, 0, v_head_103_);
return v___x_107_;
}
else
{
v_x_101_ = v_tail_104_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0___boxed(lean_object* v_x_109_){
_start:
{
lean_object* v_res_110_; 
v_res_110_ = l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(v_x_109_);
lean_dec(v_x_109_);
return v_res_110_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading(lean_object* v_xs_111_){
_start:
{
lean_object* v___x_112_; 
v___x_112_ = l_List_find_x3f___at___00Lean_Omega_IntList_leading_spec__0(v_xs_111_);
if (lean_obj_tag(v___x_112_) == 0)
{
lean_object* v___x_113_; 
v___x_113_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
return v___x_113_;
}
else
{
lean_object* v_val_114_; 
v_val_114_ = lean_ctor_get(v___x_112_, 0);
lean_inc(v_val_114_);
lean_dec_ref_known(v___x_112_, 1);
return v_val_114_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_leading___boxed(lean_object* v_xs_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_Lean_Omega_IntList_leading(v_xs_115_);
lean_dec(v_xs_115_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(lean_object* v_a_117_, lean_object* v_a_118_){
_start:
{
if (lean_obj_tag(v_a_117_) == 0)
{
lean_object* v___x_119_; 
v___x_119_ = l_List_reverse___redArg(v_a_118_);
return v___x_119_;
}
else
{
lean_object* v_head_120_; lean_object* v_tail_121_; lean_object* v___x_123_; uint8_t v_isShared_124_; uint8_t v_isSharedCheck_131_; 
v_head_120_ = lean_ctor_get(v_a_117_, 0);
v_tail_121_ = lean_ctor_get(v_a_117_, 1);
v_isSharedCheck_131_ = !lean_is_exclusive(v_a_117_);
if (v_isSharedCheck_131_ == 0)
{
v___x_123_ = v_a_117_;
v_isShared_124_ = v_isSharedCheck_131_;
goto v_resetjp_122_;
}
else
{
lean_inc(v_tail_121_);
lean_inc(v_head_120_);
lean_dec(v_a_117_);
v___x_123_ = lean_box(0);
v_isShared_124_ = v_isSharedCheck_131_;
goto v_resetjp_122_;
}
v_resetjp_122_:
{
lean_object* v___x_125_; lean_object* v___x_126_; lean_object* v___x_128_; 
v___x_125_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_126_ = lean_int_add(v___x_125_, v_head_120_);
lean_dec(v_head_120_);
if (v_isShared_124_ == 0)
{
lean_ctor_set(v___x_123_, 1, v_a_118_);
lean_ctor_set(v___x_123_, 0, v___x_126_);
v___x_128_ = v___x_123_;
goto v_reusejp_127_;
}
else
{
lean_object* v_reuseFailAlloc_130_; 
v_reuseFailAlloc_130_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_130_, 0, v___x_126_);
lean_ctor_set(v_reuseFailAlloc_130_, 1, v_a_118_);
v___x_128_ = v_reuseFailAlloc_130_;
goto v_reusejp_127_;
}
v_reusejp_127_:
{
v_a_117_ = v_tail_121_;
v_a_118_ = v___x_128_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(lean_object* v_a_132_, lean_object* v_a_133_){
_start:
{
if (lean_obj_tag(v_a_132_) == 0)
{
lean_object* v___x_134_; 
v___x_134_ = l_List_reverse___redArg(v_a_133_);
return v___x_134_;
}
else
{
lean_object* v_head_135_; lean_object* v_tail_136_; lean_object* v___x_138_; uint8_t v_isShared_139_; uint8_t v_isSharedCheck_146_; 
v_head_135_ = lean_ctor_get(v_a_132_, 0);
v_tail_136_ = lean_ctor_get(v_a_132_, 1);
v_isSharedCheck_146_ = !lean_is_exclusive(v_a_132_);
if (v_isSharedCheck_146_ == 0)
{
v___x_138_ = v_a_132_;
v_isShared_139_ = v_isSharedCheck_146_;
goto v_resetjp_137_;
}
else
{
lean_inc(v_tail_136_);
lean_inc(v_head_135_);
lean_dec(v_a_132_);
v___x_138_ = lean_box(0);
v_isShared_139_ = v_isSharedCheck_146_;
goto v_resetjp_137_;
}
v_resetjp_137_:
{
lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_143_; 
v___x_140_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_141_ = lean_int_add(v___x_140_, v_head_135_);
lean_dec(v_head_135_);
if (v_isShared_139_ == 0)
{
lean_ctor_set(v___x_138_, 1, v_a_133_);
lean_ctor_set(v___x_138_, 0, v___x_141_);
v___x_143_ = v___x_138_;
goto v_reusejp_142_;
}
else
{
lean_object* v_reuseFailAlloc_145_; 
v_reuseFailAlloc_145_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_145_, 0, v___x_141_);
lean_ctor_set(v_reuseFailAlloc_145_, 1, v_a_133_);
v___x_143_ = v_reuseFailAlloc_145_;
goto v_reusejp_142_;
}
v_reusejp_142_:
{
lean_object* v___x_144_; 
v___x_144_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0_spec__1(v_tail_136_, v___x_143_);
return v___x_144_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(lean_object* v_a_147_, lean_object* v_a_148_){
_start:
{
if (lean_obj_tag(v_a_147_) == 0)
{
lean_object* v___x_149_; 
v___x_149_ = l_List_reverse___redArg(v_a_148_);
return v___x_149_;
}
else
{
lean_object* v_head_150_; lean_object* v_tail_151_; lean_object* v___x_153_; uint8_t v_isShared_154_; uint8_t v_isSharedCheck_161_; 
v_head_150_ = lean_ctor_get(v_a_147_, 0);
v_tail_151_ = lean_ctor_get(v_a_147_, 1);
v_isSharedCheck_161_ = !lean_is_exclusive(v_a_147_);
if (v_isSharedCheck_161_ == 0)
{
v___x_153_ = v_a_147_;
v_isShared_154_ = v_isSharedCheck_161_;
goto v_resetjp_152_;
}
else
{
lean_inc(v_tail_151_);
lean_inc(v_head_150_);
lean_dec(v_a_147_);
v___x_153_ = lean_box(0);
v_isShared_154_ = v_isSharedCheck_161_;
goto v_resetjp_152_;
}
v_resetjp_152_:
{
lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_155_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_156_ = lean_int_add(v_head_150_, v___x_155_);
lean_dec(v_head_150_);
if (v_isShared_154_ == 0)
{
lean_ctor_set(v___x_153_, 1, v_a_148_);
lean_ctor_set(v___x_153_, 0, v___x_156_);
v___x_158_ = v___x_153_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_160_; 
v_reuseFailAlloc_160_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_160_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_160_, 1, v_a_148_);
v___x_158_ = v_reuseFailAlloc_160_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
v_a_147_ = v_tail_151_;
v_a_148_ = v___x_158_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(lean_object* v_a_162_, lean_object* v_a_163_){
_start:
{
if (lean_obj_tag(v_a_162_) == 0)
{
lean_object* v___x_164_; 
v___x_164_ = l_List_reverse___redArg(v_a_163_);
return v___x_164_;
}
else
{
lean_object* v_head_165_; lean_object* v_tail_166_; lean_object* v___x_168_; uint8_t v_isShared_169_; uint8_t v_isSharedCheck_176_; 
v_head_165_ = lean_ctor_get(v_a_162_, 0);
v_tail_166_ = lean_ctor_get(v_a_162_, 1);
v_isSharedCheck_176_ = !lean_is_exclusive(v_a_162_);
if (v_isSharedCheck_176_ == 0)
{
v___x_168_ = v_a_162_;
v_isShared_169_ = v_isSharedCheck_176_;
goto v_resetjp_167_;
}
else
{
lean_inc(v_tail_166_);
lean_inc(v_head_165_);
lean_dec(v_a_162_);
v___x_168_ = lean_box(0);
v_isShared_169_ = v_isSharedCheck_176_;
goto v_resetjp_167_;
}
v_resetjp_167_:
{
lean_object* v___x_170_; lean_object* v___x_171_; lean_object* v___x_173_; 
v___x_170_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_171_ = lean_int_add(v_head_165_, v___x_170_);
lean_dec(v_head_165_);
if (v_isShared_169_ == 0)
{
lean_ctor_set(v___x_168_, 1, v_a_163_);
lean_ctor_set(v___x_168_, 0, v___x_171_);
v___x_173_ = v___x_168_;
goto v_reusejp_172_;
}
else
{
lean_object* v_reuseFailAlloc_175_; 
v_reuseFailAlloc_175_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_175_, 0, v___x_171_);
lean_ctor_set(v_reuseFailAlloc_175_, 1, v_a_163_);
v___x_173_ = v_reuseFailAlloc_175_;
goto v_reusejp_172_;
}
v_reusejp_172_:
{
lean_object* v___x_174_; 
v___x_174_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1_spec__3(v_tail_166_, v___x_173_);
return v___x_174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(lean_object* v_x_177_, lean_object* v_x_178_){
_start:
{
if (lean_obj_tag(v_x_177_) == 0)
{
lean_object* v___x_179_; 
v___x_179_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__0(v_x_178_, v_x_177_);
return v___x_179_;
}
else
{
if (lean_obj_tag(v_x_178_) == 0)
{
lean_object* v___x_180_; 
v___x_180_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0_spec__1(v_x_177_, v_x_178_);
return v___x_180_;
}
else
{
lean_object* v_head_181_; lean_object* v_tail_182_; lean_object* v_head_183_; lean_object* v_tail_184_; lean_object* v___x_186_; uint8_t v_isShared_187_; uint8_t v_isSharedCheck_193_; 
v_head_181_ = lean_ctor_get(v_x_177_, 0);
lean_inc(v_head_181_);
v_tail_182_ = lean_ctor_get(v_x_177_, 1);
lean_inc(v_tail_182_);
lean_dec_ref_known(v_x_177_, 2);
v_head_183_ = lean_ctor_get(v_x_178_, 0);
v_tail_184_ = lean_ctor_get(v_x_178_, 1);
v_isSharedCheck_193_ = !lean_is_exclusive(v_x_178_);
if (v_isSharedCheck_193_ == 0)
{
v___x_186_ = v_x_178_;
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
else
{
lean_inc(v_tail_184_);
lean_inc(v_head_183_);
lean_dec(v_x_178_);
v___x_186_ = lean_box(0);
v_isShared_187_ = v_isSharedCheck_193_;
goto v_resetjp_185_;
}
v_resetjp_185_:
{
lean_object* v___x_188_; lean_object* v___x_189_; lean_object* v___x_191_; 
v___x_188_ = lean_int_add(v_head_181_, v_head_183_);
lean_dec(v_head_183_);
lean_dec(v_head_181_);
v___x_189_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_tail_182_, v_tail_184_);
if (v_isShared_187_ == 0)
{
lean_ctor_set(v___x_186_, 1, v___x_189_);
lean_ctor_set(v___x_186_, 0, v___x_188_);
v___x_191_ = v___x_186_;
goto v_reusejp_190_;
}
else
{
lean_object* v_reuseFailAlloc_192_; 
v_reuseFailAlloc_192_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_192_, 0, v___x_188_);
lean_ctor_set(v_reuseFailAlloc_192_, 1, v___x_189_);
v___x_191_ = v_reuseFailAlloc_192_;
goto v_reusejp_190_;
}
v_reusejp_190_:
{
return v___x_191_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_add(lean_object* v_xs_194_, lean_object* v_ys_195_){
_start:
{
lean_object* v___x_196_; 
v___x_196_ = l_List_zipWithAll___at___00Lean_Omega_IntList_add_spec__0(v_xs_194_, v_ys_195_);
return v___x_196_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mulImpl(lean_object* v_x_199_, lean_object* v_x_200_){
_start:
{
if (lean_obj_tag(v_x_199_) == 1)
{
if (lean_obj_tag(v_x_200_) == 1)
{
lean_object* v_head_201_; lean_object* v_tail_202_; lean_object* v_head_203_; lean_object* v_tail_204_; lean_object* v___x_206_; uint8_t v_isShared_207_; uint8_t v_isSharedCheck_213_; 
v_head_201_ = lean_ctor_get(v_x_199_, 0);
v_tail_202_ = lean_ctor_get(v_x_199_, 1);
v_head_203_ = lean_ctor_get(v_x_200_, 0);
v_tail_204_ = lean_ctor_get(v_x_200_, 1);
v_isSharedCheck_213_ = !lean_is_exclusive(v_x_200_);
if (v_isSharedCheck_213_ == 0)
{
v___x_206_ = v_x_200_;
v_isShared_207_ = v_isSharedCheck_213_;
goto v_resetjp_205_;
}
else
{
lean_inc(v_tail_204_);
lean_inc(v_head_203_);
lean_dec(v_x_200_);
v___x_206_ = lean_box(0);
v_isShared_207_ = v_isSharedCheck_213_;
goto v_resetjp_205_;
}
v_resetjp_205_:
{
lean_object* v___x_208_; lean_object* v___x_209_; lean_object* v___x_211_; 
v___x_208_ = lean_int_mul(v_head_201_, v_head_203_);
lean_dec(v_head_203_);
v___x_209_ = l_Lean_Omega_IntList_mulImpl(v_tail_202_, v_tail_204_);
if (v_isShared_207_ == 0)
{
lean_ctor_set(v___x_206_, 1, v___x_209_);
lean_ctor_set(v___x_206_, 0, v___x_208_);
v___x_211_ = v___x_206_;
goto v_reusejp_210_;
}
else
{
lean_object* v_reuseFailAlloc_212_; 
v_reuseFailAlloc_212_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_212_, 0, v___x_208_);
lean_ctor_set(v_reuseFailAlloc_212_, 1, v___x_209_);
v___x_211_ = v_reuseFailAlloc_212_;
goto v_reusejp_210_;
}
v_reusejp_210_:
{
return v___x_211_;
}
}
}
else
{
lean_object* v___x_214_; 
lean_dec(v_x_200_);
v___x_214_ = lean_box(0);
return v___x_214_;
}
}
else
{
lean_object* v___x_215_; 
lean_dec(v_x_200_);
v___x_215_ = lean_box(0);
return v___x_215_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_mulImpl___boxed(lean_object* v_x_216_, lean_object* v_x_217_){
_start:
{
lean_object* v_res_218_; 
v_res_218_ = l_Lean_Omega_IntList_mulImpl(v_x_216_, v_x_217_);
lean_dec(v_x_216_);
return v_res_218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_mulImpl_match__1_splitter___redArg(lean_object* v_x_219_, lean_object* v_x_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
_start:
{
if (lean_obj_tag(v_x_219_) == 1)
{
if (lean_obj_tag(v_x_220_) == 1)
{
lean_object* v_head_223_; lean_object* v_tail_224_; lean_object* v_head_225_; lean_object* v_tail_226_; lean_object* v___x_227_; 
lean_dec(v_h__2_222_);
v_head_223_ = lean_ctor_get(v_x_219_, 0);
lean_inc(v_head_223_);
v_tail_224_ = lean_ctor_get(v_x_219_, 1);
lean_inc(v_tail_224_);
lean_dec_ref_known(v_x_219_, 2);
v_head_225_ = lean_ctor_get(v_x_220_, 0);
lean_inc(v_head_225_);
v_tail_226_ = lean_ctor_get(v_x_220_, 1);
lean_inc(v_tail_226_);
lean_dec_ref_known(v_x_220_, 2);
v___x_227_ = lean_apply_4(v_h__1_221_, v_head_223_, v_tail_224_, v_head_225_, v_tail_226_);
return v___x_227_;
}
else
{
lean_object* v___x_228_; 
lean_dec(v_h__1_221_);
v___x_228_ = lean_apply_3(v_h__2_222_, v_x_219_, v_x_220_, lean_box(0));
return v___x_228_;
}
}
else
{
lean_object* v___x_229_; 
lean_dec(v_h__1_221_);
v___x_229_ = lean_apply_3(v_h__2_222_, v_x_219_, v_x_220_, lean_box(0));
return v___x_229_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_mulImpl_match__1_splitter(lean_object* v_motive_230_, lean_object* v_x_231_, lean_object* v_x_232_, lean_object* v_h__1_233_, lean_object* v_h__2_234_){
_start:
{
if (lean_obj_tag(v_x_231_) == 1)
{
if (lean_obj_tag(v_x_232_) == 1)
{
lean_object* v_head_235_; lean_object* v_tail_236_; lean_object* v_head_237_; lean_object* v_tail_238_; lean_object* v___x_239_; 
lean_dec(v_h__2_234_);
v_head_235_ = lean_ctor_get(v_x_231_, 0);
lean_inc(v_head_235_);
v_tail_236_ = lean_ctor_get(v_x_231_, 1);
lean_inc(v_tail_236_);
lean_dec_ref_known(v_x_231_, 2);
v_head_237_ = lean_ctor_get(v_x_232_, 0);
lean_inc(v_head_237_);
v_tail_238_ = lean_ctor_get(v_x_232_, 1);
lean_inc(v_tail_238_);
lean_dec_ref_known(v_x_232_, 2);
v___x_239_ = lean_apply_4(v_h__1_233_, v_head_235_, v_tail_236_, v_head_237_, v_tail_238_);
return v___x_239_;
}
else
{
lean_object* v___x_240_; 
lean_dec(v_h__1_233_);
v___x_240_ = lean_apply_3(v_h__2_234_, v_x_231_, v_x_232_, lean_box(0));
return v___x_240_;
}
}
else
{
lean_object* v___x_241_; 
lean_dec(v_h__1_233_);
v___x_241_ = lean_apply_3(v_h__2_234_, v_x_231_, v_x_232_, lean_box(0));
return v___x_241_;
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(lean_object* v_a_244_, lean_object* v_a_245_){
_start:
{
if (lean_obj_tag(v_a_244_) == 0)
{
lean_object* v___x_246_; 
v___x_246_ = l_List_reverse___redArg(v_a_245_);
return v___x_246_;
}
else
{
lean_object* v_head_247_; lean_object* v_tail_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_257_; 
v_head_247_ = lean_ctor_get(v_a_244_, 0);
v_tail_248_ = lean_ctor_get(v_a_244_, 1);
v_isSharedCheck_257_ = !lean_is_exclusive(v_a_244_);
if (v_isSharedCheck_257_ == 0)
{
v___x_250_ = v_a_244_;
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_tail_248_);
lean_inc(v_head_247_);
lean_dec(v_a_244_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_257_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_252_; lean_object* v___x_254_; 
v___x_252_ = lean_int_neg(v_head_247_);
lean_dec(v_head_247_);
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 1, v_a_245_);
lean_ctor_set(v___x_250_, 0, v___x_252_);
v___x_254_ = v___x_250_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_252_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_a_245_);
v___x_254_ = v_reuseFailAlloc_256_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
v_a_244_ = v_tail_248_;
v_a_245_ = v___x_254_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_neg(lean_object* v_xs_258_){
_start:
{
lean_object* v___x_259_; lean_object* v___x_260_; 
v___x_259_ = lean_box(0);
v___x_260_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_neg_spec__0(v_xs_258_, v___x_259_);
return v___x_260_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(lean_object* v_a_263_, lean_object* v_a_264_){
_start:
{
if (lean_obj_tag(v_a_263_) == 0)
{
lean_object* v___x_265_; 
v___x_265_ = l_List_reverse___redArg(v_a_264_);
return v___x_265_;
}
else
{
lean_object* v_head_266_; lean_object* v_tail_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_277_; 
v_head_266_ = lean_ctor_get(v_a_263_, 0);
v_tail_267_ = lean_ctor_get(v_a_263_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_a_263_);
if (v_isSharedCheck_277_ == 0)
{
v___x_269_ = v_a_263_;
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_tail_267_);
lean_inc(v_head_266_);
lean_dec(v_a_263_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_271_; lean_object* v___x_272_; lean_object* v___x_274_; 
v___x_271_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_272_ = lean_int_sub(v_head_266_, v___x_271_);
lean_dec(v_head_266_);
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 1, v_a_264_);
lean_ctor_set(v___x_269_, 0, v___x_272_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v___x_272_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_a_264_);
v___x_274_ = v_reuseFailAlloc_276_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
v_a_263_ = v_tail_267_;
v_a_264_ = v___x_274_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(lean_object* v_a_278_, lean_object* v_a_279_){
_start:
{
if (lean_obj_tag(v_a_278_) == 0)
{
lean_object* v___x_280_; 
v___x_280_ = l_List_reverse___redArg(v_a_279_);
return v___x_280_;
}
else
{
lean_object* v_head_281_; lean_object* v_tail_282_; lean_object* v___x_284_; uint8_t v_isShared_285_; uint8_t v_isSharedCheck_292_; 
v_head_281_ = lean_ctor_get(v_a_278_, 0);
v_tail_282_ = lean_ctor_get(v_a_278_, 1);
v_isSharedCheck_292_ = !lean_is_exclusive(v_a_278_);
if (v_isSharedCheck_292_ == 0)
{
v___x_284_ = v_a_278_;
v_isShared_285_ = v_isSharedCheck_292_;
goto v_resetjp_283_;
}
else
{
lean_inc(v_tail_282_);
lean_inc(v_head_281_);
lean_dec(v_a_278_);
v___x_284_ = lean_box(0);
v_isShared_285_ = v_isSharedCheck_292_;
goto v_resetjp_283_;
}
v_resetjp_283_:
{
lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_289_; 
v___x_286_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_287_ = lean_int_sub(v_head_281_, v___x_286_);
lean_dec(v_head_281_);
if (v_isShared_285_ == 0)
{
lean_ctor_set(v___x_284_, 1, v_a_279_);
lean_ctor_set(v___x_284_, 0, v___x_287_);
v___x_289_ = v___x_284_;
goto v_reusejp_288_;
}
else
{
lean_object* v_reuseFailAlloc_291_; 
v_reuseFailAlloc_291_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_291_, 0, v___x_287_);
lean_ctor_set(v_reuseFailAlloc_291_, 1, v_a_279_);
v___x_289_ = v_reuseFailAlloc_291_;
goto v_reusejp_288_;
}
v_reusejp_288_:
{
lean_object* v___x_290_; 
v___x_290_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1_spec__3(v_tail_282_, v___x_289_);
return v___x_290_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(lean_object* v_a_293_, lean_object* v_a_294_){
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
lean_object* v_head_296_; lean_object* v_tail_297_; lean_object* v___x_299_; uint8_t v_isShared_300_; uint8_t v_isSharedCheck_307_; 
v_head_296_ = lean_ctor_get(v_a_293_, 0);
v_tail_297_ = lean_ctor_get(v_a_293_, 1);
v_isSharedCheck_307_ = !lean_is_exclusive(v_a_293_);
if (v_isSharedCheck_307_ == 0)
{
v___x_299_ = v_a_293_;
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
else
{
lean_inc(v_tail_297_);
lean_inc(v_head_296_);
lean_dec(v_a_293_);
v___x_299_ = lean_box(0);
v_isShared_300_ = v_isSharedCheck_307_;
goto v_resetjp_298_;
}
v_resetjp_298_:
{
lean_object* v___x_301_; lean_object* v___x_302_; lean_object* v___x_304_; 
v___x_301_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_302_ = lean_int_sub(v___x_301_, v_head_296_);
lean_dec(v_head_296_);
if (v_isShared_300_ == 0)
{
lean_ctor_set(v___x_299_, 1, v_a_294_);
lean_ctor_set(v___x_299_, 0, v___x_302_);
v___x_304_ = v___x_299_;
goto v_reusejp_303_;
}
else
{
lean_object* v_reuseFailAlloc_306_; 
v_reuseFailAlloc_306_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_306_, 0, v___x_302_);
lean_ctor_set(v_reuseFailAlloc_306_, 1, v_a_294_);
v___x_304_ = v_reuseFailAlloc_306_;
goto v_reusejp_303_;
}
v_reusejp_303_:
{
v_a_293_ = v_tail_297_;
v_a_294_ = v___x_304_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(lean_object* v_a_308_, lean_object* v_a_309_){
_start:
{
if (lean_obj_tag(v_a_308_) == 0)
{
lean_object* v___x_310_; 
v___x_310_ = l_List_reverse___redArg(v_a_309_);
return v___x_310_;
}
else
{
lean_object* v_head_311_; lean_object* v_tail_312_; lean_object* v___x_314_; uint8_t v_isShared_315_; uint8_t v_isSharedCheck_322_; 
v_head_311_ = lean_ctor_get(v_a_308_, 0);
v_tail_312_ = lean_ctor_get(v_a_308_, 1);
v_isSharedCheck_322_ = !lean_is_exclusive(v_a_308_);
if (v_isSharedCheck_322_ == 0)
{
v___x_314_ = v_a_308_;
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
else
{
lean_inc(v_tail_312_);
lean_inc(v_head_311_);
lean_dec(v_a_308_);
v___x_314_ = lean_box(0);
v_isShared_315_ = v_isSharedCheck_322_;
goto v_resetjp_313_;
}
v_resetjp_313_:
{
lean_object* v___x_316_; lean_object* v___x_317_; lean_object* v___x_319_; 
v___x_316_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_317_ = lean_int_sub(v___x_316_, v_head_311_);
lean_dec(v_head_311_);
if (v_isShared_315_ == 0)
{
lean_ctor_set(v___x_314_, 1, v_a_309_);
lean_ctor_set(v___x_314_, 0, v___x_317_);
v___x_319_ = v___x_314_;
goto v_reusejp_318_;
}
else
{
lean_object* v_reuseFailAlloc_321_; 
v_reuseFailAlloc_321_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_321_, 0, v___x_317_);
lean_ctor_set(v_reuseFailAlloc_321_, 1, v_a_309_);
v___x_319_ = v_reuseFailAlloc_321_;
goto v_reusejp_318_;
}
v_reusejp_318_:
{
lean_object* v___x_320_; 
v___x_320_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0_spec__1(v_tail_312_, v___x_319_);
return v___x_320_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(lean_object* v_x_323_, lean_object* v_x_324_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_object* v___x_325_; 
v___x_325_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__0(v_x_324_, v_x_323_);
return v___x_325_;
}
else
{
if (lean_obj_tag(v_x_324_) == 0)
{
lean_object* v___x_326_; 
v___x_326_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0_spec__1(v_x_323_, v_x_324_);
return v___x_326_;
}
else
{
lean_object* v_head_327_; lean_object* v_tail_328_; lean_object* v_head_329_; lean_object* v_tail_330_; lean_object* v___x_332_; uint8_t v_isShared_333_; uint8_t v_isSharedCheck_339_; 
v_head_327_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_head_327_);
v_tail_328_ = lean_ctor_get(v_x_323_, 1);
lean_inc(v_tail_328_);
lean_dec_ref_known(v_x_323_, 2);
v_head_329_ = lean_ctor_get(v_x_324_, 0);
v_tail_330_ = lean_ctor_get(v_x_324_, 1);
v_isSharedCheck_339_ = !lean_is_exclusive(v_x_324_);
if (v_isSharedCheck_339_ == 0)
{
v___x_332_ = v_x_324_;
v_isShared_333_ = v_isSharedCheck_339_;
goto v_resetjp_331_;
}
else
{
lean_inc(v_tail_330_);
lean_inc(v_head_329_);
lean_dec(v_x_324_);
v___x_332_ = lean_box(0);
v_isShared_333_ = v_isSharedCheck_339_;
goto v_resetjp_331_;
}
v_resetjp_331_:
{
lean_object* v___x_334_; lean_object* v___x_335_; lean_object* v___x_337_; 
v___x_334_ = lean_int_sub(v_head_327_, v_head_329_);
lean_dec(v_head_329_);
lean_dec(v_head_327_);
v___x_335_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_tail_328_, v_tail_330_);
if (v_isShared_333_ == 0)
{
lean_ctor_set(v___x_332_, 1, v___x_335_);
lean_ctor_set(v___x_332_, 0, v___x_334_);
v___x_337_ = v___x_332_;
goto v_reusejp_336_;
}
else
{
lean_object* v_reuseFailAlloc_338_; 
v_reuseFailAlloc_338_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_338_, 0, v___x_334_);
lean_ctor_set(v_reuseFailAlloc_338_, 1, v___x_335_);
v___x_337_ = v_reuseFailAlloc_338_;
goto v_reusejp_336_;
}
v_reusejp_336_:
{
return v___x_337_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sub(lean_object* v_xs_340_, lean_object* v_ys_341_){
_start:
{
lean_object* v___x_342_; 
v___x_342_ = l_List_zipWithAll___at___00Lean_Omega_IntList_sub_spec__0(v_xs_340_, v_ys_341_);
return v___x_342_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(lean_object* v_i_345_, lean_object* v_a_346_, lean_object* v_a_347_){
_start:
{
if (lean_obj_tag(v_a_346_) == 0)
{
lean_object* v___x_348_; 
v___x_348_ = l_List_reverse___redArg(v_a_347_);
return v___x_348_;
}
else
{
lean_object* v_head_349_; lean_object* v_tail_350_; lean_object* v___x_352_; uint8_t v_isShared_353_; uint8_t v_isSharedCheck_359_; 
v_head_349_ = lean_ctor_get(v_a_346_, 0);
v_tail_350_ = lean_ctor_get(v_a_346_, 1);
v_isSharedCheck_359_ = !lean_is_exclusive(v_a_346_);
if (v_isSharedCheck_359_ == 0)
{
v___x_352_ = v_a_346_;
v_isShared_353_ = v_isSharedCheck_359_;
goto v_resetjp_351_;
}
else
{
lean_inc(v_tail_350_);
lean_inc(v_head_349_);
lean_dec(v_a_346_);
v___x_352_ = lean_box(0);
v_isShared_353_ = v_isSharedCheck_359_;
goto v_resetjp_351_;
}
v_resetjp_351_:
{
lean_object* v___x_354_; lean_object* v___x_356_; 
v___x_354_ = lean_int_mul(v_i_345_, v_head_349_);
lean_dec(v_head_349_);
if (v_isShared_353_ == 0)
{
lean_ctor_set(v___x_352_, 1, v_a_347_);
lean_ctor_set(v___x_352_, 0, v___x_354_);
v___x_356_ = v___x_352_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_358_; 
v_reuseFailAlloc_358_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_358_, 0, v___x_354_);
lean_ctor_set(v_reuseFailAlloc_358_, 1, v_a_347_);
v___x_356_ = v_reuseFailAlloc_358_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
v_a_346_ = v_tail_350_;
v_a_347_ = v___x_356_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0___boxed(lean_object* v_i_360_, lean_object* v_a_361_, lean_object* v_a_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_360_, v_a_361_, v_a_362_);
lean_dec(v_i_360_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul(lean_object* v_xs_364_, lean_object* v_i_365_){
_start:
{
lean_object* v___x_366_; lean_object* v___x_367_; 
v___x_366_ = lean_box(0);
v___x_367_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_smul_spec__0(v_i_365_, v_xs_364_, v___x_366_);
return v___x_367_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_smul___boxed(lean_object* v_xs_368_, lean_object* v_i_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l_Lean_Omega_IntList_smul(v_xs_368_, v_i_369_);
lean_dec(v_i_369_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0(lean_object* v_i_371_, lean_object* v_xs_372_){
_start:
{
lean_object* v___x_373_; 
v___x_373_ = l_Lean_Omega_IntList_smul(v_xs_372_, v_i_371_);
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_instHMulInt___lam__0___boxed(lean_object* v_i_374_, lean_object* v_xs_375_){
_start:
{
lean_object* v_res_376_; 
v_res_376_ = l_Lean_Omega_IntList_instHMulInt___lam__0(v_i_374_, v_xs_375_);
lean_dec(v_i_374_);
return v_res_376_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(lean_object* v_a_379_, lean_object* v_b_380_, lean_object* v_a_381_, lean_object* v_a_382_){
_start:
{
if (lean_obj_tag(v_a_381_) == 0)
{
lean_object* v___x_383_; 
v___x_383_ = l_List_reverse___redArg(v_a_382_);
return v___x_383_;
}
else
{
lean_object* v_head_384_; lean_object* v_tail_385_; lean_object* v___x_387_; uint8_t v_isShared_388_; uint8_t v_isSharedCheck_397_; 
v_head_384_ = lean_ctor_get(v_a_381_, 0);
v_tail_385_ = lean_ctor_get(v_a_381_, 1);
v_isSharedCheck_397_ = !lean_is_exclusive(v_a_381_);
if (v_isSharedCheck_397_ == 0)
{
v___x_387_ = v_a_381_;
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
else
{
lean_inc(v_tail_385_);
lean_inc(v_head_384_);
lean_dec(v_a_381_);
v___x_387_ = lean_box(0);
v_isShared_388_ = v_isSharedCheck_397_;
goto v_resetjp_386_;
}
v_resetjp_386_:
{
lean_object* v___x_389_; lean_object* v___x_390_; lean_object* v___x_391_; lean_object* v___x_392_; lean_object* v___x_394_; 
v___x_389_ = lean_int_mul(v_a_379_, v_head_384_);
lean_dec(v_head_384_);
v___x_390_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_391_ = lean_int_mul(v_b_380_, v___x_390_);
v___x_392_ = lean_int_add(v___x_389_, v___x_391_);
lean_dec(v___x_391_);
lean_dec(v___x_389_);
if (v_isShared_388_ == 0)
{
lean_ctor_set(v___x_387_, 1, v_a_382_);
lean_ctor_set(v___x_387_, 0, v___x_392_);
v___x_394_ = v___x_387_;
goto v_reusejp_393_;
}
else
{
lean_object* v_reuseFailAlloc_396_; 
v_reuseFailAlloc_396_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_396_, 0, v___x_392_);
lean_ctor_set(v_reuseFailAlloc_396_, 1, v_a_382_);
v___x_394_ = v_reuseFailAlloc_396_;
goto v_reusejp_393_;
}
v_reusejp_393_:
{
v_a_381_ = v_tail_385_;
v_a_382_ = v___x_394_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3___boxed(lean_object* v_a_398_, lean_object* v_b_399_, lean_object* v_a_400_, lean_object* v_a_401_){
_start:
{
lean_object* v_res_402_; 
v_res_402_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_398_, v_b_399_, v_a_400_, v_a_401_);
lean_dec(v_b_399_);
lean_dec(v_a_398_);
return v_res_402_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(lean_object* v_a_403_, lean_object* v_b_404_, lean_object* v_a_405_, lean_object* v_a_406_){
_start:
{
if (lean_obj_tag(v_a_405_) == 0)
{
lean_object* v___x_407_; 
v___x_407_ = l_List_reverse___redArg(v_a_406_);
return v___x_407_;
}
else
{
lean_object* v_head_408_; lean_object* v_tail_409_; lean_object* v___x_411_; uint8_t v_isShared_412_; uint8_t v_isSharedCheck_421_; 
v_head_408_ = lean_ctor_get(v_a_405_, 0);
v_tail_409_ = lean_ctor_get(v_a_405_, 1);
v_isSharedCheck_421_ = !lean_is_exclusive(v_a_405_);
if (v_isSharedCheck_421_ == 0)
{
v___x_411_ = v_a_405_;
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
else
{
lean_inc(v_tail_409_);
lean_inc(v_head_408_);
lean_dec(v_a_405_);
v___x_411_ = lean_box(0);
v_isShared_412_ = v_isSharedCheck_421_;
goto v_resetjp_410_;
}
v_resetjp_410_:
{
lean_object* v___x_413_; lean_object* v___x_414_; lean_object* v___x_415_; lean_object* v___x_416_; lean_object* v___x_418_; 
v___x_413_ = lean_int_mul(v_a_403_, v_head_408_);
lean_dec(v_head_408_);
v___x_414_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_415_ = lean_int_mul(v_b_404_, v___x_414_);
v___x_416_ = lean_int_add(v___x_413_, v___x_415_);
lean_dec(v___x_415_);
lean_dec(v___x_413_);
if (v_isShared_412_ == 0)
{
lean_ctor_set(v___x_411_, 1, v_a_406_);
lean_ctor_set(v___x_411_, 0, v___x_416_);
v___x_418_ = v___x_411_;
goto v_reusejp_417_;
}
else
{
lean_object* v_reuseFailAlloc_420_; 
v_reuseFailAlloc_420_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_420_, 0, v___x_416_);
lean_ctor_set(v_reuseFailAlloc_420_, 1, v_a_406_);
v___x_418_ = v_reuseFailAlloc_420_;
goto v_reusejp_417_;
}
v_reusejp_417_:
{
lean_object* v___x_419_; 
v___x_419_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1_spec__3(v_a_403_, v_b_404_, v_tail_409_, v___x_418_);
return v___x_419_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1___boxed(lean_object* v_a_422_, lean_object* v_b_423_, lean_object* v_a_424_, lean_object* v_a_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(v_a_422_, v_b_423_, v_a_424_, v_a_425_);
lean_dec(v_b_423_);
lean_dec(v_a_422_);
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(lean_object* v_a_427_, lean_object* v_b_428_, lean_object* v_a_429_, lean_object* v_a_430_){
_start:
{
if (lean_obj_tag(v_a_429_) == 0)
{
lean_object* v___x_431_; 
v___x_431_ = l_List_reverse___redArg(v_a_430_);
return v___x_431_;
}
else
{
lean_object* v_head_432_; lean_object* v_tail_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_445_; 
v_head_432_ = lean_ctor_get(v_a_429_, 0);
v_tail_433_ = lean_ctor_get(v_a_429_, 1);
v_isSharedCheck_445_ = !lean_is_exclusive(v_a_429_);
if (v_isSharedCheck_445_ == 0)
{
v___x_435_ = v_a_429_;
v_isShared_436_ = v_isSharedCheck_445_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_tail_433_);
lean_inc(v_head_432_);
lean_dec(v_a_429_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_445_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v___x_437_; lean_object* v___x_438_; lean_object* v___x_439_; lean_object* v___x_440_; lean_object* v___x_442_; 
v___x_437_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_438_ = lean_int_mul(v_a_427_, v___x_437_);
v___x_439_ = lean_int_mul(v_b_428_, v_head_432_);
lean_dec(v_head_432_);
v___x_440_ = lean_int_add(v___x_438_, v___x_439_);
lean_dec(v___x_439_);
lean_dec(v___x_438_);
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v_a_430_);
lean_ctor_set(v___x_435_, 0, v___x_440_);
v___x_442_ = v___x_435_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v___x_440_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_a_430_);
v___x_442_ = v_reuseFailAlloc_444_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
v_a_429_ = v_tail_433_;
v_a_430_ = v___x_442_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1___boxed(lean_object* v_a_446_, lean_object* v_b_447_, lean_object* v_a_448_, lean_object* v_a_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_446_, v_b_447_, v_a_448_, v_a_449_);
lean_dec(v_b_447_);
lean_dec(v_a_446_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(lean_object* v_a_451_, lean_object* v_b_452_, lean_object* v_a_453_, lean_object* v_a_454_){
_start:
{
if (lean_obj_tag(v_a_453_) == 0)
{
lean_object* v___x_455_; 
v___x_455_ = l_List_reverse___redArg(v_a_454_);
return v___x_455_;
}
else
{
lean_object* v_head_456_; lean_object* v_tail_457_; lean_object* v___x_459_; uint8_t v_isShared_460_; uint8_t v_isSharedCheck_469_; 
v_head_456_ = lean_ctor_get(v_a_453_, 0);
v_tail_457_ = lean_ctor_get(v_a_453_, 1);
v_isSharedCheck_469_ = !lean_is_exclusive(v_a_453_);
if (v_isSharedCheck_469_ == 0)
{
v___x_459_ = v_a_453_;
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
else
{
lean_inc(v_tail_457_);
lean_inc(v_head_456_);
lean_dec(v_a_453_);
v___x_459_ = lean_box(0);
v_isShared_460_ = v_isSharedCheck_469_;
goto v_resetjp_458_;
}
v_resetjp_458_:
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_461_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
v___x_462_ = lean_int_mul(v_a_451_, v___x_461_);
v___x_463_ = lean_int_mul(v_b_452_, v_head_456_);
lean_dec(v_head_456_);
v___x_464_ = lean_int_add(v___x_462_, v___x_463_);
lean_dec(v___x_463_);
lean_dec(v___x_462_);
if (v_isShared_460_ == 0)
{
lean_ctor_set(v___x_459_, 1, v_a_454_);
lean_ctor_set(v___x_459_, 0, v___x_464_);
v___x_466_ = v___x_459_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v_a_454_);
v___x_466_ = v_reuseFailAlloc_468_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_467_; 
v___x_467_ = l_List_mapTR_loop___at___00List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0_spec__1(v_a_451_, v_b_452_, v_tail_457_, v___x_466_);
return v___x_467_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0___boxed(lean_object* v_a_470_, lean_object* v_b_471_, lean_object* v_a_472_, lean_object* v_a_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(v_a_470_, v_b_471_, v_a_472_, v_a_473_);
lean_dec(v_b_471_);
lean_dec(v_a_470_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(lean_object* v_a_475_, lean_object* v_b_476_, lean_object* v_x_477_, lean_object* v_x_478_){
_start:
{
if (lean_obj_tag(v_x_477_) == 0)
{
lean_object* v___x_479_; 
v___x_479_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__0(v_a_475_, v_b_476_, v_x_478_, v_x_477_);
return v___x_479_;
}
else
{
if (lean_obj_tag(v_x_478_) == 0)
{
lean_object* v___x_480_; 
v___x_480_ = l_List_mapTR_loop___at___00List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0_spec__1(v_a_475_, v_b_476_, v_x_477_, v_x_478_);
return v___x_480_;
}
else
{
lean_object* v_head_481_; lean_object* v_tail_482_; lean_object* v_head_483_; lean_object* v_tail_484_; lean_object* v___x_486_; uint8_t v_isShared_487_; uint8_t v_isSharedCheck_495_; 
v_head_481_ = lean_ctor_get(v_x_477_, 0);
lean_inc(v_head_481_);
v_tail_482_ = lean_ctor_get(v_x_477_, 1);
lean_inc(v_tail_482_);
lean_dec_ref_known(v_x_477_, 2);
v_head_483_ = lean_ctor_get(v_x_478_, 0);
v_tail_484_ = lean_ctor_get(v_x_478_, 1);
v_isSharedCheck_495_ = !lean_is_exclusive(v_x_478_);
if (v_isSharedCheck_495_ == 0)
{
v___x_486_ = v_x_478_;
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
else
{
lean_inc(v_tail_484_);
lean_inc(v_head_483_);
lean_dec(v_x_478_);
v___x_486_ = lean_box(0);
v_isShared_487_ = v_isSharedCheck_495_;
goto v_resetjp_485_;
}
v_resetjp_485_:
{
lean_object* v___x_488_; lean_object* v___x_489_; lean_object* v___x_490_; lean_object* v___x_491_; lean_object* v___x_493_; 
v___x_488_ = lean_int_mul(v_a_475_, v_head_481_);
lean_dec(v_head_481_);
v___x_489_ = lean_int_mul(v_b_476_, v_head_483_);
lean_dec(v_head_483_);
v___x_490_ = lean_int_add(v___x_488_, v___x_489_);
lean_dec(v___x_489_);
lean_dec(v___x_488_);
v___x_491_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_475_, v_b_476_, v_tail_482_, v_tail_484_);
if (v_isShared_487_ == 0)
{
lean_ctor_set(v___x_486_, 1, v___x_491_);
lean_ctor_set(v___x_486_, 0, v___x_490_);
v___x_493_ = v___x_486_;
goto v_reusejp_492_;
}
else
{
lean_object* v_reuseFailAlloc_494_; 
v_reuseFailAlloc_494_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_494_, 0, v___x_490_);
lean_ctor_set(v_reuseFailAlloc_494_, 1, v___x_491_);
v___x_493_ = v_reuseFailAlloc_494_;
goto v_reusejp_492_;
}
v_reusejp_492_:
{
return v___x_493_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0___boxed(lean_object* v_a_496_, lean_object* v_b_497_, lean_object* v_x_498_, lean_object* v_x_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_496_, v_b_497_, v_x_498_, v_x_499_);
lean_dec(v_b_497_);
lean_dec(v_a_496_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo(lean_object* v_a_501_, lean_object* v_xs_502_, lean_object* v_b_503_, lean_object* v_ys_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_List_zipWithAll___at___00Lean_Omega_IntList_combo_spec__0(v_a_501_, v_b_503_, v_xs_502_, v_ys_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_combo___boxed(lean_object* v_a_506_, lean_object* v_xs_507_, lean_object* v_b_508_, lean_object* v_ys_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Omega_IntList_combo(v_a_506_, v_xs_507_, v_b_508_, v_ys_509_);
lean_dec(v_b_508_);
lean_dec(v_a_506_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sumImpl(lean_object* v_x_511_){
_start:
{
if (lean_obj_tag(v_x_511_) == 0)
{
lean_object* v___x_512_; 
v___x_512_ = lean_obj_once(&l_Lean_Omega_IntList_get___closed__0, &l_Lean_Omega_IntList_get___closed__0_once, _init_l_Lean_Omega_IntList_get___closed__0);
return v___x_512_;
}
else
{
lean_object* v_head_513_; lean_object* v_tail_514_; lean_object* v___x_515_; lean_object* v___x_516_; 
v_head_513_ = lean_ctor_get(v_x_511_, 0);
v_tail_514_ = lean_ctor_get(v_x_511_, 1);
v___x_515_ = l_Lean_Omega_IntList_sumImpl(v_tail_514_);
v___x_516_ = lean_int_add(v_head_513_, v___x_515_);
lean_dec(v___x_515_);
return v___x_516_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sumImpl___boxed(lean_object* v_x_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l_Lean_Omega_IntList_sumImpl(v_x_517_);
lean_dec(v_x_517_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_sumImpl_match__1_splitter___redArg(lean_object* v_x_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_){
_start:
{
if (lean_obj_tag(v_x_519_) == 0)
{
lean_object* v___x_522_; lean_object* v___x_523_; 
lean_dec(v_h__2_521_);
v___x_522_ = lean_box(0);
v___x_523_ = lean_apply_1(v_h__1_520_, v___x_522_);
return v___x_523_;
}
else
{
lean_object* v_head_524_; lean_object* v_tail_525_; lean_object* v___x_526_; 
lean_dec(v_h__1_520_);
v_head_524_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_head_524_);
v_tail_525_ = lean_ctor_get(v_x_519_, 1);
lean_inc(v_tail_525_);
lean_dec_ref_known(v_x_519_, 2);
v___x_526_ = lean_apply_2(v_h__2_521_, v_head_524_, v_tail_525_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Omega_IntList_0__Lean_Omega_IntList_sumImpl_match__1_splitter(lean_object* v_motive_527_, lean_object* v_x_528_, lean_object* v_h__1_529_, lean_object* v_h__2_530_){
_start:
{
if (lean_obj_tag(v_x_528_) == 0)
{
lean_object* v___x_531_; lean_object* v___x_532_; 
lean_dec(v_h__2_530_);
v___x_531_ = lean_box(0);
v___x_532_ = lean_apply_1(v_h__1_529_, v___x_531_);
return v___x_532_;
}
else
{
lean_object* v_head_533_; lean_object* v_tail_534_; lean_object* v___x_535_; 
lean_dec(v_h__1_529_);
v_head_533_ = lean_ctor_get(v_x_528_, 0);
lean_inc(v_head_533_);
v_tail_534_ = lean_ctor_get(v_x_528_, 1);
lean_inc(v_tail_534_);
lean_dec_ref_known(v_x_528_, 2);
v___x_535_ = lean_apply_2(v_h__2_530_, v_head_533_, v_tail_534_);
return v___x_535_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot(lean_object* v_xs_536_, lean_object* v_ys_537_){
_start:
{
lean_object* v___x_538_; lean_object* v___x_539_; 
v___x_538_ = l_Lean_Omega_IntList_mulImpl(v_xs_536_, v_ys_537_);
v___x_539_ = l_Lean_Omega_IntList_sumImpl(v___x_538_);
lean_dec(v___x_538_);
return v___x_539_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_dot___boxed(lean_object* v_xs_540_, lean_object* v_ys_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l_Lean_Omega_IntList_dot(v_xs_540_, v_ys_541_);
lean_dec(v_xs_540_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(lean_object* v_g_543_, lean_object* v_a_544_, lean_object* v_a_545_){
_start:
{
if (lean_obj_tag(v_a_544_) == 0)
{
lean_object* v___x_546_; 
v___x_546_ = l_List_reverse___redArg(v_a_545_);
return v___x_546_;
}
else
{
lean_object* v_head_547_; lean_object* v_tail_548_; lean_object* v___x_550_; uint8_t v_isShared_551_; uint8_t v_isSharedCheck_557_; 
v_head_547_ = lean_ctor_get(v_a_544_, 0);
v_tail_548_ = lean_ctor_get(v_a_544_, 1);
v_isSharedCheck_557_ = !lean_is_exclusive(v_a_544_);
if (v_isSharedCheck_557_ == 0)
{
v___x_550_ = v_a_544_;
v_isShared_551_ = v_isSharedCheck_557_;
goto v_resetjp_549_;
}
else
{
lean_inc(v_tail_548_);
lean_inc(v_head_547_);
lean_dec(v_a_544_);
v___x_550_ = lean_box(0);
v_isShared_551_ = v_isSharedCheck_557_;
goto v_resetjp_549_;
}
v_resetjp_549_:
{
lean_object* v___x_552_; lean_object* v___x_554_; 
v___x_552_ = lean_int_ediv(v_head_547_, v_g_543_);
lean_dec(v_head_547_);
if (v_isShared_551_ == 0)
{
lean_ctor_set(v___x_550_, 1, v_a_545_);
lean_ctor_set(v___x_550_, 0, v___x_552_);
v___x_554_ = v___x_550_;
goto v_reusejp_553_;
}
else
{
lean_object* v_reuseFailAlloc_556_; 
v_reuseFailAlloc_556_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_556_, 0, v___x_552_);
lean_ctor_set(v_reuseFailAlloc_556_, 1, v_a_545_);
v___x_554_ = v_reuseFailAlloc_556_;
goto v_reusejp_553_;
}
v_reusejp_553_:
{
v_a_544_ = v_tail_548_;
v_a_545_ = v___x_554_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0___boxed(lean_object* v_g_558_, lean_object* v_a_559_, lean_object* v_a_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(v_g_558_, v_a_559_, v_a_560_);
lean_dec(v_g_558_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv(lean_object* v_xs_562_, lean_object* v_g_563_){
_start:
{
lean_object* v___x_564_; lean_object* v___x_565_; 
v___x_564_ = lean_box(0);
v___x_565_ = l_List_mapTR_loop___at___00Lean_Omega_IntList_sdiv_spec__0(v_g_563_, v_xs_562_, v___x_564_);
return v___x_565_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_sdiv___boxed(lean_object* v_xs_566_, lean_object* v_g_567_){
_start:
{
lean_object* v_res_568_; 
v_res_568_ = l_Lean_Omega_IntList_sdiv(v_xs_566_, v_g_567_);
lean_dec(v_g_567_);
return v_res_568_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcdImpl(lean_object* v_x_569_){
_start:
{
if (lean_obj_tag(v_x_569_) == 0)
{
lean_object* v___x_570_; 
v___x_570_ = lean_unsigned_to_nat(0u);
return v___x_570_;
}
else
{
lean_object* v_head_571_; lean_object* v_tail_572_; lean_object* v___x_573_; lean_object* v___x_574_; lean_object* v___x_575_; 
v_head_571_ = lean_ctor_get(v_x_569_, 0);
v_tail_572_ = lean_ctor_get(v_x_569_, 1);
v___x_573_ = lean_nat_abs(v_head_571_);
v___x_574_ = l_Lean_Omega_IntList_gcdImpl(v_tail_572_);
v___x_575_ = lean_nat_gcd(v___x_573_, v___x_574_);
lean_dec(v___x_574_);
lean_dec(v___x_573_);
return v___x_575_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_gcdImpl___boxed(lean_object* v_x_576_){
_start:
{
lean_object* v_res_577_; 
v_res_577_ = l_Lean_Omega_IntList_gcdImpl(v_x_576_);
lean_dec(v_x_576_);
return v_res_577_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0(lean_object* v_m_578_, lean_object* v_x_579_){
_start:
{
lean_object* v___x_580_; 
v___x_580_ = l_Int_bmod(v_x_579_, v_m_578_);
return v___x_580_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod___lam__0___boxed(lean_object* v_m_581_, lean_object* v_x_582_){
_start:
{
lean_object* v_res_583_; 
v_res_583_ = l_Lean_Omega_IntList_bmod___lam__0(v_m_581_, v_x_582_);
lean_dec(v_x_582_);
return v_res_583_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod(lean_object* v_x_584_, lean_object* v_m_585_){
_start:
{
lean_object* v___f_586_; lean_object* v___x_587_; lean_object* v___x_588_; 
v___f_586_ = lean_alloc_closure((void*)(l_Lean_Omega_IntList_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_586_, 0, v_m_585_);
v___x_587_ = lean_box(0);
v___x_588_ = l_List_mapTR_loop___redArg(v___f_586_, v_x_584_, v___x_587_);
return v___x_588_;
}
}
LEAN_EXPORT lean_object* l_Lean_Omega_IntList_bmod__dot__sub__dot__bmod(lean_object* v_m_589_, lean_object* v_a_590_, lean_object* v_b_591_){
_start:
{
lean_object* v___f_592_; lean_object* v___x_593_; lean_object* v___x_594_; lean_object* v___x_595_; lean_object* v___x_596_; lean_object* v___x_597_; lean_object* v___x_598_; 
lean_inc(v_m_589_);
v___f_592_ = lean_alloc_closure((void*)(l_Lean_Omega_IntList_bmod___lam__0___boxed), 2, 1);
lean_closure_set(v___f_592_, 0, v_m_589_);
lean_inc(v_b_591_);
v___x_593_ = l_Lean_Omega_IntList_dot(v_a_590_, v_b_591_);
v___x_594_ = l_Int_bmod(v___x_593_, v_m_589_);
lean_dec(v___x_593_);
v___x_595_ = lean_box(0);
v___x_596_ = l_List_mapTR_loop___redArg(v___f_592_, v_a_590_, v___x_595_);
v___x_597_ = l_Lean_Omega_IntList_dot(v___x_596_, v_b_591_);
lean_dec(v___x_596_);
v___x_598_ = lean_int_sub(v___x_594_, v___x_597_);
lean_dec(v___x_597_);
lean_dec(v___x_594_);
return v___x_598_;
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
