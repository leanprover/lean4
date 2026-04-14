// Lean compiler output
// Module: Lean.Meta.Sym.Arith.VarRename
// Imports: public import Init.Grind.Ring.CommSemiringAdapter public import Lean.Meta.Tactic.Grind.VarRename
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
lean_object* lean_array_get_size(lean_object*);
uint64_t lean_uint64_of_nat(lean_object*);
uint64_t lean_uint64_shift_right(uint64_t, uint64_t);
uint64_t lean_uint64_xor(uint64_t, uint64_t);
size_t lean_uint64_to_usize(uint64_t);
size_t lean_usize_of_nat(lean_object*);
size_t lean_usize_sub(size_t, size_t);
size_t lean_usize_land(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* l_Lean_Meta_Grind_collectVar(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_CommRing_Expr_renameVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 3}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Grind_CommRing_Expr_renameVars___closed__0 = (const lean_object*)&l_Lean_Grind_CommRing_Expr_renameVars___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
_start:
{
if (lean_obj_tag(v_x_2_) == 0)
{
lean_object* v___x_3_; 
v___x_3_ = lean_box(0);
return v___x_3_;
}
else
{
lean_object* v_key_4_; lean_object* v_value_5_; lean_object* v_tail_6_; uint8_t v___x_7_; 
v_key_4_ = lean_ctor_get(v_x_2_, 0);
v_value_5_ = lean_ctor_get(v_x_2_, 1);
v_tail_6_ = lean_ctor_get(v_x_2_, 2);
v___x_7_ = lean_nat_dec_eq(v_key_4_, v_a_1_);
if (v___x_7_ == 0)
{
v_x_2_ = v_tail_6_;
goto _start;
}
else
{
lean_object* v___x_9_; 
lean_inc(v_value_5_);
v___x_9_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_9_, 0, v_value_5_);
return v___x_9_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(v_a_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(lean_object* v_m_13_, lean_object* v_a_14_){
_start:
{
lean_object* v_buckets_15_; lean_object* v___x_16_; uint64_t v___x_17_; uint64_t v___x_18_; uint64_t v___x_19_; uint64_t v_fold_20_; uint64_t v___x_21_; uint64_t v___x_22_; uint64_t v___x_23_; size_t v___x_24_; size_t v___x_25_; size_t v___x_26_; size_t v___x_27_; size_t v___x_28_; lean_object* v___x_29_; lean_object* v___x_30_; 
v_buckets_15_ = lean_ctor_get(v_m_13_, 1);
v___x_16_ = lean_array_get_size(v_buckets_15_);
v___x_17_ = lean_uint64_of_nat(v_a_14_);
v___x_18_ = 32ULL;
v___x_19_ = lean_uint64_shift_right(v___x_17_, v___x_18_);
v_fold_20_ = lean_uint64_xor(v___x_17_, v___x_19_);
v___x_21_ = 16ULL;
v___x_22_ = lean_uint64_shift_right(v_fold_20_, v___x_21_);
v___x_23_ = lean_uint64_xor(v_fold_20_, v___x_22_);
v___x_24_ = lean_uint64_to_usize(v___x_23_);
v___x_25_ = lean_usize_of_nat(v___x_16_);
v___x_26_ = ((size_t)1ULL);
v___x_27_ = lean_usize_sub(v___x_25_, v___x_26_);
v___x_28_ = lean_usize_land(v___x_24_, v___x_27_);
v___x_29_ = lean_array_uget_borrowed(v_buckets_15_, v___x_28_);
v___x_30_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(v_a_14_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg___boxed(lean_object* v_m_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_m_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_m_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars(lean_object* v_pw_34_, lean_object* v_f_35_){
_start:
{
lean_object* v_x_36_; lean_object* v_k_37_; lean_object* v___x_39_; uint8_t v_isShared_40_; uint8_t v_isSharedCheck_50_; 
v_x_36_ = lean_ctor_get(v_pw_34_, 0);
v_k_37_ = lean_ctor_get(v_pw_34_, 1);
v_isSharedCheck_50_ = !lean_is_exclusive(v_pw_34_);
if (v_isSharedCheck_50_ == 0)
{
v___x_39_ = v_pw_34_;
v_isShared_40_ = v_isSharedCheck_50_;
goto v_resetjp_38_;
}
else
{
lean_inc(v_k_37_);
lean_inc(v_x_36_);
lean_dec(v_pw_34_);
v___x_39_ = lean_box(0);
v_isShared_40_ = v_isSharedCheck_50_;
goto v_resetjp_38_;
}
v_resetjp_38_:
{
lean_object* v___x_41_; 
v___x_41_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_f_35_, v_x_36_);
lean_dec(v_x_36_);
if (lean_obj_tag(v___x_41_) == 0)
{
lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_42_ = lean_unsigned_to_nat(0u);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 0, v___x_42_);
v___x_44_ = v___x_39_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_45_; 
v_reuseFailAlloc_45_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_45_, 0, v___x_42_);
lean_ctor_set(v_reuseFailAlloc_45_, 1, v_k_37_);
v___x_44_ = v_reuseFailAlloc_45_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
return v___x_44_;
}
}
else
{
lean_object* v_val_46_; lean_object* v___x_48_; 
v_val_46_ = lean_ctor_get(v___x_41_, 0);
lean_inc(v_val_46_);
lean_dec_ref(v___x_41_);
if (v_isShared_40_ == 0)
{
lean_ctor_set(v___x_39_, 0, v_val_46_);
v___x_48_ = v___x_39_;
goto v_reusejp_47_;
}
else
{
lean_object* v_reuseFailAlloc_49_; 
v_reuseFailAlloc_49_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_49_, 0, v_val_46_);
lean_ctor_set(v_reuseFailAlloc_49_, 1, v_k_37_);
v___x_48_ = v_reuseFailAlloc_49_;
goto v_reusejp_47_;
}
v_reusejp_47_:
{
return v___x_48_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_renameVars___boxed(lean_object* v_pw_51_, lean_object* v_f_52_){
_start:
{
lean_object* v_res_53_; 
v_res_53_ = l_Lean_Grind_CommRing_Power_renameVars(v_pw_51_, v_f_52_);
lean_dec_ref(v_f_52_);
return v_res_53_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0(lean_object* v_00_u03b2_54_, lean_object* v_m_55_, lean_object* v_a_56_){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_m_55_, v_a_56_);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___boxed(lean_object* v_00_u03b2_58_, lean_object* v_m_59_, lean_object* v_a_60_){
_start:
{
lean_object* v_res_61_; 
v_res_61_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0(v_00_u03b2_58_, v_m_59_, v_a_60_);
lean_dec(v_a_60_);
lean_dec_ref(v_m_59_);
return v_res_61_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0(lean_object* v_00_u03b2_62_, lean_object* v_a_63_, lean_object* v_x_64_){
_start:
{
lean_object* v___x_65_; 
v___x_65_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___redArg(v_a_63_, v_x_64_);
return v___x_65_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_66_, lean_object* v_a_67_, lean_object* v_x_68_){
_start:
{
lean_object* v_res_69_; 
v_res_69_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0_spec__0(v_00_u03b2_66_, v_a_67_, v_x_68_);
lean_dec(v_x_68_);
lean_dec(v_a_67_);
return v_res_69_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars(lean_object* v_m_70_, lean_object* v_f_71_){
_start:
{
if (lean_obj_tag(v_m_70_) == 0)
{
return v_m_70_;
}
else
{
lean_object* v_p_72_; lean_object* v_m_73_; lean_object* v___x_75_; uint8_t v_isShared_76_; uint8_t v_isSharedCheck_82_; 
v_p_72_ = lean_ctor_get(v_m_70_, 0);
v_m_73_ = lean_ctor_get(v_m_70_, 1);
v_isSharedCheck_82_ = !lean_is_exclusive(v_m_70_);
if (v_isSharedCheck_82_ == 0)
{
v___x_75_ = v_m_70_;
v_isShared_76_ = v_isSharedCheck_82_;
goto v_resetjp_74_;
}
else
{
lean_inc(v_m_73_);
lean_inc(v_p_72_);
lean_dec(v_m_70_);
v___x_75_ = lean_box(0);
v_isShared_76_ = v_isSharedCheck_82_;
goto v_resetjp_74_;
}
v_resetjp_74_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_77_ = l_Lean_Grind_CommRing_Power_renameVars(v_p_72_, v_f_71_);
v___x_78_ = l_Lean_Grind_CommRing_Mon_renameVars(v_m_73_, v_f_71_);
if (v_isShared_76_ == 0)
{
lean_ctor_set(v___x_75_, 1, v___x_78_);
lean_ctor_set(v___x_75_, 0, v___x_77_);
v___x_80_ = v___x_75_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_77_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_renameVars___boxed(lean_object* v_m_83_, lean_object* v_f_84_){
_start:
{
lean_object* v_res_85_; 
v_res_85_ = l_Lean_Grind_CommRing_Mon_renameVars(v_m_83_, v_f_84_);
lean_dec_ref(v_f_84_);
return v_res_85_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars(lean_object* v_p_86_, lean_object* v_f_87_){
_start:
{
if (lean_obj_tag(v_p_86_) == 0)
{
return v_p_86_;
}
else
{
lean_object* v_k_88_; lean_object* v_v_89_; lean_object* v_p_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_99_; 
v_k_88_ = lean_ctor_get(v_p_86_, 0);
v_v_89_ = lean_ctor_get(v_p_86_, 1);
v_p_90_ = lean_ctor_get(v_p_86_, 2);
v_isSharedCheck_99_ = !lean_is_exclusive(v_p_86_);
if (v_isSharedCheck_99_ == 0)
{
v___x_92_ = v_p_86_;
v_isShared_93_ = v_isSharedCheck_99_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_p_90_);
lean_inc(v_v_89_);
lean_inc(v_k_88_);
lean_dec(v_p_86_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_99_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_97_; 
v___x_94_ = l_Lean_Grind_CommRing_Mon_renameVars(v_v_89_, v_f_87_);
v___x_95_ = l_Lean_Grind_CommRing_Poly_renameVars(v_p_90_, v_f_87_);
if (v_isShared_93_ == 0)
{
lean_ctor_set(v___x_92_, 2, v___x_95_);
lean_ctor_set(v___x_92_, 1, v___x_94_);
v___x_97_ = v___x_92_;
goto v_reusejp_96_;
}
else
{
lean_object* v_reuseFailAlloc_98_; 
v_reuseFailAlloc_98_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_98_, 0, v_k_88_);
lean_ctor_set(v_reuseFailAlloc_98_, 1, v___x_94_);
lean_ctor_set(v_reuseFailAlloc_98_, 2, v___x_95_);
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
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_renameVars___boxed(lean_object* v_p_100_, lean_object* v_f_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_Lean_Grind_CommRing_Poly_renameVars(v_p_100_, v_f_101_);
lean_dec_ref(v_f_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars(lean_object* v_e_105_, lean_object* v_f_106_){
_start:
{
switch(lean_obj_tag(v_e_105_))
{
case 3:
{
lean_object* v_i_107_; lean_object* v___x_109_; uint8_t v_isShared_110_; uint8_t v_isSharedCheck_117_; 
v_i_107_ = lean_ctor_get(v_e_105_, 0);
v_isSharedCheck_117_ = !lean_is_exclusive(v_e_105_);
if (v_isSharedCheck_117_ == 0)
{
v___x_109_ = v_e_105_;
v_isShared_110_ = v_isSharedCheck_117_;
goto v_resetjp_108_;
}
else
{
lean_inc(v_i_107_);
lean_dec(v_e_105_);
v___x_109_ = lean_box(0);
v_isShared_110_ = v_isSharedCheck_117_;
goto v_resetjp_108_;
}
v_resetjp_108_:
{
lean_object* v___x_111_; 
v___x_111_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_CommRing_Power_renameVars_spec__0___redArg(v_f_106_, v_i_107_);
lean_dec(v_i_107_);
if (lean_obj_tag(v___x_111_) == 0)
{
lean_object* v___x_112_; 
lean_del_object(v___x_109_);
v___x_112_ = ((lean_object*)(l_Lean_Grind_CommRing_Expr_renameVars___closed__0));
return v___x_112_;
}
else
{
lean_object* v_val_113_; lean_object* v___x_115_; 
v_val_113_ = lean_ctor_get(v___x_111_, 0);
lean_inc(v_val_113_);
lean_dec_ref(v___x_111_);
if (v_isShared_110_ == 0)
{
lean_ctor_set(v___x_109_, 0, v_val_113_);
v___x_115_ = v___x_109_;
goto v_reusejp_114_;
}
else
{
lean_object* v_reuseFailAlloc_116_; 
v_reuseFailAlloc_116_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v_reuseFailAlloc_116_, 0, v_val_113_);
v___x_115_ = v_reuseFailAlloc_116_;
goto v_reusejp_114_;
}
v_reusejp_114_:
{
return v___x_115_;
}
}
}
}
case 4:
{
lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
v_a_118_ = lean_ctor_get(v_e_105_, 0);
v_isSharedCheck_126_ = !lean_is_exclusive(v_e_105_);
if (v_isSharedCheck_126_ == 0)
{
v___x_120_ = v_e_105_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_dec(v_e_105_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_118_, v_f_106_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 0, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
case 5:
{
lean_object* v_a_127_; lean_object* v_b_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_137_; 
v_a_127_ = lean_ctor_get(v_e_105_, 0);
v_b_128_ = lean_ctor_get(v_e_105_, 1);
v_isSharedCheck_137_ = !lean_is_exclusive(v_e_105_);
if (v_isSharedCheck_137_ == 0)
{
v___x_130_ = v_e_105_;
v_isShared_131_ = v_isSharedCheck_137_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_b_128_);
lean_inc(v_a_127_);
lean_dec(v_e_105_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_137_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_133_; lean_object* v___x_135_; 
v___x_132_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_127_, v_f_106_);
v___x_133_ = l_Lean_Grind_CommRing_Expr_renameVars(v_b_128_, v_f_106_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_133_);
lean_ctor_set(v___x_130_, 0, v___x_132_);
v___x_135_ = v___x_130_;
goto v_reusejp_134_;
}
else
{
lean_object* v_reuseFailAlloc_136_; 
v_reuseFailAlloc_136_ = lean_alloc_ctor(5, 2, 0);
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
case 6:
{
lean_object* v_a_138_; lean_object* v_b_139_; lean_object* v___x_141_; uint8_t v_isShared_142_; uint8_t v_isSharedCheck_148_; 
v_a_138_ = lean_ctor_get(v_e_105_, 0);
v_b_139_ = lean_ctor_get(v_e_105_, 1);
v_isSharedCheck_148_ = !lean_is_exclusive(v_e_105_);
if (v_isSharedCheck_148_ == 0)
{
v___x_141_ = v_e_105_;
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
else
{
lean_inc(v_b_139_);
lean_inc(v_a_138_);
lean_dec(v_e_105_);
v___x_141_ = lean_box(0);
v_isShared_142_ = v_isSharedCheck_148_;
goto v_resetjp_140_;
}
v_resetjp_140_:
{
lean_object* v___x_143_; lean_object* v___x_144_; lean_object* v___x_146_; 
v___x_143_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_138_, v_f_106_);
v___x_144_ = l_Lean_Grind_CommRing_Expr_renameVars(v_b_139_, v_f_106_);
if (v_isShared_142_ == 0)
{
lean_ctor_set(v___x_141_, 1, v___x_144_);
lean_ctor_set(v___x_141_, 0, v___x_143_);
v___x_146_ = v___x_141_;
goto v_reusejp_145_;
}
else
{
lean_object* v_reuseFailAlloc_147_; 
v_reuseFailAlloc_147_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_147_, 0, v___x_143_);
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
case 7:
{
lean_object* v_a_149_; lean_object* v_b_150_; lean_object* v___x_152_; uint8_t v_isShared_153_; uint8_t v_isSharedCheck_159_; 
v_a_149_ = lean_ctor_get(v_e_105_, 0);
v_b_150_ = lean_ctor_get(v_e_105_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_e_105_);
if (v_isSharedCheck_159_ == 0)
{
v___x_152_ = v_e_105_;
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
else
{
lean_inc(v_b_150_);
lean_inc(v_a_149_);
lean_dec(v_e_105_);
v___x_152_ = lean_box(0);
v_isShared_153_ = v_isSharedCheck_159_;
goto v_resetjp_151_;
}
v_resetjp_151_:
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_157_; 
v___x_154_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_149_, v_f_106_);
v___x_155_ = l_Lean_Grind_CommRing_Expr_renameVars(v_b_150_, v_f_106_);
if (v_isShared_153_ == 0)
{
lean_ctor_set(v___x_152_, 1, v___x_155_);
lean_ctor_set(v___x_152_, 0, v___x_154_);
v___x_157_ = v___x_152_;
goto v_reusejp_156_;
}
else
{
lean_object* v_reuseFailAlloc_158_; 
v_reuseFailAlloc_158_ = lean_alloc_ctor(7, 2, 0);
lean_ctor_set(v_reuseFailAlloc_158_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_158_, 1, v___x_155_);
v___x_157_ = v_reuseFailAlloc_158_;
goto v_reusejp_156_;
}
v_reusejp_156_:
{
return v___x_157_;
}
}
}
case 8:
{
lean_object* v_a_160_; lean_object* v_k_161_; lean_object* v___x_163_; uint8_t v_isShared_164_; uint8_t v_isSharedCheck_169_; 
v_a_160_ = lean_ctor_get(v_e_105_, 0);
v_k_161_ = lean_ctor_get(v_e_105_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_e_105_);
if (v_isSharedCheck_169_ == 0)
{
v___x_163_ = v_e_105_;
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
else
{
lean_inc(v_k_161_);
lean_inc(v_a_160_);
lean_dec(v_e_105_);
v___x_163_ = lean_box(0);
v_isShared_164_ = v_isSharedCheck_169_;
goto v_resetjp_162_;
}
v_resetjp_162_:
{
lean_object* v___x_165_; lean_object* v___x_167_; 
v___x_165_ = l_Lean_Grind_CommRing_Expr_renameVars(v_a_160_, v_f_106_);
if (v_isShared_164_ == 0)
{
lean_ctor_set(v___x_163_, 0, v___x_165_);
v___x_167_ = v___x_163_;
goto v_reusejp_166_;
}
else
{
lean_object* v_reuseFailAlloc_168_; 
v_reuseFailAlloc_168_ = lean_alloc_ctor(8, 2, 0);
lean_ctor_set(v_reuseFailAlloc_168_, 0, v___x_165_);
lean_ctor_set(v_reuseFailAlloc_168_, 1, v_k_161_);
v___x_167_ = v_reuseFailAlloc_168_;
goto v_reusejp_166_;
}
v_reusejp_166_:
{
return v___x_167_;
}
}
}
default: 
{
return v_e_105_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_renameVars___boxed(lean_object* v_e_170_, lean_object* v_f_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_Lean_Grind_CommRing_Expr_renameVars(v_e_170_, v_f_171_);
lean_dec_ref(v_f_171_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Power_collectVars(lean_object* v_pw_173_, lean_object* v_a_174_){
_start:
{
lean_object* v_x_175_; lean_object* v___x_176_; 
v_x_175_ = lean_ctor_get(v_pw_173_, 0);
lean_inc(v_x_175_);
lean_dec_ref(v_pw_173_);
v___x_176_ = l_Lean_Meta_Grind_collectVar(v_x_175_, v_a_174_);
return v___x_176_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Mon_collectVars(lean_object* v_m_177_, lean_object* v_a_178_){
_start:
{
if (lean_obj_tag(v_m_177_) == 0)
{
return v_a_178_;
}
else
{
lean_object* v_p_179_; lean_object* v_m_180_; lean_object* v___x_181_; 
v_p_179_ = lean_ctor_get(v_m_177_, 0);
lean_inc_ref(v_p_179_);
v_m_180_ = lean_ctor_get(v_m_177_, 1);
lean_inc(v_m_180_);
lean_dec_ref(v_m_177_);
v___x_181_ = l_Lean_Grind_CommRing_Power_collectVars(v_p_179_, v_a_178_);
v_m_177_ = v_m_180_;
v_a_178_ = v___x_181_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Poly_collectVars(lean_object* v_p_183_, lean_object* v_a_184_){
_start:
{
if (lean_obj_tag(v_p_183_) == 0)
{
lean_dec_ref(v_p_183_);
return v_a_184_;
}
else
{
lean_object* v_v_185_; lean_object* v_p_186_; lean_object* v___x_187_; 
v_v_185_ = lean_ctor_get(v_p_183_, 1);
lean_inc(v_v_185_);
v_p_186_ = lean_ctor_get(v_p_183_, 2);
lean_inc_ref(v_p_186_);
lean_dec_ref(v_p_183_);
v___x_187_ = l_Lean_Grind_CommRing_Mon_collectVars(v_v_185_, v_a_184_);
v_p_183_ = v_p_186_;
v_a_184_ = v___x_187_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_CommRing_Expr_collectVars(lean_object* v_e_189_, lean_object* v_a_190_){
_start:
{
lean_object* v_a_192_; lean_object* v_b_193_; lean_object* v___y_194_; 
switch(lean_obj_tag(v_e_189_))
{
case 3:
{
lean_object* v_i_197_; lean_object* v___x_198_; 
v_i_197_ = lean_ctor_get(v_e_189_, 0);
lean_inc(v_i_197_);
lean_dec_ref(v_e_189_);
v___x_198_ = l_Lean_Meta_Grind_collectVar(v_i_197_, v_a_190_);
return v___x_198_;
}
case 4:
{
lean_object* v_a_199_; 
v_a_199_ = lean_ctor_get(v_e_189_, 0);
lean_inc_ref(v_a_199_);
lean_dec_ref(v_e_189_);
v_e_189_ = v_a_199_;
goto _start;
}
case 5:
{
lean_object* v_a_201_; lean_object* v_b_202_; 
v_a_201_ = lean_ctor_get(v_e_189_, 0);
lean_inc_ref(v_a_201_);
v_b_202_ = lean_ctor_get(v_e_189_, 1);
lean_inc_ref(v_b_202_);
lean_dec_ref(v_e_189_);
v_a_192_ = v_a_201_;
v_b_193_ = v_b_202_;
v___y_194_ = v_a_190_;
goto v___jp_191_;
}
case 6:
{
lean_object* v_a_203_; lean_object* v_b_204_; 
v_a_203_ = lean_ctor_get(v_e_189_, 0);
lean_inc_ref(v_a_203_);
v_b_204_ = lean_ctor_get(v_e_189_, 1);
lean_inc_ref(v_b_204_);
lean_dec_ref(v_e_189_);
v_a_192_ = v_a_203_;
v_b_193_ = v_b_204_;
v___y_194_ = v_a_190_;
goto v___jp_191_;
}
case 7:
{
lean_object* v_a_205_; lean_object* v_b_206_; 
v_a_205_ = lean_ctor_get(v_e_189_, 0);
lean_inc_ref(v_a_205_);
v_b_206_ = lean_ctor_get(v_e_189_, 1);
lean_inc_ref(v_b_206_);
lean_dec_ref(v_e_189_);
v_a_192_ = v_a_205_;
v_b_193_ = v_b_206_;
v___y_194_ = v_a_190_;
goto v___jp_191_;
}
case 8:
{
lean_object* v_a_207_; 
v_a_207_ = lean_ctor_get(v_e_189_, 0);
lean_inc_ref(v_a_207_);
lean_dec_ref(v_e_189_);
v_e_189_ = v_a_207_;
goto _start;
}
default: 
{
lean_dec_ref(v_e_189_);
return v_a_190_;
}
}
v___jp_191_:
{
lean_object* v___x_195_; 
v___x_195_ = l_Lean_Grind_CommRing_Expr_collectVars(v_a_192_, v___y_194_);
v_e_189_ = v_b_193_;
v_a_190_ = v___x_195_;
goto _start;
}
}
}
lean_object* runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Sym_Arith_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Sym_Arith_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ring_CommSemiringAdapter(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Sym_Arith_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ring_CommSemiringAdapter(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Sym_Arith_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Sym_Arith_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Sym_Arith_VarRename(builtin);
}
#ifdef __cplusplus
}
#endif
