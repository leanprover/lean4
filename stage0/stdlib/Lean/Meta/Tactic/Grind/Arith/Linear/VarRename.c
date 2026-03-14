// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.Arith.Linear.VarRename
// Imports: public import Init.Grind.Ordered.Linarith public import Lean.Meta.Tactic.Grind.VarRename
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_Linarith_Expr_renameVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 1}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Grind_Linarith_Expr_renameVars___closed__0 = (const lean_object*)&l_Lean_Grind_Linarith_Expr_renameVars___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg(v_a_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(lean_object* v_m_13_, lean_object* v_a_14_){
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
v___x_30_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg(v_a_14_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg___boxed(lean_object* v_m_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(v_m_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_m_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_renameVars(lean_object* v_p_34_, lean_object* v_f_35_){
_start:
{
if (lean_obj_tag(v_p_34_) == 0)
{
return v_p_34_;
}
else
{
lean_object* v_k_36_; lean_object* v_v_37_; lean_object* v_p_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_51_; 
v_k_36_ = lean_ctor_get(v_p_34_, 0);
v_v_37_ = lean_ctor_get(v_p_34_, 1);
v_p_38_ = lean_ctor_get(v_p_34_, 2);
v_isSharedCheck_51_ = !lean_is_exclusive(v_p_34_);
if (v_isSharedCheck_51_ == 0)
{
v___x_40_ = v_p_34_;
v_isShared_41_ = v_isSharedCheck_51_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_p_38_);
lean_inc(v_v_37_);
lean_inc(v_k_36_);
lean_dec(v_p_34_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_51_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___y_43_; lean_object* v___x_48_; 
v___x_48_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(v_f_35_, v_v_37_);
lean_dec(v_v_37_);
if (lean_obj_tag(v___x_48_) == 0)
{
lean_object* v___x_49_; 
v___x_49_ = lean_unsigned_to_nat(0u);
v___y_43_ = v___x_49_;
goto v___jp_42_;
}
else
{
lean_object* v_val_50_; 
v_val_50_ = lean_ctor_get(v___x_48_, 0);
lean_inc(v_val_50_);
lean_dec_ref(v___x_48_);
v___y_43_ = v_val_50_;
goto v___jp_42_;
}
v___jp_42_:
{
lean_object* v___x_44_; lean_object* v___x_46_; 
v___x_44_ = l_Lean_Grind_Linarith_Poly_renameVars(v_p_38_, v_f_35_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 2, v___x_44_);
lean_ctor_set(v___x_40_, 1, v___y_43_);
v___x_46_ = v___x_40_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(1, 3, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_k_36_);
lean_ctor_set(v_reuseFailAlloc_47_, 1, v___y_43_);
lean_ctor_set(v_reuseFailAlloc_47_, 2, v___x_44_);
v___x_46_ = v_reuseFailAlloc_47_;
goto v_reusejp_45_;
}
v_reusejp_45_:
{
return v___x_46_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_renameVars___boxed(lean_object* v_p_52_, lean_object* v_f_53_){
_start:
{
lean_object* v_res_54_; 
v_res_54_ = l_Lean_Grind_Linarith_Poly_renameVars(v_p_52_, v_f_53_);
lean_dec_ref(v_f_53_);
return v_res_54_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0(lean_object* v_00_u03b2_55_, lean_object* v_m_56_, lean_object* v_a_57_){
_start:
{
lean_object* v___x_58_; 
v___x_58_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(v_m_56_, v_a_57_);
return v___x_58_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___boxed(lean_object* v_00_u03b2_59_, lean_object* v_m_60_, lean_object* v_a_61_){
_start:
{
lean_object* v_res_62_; 
v_res_62_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0(v_00_u03b2_59_, v_m_60_, v_a_61_);
lean_dec(v_a_61_);
lean_dec_ref(v_m_60_);
return v_res_62_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0(lean_object* v_00_u03b2_63_, lean_object* v_a_64_, lean_object* v_x_65_){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___redArg(v_a_64_, v_x_65_);
return v___x_66_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_67_, lean_object* v_a_68_, lean_object* v_x_69_){
_start:
{
lean_object* v_res_70_; 
v_res_70_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0_spec__0(v_00_u03b2_67_, v_a_68_, v_x_69_);
lean_dec(v_x_69_);
lean_dec(v_a_68_);
return v_res_70_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_renameVars(lean_object* v_e_73_, lean_object* v_f_74_){
_start:
{
switch(lean_obj_tag(v_e_73_))
{
case 0:
{
return v_e_73_;
}
case 1:
{
lean_object* v_i_75_; lean_object* v___x_77_; uint8_t v_isShared_78_; uint8_t v_isSharedCheck_85_; 
v_i_75_ = lean_ctor_get(v_e_73_, 0);
v_isSharedCheck_85_ = !lean_is_exclusive(v_e_73_);
if (v_isSharedCheck_85_ == 0)
{
v___x_77_ = v_e_73_;
v_isShared_78_ = v_isSharedCheck_85_;
goto v_resetjp_76_;
}
else
{
lean_inc(v_i_75_);
lean_dec(v_e_73_);
v___x_77_ = lean_box(0);
v_isShared_78_ = v_isSharedCheck_85_;
goto v_resetjp_76_;
}
v_resetjp_76_:
{
lean_object* v___x_79_; 
v___x_79_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_Linarith_Poly_renameVars_spec__0___redArg(v_f_74_, v_i_75_);
lean_dec(v_i_75_);
if (lean_obj_tag(v___x_79_) == 0)
{
lean_object* v___x_80_; 
lean_del_object(v___x_77_);
v___x_80_ = ((lean_object*)(l_Lean_Grind_Linarith_Expr_renameVars___closed__0));
return v___x_80_;
}
else
{
lean_object* v_val_81_; lean_object* v___x_83_; 
v_val_81_ = lean_ctor_get(v___x_79_, 0);
lean_inc(v_val_81_);
lean_dec_ref(v___x_79_);
if (v_isShared_78_ == 0)
{
lean_ctor_set(v___x_77_, 0, v_val_81_);
v___x_83_ = v___x_77_;
goto v_reusejp_82_;
}
else
{
lean_object* v_reuseFailAlloc_84_; 
v_reuseFailAlloc_84_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_84_, 0, v_val_81_);
v___x_83_ = v_reuseFailAlloc_84_;
goto v_reusejp_82_;
}
v_reusejp_82_:
{
return v___x_83_;
}
}
}
}
case 2:
{
lean_object* v_a_86_; lean_object* v_b_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_96_; 
v_a_86_ = lean_ctor_get(v_e_73_, 0);
v_b_87_ = lean_ctor_get(v_e_73_, 1);
v_isSharedCheck_96_ = !lean_is_exclusive(v_e_73_);
if (v_isSharedCheck_96_ == 0)
{
v___x_89_ = v_e_73_;
v_isShared_90_ = v_isSharedCheck_96_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_b_87_);
lean_inc(v_a_86_);
lean_dec(v_e_73_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_96_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; lean_object* v___x_92_; lean_object* v___x_94_; 
v___x_91_ = l_Lean_Grind_Linarith_Expr_renameVars(v_a_86_, v_f_74_);
v___x_92_ = l_Lean_Grind_Linarith_Expr_renameVars(v_b_87_, v_f_74_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 1, v___x_92_);
lean_ctor_set(v___x_89_, 0, v___x_91_);
v___x_94_ = v___x_89_;
goto v_reusejp_93_;
}
else
{
lean_object* v_reuseFailAlloc_95_; 
v_reuseFailAlloc_95_ = lean_alloc_ctor(2, 2, 0);
lean_ctor_set(v_reuseFailAlloc_95_, 0, v___x_91_);
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
case 3:
{
lean_object* v_a_97_; lean_object* v_b_98_; lean_object* v___x_100_; uint8_t v_isShared_101_; uint8_t v_isSharedCheck_107_; 
v_a_97_ = lean_ctor_get(v_e_73_, 0);
v_b_98_ = lean_ctor_get(v_e_73_, 1);
v_isSharedCheck_107_ = !lean_is_exclusive(v_e_73_);
if (v_isSharedCheck_107_ == 0)
{
v___x_100_ = v_e_73_;
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
else
{
lean_inc(v_b_98_);
lean_inc(v_a_97_);
lean_dec(v_e_73_);
v___x_100_ = lean_box(0);
v_isShared_101_ = v_isSharedCheck_107_;
goto v_resetjp_99_;
}
v_resetjp_99_:
{
lean_object* v___x_102_; lean_object* v___x_103_; lean_object* v___x_105_; 
v___x_102_ = l_Lean_Grind_Linarith_Expr_renameVars(v_a_97_, v_f_74_);
v___x_103_ = l_Lean_Grind_Linarith_Expr_renameVars(v_b_98_, v_f_74_);
if (v_isShared_101_ == 0)
{
lean_ctor_set(v___x_100_, 1, v___x_103_);
lean_ctor_set(v___x_100_, 0, v___x_102_);
v___x_105_ = v___x_100_;
goto v_reusejp_104_;
}
else
{
lean_object* v_reuseFailAlloc_106_; 
v_reuseFailAlloc_106_ = lean_alloc_ctor(3, 2, 0);
lean_ctor_set(v_reuseFailAlloc_106_, 0, v___x_102_);
lean_ctor_set(v_reuseFailAlloc_106_, 1, v___x_103_);
v___x_105_ = v_reuseFailAlloc_106_;
goto v_reusejp_104_;
}
v_reusejp_104_:
{
return v___x_105_;
}
}
}
case 4:
{
lean_object* v_a_108_; lean_object* v___x_110_; uint8_t v_isShared_111_; uint8_t v_isSharedCheck_116_; 
v_a_108_ = lean_ctor_get(v_e_73_, 0);
v_isSharedCheck_116_ = !lean_is_exclusive(v_e_73_);
if (v_isSharedCheck_116_ == 0)
{
v___x_110_ = v_e_73_;
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
else
{
lean_inc(v_a_108_);
lean_dec(v_e_73_);
v___x_110_ = lean_box(0);
v_isShared_111_ = v_isSharedCheck_116_;
goto v_resetjp_109_;
}
v_resetjp_109_:
{
lean_object* v___x_112_; lean_object* v___x_114_; 
v___x_112_ = l_Lean_Grind_Linarith_Expr_renameVars(v_a_108_, v_f_74_);
if (v_isShared_111_ == 0)
{
lean_ctor_set(v___x_110_, 0, v___x_112_);
v___x_114_ = v___x_110_;
goto v_reusejp_113_;
}
else
{
lean_object* v_reuseFailAlloc_115_; 
v_reuseFailAlloc_115_ = lean_alloc_ctor(4, 1, 0);
lean_ctor_set(v_reuseFailAlloc_115_, 0, v___x_112_);
v___x_114_ = v_reuseFailAlloc_115_;
goto v_reusejp_113_;
}
v_reusejp_113_:
{
return v___x_114_;
}
}
}
case 5:
{
lean_object* v_k_117_; lean_object* v_a_118_; lean_object* v___x_120_; uint8_t v_isShared_121_; uint8_t v_isSharedCheck_126_; 
v_k_117_ = lean_ctor_get(v_e_73_, 0);
v_a_118_ = lean_ctor_get(v_e_73_, 1);
v_isSharedCheck_126_ = !lean_is_exclusive(v_e_73_);
if (v_isSharedCheck_126_ == 0)
{
v___x_120_ = v_e_73_;
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
else
{
lean_inc(v_a_118_);
lean_inc(v_k_117_);
lean_dec(v_e_73_);
v___x_120_ = lean_box(0);
v_isShared_121_ = v_isSharedCheck_126_;
goto v_resetjp_119_;
}
v_resetjp_119_:
{
lean_object* v___x_122_; lean_object* v___x_124_; 
v___x_122_ = l_Lean_Grind_Linarith_Expr_renameVars(v_a_118_, v_f_74_);
if (v_isShared_121_ == 0)
{
lean_ctor_set(v___x_120_, 1, v___x_122_);
v___x_124_ = v___x_120_;
goto v_reusejp_123_;
}
else
{
lean_object* v_reuseFailAlloc_125_; 
v_reuseFailAlloc_125_ = lean_alloc_ctor(5, 2, 0);
lean_ctor_set(v_reuseFailAlloc_125_, 0, v_k_117_);
lean_ctor_set(v_reuseFailAlloc_125_, 1, v___x_122_);
v___x_124_ = v_reuseFailAlloc_125_;
goto v_reusejp_123_;
}
v_reusejp_123_:
{
return v___x_124_;
}
}
}
default: 
{
lean_object* v_k_127_; lean_object* v_a_128_; lean_object* v___x_130_; uint8_t v_isShared_131_; uint8_t v_isSharedCheck_136_; 
v_k_127_ = lean_ctor_get(v_e_73_, 0);
v_a_128_ = lean_ctor_get(v_e_73_, 1);
v_isSharedCheck_136_ = !lean_is_exclusive(v_e_73_);
if (v_isSharedCheck_136_ == 0)
{
v___x_130_ = v_e_73_;
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
else
{
lean_inc(v_a_128_);
lean_inc(v_k_127_);
lean_dec(v_e_73_);
v___x_130_ = lean_box(0);
v_isShared_131_ = v_isSharedCheck_136_;
goto v_resetjp_129_;
}
v_resetjp_129_:
{
lean_object* v___x_132_; lean_object* v___x_134_; 
v___x_132_ = l_Lean_Grind_Linarith_Expr_renameVars(v_a_128_, v_f_74_);
if (v_isShared_131_ == 0)
{
lean_ctor_set(v___x_130_, 1, v___x_132_);
v___x_134_ = v___x_130_;
goto v_reusejp_133_;
}
else
{
lean_object* v_reuseFailAlloc_135_; 
v_reuseFailAlloc_135_ = lean_alloc_ctor(6, 2, 0);
lean_ctor_set(v_reuseFailAlloc_135_, 0, v_k_127_);
lean_ctor_set(v_reuseFailAlloc_135_, 1, v___x_132_);
v___x_134_ = v_reuseFailAlloc_135_;
goto v_reusejp_133_;
}
v_reusejp_133_:
{
return v___x_134_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_renameVars___boxed(lean_object* v_e_137_, lean_object* v_f_138_){
_start:
{
lean_object* v_res_139_; 
v_res_139_ = l_Lean_Grind_Linarith_Expr_renameVars(v_e_137_, v_f_138_);
lean_dec_ref(v_f_138_);
return v_res_139_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Poly_collectVars(lean_object* v_p_140_, lean_object* v_a_141_){
_start:
{
if (lean_obj_tag(v_p_140_) == 0)
{
return v_a_141_;
}
else
{
lean_object* v_v_142_; lean_object* v_p_143_; lean_object* v___x_144_; 
v_v_142_ = lean_ctor_get(v_p_140_, 1);
lean_inc(v_v_142_);
v_p_143_ = lean_ctor_get(v_p_140_, 2);
lean_inc(v_p_143_);
lean_dec_ref(v_p_140_);
v___x_144_ = l_Lean_Meta_Grind_collectVar(v_v_142_, v_a_141_);
v_p_140_ = v_p_143_;
v_a_141_ = v___x_144_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_Linarith_Expr_collectVars(lean_object* v_e_146_, lean_object* v_a_147_){
_start:
{
lean_object* v_a_149_; lean_object* v_b_150_; lean_object* v___y_151_; 
switch(lean_obj_tag(v_e_146_))
{
case 0:
{
return v_a_147_;
}
case 1:
{
lean_object* v_i_154_; lean_object* v___x_155_; 
v_i_154_ = lean_ctor_get(v_e_146_, 0);
lean_inc(v_i_154_);
lean_dec_ref(v_e_146_);
v___x_155_ = l_Lean_Meta_Grind_collectVar(v_i_154_, v_a_147_);
return v___x_155_;
}
case 4:
{
lean_object* v_a_156_; 
v_a_156_ = lean_ctor_get(v_e_146_, 0);
lean_inc(v_a_156_);
lean_dec_ref(v_e_146_);
v_e_146_ = v_a_156_;
goto _start;
}
case 5:
{
lean_object* v_a_158_; 
v_a_158_ = lean_ctor_get(v_e_146_, 1);
lean_inc(v_a_158_);
lean_dec_ref(v_e_146_);
v_e_146_ = v_a_158_;
goto _start;
}
case 6:
{
lean_object* v_a_160_; 
v_a_160_ = lean_ctor_get(v_e_146_, 1);
lean_inc(v_a_160_);
lean_dec_ref(v_e_146_);
v_e_146_ = v_a_160_;
goto _start;
}
default: 
{
lean_object* v_a_162_; lean_object* v_b_163_; 
v_a_162_ = lean_ctor_get(v_e_146_, 0);
lean_inc(v_a_162_);
v_b_163_ = lean_ctor_get(v_e_146_, 1);
lean_inc(v_b_163_);
lean_dec(v_e_146_);
v_a_149_ = v_a_162_;
v_b_150_ = v_b_163_;
v___y_151_ = v_a_147_;
goto v___jp_148_;
}
}
v___jp_148_:
{
lean_object* v___x_152_; 
v___x_152_ = l_Lean_Grind_Linarith_Expr_collectVars(v_a_149_, v___y_151_);
v_e_146_ = v_b_150_;
v_a_147_ = v___x_152_;
goto _start;
}
}
}
lean_object* runtime_initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_Ordered_Linarith(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_Ordered_Linarith(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_Arith_Linear_VarRename(builtin);
}
#ifdef __cplusplus
}
#endif
