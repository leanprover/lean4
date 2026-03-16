// Lean compiler output
// Module: Lean.Meta.Tactic.Grind.AC.VarRename
// Imports: public import Init.Grind.AC public import Lean.Meta.Tactic.Grind.VarRename
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg___boxed(lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_AC_Seq_renameVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Grind_AC_Seq_renameVars___closed__0 = (const lean_object*)&l_Lean_Grind_AC_Seq_renameVars___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Grind_AC_Expr_renameVars___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_Lean_Grind_AC_Expr_renameVars___closed__0 = (const lean_object*)&l_Lean_Grind_AC_Expr_renameVars___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_renameVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_renameVars___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_collectVars(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(lean_object* v_a_1_, lean_object* v_x_2_){
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
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg___boxed(lean_object* v_a_10_, lean_object* v_x_11_){
_start:
{
lean_object* v_res_12_; 
v_res_12_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(v_a_10_, v_x_11_);
lean_dec(v_x_11_);
lean_dec(v_a_10_);
return v_res_12_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(lean_object* v_m_13_, lean_object* v_a_14_){
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
v___x_30_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(v_a_14_, v___x_29_);
return v___x_30_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg___boxed(lean_object* v_m_31_, lean_object* v_a_32_){
_start:
{
lean_object* v_res_33_; 
v_res_33_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_m_31_, v_a_32_);
lean_dec(v_a_32_);
lean_dec_ref(v_m_31_);
return v_res_33_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_renameVars(lean_object* v_s_36_, lean_object* v_f_37_){
_start:
{
if (lean_obj_tag(v_s_36_) == 0)
{
lean_object* v_x_38_; lean_object* v___x_40_; uint8_t v_isShared_41_; uint8_t v_isSharedCheck_48_; 
v_x_38_ = lean_ctor_get(v_s_36_, 0);
v_isSharedCheck_48_ = !lean_is_exclusive(v_s_36_);
if (v_isSharedCheck_48_ == 0)
{
v___x_40_ = v_s_36_;
v_isShared_41_ = v_isSharedCheck_48_;
goto v_resetjp_39_;
}
else
{
lean_inc(v_x_38_);
lean_dec(v_s_36_);
v___x_40_ = lean_box(0);
v_isShared_41_ = v_isSharedCheck_48_;
goto v_resetjp_39_;
}
v_resetjp_39_:
{
lean_object* v___x_42_; 
v___x_42_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_f_37_, v_x_38_);
lean_dec(v_x_38_);
if (lean_obj_tag(v___x_42_) == 0)
{
lean_object* v___x_43_; 
lean_del_object(v___x_40_);
v___x_43_ = ((lean_object*)(l_Lean_Grind_AC_Seq_renameVars___closed__0));
return v___x_43_;
}
else
{
lean_object* v_val_44_; lean_object* v___x_46_; 
v_val_44_ = lean_ctor_get(v___x_42_, 0);
lean_inc(v_val_44_);
lean_dec_ref(v___x_42_);
if (v_isShared_41_ == 0)
{
lean_ctor_set(v___x_40_, 0, v_val_44_);
v___x_46_ = v___x_40_;
goto v_reusejp_45_;
}
else
{
lean_object* v_reuseFailAlloc_47_; 
v_reuseFailAlloc_47_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_47_, 0, v_val_44_);
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
else
{
lean_object* v_x_49_; lean_object* v_s_50_; lean_object* v___x_52_; uint8_t v_isShared_53_; uint8_t v_isSharedCheck_63_; 
v_x_49_ = lean_ctor_get(v_s_36_, 0);
v_s_50_ = lean_ctor_get(v_s_36_, 1);
v_isSharedCheck_63_ = !lean_is_exclusive(v_s_36_);
if (v_isSharedCheck_63_ == 0)
{
v___x_52_ = v_s_36_;
v_isShared_53_ = v_isSharedCheck_63_;
goto v_resetjp_51_;
}
else
{
lean_inc(v_s_50_);
lean_inc(v_x_49_);
lean_dec(v_s_36_);
v___x_52_ = lean_box(0);
v_isShared_53_ = v_isSharedCheck_63_;
goto v_resetjp_51_;
}
v_resetjp_51_:
{
lean_object* v___y_55_; lean_object* v___x_60_; 
v___x_60_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_f_37_, v_x_49_);
lean_dec(v_x_49_);
if (lean_obj_tag(v___x_60_) == 0)
{
lean_object* v___x_61_; 
v___x_61_ = lean_unsigned_to_nat(0u);
v___y_55_ = v___x_61_;
goto v___jp_54_;
}
else
{
lean_object* v_val_62_; 
v_val_62_ = lean_ctor_get(v___x_60_, 0);
lean_inc(v_val_62_);
lean_dec_ref(v___x_60_);
v___y_55_ = v_val_62_;
goto v___jp_54_;
}
v___jp_54_:
{
lean_object* v___x_56_; lean_object* v___x_58_; 
v___x_56_ = l_Lean_Grind_AC_Seq_renameVars(v_s_50_, v_f_37_);
if (v_isShared_53_ == 0)
{
lean_ctor_set(v___x_52_, 1, v___x_56_);
lean_ctor_set(v___x_52_, 0, v___y_55_);
v___x_58_ = v___x_52_;
goto v_reusejp_57_;
}
else
{
lean_object* v_reuseFailAlloc_59_; 
v_reuseFailAlloc_59_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_59_, 0, v___y_55_);
lean_ctor_set(v_reuseFailAlloc_59_, 1, v___x_56_);
v___x_58_ = v_reuseFailAlloc_59_;
goto v_reusejp_57_;
}
v_reusejp_57_:
{
return v___x_58_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_renameVars___boxed(lean_object* v_s_64_, lean_object* v_f_65_){
_start:
{
lean_object* v_res_66_; 
v_res_66_ = l_Lean_Grind_AC_Seq_renameVars(v_s_64_, v_f_65_);
lean_dec_ref(v_f_65_);
return v_res_66_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0(lean_object* v_00_u03b2_67_, lean_object* v_m_68_, lean_object* v_a_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_m_68_, v_a_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___boxed(lean_object* v_00_u03b2_71_, lean_object* v_m_72_, lean_object* v_a_73_){
_start:
{
lean_object* v_res_74_; 
v_res_74_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0(v_00_u03b2_71_, v_m_72_, v_a_73_);
lean_dec(v_a_73_);
lean_dec_ref(v_m_72_);
return v_res_74_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0(lean_object* v_00_u03b2_75_, lean_object* v_a_76_, lean_object* v_x_77_){
_start:
{
lean_object* v___x_78_; 
v___x_78_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___redArg(v_a_76_, v_x_77_);
return v___x_78_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0___boxed(lean_object* v_00_u03b2_79_, lean_object* v_a_80_, lean_object* v_x_81_){
_start:
{
lean_object* v_res_82_; 
v_res_82_ = l_Std_DHashMap_Internal_AssocList_get_x3f___at___00Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0_spec__0(v_00_u03b2_79_, v_a_80_, v_x_81_);
lean_dec(v_x_81_);
lean_dec(v_a_80_);
return v_res_82_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_renameVars(lean_object* v_e_85_, lean_object* v_f_86_){
_start:
{
if (lean_obj_tag(v_e_85_) == 0)
{
lean_object* v_x_87_; lean_object* v___x_89_; uint8_t v_isShared_90_; uint8_t v_isSharedCheck_97_; 
v_x_87_ = lean_ctor_get(v_e_85_, 0);
v_isSharedCheck_97_ = !lean_is_exclusive(v_e_85_);
if (v_isSharedCheck_97_ == 0)
{
v___x_89_ = v_e_85_;
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
else
{
lean_inc(v_x_87_);
lean_dec(v_e_85_);
v___x_89_ = lean_box(0);
v_isShared_90_ = v_isSharedCheck_97_;
goto v_resetjp_88_;
}
v_resetjp_88_:
{
lean_object* v___x_91_; 
v___x_91_ = l_Std_DHashMap_Internal_Raw_u2080_Const_get_x3f___at___00Lean_Grind_AC_Seq_renameVars_spec__0___redArg(v_f_86_, v_x_87_);
lean_dec(v_x_87_);
if (lean_obj_tag(v___x_91_) == 0)
{
lean_object* v___x_92_; 
lean_del_object(v___x_89_);
v___x_92_ = ((lean_object*)(l_Lean_Grind_AC_Expr_renameVars___closed__0));
return v___x_92_;
}
else
{
lean_object* v_val_93_; lean_object* v___x_95_; 
v_val_93_ = lean_ctor_get(v___x_91_, 0);
lean_inc(v_val_93_);
lean_dec_ref(v___x_91_);
if (v_isShared_90_ == 0)
{
lean_ctor_set(v___x_89_, 0, v_val_93_);
v___x_95_ = v___x_89_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_96_; 
v_reuseFailAlloc_96_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v_reuseFailAlloc_96_, 0, v_val_93_);
v___x_95_ = v_reuseFailAlloc_96_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
return v___x_95_;
}
}
}
}
else
{
lean_object* v_lhs_98_; lean_object* v_rhs_99_; lean_object* v___x_101_; uint8_t v_isShared_102_; uint8_t v_isSharedCheck_108_; 
v_lhs_98_ = lean_ctor_get(v_e_85_, 0);
v_rhs_99_ = lean_ctor_get(v_e_85_, 1);
v_isSharedCheck_108_ = !lean_is_exclusive(v_e_85_);
if (v_isSharedCheck_108_ == 0)
{
v___x_101_ = v_e_85_;
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
else
{
lean_inc(v_rhs_99_);
lean_inc(v_lhs_98_);
lean_dec(v_e_85_);
v___x_101_ = lean_box(0);
v_isShared_102_ = v_isSharedCheck_108_;
goto v_resetjp_100_;
}
v_resetjp_100_:
{
lean_object* v___x_103_; lean_object* v___x_104_; lean_object* v___x_106_; 
v___x_103_ = l_Lean_Grind_AC_Expr_renameVars(v_lhs_98_, v_f_86_);
v___x_104_ = l_Lean_Grind_AC_Expr_renameVars(v_rhs_99_, v_f_86_);
if (v_isShared_102_ == 0)
{
lean_ctor_set(v___x_101_, 1, v___x_104_);
lean_ctor_set(v___x_101_, 0, v___x_103_);
v___x_106_ = v___x_101_;
goto v_reusejp_105_;
}
else
{
lean_object* v_reuseFailAlloc_107_; 
v_reuseFailAlloc_107_ = lean_alloc_ctor(1, 2, 0);
lean_ctor_set(v_reuseFailAlloc_107_, 0, v___x_103_);
lean_ctor_set(v_reuseFailAlloc_107_, 1, v___x_104_);
v___x_106_ = v_reuseFailAlloc_107_;
goto v_reusejp_105_;
}
v_reusejp_105_:
{
return v___x_106_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_renameVars___boxed(lean_object* v_e_109_, lean_object* v_f_110_){
_start:
{
lean_object* v_res_111_; 
v_res_111_ = l_Lean_Grind_AC_Expr_renameVars(v_e_109_, v_f_110_);
lean_dec_ref(v_f_110_);
return v_res_111_;
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Seq_collectVars(lean_object* v_s_112_, lean_object* v_a_113_){
_start:
{
if (lean_obj_tag(v_s_112_) == 0)
{
lean_object* v_x_114_; lean_object* v___x_115_; 
v_x_114_ = lean_ctor_get(v_s_112_, 0);
lean_inc(v_x_114_);
lean_dec_ref(v_s_112_);
v___x_115_ = l_Lean_Meta_Grind_collectVar(v_x_114_, v_a_113_);
return v___x_115_;
}
else
{
lean_object* v_x_116_; lean_object* v_s_117_; lean_object* v___x_118_; 
v_x_116_ = lean_ctor_get(v_s_112_, 0);
lean_inc(v_x_116_);
v_s_117_ = lean_ctor_get(v_s_112_, 1);
lean_inc_ref(v_s_117_);
lean_dec_ref(v_s_112_);
v___x_118_ = l_Lean_Meta_Grind_collectVar(v_x_116_, v_a_113_);
v_s_112_ = v_s_117_;
v_a_113_ = v___x_118_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Grind_AC_Expr_collectVars(lean_object* v_e_120_, lean_object* v_a_121_){
_start:
{
if (lean_obj_tag(v_e_120_) == 0)
{
lean_object* v_x_122_; lean_object* v___x_123_; 
v_x_122_ = lean_ctor_get(v_e_120_, 0);
lean_inc(v_x_122_);
lean_dec_ref(v_e_120_);
v___x_123_ = l_Lean_Meta_Grind_collectVar(v_x_122_, v_a_121_);
return v___x_123_;
}
else
{
lean_object* v_lhs_124_; lean_object* v_rhs_125_; lean_object* v___x_126_; 
v_lhs_124_ = lean_ctor_get(v_e_120_, 0);
lean_inc_ref(v_lhs_124_);
v_rhs_125_ = lean_ctor_get(v_e_120_, 1);
lean_inc_ref(v_rhs_125_);
lean_dec_ref(v_e_120_);
v___x_126_ = l_Lean_Grind_AC_Expr_collectVars(v_lhs_124_, v_a_121_);
v_e_120_ = v_rhs_125_;
v_a_121_ = v___x_126_;
goto _start;
}
}
}
lean_object* runtime_initialize_Init_Grind_AC(uint8_t builtin);
lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Grind_AC(uint8_t builtin);
lean_object* initialize_Lean_Meta_Tactic_Grind_VarRename(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Meta_Tactic_Grind_AC_VarRename(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Grind_AC(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Lean_Meta_Tactic_Grind_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Meta_Tactic_Grind_AC_VarRename(builtin);
}
#ifdef __cplusplus
}
#endif
