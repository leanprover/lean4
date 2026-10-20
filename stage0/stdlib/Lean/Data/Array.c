// Lean compiler output
// Module: Lean.Data.Array
// Imports: import Init.Data.Stream public import Init.Data.Range.Polymorphic.Nat public import Init.Data.Range.Polymorphic.Iterators
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
lean_object* lean_nat_add(lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Lean_Array_mask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Lean_Array_mask___redArg___closed__0 = (const lean_object*)&l_Lean_Array_mask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Lean_Array_mask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_mask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_mask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_mask___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Lean_Array_zipMasked___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Array_mask___redArg___closed__0_value)}};
static const lean_object* l_Lean_Array_zipMasked___redArg___closed__0 = (const lean_object*)&l_Lean_Array_zipMasked___redArg___closed__0_value;
static const lean_ctor_object l_Lean_Array_zipMasked___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Lean_Array_zipMasked___redArg___closed__0_value)}};
static const lean_object* l_Lean_Array_zipMasked___redArg___closed__1 = (const lean_object*)&l_Lean_Array_zipMasked___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_____do__lift_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_2(v_toPure_1_, lean_box(0), v_____do__lift_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__2(lean_object* v_toPure_4_, lean_object* v_____do__lift_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_2(v_toPure_4_, lean_box(0), v_____do__lift_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__1(lean_object* v_toPure_7_, lean_object* v_____s_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_2(v_toPure_7_, lean_box(0), v_____s_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__3(lean_object* v_toPure_10_, lean_object* v_next_11_, lean_object* v_G_12_, lean_object* v_____do__lift_13_){
_start:
{
if (lean_obj_tag(v_____do__lift_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
lean_dec(v_G_12_);
v_a_14_ = lean_ctor_get(v_____do__lift_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref_known(v_____do__lift_13_, 1);
v___x_15_ = lean_apply_2(v_toPure_10_, lean_box(0), v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_toPure_10_);
v_a_16_ = lean_ctor_get(v_____do__lift_13_, 0);
lean_inc(v_a_16_);
lean_dec_ref_known(v_____do__lift_13_, 1);
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_add(v_next_11_, v___x_17_);
v___x_19_ = lean_apply_4(v_G_12_, v___x_18_, v_a_16_, lean_box(0), lean_box(0));
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__3___boxed(lean_object* v_toPure_20_, lean_object* v_next_21_, lean_object* v_G_22_, lean_object* v_____do__lift_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Lean_Array_filterPairsM___redArg___lam__3(v_toPure_20_, v_next_21_, v_G_22_, v_____do__lift_23_);
lean_dec(v_next_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__4(lean_object* v___x_25_, lean_object* v_toPure_26_, lean_object* v_toBind_27_, lean_object* v___f_28_, uint8_t v___x_29_, lean_object* v_fst_30_, lean_object* v_a_31_, lean_object* v_next_32_, lean_object* v_acc_33_, lean_object* v_h_34_, lean_object* v_G_35_){
_start:
{
uint8_t v___x_36_; 
v___x_36_ = lean_nat_dec_lt(v_next_32_, v___x_25_);
if (v___x_36_ == 0)
{
lean_object* v___x_37_; 
lean_dec(v_G_35_);
lean_dec(v_next_32_);
lean_dec(v___f_28_);
lean_dec(v_toBind_27_);
v___x_37_ = lean_apply_2(v_toPure_26_, lean_box(0), v_acc_33_);
return v___x_37_;
}
else
{
lean_object* v___f_38_; lean_object* v___y_40_; lean_object* v___x_43_; lean_object* v___x_44_; uint8_t v___x_45_; 
lean_inc(v_next_32_);
lean_inc(v_toPure_26_);
v___f_38_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__3___boxed), 4, 3);
lean_closure_set(v___f_38_, 0, v_toPure_26_);
lean_closure_set(v___f_38_, 1, v_next_32_);
lean_closure_set(v___f_38_, 2, v_G_35_);
v___x_43_ = lean_box(v___x_29_);
v___x_44_ = lean_array_get(v___x_43_, v_fst_30_, v_next_32_);
lean_dec(v___x_43_);
v___x_45_ = lean_unbox(v___x_44_);
lean_dec(v___x_44_);
if (v___x_45_ == 0)
{
lean_object* v___x_46_; lean_object* v___x_47_; lean_object* v___x_48_; lean_object* v___x_49_; 
v___x_46_ = lean_array_fget_borrowed(v_a_31_, v_next_32_);
lean_dec(v_next_32_);
lean_inc(v___x_46_);
v___x_47_ = lean_array_push(v_acc_33_, v___x_46_);
v___x_48_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_48_, 0, v___x_47_);
v___x_49_ = lean_apply_2(v_toPure_26_, lean_box(0), v___x_48_);
v___y_40_ = v___x_49_;
goto v___jp_39_;
}
else
{
lean_object* v___x_50_; lean_object* v___x_51_; 
lean_dec(v_next_32_);
v___x_50_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_50_, 0, v_acc_33_);
v___x_51_ = lean_apply_2(v_toPure_26_, lean_box(0), v___x_50_);
v___y_40_ = v___x_51_;
goto v___jp_39_;
}
v___jp_39_:
{
lean_object* v___x_41_; lean_object* v___x_42_; 
lean_inc(v_toBind_27_);
v___x_41_ = lean_apply_4(v_toBind_27_, lean_box(0), lean_box(0), v___y_40_, v___f_28_);
v___x_42_ = lean_apply_4(v_toBind_27_, lean_box(0), lean_box(0), v___x_41_, v___f_38_);
return v___x_42_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__4___boxed(lean_object* v___x_52_, lean_object* v_toPure_53_, lean_object* v_toBind_54_, lean_object* v___f_55_, lean_object* v___x_56_, lean_object* v_fst_57_, lean_object* v_a_58_, lean_object* v_next_59_, lean_object* v_acc_60_, lean_object* v_h_61_, lean_object* v_G_62_){
_start:
{
uint8_t v___x_890__boxed_63_; lean_object* v_res_64_; 
v___x_890__boxed_63_ = lean_unbox(v___x_56_);
v_res_64_ = l_Lean_Array_filterPairsM___redArg___lam__4(v___x_52_, v_toPure_53_, v_toBind_54_, v___f_55_, v___x_890__boxed_63_, v_fst_57_, v_a_58_, v_next_59_, v_acc_60_, v_h_61_, v_G_62_);
lean_dec_ref(v_a_58_);
lean_dec(v_fst_57_);
lean_dec(v___x_52_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__5(lean_object* v___x_65_, lean_object* v_toPure_66_, lean_object* v_toBind_67_, lean_object* v___f_68_, uint8_t v___x_69_, lean_object* v_a_70_, lean_object* v___f_71_, lean_object* v_____s_72_){
_start:
{
lean_object* v_fst_73_; lean_object* v_snd_74_; lean_object* v___x_75_; lean_object* v___x_76_; lean_object* v___f_77_; lean_object* v_a_x27_78_; lean_object* v___x_79_; lean_object* v___x_80_; 
v_fst_73_ = lean_ctor_get(v_____s_72_, 0);
lean_inc(v_fst_73_);
v_snd_74_ = lean_ctor_get(v_____s_72_, 1);
lean_inc(v_snd_74_);
lean_dec_ref(v_____s_72_);
v___x_75_ = lean_unsigned_to_nat(0u);
v___x_76_ = lean_box(v___x_69_);
lean_inc(v_toBind_67_);
v___f_77_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__4___boxed), 11, 7);
lean_closure_set(v___f_77_, 0, v___x_65_);
lean_closure_set(v___f_77_, 1, v_toPure_66_);
lean_closure_set(v___f_77_, 2, v_toBind_67_);
lean_closure_set(v___f_77_, 3, v___f_68_);
lean_closure_set(v___f_77_, 4, v___x_76_);
lean_closure_set(v___f_77_, 5, v_fst_73_);
lean_closure_set(v___f_77_, 6, v_a_70_);
v_a_x27_78_ = lean_mk_empty_array_with_capacity(v_snd_74_);
lean_dec(v_snd_74_);
v___x_79_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_77_, v___x_75_, v_a_x27_78_, lean_box(0));
v___x_80_ = lean_apply_4(v_toBind_67_, lean_box(0), lean_box(0), v___x_79_, v___f_71_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__5___boxed(lean_object* v___x_81_, lean_object* v_toPure_82_, lean_object* v_toBind_83_, lean_object* v___f_84_, lean_object* v___x_85_, lean_object* v_a_86_, lean_object* v___f_87_, lean_object* v_____s_88_){
_start:
{
uint8_t v___x_931__boxed_89_; lean_object* v_res_90_; 
v___x_931__boxed_89_ = lean_unbox(v___x_85_);
v_res_90_ = l_Lean_Array_filterPairsM___redArg___lam__5(v___x_81_, v_toPure_82_, v_toBind_83_, v___f_84_, v___x_931__boxed_89_, v_a_86_, v___f_87_, v_____s_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__6(lean_object* v_toPure_91_, lean_object* v_____s_92_){
_start:
{
lean_object* v_fst_93_; lean_object* v_snd_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_103_; 
v_fst_93_ = lean_ctor_get(v_____s_92_, 0);
v_snd_94_ = lean_ctor_get(v_____s_92_, 1);
v_isSharedCheck_103_ = !lean_is_exclusive(v_____s_92_);
if (v_isSharedCheck_103_ == 0)
{
v___x_96_ = v_____s_92_;
v_isShared_97_ = v_isSharedCheck_103_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_snd_94_);
lean_inc(v_fst_93_);
lean_dec(v_____s_92_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_103_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v___x_99_; 
if (v_isShared_97_ == 0)
{
v___x_99_ = v___x_96_;
goto v_reusejp_98_;
}
else
{
lean_object* v_reuseFailAlloc_102_; 
v_reuseFailAlloc_102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_102_, 0, v_fst_93_);
lean_ctor_set(v_reuseFailAlloc_102_, 1, v_snd_94_);
v___x_99_ = v_reuseFailAlloc_102_;
goto v_reusejp_98_;
}
v_reusejp_98_:
{
lean_object* v___x_100_; lean_object* v___x_101_; 
v___x_100_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_100_, 0, v___x_99_);
v___x_101_ = lean_apply_2(v_toPure_91_, lean_box(0), v___x_100_);
return v___x_101_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__7(lean_object* v_toPure_104_, lean_object* v_next_105_, lean_object* v_G_106_, lean_object* v_____do__lift_107_){
_start:
{
if (lean_obj_tag(v_____do__lift_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_109_; 
lean_dec(v_G_106_);
v_a_108_ = lean_ctor_get(v_____do__lift_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref_known(v_____do__lift_107_, 1);
v___x_109_ = lean_apply_2(v_toPure_104_, lean_box(0), v_a_108_);
return v___x_109_;
}
else
{
lean_object* v_a_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_toPure_104_);
v_a_110_ = lean_ctor_get(v_____do__lift_107_, 0);
lean_inc(v_a_110_);
lean_dec_ref_known(v_____do__lift_107_, 1);
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_next_105_, v___x_111_);
v___x_113_ = lean_apply_4(v_G_106_, v___x_112_, v_a_110_, lean_box(0), lean_box(0));
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__7___boxed(lean_object* v_toPure_114_, lean_object* v_next_115_, lean_object* v_G_116_, lean_object* v_____do__lift_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Lean_Array_filterPairsM___redArg___lam__7(v_toPure_114_, v_next_115_, v_G_116_, v_____do__lift_117_);
lean_dec(v_next_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__8(lean_object* v_toPure_119_, lean_object* v_next_120_, lean_object* v___x_121_, lean_object* v_G_122_, lean_object* v_____do__lift_123_){
_start:
{
if (lean_obj_tag(v_____do__lift_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_125_; 
lean_dec(v_G_122_);
v_a_124_ = lean_ctor_get(v_____do__lift_123_, 0);
lean_inc(v_a_124_);
lean_dec_ref_known(v_____do__lift_123_, 1);
v___x_125_ = lean_apply_2(v_toPure_119_, lean_box(0), v_a_124_);
return v___x_125_;
}
else
{
lean_object* v_a_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v_toPure_119_);
v_a_126_ = lean_ctor_get(v_____do__lift_123_, 0);
lean_inc(v_a_126_);
lean_dec_ref_known(v_____do__lift_123_, 1);
v___x_127_ = lean_nat_add(v_next_120_, v___x_121_);
v___x_128_ = lean_apply_4(v_G_122_, v___x_127_, v_a_126_, lean_box(0), lean_box(0));
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__8___boxed(lean_object* v_toPure_129_, lean_object* v_next_130_, lean_object* v___x_131_, lean_object* v_G_132_, lean_object* v_____do__lift_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Lean_Array_filterPairsM___redArg___lam__8(v_toPure_129_, v_next_130_, v___x_131_, v_G_132_, v_____do__lift_133_);
lean_dec(v___x_131_);
lean_dec(v_next_130_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__9(lean_object* v___x_135_, lean_object* v_next_136_, uint8_t v___x_137_, lean_object* v_toPure_138_, lean_object* v_snd_139_, lean_object* v_fst_140_, lean_object* v_next_141_, lean_object* v_____x_142_){
_start:
{
lean_object* v_fst_143_; lean_object* v_snd_144_; lean_object* v___x_146_; uint8_t v_isShared_147_; uint8_t v_isSharedCheck_169_; 
v_fst_143_ = lean_ctor_get(v_____x_142_, 0);
v_snd_144_ = lean_ctor_get(v_____x_142_, 1);
v_isSharedCheck_169_ = !lean_is_exclusive(v_____x_142_);
if (v_isSharedCheck_169_ == 0)
{
v___x_146_ = v_____x_142_;
v_isShared_147_ = v_isSharedCheck_169_;
goto v_resetjp_145_;
}
else
{
lean_inc(v_snd_144_);
lean_inc(v_fst_143_);
lean_dec(v_____x_142_);
v___x_146_ = lean_box(0);
v_isShared_147_ = v_isSharedCheck_169_;
goto v_resetjp_145_;
}
v_resetjp_145_:
{
lean_object* v_removed_149_; lean_object* v_numRemoved_150_; uint8_t v___x_165_; 
v___x_165_ = lean_unbox(v_fst_143_);
lean_dec(v_fst_143_);
if (v___x_165_ == 0)
{
lean_object* v___x_166_; lean_object* v___x_167_; lean_object* v___x_168_; 
v___x_166_ = lean_nat_add(v_snd_139_, v___x_135_);
lean_dec(v_snd_139_);
v___x_167_ = lean_box(v___x_137_);
v___x_168_ = lean_array_set(v_fst_140_, v_next_141_, v___x_167_);
v_removed_149_ = v___x_168_;
v_numRemoved_150_ = v___x_166_;
goto v___jp_148_;
}
else
{
v_removed_149_ = v_fst_140_;
v_numRemoved_150_ = v_snd_139_;
goto v___jp_148_;
}
v___jp_148_:
{
uint8_t v___x_151_; 
v___x_151_ = lean_unbox(v_snd_144_);
lean_dec(v_snd_144_);
if (v___x_151_ == 0)
{
lean_object* v___x_152_; lean_object* v___x_153_; lean_object* v___x_154_; lean_object* v___x_156_; 
v___x_152_ = lean_nat_add(v_numRemoved_150_, v___x_135_);
lean_dec(v_numRemoved_150_);
v___x_153_ = lean_box(v___x_137_);
v___x_154_ = lean_array_set(v_removed_149_, v_next_136_, v___x_153_);
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v___x_152_);
lean_ctor_set(v___x_146_, 0, v___x_154_);
v___x_156_ = v___x_146_;
goto v_reusejp_155_;
}
else
{
lean_object* v_reuseFailAlloc_159_; 
v_reuseFailAlloc_159_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_159_, 0, v___x_154_);
lean_ctor_set(v_reuseFailAlloc_159_, 1, v___x_152_);
v___x_156_ = v_reuseFailAlloc_159_;
goto v_reusejp_155_;
}
v_reusejp_155_:
{
lean_object* v___x_157_; lean_object* v___x_158_; 
v___x_157_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_157_, 0, v___x_156_);
v___x_158_ = lean_apply_2(v_toPure_138_, lean_box(0), v___x_157_);
return v___x_158_;
}
}
else
{
lean_object* v___x_161_; 
if (v_isShared_147_ == 0)
{
lean_ctor_set(v___x_146_, 1, v_numRemoved_150_);
lean_ctor_set(v___x_146_, 0, v_removed_149_);
v___x_161_ = v___x_146_;
goto v_reusejp_160_;
}
else
{
lean_object* v_reuseFailAlloc_164_; 
v_reuseFailAlloc_164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_164_, 0, v_removed_149_);
lean_ctor_set(v_reuseFailAlloc_164_, 1, v_numRemoved_150_);
v___x_161_ = v_reuseFailAlloc_164_;
goto v_reusejp_160_;
}
v_reusejp_160_:
{
lean_object* v___x_162_; lean_object* v___x_163_; 
v___x_162_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_162_, 0, v___x_161_);
v___x_163_ = lean_apply_2(v_toPure_138_, lean_box(0), v___x_162_);
return v___x_163_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__9___boxed(lean_object* v___x_170_, lean_object* v_next_171_, lean_object* v___x_172_, lean_object* v_toPure_173_, lean_object* v_snd_174_, lean_object* v_fst_175_, lean_object* v_next_176_, lean_object* v_____x_177_){
_start:
{
uint8_t v___x_1006__boxed_178_; lean_object* v_res_179_; 
v___x_1006__boxed_178_ = lean_unbox(v___x_172_);
v_res_179_ = l_Lean_Array_filterPairsM___redArg___lam__9(v___x_170_, v_next_171_, v___x_1006__boxed_178_, v_toPure_173_, v_snd_174_, v_fst_175_, v_next_176_, v_____x_177_);
lean_dec(v_next_176_);
lean_dec(v_next_171_);
lean_dec(v___x_170_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__10(lean_object* v___x_180_, lean_object* v_toPure_181_, lean_object* v___x_182_, lean_object* v_toBind_183_, lean_object* v___f_184_, uint8_t v___x_185_, lean_object* v_next_186_, lean_object* v_a_187_, lean_object* v_f_188_, lean_object* v_next_189_, lean_object* v_acc_190_, lean_object* v_h_191_, lean_object* v_G_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = lean_nat_dec_lt(v_next_189_, v___x_180_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_dec(v_G_192_);
lean_dec(v_next_189_);
lean_dec(v_f_188_);
lean_dec(v_next_186_);
lean_dec(v___f_184_);
lean_dec(v_toBind_183_);
lean_dec(v___x_182_);
v___x_194_ = lean_apply_2(v_toPure_181_, lean_box(0), v_acc_190_);
return v___x_194_;
}
else
{
lean_object* v_fst_195_; lean_object* v_snd_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_223_; 
v_fst_195_ = lean_ctor_get(v_acc_190_, 0);
v_snd_196_ = lean_ctor_get(v_acc_190_, 1);
v_isSharedCheck_223_ = !lean_is_exclusive(v_acc_190_);
if (v_isSharedCheck_223_ == 0)
{
v___x_198_ = v_acc_190_;
v_isShared_199_ = v_isSharedCheck_223_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_snd_196_);
lean_inc(v_fst_195_);
lean_dec(v_acc_190_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_223_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___f_200_; lean_object* v___y_202_; lean_object* v___x_211_; lean_object* v___x_212_; uint8_t v___x_213_; 
lean_inc(v___x_182_);
lean_inc(v_next_189_);
lean_inc(v_toPure_181_);
v___f_200_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_200_, 0, v_toPure_181_);
lean_closure_set(v___f_200_, 1, v_next_189_);
lean_closure_set(v___f_200_, 2, v___x_182_);
lean_closure_set(v___f_200_, 3, v_G_192_);
v___x_211_ = lean_box(v___x_185_);
v___x_212_ = lean_array_get(v___x_211_, v_fst_195_, v_next_186_);
lean_dec(v___x_211_);
v___x_213_ = lean_unbox(v___x_212_);
lean_dec(v___x_212_);
if (v___x_213_ == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; uint8_t v___x_216_; 
v___x_214_ = lean_box(v___x_185_);
v___x_215_ = lean_array_get(v___x_214_, v_fst_195_, v_next_189_);
lean_dec(v___x_214_);
v___x_216_ = lean_unbox(v___x_215_);
lean_dec(v___x_215_);
if (v___x_216_ == 0)
{
lean_object* v___x_217_; lean_object* v___f_218_; lean_object* v___x_219_; lean_object* v___x_220_; lean_object* v___x_221_; lean_object* v___x_222_; 
lean_del_object(v___x_198_);
v___x_217_ = lean_box(v___x_193_);
lean_inc(v_next_186_);
lean_inc(v_next_189_);
v___f_218_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__9___boxed), 8, 7);
lean_closure_set(v___f_218_, 0, v___x_182_);
lean_closure_set(v___f_218_, 1, v_next_189_);
lean_closure_set(v___f_218_, 2, v___x_217_);
lean_closure_set(v___f_218_, 3, v_toPure_181_);
lean_closure_set(v___f_218_, 4, v_snd_196_);
lean_closure_set(v___f_218_, 5, v_fst_195_);
lean_closure_set(v___f_218_, 6, v_next_186_);
v___x_219_ = lean_array_fget_borrowed(v_a_187_, v_next_186_);
lean_dec(v_next_186_);
v___x_220_ = lean_array_fget_borrowed(v_a_187_, v_next_189_);
lean_dec(v_next_189_);
lean_inc(v___x_220_);
lean_inc(v___x_219_);
v___x_221_ = lean_apply_2(v_f_188_, v___x_219_, v___x_220_);
lean_inc(v_toBind_183_);
v___x_222_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___x_221_, v___f_218_);
v___y_202_ = v___x_222_;
goto v___jp_201_;
}
else
{
lean_dec(v_next_189_);
lean_dec(v_f_188_);
lean_dec(v_next_186_);
lean_dec(v___x_182_);
goto v___jp_205_;
}
}
else
{
lean_dec(v_next_189_);
lean_dec(v_f_188_);
lean_dec(v_next_186_);
lean_dec(v___x_182_);
goto v___jp_205_;
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_inc(v_toBind_183_);
v___x_203_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___y_202_, v___f_184_);
v___x_204_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___x_203_, v___f_200_);
return v___x_204_;
}
v___jp_205_:
{
lean_object* v___x_207_; 
if (v_isShared_199_ == 0)
{
v___x_207_ = v___x_198_;
goto v_reusejp_206_;
}
else
{
lean_object* v_reuseFailAlloc_210_; 
v_reuseFailAlloc_210_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_210_, 0, v_fst_195_);
lean_ctor_set(v_reuseFailAlloc_210_, 1, v_snd_196_);
v___x_207_ = v_reuseFailAlloc_210_;
goto v_reusejp_206_;
}
v_reusejp_206_:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_208_, 0, v___x_207_);
v___x_209_ = lean_apply_2(v_toPure_181_, lean_box(0), v___x_208_);
v___y_202_ = v___x_209_;
goto v___jp_201_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__10___boxed(lean_object* v___x_224_, lean_object* v_toPure_225_, lean_object* v___x_226_, lean_object* v_toBind_227_, lean_object* v___f_228_, lean_object* v___x_229_, lean_object* v_next_230_, lean_object* v_a_231_, lean_object* v_f_232_, lean_object* v_next_233_, lean_object* v_acc_234_, lean_object* v_h_235_, lean_object* v_G_236_){
_start:
{
uint8_t v___x_1067__boxed_237_; lean_object* v_res_238_; 
v___x_1067__boxed_237_ = lean_unbox(v___x_229_);
v_res_238_ = l_Lean_Array_filterPairsM___redArg___lam__10(v___x_224_, v_toPure_225_, v___x_226_, v_toBind_227_, v___f_228_, v___x_1067__boxed_237_, v_next_230_, v_a_231_, v_f_232_, v_next_233_, v_acc_234_, v_h_235_, v_G_236_);
lean_dec_ref(v_a_231_);
lean_dec(v___x_224_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__11(lean_object* v___x_239_, lean_object* v_toPure_240_, lean_object* v_toBind_241_, lean_object* v___f_242_, uint8_t v___x_243_, lean_object* v_a_244_, lean_object* v_f_245_, lean_object* v___f_246_, lean_object* v___f_247_, lean_object* v_next_248_, lean_object* v_acc_249_, lean_object* v_h_250_, lean_object* v_G_251_){
_start:
{
uint8_t v___x_252_; 
v___x_252_ = lean_nat_dec_lt(v_next_248_, v___x_239_);
if (v___x_252_ == 0)
{
lean_object* v___x_253_; 
lean_dec(v_G_251_);
lean_dec(v_next_248_);
lean_dec(v___f_247_);
lean_dec(v___f_246_);
lean_dec(v_f_245_);
lean_dec_ref(v_a_244_);
lean_dec(v___f_242_);
lean_dec(v_toBind_241_);
lean_dec(v___x_239_);
v___x_253_ = lean_apply_2(v_toPure_240_, lean_box(0), v_acc_249_);
return v___x_253_;
}
else
{
lean_object* v_fst_254_; lean_object* v_snd_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_271_; 
v_fst_254_ = lean_ctor_get(v_acc_249_, 0);
v_snd_255_ = lean_ctor_get(v_acc_249_, 1);
v_isSharedCheck_271_ = !lean_is_exclusive(v_acc_249_);
if (v_isSharedCheck_271_ == 0)
{
v___x_257_ = v_acc_249_;
v_isShared_258_ = v_isSharedCheck_271_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_snd_255_);
lean_inc(v_fst_254_);
lean_dec(v_acc_249_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_271_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v___f_259_; lean_object* v___x_260_; lean_object* v___x_261_; lean_object* v___f_262_; lean_object* v___x_263_; lean_object* v___x_265_; 
lean_inc_n(v_next_248_, 2);
lean_inc(v_toPure_240_);
v___f_259_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_259_, 0, v_toPure_240_);
lean_closure_set(v___f_259_, 1, v_next_248_);
lean_closure_set(v___f_259_, 2, v_G_251_);
v___x_260_ = lean_unsigned_to_nat(1u);
v___x_261_ = lean_box(v___x_243_);
lean_inc(v_toBind_241_);
v___f_262_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__10___boxed), 13, 9);
lean_closure_set(v___f_262_, 0, v___x_239_);
lean_closure_set(v___f_262_, 1, v_toPure_240_);
lean_closure_set(v___f_262_, 2, v___x_260_);
lean_closure_set(v___f_262_, 3, v_toBind_241_);
lean_closure_set(v___f_262_, 4, v___f_242_);
lean_closure_set(v___f_262_, 5, v___x_261_);
lean_closure_set(v___f_262_, 6, v_next_248_);
lean_closure_set(v___f_262_, 7, v_a_244_);
lean_closure_set(v___f_262_, 8, v_f_245_);
v___x_263_ = lean_nat_add(v_next_248_, v___x_260_);
lean_dec(v_next_248_);
if (v_isShared_258_ == 0)
{
v___x_265_ = v___x_257_;
goto v_reusejp_264_;
}
else
{
lean_object* v_reuseFailAlloc_270_; 
v_reuseFailAlloc_270_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_270_, 0, v_fst_254_);
lean_ctor_set(v_reuseFailAlloc_270_, 1, v_snd_255_);
v___x_265_ = v_reuseFailAlloc_270_;
goto v_reusejp_264_;
}
v_reusejp_264_:
{
lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___x_268_; lean_object* v___x_269_; 
v___x_266_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_262_, v___x_263_, v___x_265_, lean_box(0));
lean_inc_n(v_toBind_241_, 2);
v___x_267_ = lean_apply_4(v_toBind_241_, lean_box(0), lean_box(0), v___x_266_, v___f_246_);
v___x_268_ = lean_apply_4(v_toBind_241_, lean_box(0), lean_box(0), v___x_267_, v___f_247_);
v___x_269_ = lean_apply_4(v_toBind_241_, lean_box(0), lean_box(0), v___x_268_, v___f_259_);
return v___x_269_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__11___boxed(lean_object* v___x_272_, lean_object* v_toPure_273_, lean_object* v_toBind_274_, lean_object* v___f_275_, lean_object* v___x_276_, lean_object* v_a_277_, lean_object* v_f_278_, lean_object* v___f_279_, lean_object* v___f_280_, lean_object* v_next_281_, lean_object* v_acc_282_, lean_object* v_h_283_, lean_object* v_G_284_){
_start:
{
uint8_t v___x_1136__boxed_285_; lean_object* v_res_286_; 
v___x_1136__boxed_285_ = lean_unbox(v___x_276_);
v_res_286_ = l_Lean_Array_filterPairsM___redArg___lam__11(v___x_272_, v_toPure_273_, v_toBind_274_, v___f_275_, v___x_1136__boxed_285_, v_a_277_, v_f_278_, v___f_279_, v___f_280_, v_next_281_, v_acc_282_, v_h_283_, v_G_284_);
return v_res_286_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg(lean_object* v_inst_287_, lean_object* v_a_288_, lean_object* v_f_289_){
_start:
{
lean_object* v_toApplicative_290_; lean_object* v_toBind_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_314_; 
v_toApplicative_290_ = lean_ctor_get(v_inst_287_, 0);
v_toBind_291_ = lean_ctor_get(v_inst_287_, 1);
v_isSharedCheck_314_ = !lean_is_exclusive(v_inst_287_);
if (v_isSharedCheck_314_ == 0)
{
v___x_293_ = v_inst_287_;
v_isShared_294_ = v_isSharedCheck_314_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_toBind_291_);
lean_inc(v_toApplicative_290_);
lean_dec(v_inst_287_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_314_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v_toPure_295_; uint8_t v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v_removed_299_; lean_object* v___f_300_; lean_object* v___f_301_; lean_object* v___f_302_; lean_object* v___x_303_; lean_object* v___f_304_; lean_object* v___f_305_; lean_object* v___x_306_; lean_object* v___f_307_; lean_object* v___x_308_; lean_object* v___x_310_; 
v_toPure_295_ = lean_ctor_get(v_toApplicative_290_, 1);
lean_inc_n(v_toPure_295_, 6);
lean_dec_ref(v_toApplicative_290_);
v___x_296_ = 0;
v___x_297_ = lean_array_get_size(v_a_288_);
v___x_298_ = lean_box(v___x_296_);
v_removed_299_ = lean_mk_array(v___x_297_, v___x_298_);
v___f_300_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_300_, 0, v_toPure_295_);
v___f_301_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_301_, 0, v_toPure_295_);
v___f_302_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_302_, 0, v_toPure_295_);
v___x_303_ = lean_box(v___x_296_);
lean_inc_ref(v_a_288_);
lean_inc_n(v_toBind_291_, 2);
v___f_304_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_304_, 0, v___x_297_);
lean_closure_set(v___f_304_, 1, v_toPure_295_);
lean_closure_set(v___f_304_, 2, v_toBind_291_);
lean_closure_set(v___f_304_, 3, v___f_301_);
lean_closure_set(v___f_304_, 4, v___x_303_);
lean_closure_set(v___f_304_, 5, v_a_288_);
lean_closure_set(v___f_304_, 6, v___f_302_);
v___f_305_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__6), 2, 1);
lean_closure_set(v___f_305_, 0, v_toPure_295_);
v___x_306_ = lean_box(v___x_296_);
lean_inc_ref(v___f_300_);
v___f_307_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__11___boxed), 13, 9);
lean_closure_set(v___f_307_, 0, v___x_297_);
lean_closure_set(v___f_307_, 1, v_toPure_295_);
lean_closure_set(v___f_307_, 2, v_toBind_291_);
lean_closure_set(v___f_307_, 3, v___f_300_);
lean_closure_set(v___f_307_, 4, v___x_306_);
lean_closure_set(v___f_307_, 5, v_a_288_);
lean_closure_set(v___f_307_, 6, v_f_289_);
lean_closure_set(v___f_307_, 7, v___f_305_);
lean_closure_set(v___f_307_, 8, v___f_300_);
v___x_308_ = lean_unsigned_to_nat(0u);
if (v_isShared_294_ == 0)
{
lean_ctor_set(v___x_293_, 1, v___x_308_);
lean_ctor_set(v___x_293_, 0, v_removed_299_);
v___x_310_ = v___x_293_;
goto v_reusejp_309_;
}
else
{
lean_object* v_reuseFailAlloc_313_; 
v_reuseFailAlloc_313_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_313_, 0, v_removed_299_);
lean_ctor_set(v_reuseFailAlloc_313_, 1, v___x_308_);
v___x_310_ = v_reuseFailAlloc_313_;
goto v_reusejp_309_;
}
v_reusejp_309_:
{
lean_object* v___x_311_; lean_object* v___x_312_; 
v___x_311_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_307_, v___x_308_, v___x_310_, lean_box(0));
v___x_312_ = lean_apply_4(v_toBind_291_, lean_box(0), lean_box(0), v___x_311_, v___f_304_);
return v___x_312_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM(lean_object* v_m_315_, lean_object* v_inst_316_, lean_object* v_00_u03b1_317_, lean_object* v_a_318_, lean_object* v_f_319_){
_start:
{
lean_object* v___x_320_; 
v___x_320_ = l_Lean_Array_filterPairsM___redArg(v_inst_316_, v_a_318_, v_f_319_);
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg(lean_object* v_as_321_, size_t v_sz_322_, size_t v_i_323_, lean_object* v_b_324_){
_start:
{
lean_object* v_a_326_; uint8_t v___x_330_; 
v___x_330_ = lean_usize_dec_lt(v_i_323_, v_sz_322_);
if (v___x_330_ == 0)
{
return v_b_324_;
}
else
{
lean_object* v_snd_331_; lean_object* v_fst_332_; lean_object* v___x_334_; uint8_t v_isShared_335_; uint8_t v_isSharedCheck_365_; 
v_snd_331_ = lean_ctor_get(v_b_324_, 1);
v_fst_332_ = lean_ctor_get(v_b_324_, 0);
v_isSharedCheck_365_ = !lean_is_exclusive(v_b_324_);
if (v_isSharedCheck_365_ == 0)
{
v___x_334_ = v_b_324_;
v_isShared_335_ = v_isSharedCheck_365_;
goto v_resetjp_333_;
}
else
{
lean_inc(v_snd_331_);
lean_inc(v_fst_332_);
lean_dec(v_b_324_);
v___x_334_ = lean_box(0);
v_isShared_335_ = v_isSharedCheck_365_;
goto v_resetjp_333_;
}
v_resetjp_333_:
{
lean_object* v_array_336_; lean_object* v_start_337_; lean_object* v_stop_338_; uint8_t v___x_339_; 
v_array_336_ = lean_ctor_get(v_snd_331_, 0);
v_start_337_ = lean_ctor_get(v_snd_331_, 1);
v_stop_338_ = lean_ctor_get(v_snd_331_, 2);
v___x_339_ = lean_nat_dec_lt(v_start_337_, v_stop_338_);
if (v___x_339_ == 0)
{
lean_object* v___x_341_; 
if (v_isShared_335_ == 0)
{
v___x_341_ = v___x_334_;
goto v_reusejp_340_;
}
else
{
lean_object* v_reuseFailAlloc_342_; 
v_reuseFailAlloc_342_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_342_, 0, v_fst_332_);
lean_ctor_set(v_reuseFailAlloc_342_, 1, v_snd_331_);
v___x_341_ = v_reuseFailAlloc_342_;
goto v_reusejp_340_;
}
v_reusejp_340_:
{
return v___x_341_;
}
}
else
{
lean_object* v___x_344_; uint8_t v_isShared_345_; uint8_t v_isSharedCheck_361_; 
lean_inc(v_stop_338_);
lean_inc(v_start_337_);
lean_inc_ref(v_array_336_);
v_isSharedCheck_361_ = !lean_is_exclusive(v_snd_331_);
if (v_isSharedCheck_361_ == 0)
{
lean_object* v_unused_362_; lean_object* v_unused_363_; lean_object* v_unused_364_; 
v_unused_362_ = lean_ctor_get(v_snd_331_, 2);
lean_dec(v_unused_362_);
v_unused_363_ = lean_ctor_get(v_snd_331_, 1);
lean_dec(v_unused_363_);
v_unused_364_ = lean_ctor_get(v_snd_331_, 0);
lean_dec(v_unused_364_);
v___x_344_ = v_snd_331_;
v_isShared_345_ = v_isSharedCheck_361_;
goto v_resetjp_343_;
}
else
{
lean_dec(v_snd_331_);
v___x_344_ = lean_box(0);
v_isShared_345_ = v_isSharedCheck_361_;
goto v_resetjp_343_;
}
v_resetjp_343_:
{
lean_object* v_a_346_; lean_object* v___x_347_; lean_object* v___x_348_; lean_object* v___x_349_; lean_object* v___x_351_; 
v_a_346_ = lean_array_uget_borrowed(v_as_321_, v_i_323_);
v___x_347_ = lean_array_fget(v_array_336_, v_start_337_);
v___x_348_ = lean_unsigned_to_nat(1u);
v___x_349_ = lean_nat_add(v_start_337_, v___x_348_);
lean_dec(v_start_337_);
if (v_isShared_345_ == 0)
{
lean_ctor_set(v___x_344_, 1, v___x_349_);
v___x_351_ = v___x_344_;
goto v_reusejp_350_;
}
else
{
lean_object* v_reuseFailAlloc_360_; 
v_reuseFailAlloc_360_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_360_, 0, v_array_336_);
lean_ctor_set(v_reuseFailAlloc_360_, 1, v___x_349_);
lean_ctor_set(v_reuseFailAlloc_360_, 2, v_stop_338_);
v___x_351_ = v_reuseFailAlloc_360_;
goto v_reusejp_350_;
}
v_reusejp_350_:
{
uint8_t v___x_352_; 
v___x_352_ = lean_unbox(v_a_346_);
if (v___x_352_ == 0)
{
lean_object* v___x_354_; 
lean_dec(v___x_347_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 1, v___x_351_);
v___x_354_ = v___x_334_;
goto v_reusejp_353_;
}
else
{
lean_object* v_reuseFailAlloc_355_; 
v_reuseFailAlloc_355_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_355_, 0, v_fst_332_);
lean_ctor_set(v_reuseFailAlloc_355_, 1, v___x_351_);
v___x_354_ = v_reuseFailAlloc_355_;
goto v_reusejp_353_;
}
v_reusejp_353_:
{
v_a_326_ = v___x_354_;
goto v___jp_325_;
}
}
else
{
lean_object* v___x_356_; lean_object* v___x_358_; 
v___x_356_ = lean_array_push(v_fst_332_, v___x_347_);
if (v_isShared_335_ == 0)
{
lean_ctor_set(v___x_334_, 1, v___x_351_);
lean_ctor_set(v___x_334_, 0, v___x_356_);
v___x_358_ = v___x_334_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_359_; 
v_reuseFailAlloc_359_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_359_, 0, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_359_, 1, v___x_351_);
v___x_358_ = v_reuseFailAlloc_359_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
v_a_326_ = v___x_358_;
goto v___jp_325_;
}
}
}
}
}
}
}
v___jp_325_:
{
size_t v___x_327_; size_t v___x_328_; 
v___x_327_ = ((size_t)1ULL);
v___x_328_ = lean_usize_add(v_i_323_, v___x_327_);
v_i_323_ = v___x_328_;
v_b_324_ = v_a_326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg___boxed(lean_object* v_as_366_, lean_object* v_sz_367_, lean_object* v_i_368_, lean_object* v_b_369_){
_start:
{
size_t v_sz_boxed_370_; size_t v_i_boxed_371_; lean_object* v_res_372_; 
v_sz_boxed_370_ = lean_unbox_usize(v_sz_367_);
lean_dec(v_sz_367_);
v_i_boxed_371_ = lean_unbox_usize(v_i_368_);
lean_dec(v_i_368_);
v_res_372_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg(v_as_366_, v_sz_boxed_370_, v_i_boxed_371_, v_b_369_);
lean_dec_ref(v_as_366_);
return v_res_372_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_mask___redArg(lean_object* v_mask_375_, lean_object* v_xs_376_){
_start:
{
lean_object* v___x_377_; lean_object* v_ys_378_; lean_object* v___x_379_; lean_object* v___x_380_; lean_object* v___x_381_; size_t v_sz_382_; size_t v___x_383_; lean_object* v___x_384_; lean_object* v_fst_385_; 
v___x_377_ = lean_unsigned_to_nat(0u);
v_ys_378_ = ((lean_object*)(l_Lean_Array_mask___redArg___closed__0));
v___x_379_ = lean_array_get_size(v_xs_376_);
v___x_380_ = l_Array_toSubarray___redArg(v_xs_376_, v___x_377_, v___x_379_);
v___x_381_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_381_, 0, v_ys_378_);
lean_ctor_set(v___x_381_, 1, v___x_380_);
v_sz_382_ = lean_array_size(v_mask_375_);
v___x_383_ = ((size_t)0ULL);
v___x_384_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg(v_mask_375_, v_sz_382_, v___x_383_, v___x_381_);
v_fst_385_ = lean_ctor_get(v___x_384_, 0);
lean_inc(v_fst_385_);
lean_dec_ref(v___x_384_);
return v_fst_385_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_mask___redArg___boxed(lean_object* v_mask_386_, lean_object* v_xs_387_){
_start:
{
lean_object* v_res_388_; 
v_res_388_ = l_Lean_Array_mask___redArg(v_mask_386_, v_xs_387_);
lean_dec_ref(v_mask_386_);
return v_res_388_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_mask(lean_object* v_00_u03b1_389_, lean_object* v_mask_390_, lean_object* v_xs_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Lean_Array_mask___redArg(v_mask_390_, v_xs_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_mask___boxed(lean_object* v_00_u03b1_393_, lean_object* v_mask_394_, lean_object* v_xs_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Array_mask(v_00_u03b1_393_, v_mask_394_, v_xs_395_);
lean_dec_ref(v_mask_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0(lean_object* v_00_u03b1_397_, lean_object* v_as_398_, size_t v_sz_399_, size_t v_i_400_, lean_object* v_b_401_){
_start:
{
lean_object* v___x_402_; 
v___x_402_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg(v_as_398_, v_sz_399_, v_i_400_, v_b_401_);
return v___x_402_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___boxed(lean_object* v_00_u03b1_403_, lean_object* v_as_404_, lean_object* v_sz_405_, lean_object* v_i_406_, lean_object* v_b_407_){
_start:
{
size_t v_sz_boxed_408_; size_t v_i_boxed_409_; lean_object* v_res_410_; 
v_sz_boxed_408_ = lean_unbox_usize(v_sz_405_);
lean_dec(v_sz_405_);
v_i_boxed_409_ = lean_unbox_usize(v_i_406_);
lean_dec(v_i_406_);
v_res_410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0(v_00_u03b1_403_, v_as_404_, v_sz_boxed_408_, v_i_boxed_409_, v_b_407_);
lean_dec_ref(v_as_404_);
return v_res_410_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg(lean_object* v_xs_411_, lean_object* v_ys_412_, lean_object* v_as_413_, size_t v_sz_414_, size_t v_i_415_, lean_object* v_b_416_){
_start:
{
lean_object* v_a_418_; uint8_t v___x_422_; 
v___x_422_ = lean_usize_dec_lt(v_i_415_, v_sz_414_);
if (v___x_422_ == 0)
{
return v_b_416_;
}
else
{
lean_object* v_snd_423_; lean_object* v_fst_424_; lean_object* v___x_426_; uint8_t v_isShared_427_; uint8_t v_isSharedCheck_472_; 
v_snd_423_ = lean_ctor_get(v_b_416_, 1);
v_fst_424_ = lean_ctor_get(v_b_416_, 0);
v_isSharedCheck_472_ = !lean_is_exclusive(v_b_416_);
if (v_isSharedCheck_472_ == 0)
{
v___x_426_ = v_b_416_;
v_isShared_427_ = v_isSharedCheck_472_;
goto v_resetjp_425_;
}
else
{
lean_inc(v_snd_423_);
lean_inc(v_fst_424_);
lean_dec(v_b_416_);
v___x_426_ = lean_box(0);
v_isShared_427_ = v_isSharedCheck_472_;
goto v_resetjp_425_;
}
v_resetjp_425_:
{
lean_object* v_fst_428_; lean_object* v_snd_429_; lean_object* v___x_431_; uint8_t v_isShared_432_; uint8_t v_isSharedCheck_471_; 
v_fst_428_ = lean_ctor_get(v_snd_423_, 0);
v_snd_429_ = lean_ctor_get(v_snd_423_, 1);
v_isSharedCheck_471_ = !lean_is_exclusive(v_snd_423_);
if (v_isSharedCheck_471_ == 0)
{
v___x_431_ = v_snd_423_;
v_isShared_432_ = v_isSharedCheck_471_;
goto v_resetjp_430_;
}
else
{
lean_inc(v_snd_429_);
lean_inc(v_fst_428_);
lean_dec(v_snd_423_);
v___x_431_ = lean_box(0);
v_isShared_432_ = v_isSharedCheck_471_;
goto v_resetjp_430_;
}
v_resetjp_430_:
{
lean_object* v_a_433_; uint8_t v___x_434_; 
v_a_433_ = lean_array_uget_borrowed(v_as_413_, v_i_415_);
v___x_434_ = lean_unbox(v_a_433_);
if (v___x_434_ == 0)
{
lean_object* v___x_435_; uint8_t v___x_436_; 
v___x_435_ = lean_array_get_size(v_xs_411_);
v___x_436_ = lean_nat_dec_lt(v_fst_424_, v___x_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_438_; 
if (v_isShared_432_ == 0)
{
v___x_438_ = v___x_431_;
goto v_reusejp_437_;
}
else
{
lean_object* v_reuseFailAlloc_442_; 
v_reuseFailAlloc_442_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_442_, 0, v_fst_428_);
lean_ctor_set(v_reuseFailAlloc_442_, 1, v_snd_429_);
v___x_438_ = v_reuseFailAlloc_442_;
goto v_reusejp_437_;
}
v_reusejp_437_:
{
lean_object* v___x_440_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_438_);
v___x_440_ = v___x_426_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_441_; 
v_reuseFailAlloc_441_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_441_, 0, v_fst_424_);
lean_ctor_set(v_reuseFailAlloc_441_, 1, v___x_438_);
v___x_440_ = v_reuseFailAlloc_441_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
v_a_418_ = v___x_440_;
goto v___jp_417_;
}
}
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_448_; 
v___x_443_ = lean_array_fget_borrowed(v_xs_411_, v_fst_424_);
lean_inc(v___x_443_);
v___x_444_ = lean_array_push(v_snd_429_, v___x_443_);
v___x_445_ = lean_unsigned_to_nat(1u);
v___x_446_ = lean_nat_add(v_fst_424_, v___x_445_);
lean_dec(v_fst_424_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_444_);
v___x_448_ = v___x_431_;
goto v_reusejp_447_;
}
else
{
lean_object* v_reuseFailAlloc_452_; 
v_reuseFailAlloc_452_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_452_, 0, v_fst_428_);
lean_ctor_set(v_reuseFailAlloc_452_, 1, v___x_444_);
v___x_448_ = v_reuseFailAlloc_452_;
goto v_reusejp_447_;
}
v_reusejp_447_:
{
lean_object* v___x_450_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_448_);
lean_ctor_set(v___x_426_, 0, v___x_446_);
v___x_450_ = v___x_426_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v___x_446_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v___x_448_);
v___x_450_ = v_reuseFailAlloc_451_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
v_a_418_ = v___x_450_;
goto v___jp_417_;
}
}
}
}
else
{
lean_object* v___x_453_; uint8_t v___x_454_; 
v___x_453_ = lean_array_get_size(v_ys_412_);
v___x_454_ = lean_nat_dec_lt(v_fst_428_, v___x_453_);
if (v___x_454_ == 0)
{
lean_object* v___x_456_; 
if (v_isShared_432_ == 0)
{
v___x_456_ = v___x_431_;
goto v_reusejp_455_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v_fst_428_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v_snd_429_);
v___x_456_ = v_reuseFailAlloc_460_;
goto v_reusejp_455_;
}
v_reusejp_455_:
{
lean_object* v___x_458_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_456_);
v___x_458_ = v___x_426_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_459_; 
v_reuseFailAlloc_459_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_459_, 0, v_fst_424_);
lean_ctor_set(v_reuseFailAlloc_459_, 1, v___x_456_);
v___x_458_ = v_reuseFailAlloc_459_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
v_a_418_ = v___x_458_;
goto v___jp_417_;
}
}
}
else
{
lean_object* v___x_461_; lean_object* v___x_462_; lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_466_; 
v___x_461_ = lean_array_fget_borrowed(v_ys_412_, v_fst_428_);
lean_inc(v___x_461_);
v___x_462_ = lean_array_push(v_snd_429_, v___x_461_);
v___x_463_ = lean_unsigned_to_nat(1u);
v___x_464_ = lean_nat_add(v_fst_428_, v___x_463_);
lean_dec(v_fst_428_);
if (v_isShared_432_ == 0)
{
lean_ctor_set(v___x_431_, 1, v___x_462_);
lean_ctor_set(v___x_431_, 0, v___x_464_);
v___x_466_ = v___x_431_;
goto v_reusejp_465_;
}
else
{
lean_object* v_reuseFailAlloc_470_; 
v_reuseFailAlloc_470_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_470_, 0, v___x_464_);
lean_ctor_set(v_reuseFailAlloc_470_, 1, v___x_462_);
v___x_466_ = v_reuseFailAlloc_470_;
goto v_reusejp_465_;
}
v_reusejp_465_:
{
lean_object* v___x_468_; 
if (v_isShared_427_ == 0)
{
lean_ctor_set(v___x_426_, 1, v___x_466_);
v___x_468_ = v___x_426_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_fst_424_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v___x_466_);
v___x_468_ = v_reuseFailAlloc_469_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
v_a_418_ = v___x_468_;
goto v___jp_417_;
}
}
}
}
}
}
}
v___jp_417_:
{
size_t v___x_419_; size_t v___x_420_; 
v___x_419_ = ((size_t)1ULL);
v___x_420_ = lean_usize_add(v_i_415_, v___x_419_);
v_i_415_ = v___x_420_;
v_b_416_ = v_a_418_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg___boxed(lean_object* v_xs_473_, lean_object* v_ys_474_, lean_object* v_as_475_, lean_object* v_sz_476_, lean_object* v_i_477_, lean_object* v_b_478_){
_start:
{
size_t v_sz_boxed_479_; size_t v_i_boxed_480_; lean_object* v_res_481_; 
v_sz_boxed_479_ = lean_unbox_usize(v_sz_476_);
lean_dec(v_sz_476_);
v_i_boxed_480_ = lean_unbox_usize(v_i_477_);
lean_dec(v_i_477_);
v_res_481_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg(v_xs_473_, v_ys_474_, v_as_475_, v_sz_boxed_479_, v_i_boxed_480_, v_b_478_);
lean_dec_ref(v_as_475_);
lean_dec_ref(v_ys_474_);
lean_dec_ref(v_xs_473_);
return v_res_481_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked___redArg(lean_object* v_mask_488_, lean_object* v_xs_489_, lean_object* v_ys_490_){
_start:
{
lean_object* v___x_491_; size_t v_sz_492_; size_t v___x_493_; lean_object* v___x_494_; lean_object* v_snd_495_; lean_object* v_snd_496_; 
v___x_491_ = ((lean_object*)(l_Lean_Array_zipMasked___redArg___closed__1));
v_sz_492_ = lean_array_size(v_mask_488_);
v___x_493_ = ((size_t)0ULL);
v___x_494_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg(v_xs_489_, v_ys_490_, v_mask_488_, v_sz_492_, v___x_493_, v___x_491_);
v_snd_495_ = lean_ctor_get(v___x_494_, 1);
lean_inc(v_snd_495_);
lean_dec_ref(v___x_494_);
v_snd_496_ = lean_ctor_get(v_snd_495_, 1);
lean_inc(v_snd_496_);
lean_dec(v_snd_495_);
return v_snd_496_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked___redArg___boxed(lean_object* v_mask_497_, lean_object* v_xs_498_, lean_object* v_ys_499_){
_start:
{
lean_object* v_res_500_; 
v_res_500_ = l_Lean_Array_zipMasked___redArg(v_mask_497_, v_xs_498_, v_ys_499_);
lean_dec_ref(v_ys_499_);
lean_dec_ref(v_xs_498_);
lean_dec_ref(v_mask_497_);
return v_res_500_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked(lean_object* v_00_u03b1_501_, lean_object* v_mask_502_, lean_object* v_xs_503_, lean_object* v_ys_504_){
_start:
{
lean_object* v___x_505_; 
v___x_505_ = l_Lean_Array_zipMasked___redArg(v_mask_502_, v_xs_503_, v_ys_504_);
return v___x_505_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked___boxed(lean_object* v_00_u03b1_506_, lean_object* v_mask_507_, lean_object* v_xs_508_, lean_object* v_ys_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Array_zipMasked(v_00_u03b1_506_, v_mask_507_, v_xs_508_, v_ys_509_);
lean_dec_ref(v_ys_509_);
lean_dec_ref(v_xs_508_);
lean_dec_ref(v_mask_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0(lean_object* v_00_u03b1_511_, lean_object* v_xs_512_, lean_object* v_ys_513_, lean_object* v_as_514_, size_t v_sz_515_, size_t v_i_516_, lean_object* v_b_517_){
_start:
{
lean_object* v___x_518_; 
v___x_518_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg(v_xs_512_, v_ys_513_, v_as_514_, v_sz_515_, v_i_516_, v_b_517_);
return v___x_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___boxed(lean_object* v_00_u03b1_519_, lean_object* v_xs_520_, lean_object* v_ys_521_, lean_object* v_as_522_, lean_object* v_sz_523_, lean_object* v_i_524_, lean_object* v_b_525_){
_start:
{
size_t v_sz_boxed_526_; size_t v_i_boxed_527_; lean_object* v_res_528_; 
v_sz_boxed_526_ = lean_unbox_usize(v_sz_523_);
lean_dec(v_sz_523_);
v_i_boxed_527_ = lean_unbox_usize(v_i_524_);
lean_dec(v_i_524_);
v_res_528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0(v_00_u03b1_519_, v_xs_520_, v_ys_521_, v_as_522_, v_sz_boxed_526_, v_i_boxed_527_, v_b_525_);
lean_dec_ref(v_as_522_);
lean_dec_ref(v_ys_521_);
lean_dec_ref(v_xs_520_);
return v_res_528_;
}
}
lean_object* runtime_initialize_Init_Data_Stream(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Array(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Lean_Data_Array(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Stream(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Lean_Data_Array(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Stream(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Nat(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_Iterators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Lean_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Lean_Data_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Lean_Data_Array(builtin);
}
#ifdef __cplusplus
}
#endif
