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
size_t lean_usize_add(size_t, size_t);
uint8_t lean_usize_dec_lt(size_t, size_t);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_uget_borrowed(lean_object*, size_t);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_push(lean_object*, lean_object*);
lean_object* lean_array_get(lean_object*, lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
lean_object* lean_mk_empty_array_with_capacity(lean_object*);
lean_object* lean_array_get_size(lean_object*);
lean_object* l_Array_toSubarray___redArg(lean_object*, lean_object*, lean_object*);
size_t lean_array_size(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_array_set(lean_object*, lean_object*, lean_object*);
lean_object* lean_mk_array(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__2(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__4___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__5___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__6(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__8(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__8___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__9(lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__9___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_array_object l_Array_mask___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_array_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 246}, .m_size = 0, .m_capacity = 0, .m_data = {}};
static const lean_object* l_Array_mask___redArg___closed__0 = (const lean_object*)&l_Array_mask___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Array_mask___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mask___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mask(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_mask___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_Array_zipMasked___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_mask___redArg___closed__0_value)}};
static const lean_object* l_Array_zipMasked___redArg___closed__0 = (const lean_object*)&l_Array_zipMasked___redArg___closed__0_value;
static const lean_ctor_object l_Array_zipMasked___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)&l_Array_zipMasked___redArg___closed__0_value)}};
static const lean_object* l_Array_zipMasked___redArg___closed__1 = (const lean_object*)&l_Array_zipMasked___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_Array_zipMasked___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipMasked___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipMasked(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_zipMasked___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, size_t, size_t, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__0(lean_object* v_toPure_1_, lean_object* v_____do__lift_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_apply_2(v_toPure_1_, lean_box(0), v_____do__lift_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__2(lean_object* v_toPure_4_, lean_object* v_____do__lift_5_){
_start:
{
lean_object* v___x_6_; 
v___x_6_ = lean_apply_2(v_toPure_4_, lean_box(0), v_____do__lift_5_);
return v___x_6_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__1(lean_object* v_toPure_7_, lean_object* v_____s_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_apply_2(v_toPure_7_, lean_box(0), v_____s_8_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3(lean_object* v_toPure_10_, lean_object* v_next_11_, lean_object* v_G_12_, lean_object* v_____do__lift_13_){
_start:
{
if (lean_obj_tag(v_____do__lift_13_) == 0)
{
lean_object* v_a_14_; lean_object* v___x_15_; 
lean_dec(v_G_12_);
v_a_14_ = lean_ctor_get(v_____do__lift_13_, 0);
lean_inc(v_a_14_);
lean_dec_ref(v_____do__lift_13_);
v___x_15_ = lean_apply_2(v_toPure_10_, lean_box(0), v_a_14_);
return v___x_15_;
}
else
{
lean_object* v_a_16_; lean_object* v___x_17_; lean_object* v___x_18_; lean_object* v___x_19_; 
lean_dec(v_toPure_10_);
v_a_16_ = lean_ctor_get(v_____do__lift_13_, 0);
lean_inc(v_a_16_);
lean_dec_ref(v_____do__lift_13_);
v___x_17_ = lean_unsigned_to_nat(1u);
v___x_18_ = lean_nat_add(v_next_11_, v___x_17_);
v___x_19_ = lean_apply_4(v_G_12_, v___x_18_, v_a_16_, lean_box(0), lean_box(0));
return v___x_19_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__3___boxed(lean_object* v_toPure_20_, lean_object* v_next_21_, lean_object* v_G_22_, lean_object* v_____do__lift_23_){
_start:
{
lean_object* v_res_24_; 
v_res_24_ = l_Array_filterPairsM___redArg___lam__3(v_toPure_20_, v_next_21_, v_G_22_, v_____do__lift_23_);
lean_dec(v_next_21_);
return v_res_24_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__4(lean_object* v___x_25_, lean_object* v_toPure_26_, lean_object* v_toBind_27_, lean_object* v___f_28_, uint8_t v___x_29_, lean_object* v_fst_30_, lean_object* v_a_31_, lean_object* v_next_32_, lean_object* v_acc_33_, lean_object* v_h_34_, lean_object* v_G_35_){
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
v___f_38_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__3___boxed), 4, 3);
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
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__4___boxed(lean_object* v___x_52_, lean_object* v_toPure_53_, lean_object* v_toBind_54_, lean_object* v___f_55_, lean_object* v___x_56_, lean_object* v_fst_57_, lean_object* v_a_58_, lean_object* v_next_59_, lean_object* v_acc_60_, lean_object* v_h_61_, lean_object* v_G_62_){
_start:
{
uint8_t v___x_1057__boxed_63_; lean_object* v_res_64_; 
v___x_1057__boxed_63_ = lean_unbox(v___x_56_);
v_res_64_ = l_Array_filterPairsM___redArg___lam__4(v___x_52_, v_toPure_53_, v_toBind_54_, v___f_55_, v___x_1057__boxed_63_, v_fst_57_, v_a_58_, v_next_59_, v_acc_60_, v_h_61_, v_G_62_);
lean_dec_ref(v_a_58_);
lean_dec(v_fst_57_);
lean_dec(v___x_52_);
return v_res_64_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__5(lean_object* v___x_65_, lean_object* v_toPure_66_, lean_object* v_toBind_67_, lean_object* v___f_68_, uint8_t v___x_69_, lean_object* v_a_70_, lean_object* v___f_71_, lean_object* v_____s_72_){
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
v___f_77_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__4___boxed), 11, 7);
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
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__5___boxed(lean_object* v___x_81_, lean_object* v_toPure_82_, lean_object* v_toBind_83_, lean_object* v___f_84_, lean_object* v___x_85_, lean_object* v_a_86_, lean_object* v___f_87_, lean_object* v_____s_88_){
_start:
{
uint8_t v___x_1098__boxed_89_; lean_object* v_res_90_; 
v___x_1098__boxed_89_ = lean_unbox(v___x_85_);
v_res_90_ = l_Array_filterPairsM___redArg___lam__5(v___x_81_, v_toPure_82_, v_toBind_83_, v___f_84_, v___x_1098__boxed_89_, v_a_86_, v___f_87_, v_____s_88_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__6(lean_object* v_toPure_91_, lean_object* v_____s_92_){
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
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7(lean_object* v_toPure_104_, lean_object* v_next_105_, lean_object* v_G_106_, lean_object* v_____do__lift_107_){
_start:
{
if (lean_obj_tag(v_____do__lift_107_) == 0)
{
lean_object* v_a_108_; lean_object* v___x_109_; 
lean_dec(v_G_106_);
v_a_108_ = lean_ctor_get(v_____do__lift_107_, 0);
lean_inc(v_a_108_);
lean_dec_ref(v_____do__lift_107_);
v___x_109_ = lean_apply_2(v_toPure_104_, lean_box(0), v_a_108_);
return v___x_109_;
}
else
{
lean_object* v_a_110_; lean_object* v___x_111_; lean_object* v___x_112_; lean_object* v___x_113_; 
lean_dec(v_toPure_104_);
v_a_110_ = lean_ctor_get(v_____do__lift_107_, 0);
lean_inc(v_a_110_);
lean_dec_ref(v_____do__lift_107_);
v___x_111_ = lean_unsigned_to_nat(1u);
v___x_112_ = lean_nat_add(v_next_105_, v___x_111_);
v___x_113_ = lean_apply_4(v_G_106_, v___x_112_, v_a_110_, lean_box(0), lean_box(0));
return v___x_113_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__7___boxed(lean_object* v_toPure_114_, lean_object* v_next_115_, lean_object* v_G_116_, lean_object* v_____do__lift_117_){
_start:
{
lean_object* v_res_118_; 
v_res_118_ = l_Array_filterPairsM___redArg___lam__7(v_toPure_114_, v_next_115_, v_G_116_, v_____do__lift_117_);
lean_dec(v_next_115_);
return v_res_118_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__8(lean_object* v_toPure_119_, lean_object* v_next_120_, lean_object* v___x_121_, lean_object* v_G_122_, lean_object* v_____do__lift_123_){
_start:
{
if (lean_obj_tag(v_____do__lift_123_) == 0)
{
lean_object* v_a_124_; lean_object* v___x_125_; 
lean_dec(v_G_122_);
v_a_124_ = lean_ctor_get(v_____do__lift_123_, 0);
lean_inc(v_a_124_);
lean_dec_ref(v_____do__lift_123_);
v___x_125_ = lean_apply_2(v_toPure_119_, lean_box(0), v_a_124_);
return v___x_125_;
}
else
{
lean_object* v_a_126_; lean_object* v___x_127_; lean_object* v___x_128_; 
lean_dec(v_toPure_119_);
v_a_126_ = lean_ctor_get(v_____do__lift_123_, 0);
lean_inc(v_a_126_);
lean_dec_ref(v_____do__lift_123_);
v___x_127_ = lean_nat_add(v_next_120_, v___x_121_);
v___x_128_ = lean_apply_4(v_G_122_, v___x_127_, v_a_126_, lean_box(0), lean_box(0));
return v___x_128_;
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__8___boxed(lean_object* v_toPure_129_, lean_object* v_next_130_, lean_object* v___x_131_, lean_object* v_G_132_, lean_object* v_____do__lift_133_){
_start:
{
lean_object* v_res_134_; 
v_res_134_ = l_Array_filterPairsM___redArg___lam__8(v_toPure_129_, v_next_130_, v___x_131_, v_G_132_, v_____do__lift_133_);
lean_dec(v___x_131_);
lean_dec(v_next_130_);
return v_res_134_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__9(lean_object* v___x_135_, lean_object* v_next_136_, uint8_t v___x_137_, lean_object* v_toPure_138_, lean_object* v_snd_139_, lean_object* v_fst_140_, lean_object* v_next_141_, lean_object* v_____x_142_){
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
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__9___boxed(lean_object* v___x_170_, lean_object* v_next_171_, lean_object* v___x_172_, lean_object* v_toPure_173_, lean_object* v_snd_174_, lean_object* v_fst_175_, lean_object* v_next_176_, lean_object* v_____x_177_){
_start:
{
uint8_t v___x_1173__boxed_178_; lean_object* v_res_179_; 
v___x_1173__boxed_178_ = lean_unbox(v___x_172_);
v_res_179_ = l_Array_filterPairsM___redArg___lam__9(v___x_170_, v_next_171_, v___x_1173__boxed_178_, v_toPure_173_, v_snd_174_, v_fst_175_, v_next_176_, v_____x_177_);
lean_dec(v_next_176_);
lean_dec(v_next_171_);
lean_dec(v___x_170_);
return v_res_179_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__10(lean_object* v___x_180_, lean_object* v_toPure_181_, lean_object* v___x_182_, lean_object* v_toBind_183_, lean_object* v___f_184_, lean_object* v_next_185_, lean_object* v_a_186_, lean_object* v_f_187_, uint8_t v___x_188_, lean_object* v_next_189_, lean_object* v_acc_190_, lean_object* v_h_191_, lean_object* v_G_192_){
_start:
{
uint8_t v___x_193_; 
v___x_193_ = lean_nat_dec_lt(v_next_189_, v___x_180_);
if (v___x_193_ == 0)
{
lean_object* v___x_194_; 
lean_dec(v_G_192_);
lean_dec(v_next_189_);
lean_dec(v_f_187_);
lean_dec(v_next_185_);
lean_dec(v___f_184_);
lean_dec(v_toBind_183_);
lean_dec(v___x_182_);
v___x_194_ = lean_apply_2(v_toPure_181_, lean_box(0), v_acc_190_);
return v___x_194_;
}
else
{
lean_object* v_fst_195_; lean_object* v_snd_196_; lean_object* v___x_198_; uint8_t v_isShared_199_; uint8_t v_isSharedCheck_225_; 
v_fst_195_ = lean_ctor_get(v_acc_190_, 0);
v_snd_196_ = lean_ctor_get(v_acc_190_, 1);
v_isSharedCheck_225_ = !lean_is_exclusive(v_acc_190_);
if (v_isSharedCheck_225_ == 0)
{
v___x_198_ = v_acc_190_;
v_isShared_199_ = v_isSharedCheck_225_;
goto v_resetjp_197_;
}
else
{
lean_inc(v_snd_196_);
lean_inc(v_fst_195_);
lean_dec(v_acc_190_);
v___x_198_ = lean_box(0);
v_isShared_199_ = v_isSharedCheck_225_;
goto v_resetjp_197_;
}
v_resetjp_197_:
{
lean_object* v___f_200_; lean_object* v___y_202_; lean_object* v___x_205_; lean_object* v___f_206_; uint8_t v___y_208_; lean_object* v___x_218_; lean_object* v___x_219_; uint8_t v___x_220_; 
lean_inc(v___x_182_);
lean_inc_n(v_next_189_, 2);
lean_inc_n(v_toPure_181_, 2);
v___f_200_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_200_, 0, v_toPure_181_);
lean_closure_set(v___f_200_, 1, v_next_189_);
lean_closure_set(v___f_200_, 2, v___x_182_);
lean_closure_set(v___f_200_, 3, v_G_192_);
v___x_205_ = lean_box(v___x_193_);
lean_inc(v_next_185_);
lean_inc(v_fst_195_);
lean_inc(v_snd_196_);
v___f_206_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__9___boxed), 8, 7);
lean_closure_set(v___f_206_, 0, v___x_182_);
lean_closure_set(v___f_206_, 1, v_next_189_);
lean_closure_set(v___f_206_, 2, v___x_205_);
lean_closure_set(v___f_206_, 3, v_toPure_181_);
lean_closure_set(v___f_206_, 4, v_snd_196_);
lean_closure_set(v___f_206_, 5, v_fst_195_);
lean_closure_set(v___f_206_, 6, v_next_185_);
v___x_218_ = lean_box(v___x_188_);
v___x_219_ = lean_array_get(v___x_218_, v_fst_195_, v_next_185_);
lean_dec(v___x_218_);
v___x_220_ = lean_unbox(v___x_219_);
if (v___x_220_ == 0)
{
lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
lean_dec(v___x_219_);
v___x_221_ = lean_box(v___x_188_);
v___x_222_ = lean_array_get(v___x_221_, v_fst_195_, v_next_189_);
lean_dec(v___x_221_);
v___x_223_ = lean_unbox(v___x_222_);
lean_dec(v___x_222_);
v___y_208_ = v___x_223_;
goto v___jp_207_;
}
else
{
uint8_t v___x_224_; 
v___x_224_ = lean_unbox(v___x_219_);
lean_dec(v___x_219_);
v___y_208_ = v___x_224_;
goto v___jp_207_;
}
v___jp_201_:
{
lean_object* v___x_203_; lean_object* v___x_204_; 
lean_inc(v_toBind_183_);
v___x_203_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___y_202_, v___f_184_);
v___x_204_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___x_203_, v___f_200_);
return v___x_204_;
}
v___jp_207_:
{
if (v___y_208_ == 0)
{
lean_object* v___x_209_; lean_object* v___x_210_; lean_object* v___x_211_; lean_object* v___x_212_; 
lean_del_object(v___x_198_);
lean_dec(v_snd_196_);
lean_dec(v_fst_195_);
lean_dec(v_toPure_181_);
v___x_209_ = lean_array_fget_borrowed(v_a_186_, v_next_185_);
lean_dec(v_next_185_);
v___x_210_ = lean_array_fget_borrowed(v_a_186_, v_next_189_);
lean_dec(v_next_189_);
lean_inc(v___x_210_);
lean_inc(v___x_209_);
v___x_211_ = lean_apply_2(v_f_187_, v___x_209_, v___x_210_);
lean_inc(v_toBind_183_);
v___x_212_ = lean_apply_4(v_toBind_183_, lean_box(0), lean_box(0), v___x_211_, v___f_206_);
v___y_202_ = v___x_212_;
goto v___jp_201_;
}
else
{
lean_object* v___x_214_; 
lean_dec_ref(v___f_206_);
lean_dec(v_next_189_);
lean_dec(v_f_187_);
lean_dec(v_next_185_);
if (v_isShared_199_ == 0)
{
v___x_214_ = v___x_198_;
goto v_reusejp_213_;
}
else
{
lean_object* v_reuseFailAlloc_217_; 
v_reuseFailAlloc_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_217_, 0, v_fst_195_);
lean_ctor_set(v_reuseFailAlloc_217_, 1, v_snd_196_);
v___x_214_ = v_reuseFailAlloc_217_;
goto v_reusejp_213_;
}
v_reusejp_213_:
{
lean_object* v___x_215_; lean_object* v___x_216_; 
v___x_215_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_215_, 0, v___x_214_);
v___x_216_ = lean_apply_2(v_toPure_181_, lean_box(0), v___x_215_);
v___y_202_ = v___x_216_;
goto v___jp_201_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__10___boxed(lean_object* v___x_226_, lean_object* v_toPure_227_, lean_object* v___x_228_, lean_object* v_toBind_229_, lean_object* v___f_230_, lean_object* v_next_231_, lean_object* v_a_232_, lean_object* v_f_233_, lean_object* v___x_234_, lean_object* v_next_235_, lean_object* v_acc_236_, lean_object* v_h_237_, lean_object* v_G_238_){
_start:
{
uint8_t v___x_1234__boxed_239_; lean_object* v_res_240_; 
v___x_1234__boxed_239_ = lean_unbox(v___x_234_);
v_res_240_ = l_Array_filterPairsM___redArg___lam__10(v___x_226_, v_toPure_227_, v___x_228_, v_toBind_229_, v___f_230_, v_next_231_, v_a_232_, v_f_233_, v___x_1234__boxed_239_, v_next_235_, v_acc_236_, v_h_237_, v_G_238_);
lean_dec_ref(v_a_232_);
lean_dec(v___x_226_);
return v_res_240_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11(lean_object* v___x_241_, lean_object* v_toPure_242_, lean_object* v_toBind_243_, lean_object* v___f_244_, lean_object* v_a_245_, lean_object* v_f_246_, uint8_t v___x_247_, lean_object* v___f_248_, lean_object* v___f_249_, lean_object* v_next_250_, lean_object* v_acc_251_, lean_object* v_h_252_, lean_object* v_G_253_){
_start:
{
uint8_t v___x_254_; 
v___x_254_ = lean_nat_dec_lt(v_next_250_, v___x_241_);
if (v___x_254_ == 0)
{
lean_object* v___x_255_; 
lean_dec(v_G_253_);
lean_dec(v_next_250_);
lean_dec(v___f_249_);
lean_dec(v___f_248_);
lean_dec(v_f_246_);
lean_dec_ref(v_a_245_);
lean_dec(v___f_244_);
lean_dec(v_toBind_243_);
lean_dec(v___x_241_);
v___x_255_ = lean_apply_2(v_toPure_242_, lean_box(0), v_acc_251_);
return v___x_255_;
}
else
{
lean_object* v_fst_256_; lean_object* v_snd_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_273_; 
v_fst_256_ = lean_ctor_get(v_acc_251_, 0);
v_snd_257_ = lean_ctor_get(v_acc_251_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_acc_251_);
if (v_isSharedCheck_273_ == 0)
{
v___x_259_ = v_acc_251_;
v_isShared_260_ = v_isSharedCheck_273_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_snd_257_);
lean_inc(v_fst_256_);
lean_dec(v_acc_251_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_273_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___f_261_; lean_object* v___x_262_; lean_object* v___x_263_; lean_object* v___f_264_; lean_object* v___x_265_; lean_object* v___x_267_; 
lean_inc_n(v_next_250_, 2);
lean_inc(v_toPure_242_);
v___f_261_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_261_, 0, v_toPure_242_);
lean_closure_set(v___f_261_, 1, v_next_250_);
lean_closure_set(v___f_261_, 2, v_G_253_);
v___x_262_ = lean_unsigned_to_nat(1u);
v___x_263_ = lean_box(v___x_247_);
lean_inc(v_toBind_243_);
v___f_264_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__10___boxed), 13, 9);
lean_closure_set(v___f_264_, 0, v___x_241_);
lean_closure_set(v___f_264_, 1, v_toPure_242_);
lean_closure_set(v___f_264_, 2, v___x_262_);
lean_closure_set(v___f_264_, 3, v_toBind_243_);
lean_closure_set(v___f_264_, 4, v___f_244_);
lean_closure_set(v___f_264_, 5, v_next_250_);
lean_closure_set(v___f_264_, 6, v_a_245_);
lean_closure_set(v___f_264_, 7, v_f_246_);
lean_closure_set(v___f_264_, 8, v___x_263_);
v___x_265_ = lean_nat_add(v_next_250_, v___x_262_);
lean_dec(v_next_250_);
if (v_isShared_260_ == 0)
{
v___x_267_ = v___x_259_;
goto v_reusejp_266_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v_fst_256_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_snd_257_);
v___x_267_ = v_reuseFailAlloc_272_;
goto v_reusejp_266_;
}
v_reusejp_266_:
{
lean_object* v___x_268_; lean_object* v___x_269_; lean_object* v___x_270_; lean_object* v___x_271_; 
v___x_268_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_264_, v___x_265_, v___x_267_, lean_box(0));
lean_inc_n(v_toBind_243_, 2);
v___x_269_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v___x_268_, v___f_248_);
v___x_270_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v___x_269_, v___f_249_);
v___x_271_ = lean_apply_4(v_toBind_243_, lean_box(0), lean_box(0), v___x_270_, v___f_261_);
return v___x_271_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg___lam__11___boxed(lean_object* v___x_274_, lean_object* v_toPure_275_, lean_object* v_toBind_276_, lean_object* v___f_277_, lean_object* v_a_278_, lean_object* v_f_279_, lean_object* v___x_280_, lean_object* v___f_281_, lean_object* v___f_282_, lean_object* v_next_283_, lean_object* v_acc_284_, lean_object* v_h_285_, lean_object* v_G_286_){
_start:
{
uint8_t v___x_1307__boxed_287_; lean_object* v_res_288_; 
v___x_1307__boxed_287_ = lean_unbox(v___x_280_);
v_res_288_ = l_Array_filterPairsM___redArg___lam__11(v___x_274_, v_toPure_275_, v_toBind_276_, v___f_277_, v_a_278_, v_f_279_, v___x_1307__boxed_287_, v___f_281_, v___f_282_, v_next_283_, v_acc_284_, v_h_285_, v_G_286_);
return v_res_288_;
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM___redArg(lean_object* v_inst_289_, lean_object* v_a_290_, lean_object* v_f_291_){
_start:
{
lean_object* v_toApplicative_292_; lean_object* v_toBind_293_; lean_object* v___x_295_; uint8_t v_isShared_296_; uint8_t v_isSharedCheck_316_; 
v_toApplicative_292_ = lean_ctor_get(v_inst_289_, 0);
v_toBind_293_ = lean_ctor_get(v_inst_289_, 1);
v_isSharedCheck_316_ = !lean_is_exclusive(v_inst_289_);
if (v_isSharedCheck_316_ == 0)
{
v___x_295_ = v_inst_289_;
v_isShared_296_ = v_isSharedCheck_316_;
goto v_resetjp_294_;
}
else
{
lean_inc(v_toBind_293_);
lean_inc(v_toApplicative_292_);
lean_dec(v_inst_289_);
v___x_295_ = lean_box(0);
v_isShared_296_ = v_isSharedCheck_316_;
goto v_resetjp_294_;
}
v_resetjp_294_:
{
lean_object* v_toPure_297_; uint8_t v___x_298_; lean_object* v___x_299_; lean_object* v___x_300_; lean_object* v_removed_301_; lean_object* v___f_302_; lean_object* v___f_303_; lean_object* v___f_304_; lean_object* v___x_305_; lean_object* v___f_306_; lean_object* v___f_307_; lean_object* v___x_308_; lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_312_; 
v_toPure_297_ = lean_ctor_get(v_toApplicative_292_, 1);
lean_inc_n(v_toPure_297_, 6);
lean_dec_ref(v_toApplicative_292_);
v___x_298_ = 0;
v___x_299_ = lean_array_get_size(v_a_290_);
v___x_300_ = lean_box(v___x_298_);
v_removed_301_ = lean_mk_array(v___x_299_, v___x_300_);
v___f_302_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_302_, 0, v_toPure_297_);
v___f_303_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_303_, 0, v_toPure_297_);
v___f_304_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_304_, 0, v_toPure_297_);
v___x_305_ = lean_box(v___x_298_);
lean_inc_ref(v_a_290_);
lean_inc_n(v_toBind_293_, 2);
v___f_306_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_306_, 0, v___x_299_);
lean_closure_set(v___f_306_, 1, v_toPure_297_);
lean_closure_set(v___f_306_, 2, v_toBind_293_);
lean_closure_set(v___f_306_, 3, v___f_303_);
lean_closure_set(v___f_306_, 4, v___x_305_);
lean_closure_set(v___f_306_, 5, v_a_290_);
lean_closure_set(v___f_306_, 6, v___f_304_);
v___f_307_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__6), 2, 1);
lean_closure_set(v___f_307_, 0, v_toPure_297_);
v___x_308_ = lean_box(v___x_298_);
lean_inc_ref(v___f_302_);
v___f_309_ = lean_alloc_closure((void*)(l_Array_filterPairsM___redArg___lam__11___boxed), 13, 9);
lean_closure_set(v___f_309_, 0, v___x_299_);
lean_closure_set(v___f_309_, 1, v_toPure_297_);
lean_closure_set(v___f_309_, 2, v_toBind_293_);
lean_closure_set(v___f_309_, 3, v___f_302_);
lean_closure_set(v___f_309_, 4, v_a_290_);
lean_closure_set(v___f_309_, 5, v_f_291_);
lean_closure_set(v___f_309_, 6, v___x_308_);
lean_closure_set(v___f_309_, 7, v___f_307_);
lean_closure_set(v___f_309_, 8, v___f_302_);
v___x_310_ = lean_unsigned_to_nat(0u);
if (v_isShared_296_ == 0)
{
lean_ctor_set(v___x_295_, 1, v___x_310_);
lean_ctor_set(v___x_295_, 0, v_removed_301_);
v___x_312_ = v___x_295_;
goto v_reusejp_311_;
}
else
{
lean_object* v_reuseFailAlloc_315_; 
v_reuseFailAlloc_315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_315_, 0, v_removed_301_);
lean_ctor_set(v_reuseFailAlloc_315_, 1, v___x_310_);
v___x_312_ = v_reuseFailAlloc_315_;
goto v_reusejp_311_;
}
v_reusejp_311_:
{
lean_object* v___x_313_; lean_object* v___x_314_; 
v___x_313_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_309_, v___x_310_, v___x_312_, lean_box(0));
v___x_314_ = lean_apply_4(v_toBind_293_, lean_box(0), lean_box(0), v___x_313_, v___f_306_);
return v___x_314_;
}
}
}
}
LEAN_EXPORT lean_object* l_Array_filterPairsM(lean_object* v_m_317_, lean_object* v_inst_318_, lean_object* v_00_u03b1_319_, lean_object* v_a_320_, lean_object* v_f_321_){
_start:
{
lean_object* v___x_322_; 
v___x_322_ = l_Array_filterPairsM___redArg(v_inst_318_, v_a_320_, v_f_321_);
return v___x_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(lean_object* v_as_323_, size_t v_sz_324_, size_t v_i_325_, lean_object* v_b_326_){
_start:
{
lean_object* v_a_328_; uint8_t v___x_332_; 
v___x_332_ = lean_usize_dec_lt(v_i_325_, v_sz_324_);
if (v___x_332_ == 0)
{
return v_b_326_;
}
else
{
lean_object* v_snd_333_; lean_object* v_fst_334_; lean_object* v___x_336_; uint8_t v_isShared_337_; uint8_t v_isSharedCheck_367_; 
v_snd_333_ = lean_ctor_get(v_b_326_, 1);
v_fst_334_ = lean_ctor_get(v_b_326_, 0);
v_isSharedCheck_367_ = !lean_is_exclusive(v_b_326_);
if (v_isSharedCheck_367_ == 0)
{
v___x_336_ = v_b_326_;
v_isShared_337_ = v_isSharedCheck_367_;
goto v_resetjp_335_;
}
else
{
lean_inc(v_snd_333_);
lean_inc(v_fst_334_);
lean_dec(v_b_326_);
v___x_336_ = lean_box(0);
v_isShared_337_ = v_isSharedCheck_367_;
goto v_resetjp_335_;
}
v_resetjp_335_:
{
lean_object* v_array_338_; lean_object* v_start_339_; lean_object* v_stop_340_; uint8_t v___x_341_; 
v_array_338_ = lean_ctor_get(v_snd_333_, 0);
v_start_339_ = lean_ctor_get(v_snd_333_, 1);
v_stop_340_ = lean_ctor_get(v_snd_333_, 2);
v___x_341_ = lean_nat_dec_lt(v_start_339_, v_stop_340_);
if (v___x_341_ == 0)
{
lean_object* v___x_343_; 
if (v_isShared_337_ == 0)
{
v___x_343_ = v___x_336_;
goto v_reusejp_342_;
}
else
{
lean_object* v_reuseFailAlloc_344_; 
v_reuseFailAlloc_344_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_344_, 0, v_fst_334_);
lean_ctor_set(v_reuseFailAlloc_344_, 1, v_snd_333_);
v___x_343_ = v_reuseFailAlloc_344_;
goto v_reusejp_342_;
}
v_reusejp_342_:
{
return v___x_343_;
}
}
else
{
lean_object* v___x_346_; uint8_t v_isShared_347_; uint8_t v_isSharedCheck_363_; 
lean_inc(v_stop_340_);
lean_inc(v_start_339_);
lean_inc_ref(v_array_338_);
v_isSharedCheck_363_ = !lean_is_exclusive(v_snd_333_);
if (v_isSharedCheck_363_ == 0)
{
lean_object* v_unused_364_; lean_object* v_unused_365_; lean_object* v_unused_366_; 
v_unused_364_ = lean_ctor_get(v_snd_333_, 2);
lean_dec(v_unused_364_);
v_unused_365_ = lean_ctor_get(v_snd_333_, 1);
lean_dec(v_unused_365_);
v_unused_366_ = lean_ctor_get(v_snd_333_, 0);
lean_dec(v_unused_366_);
v___x_346_ = v_snd_333_;
v_isShared_347_ = v_isSharedCheck_363_;
goto v_resetjp_345_;
}
else
{
lean_dec(v_snd_333_);
v___x_346_ = lean_box(0);
v_isShared_347_ = v_isSharedCheck_363_;
goto v_resetjp_345_;
}
v_resetjp_345_:
{
lean_object* v_a_348_; lean_object* v___x_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___x_353_; 
v_a_348_ = lean_array_uget_borrowed(v_as_323_, v_i_325_);
v___x_349_ = lean_array_fget(v_array_338_, v_start_339_);
v___x_350_ = lean_unsigned_to_nat(1u);
v___x_351_ = lean_nat_add(v_start_339_, v___x_350_);
lean_dec(v_start_339_);
if (v_isShared_347_ == 0)
{
lean_ctor_set(v___x_346_, 1, v___x_351_);
v___x_353_ = v___x_346_;
goto v_reusejp_352_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_array_338_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_351_);
lean_ctor_set(v_reuseFailAlloc_362_, 2, v_stop_340_);
v___x_353_ = v_reuseFailAlloc_362_;
goto v_reusejp_352_;
}
v_reusejp_352_:
{
uint8_t v___x_354_; 
v___x_354_ = lean_unbox(v_a_348_);
if (v___x_354_ == 0)
{
lean_object* v___x_356_; 
lean_dec(v___x_349_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v___x_353_);
v___x_356_ = v___x_336_;
goto v_reusejp_355_;
}
else
{
lean_object* v_reuseFailAlloc_357_; 
v_reuseFailAlloc_357_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_357_, 0, v_fst_334_);
lean_ctor_set(v_reuseFailAlloc_357_, 1, v___x_353_);
v___x_356_ = v_reuseFailAlloc_357_;
goto v_reusejp_355_;
}
v_reusejp_355_:
{
v_a_328_ = v___x_356_;
goto v___jp_327_;
}
}
else
{
lean_object* v___x_358_; lean_object* v___x_360_; 
v___x_358_ = lean_array_push(v_fst_334_, v___x_349_);
if (v_isShared_337_ == 0)
{
lean_ctor_set(v___x_336_, 1, v___x_353_);
lean_ctor_set(v___x_336_, 0, v___x_358_);
v___x_360_ = v___x_336_;
goto v_reusejp_359_;
}
else
{
lean_object* v_reuseFailAlloc_361_; 
v_reuseFailAlloc_361_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_361_, 0, v___x_358_);
lean_ctor_set(v_reuseFailAlloc_361_, 1, v___x_353_);
v___x_360_ = v_reuseFailAlloc_361_;
goto v_reusejp_359_;
}
v_reusejp_359_:
{
v_a_328_ = v___x_360_;
goto v___jp_327_;
}
}
}
}
}
}
}
v___jp_327_:
{
size_t v___x_329_; size_t v___x_330_; 
v___x_329_ = ((size_t)1ULL);
v___x_330_ = lean_usize_add(v_i_325_, v___x_329_);
v_i_325_ = v___x_330_;
v_b_326_ = v_a_328_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg___boxed(lean_object* v_as_368_, lean_object* v_sz_369_, lean_object* v_i_370_, lean_object* v_b_371_){
_start:
{
size_t v_sz_boxed_372_; size_t v_i_boxed_373_; lean_object* v_res_374_; 
v_sz_boxed_372_ = lean_unbox_usize(v_sz_369_);
lean_dec(v_sz_369_);
v_i_boxed_373_ = lean_unbox_usize(v_i_370_);
lean_dec(v_i_370_);
v_res_374_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_as_368_, v_sz_boxed_372_, v_i_boxed_373_, v_b_371_);
lean_dec_ref(v_as_368_);
return v_res_374_;
}
}
LEAN_EXPORT lean_object* l_Array_mask___redArg(lean_object* v_mask_377_, lean_object* v_xs_378_){
_start:
{
lean_object* v___x_379_; lean_object* v_ys_380_; lean_object* v___x_381_; lean_object* v___x_382_; lean_object* v___x_383_; size_t v_sz_384_; size_t v___x_385_; lean_object* v___x_386_; lean_object* v_fst_387_; 
v___x_379_ = lean_unsigned_to_nat(0u);
v_ys_380_ = ((lean_object*)(l_Array_mask___redArg___closed__0));
v___x_381_ = lean_array_get_size(v_xs_378_);
v___x_382_ = l_Array_toSubarray___redArg(v_xs_378_, v___x_379_, v___x_381_);
v___x_383_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_383_, 0, v_ys_380_);
lean_ctor_set(v___x_383_, 1, v___x_382_);
v_sz_384_ = lean_array_size(v_mask_377_);
v___x_385_ = ((size_t)0ULL);
v___x_386_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_mask_377_, v_sz_384_, v___x_385_, v___x_383_);
v_fst_387_ = lean_ctor_get(v___x_386_, 0);
lean_inc(v_fst_387_);
lean_dec_ref(v___x_386_);
return v_fst_387_;
}
}
LEAN_EXPORT lean_object* l_Array_mask___redArg___boxed(lean_object* v_mask_388_, lean_object* v_xs_389_){
_start:
{
lean_object* v_res_390_; 
v_res_390_ = l_Array_mask___redArg(v_mask_388_, v_xs_389_);
lean_dec_ref(v_mask_388_);
return v_res_390_;
}
}
LEAN_EXPORT lean_object* l_Array_mask(lean_object* v_00_u03b1_391_, lean_object* v_mask_392_, lean_object* v_xs_393_){
_start:
{
lean_object* v___x_394_; 
v___x_394_ = l_Array_mask___redArg(v_mask_392_, v_xs_393_);
return v___x_394_;
}
}
LEAN_EXPORT lean_object* l_Array_mask___boxed(lean_object* v_00_u03b1_395_, lean_object* v_mask_396_, lean_object* v_xs_397_){
_start:
{
lean_object* v_res_398_; 
v_res_398_ = l_Array_mask(v_00_u03b1_395_, v_mask_396_, v_xs_397_);
lean_dec_ref(v_mask_396_);
return v_res_398_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(lean_object* v_00_u03b1_399_, lean_object* v_as_400_, size_t v_sz_401_, size_t v_i_402_, lean_object* v_b_403_){
_start:
{
lean_object* v___x_404_; 
v___x_404_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___redArg(v_as_400_, v_sz_401_, v_i_402_, v_b_403_);
return v___x_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0___boxed(lean_object* v_00_u03b1_405_, lean_object* v_as_406_, lean_object* v_sz_407_, lean_object* v_i_408_, lean_object* v_b_409_){
_start:
{
size_t v_sz_boxed_410_; size_t v_i_boxed_411_; lean_object* v_res_412_; 
v_sz_boxed_410_ = lean_unbox_usize(v_sz_407_);
lean_dec(v_sz_407_);
v_i_boxed_411_ = lean_unbox_usize(v_i_408_);
lean_dec(v_i_408_);
v_res_412_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_mask_spec__0(v_00_u03b1_405_, v_as_406_, v_sz_boxed_410_, v_i_boxed_411_, v_b_409_);
lean_dec_ref(v_as_406_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(lean_object* v_xs_413_, lean_object* v_ys_414_, lean_object* v_as_415_, size_t v_sz_416_, size_t v_i_417_, lean_object* v_b_418_){
_start:
{
lean_object* v_a_420_; uint8_t v___x_424_; 
v___x_424_ = lean_usize_dec_lt(v_i_417_, v_sz_416_);
if (v___x_424_ == 0)
{
return v_b_418_;
}
else
{
lean_object* v_snd_425_; lean_object* v_fst_426_; lean_object* v___x_428_; uint8_t v_isShared_429_; uint8_t v_isSharedCheck_474_; 
v_snd_425_ = lean_ctor_get(v_b_418_, 1);
v_fst_426_ = lean_ctor_get(v_b_418_, 0);
v_isSharedCheck_474_ = !lean_is_exclusive(v_b_418_);
if (v_isSharedCheck_474_ == 0)
{
v___x_428_ = v_b_418_;
v_isShared_429_ = v_isSharedCheck_474_;
goto v_resetjp_427_;
}
else
{
lean_inc(v_snd_425_);
lean_inc(v_fst_426_);
lean_dec(v_b_418_);
v___x_428_ = lean_box(0);
v_isShared_429_ = v_isSharedCheck_474_;
goto v_resetjp_427_;
}
v_resetjp_427_:
{
lean_object* v_fst_430_; lean_object* v_snd_431_; lean_object* v___x_433_; uint8_t v_isShared_434_; uint8_t v_isSharedCheck_473_; 
v_fst_430_ = lean_ctor_get(v_snd_425_, 0);
v_snd_431_ = lean_ctor_get(v_snd_425_, 1);
v_isSharedCheck_473_ = !lean_is_exclusive(v_snd_425_);
if (v_isSharedCheck_473_ == 0)
{
v___x_433_ = v_snd_425_;
v_isShared_434_ = v_isSharedCheck_473_;
goto v_resetjp_432_;
}
else
{
lean_inc(v_snd_431_);
lean_inc(v_fst_430_);
lean_dec(v_snd_425_);
v___x_433_ = lean_box(0);
v_isShared_434_ = v_isSharedCheck_473_;
goto v_resetjp_432_;
}
v_resetjp_432_:
{
lean_object* v_a_435_; uint8_t v___x_436_; 
v_a_435_ = lean_array_uget_borrowed(v_as_415_, v_i_417_);
v___x_436_ = lean_unbox(v_a_435_);
if (v___x_436_ == 0)
{
lean_object* v___x_437_; uint8_t v___x_438_; 
v___x_437_ = lean_array_get_size(v_xs_413_);
v___x_438_ = lean_nat_dec_lt(v_fst_426_, v___x_437_);
if (v___x_438_ == 0)
{
lean_object* v___x_440_; 
if (v_isShared_434_ == 0)
{
v___x_440_ = v___x_433_;
goto v_reusejp_439_;
}
else
{
lean_object* v_reuseFailAlloc_444_; 
v_reuseFailAlloc_444_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_444_, 0, v_fst_430_);
lean_ctor_set(v_reuseFailAlloc_444_, 1, v_snd_431_);
v___x_440_ = v_reuseFailAlloc_444_;
goto v_reusejp_439_;
}
v_reusejp_439_:
{
lean_object* v___x_442_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_440_);
v___x_442_ = v___x_428_;
goto v_reusejp_441_;
}
else
{
lean_object* v_reuseFailAlloc_443_; 
v_reuseFailAlloc_443_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_443_, 0, v_fst_426_);
lean_ctor_set(v_reuseFailAlloc_443_, 1, v___x_440_);
v___x_442_ = v_reuseFailAlloc_443_;
goto v_reusejp_441_;
}
v_reusejp_441_:
{
v_a_420_ = v___x_442_;
goto v___jp_419_;
}
}
}
else
{
lean_object* v___x_445_; lean_object* v___x_446_; lean_object* v___x_447_; lean_object* v___x_448_; lean_object* v___x_450_; 
v___x_445_ = lean_array_fget_borrowed(v_xs_413_, v_fst_426_);
lean_inc(v___x_445_);
v___x_446_ = lean_array_push(v_snd_431_, v___x_445_);
v___x_447_ = lean_unsigned_to_nat(1u);
v___x_448_ = lean_nat_add(v_fst_426_, v___x_447_);
lean_dec(v_fst_426_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_446_);
v___x_450_ = v___x_433_;
goto v_reusejp_449_;
}
else
{
lean_object* v_reuseFailAlloc_454_; 
v_reuseFailAlloc_454_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_454_, 0, v_fst_430_);
lean_ctor_set(v_reuseFailAlloc_454_, 1, v___x_446_);
v___x_450_ = v_reuseFailAlloc_454_;
goto v_reusejp_449_;
}
v_reusejp_449_:
{
lean_object* v___x_452_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_450_);
lean_ctor_set(v___x_428_, 0, v___x_448_);
v___x_452_ = v___x_428_;
goto v_reusejp_451_;
}
else
{
lean_object* v_reuseFailAlloc_453_; 
v_reuseFailAlloc_453_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_453_, 0, v___x_448_);
lean_ctor_set(v_reuseFailAlloc_453_, 1, v___x_450_);
v___x_452_ = v_reuseFailAlloc_453_;
goto v_reusejp_451_;
}
v_reusejp_451_:
{
v_a_420_ = v___x_452_;
goto v___jp_419_;
}
}
}
}
else
{
lean_object* v___x_455_; uint8_t v___x_456_; 
v___x_455_ = lean_array_get_size(v_ys_414_);
v___x_456_ = lean_nat_dec_lt(v_fst_430_, v___x_455_);
if (v___x_456_ == 0)
{
lean_object* v___x_458_; 
if (v_isShared_434_ == 0)
{
v___x_458_ = v___x_433_;
goto v_reusejp_457_;
}
else
{
lean_object* v_reuseFailAlloc_462_; 
v_reuseFailAlloc_462_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_462_, 0, v_fst_430_);
lean_ctor_set(v_reuseFailAlloc_462_, 1, v_snd_431_);
v___x_458_ = v_reuseFailAlloc_462_;
goto v_reusejp_457_;
}
v_reusejp_457_:
{
lean_object* v___x_460_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_458_);
v___x_460_ = v___x_428_;
goto v_reusejp_459_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_fst_426_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_458_);
v___x_460_ = v_reuseFailAlloc_461_;
goto v_reusejp_459_;
}
v_reusejp_459_:
{
v_a_420_ = v___x_460_;
goto v___jp_419_;
}
}
}
else
{
lean_object* v___x_463_; lean_object* v___x_464_; lean_object* v___x_465_; lean_object* v___x_466_; lean_object* v___x_468_; 
v___x_463_ = lean_array_fget_borrowed(v_ys_414_, v_fst_430_);
lean_inc(v___x_463_);
v___x_464_ = lean_array_push(v_snd_431_, v___x_463_);
v___x_465_ = lean_unsigned_to_nat(1u);
v___x_466_ = lean_nat_add(v_fst_430_, v___x_465_);
lean_dec(v_fst_430_);
if (v_isShared_434_ == 0)
{
lean_ctor_set(v___x_433_, 1, v___x_464_);
lean_ctor_set(v___x_433_, 0, v___x_466_);
v___x_468_ = v___x_433_;
goto v_reusejp_467_;
}
else
{
lean_object* v_reuseFailAlloc_472_; 
v_reuseFailAlloc_472_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_472_, 0, v___x_466_);
lean_ctor_set(v_reuseFailAlloc_472_, 1, v___x_464_);
v___x_468_ = v_reuseFailAlloc_472_;
goto v_reusejp_467_;
}
v_reusejp_467_:
{
lean_object* v___x_470_; 
if (v_isShared_429_ == 0)
{
lean_ctor_set(v___x_428_, 1, v___x_468_);
v___x_470_ = v___x_428_;
goto v_reusejp_469_;
}
else
{
lean_object* v_reuseFailAlloc_471_; 
v_reuseFailAlloc_471_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_471_, 0, v_fst_426_);
lean_ctor_set(v_reuseFailAlloc_471_, 1, v___x_468_);
v___x_470_ = v_reuseFailAlloc_471_;
goto v_reusejp_469_;
}
v_reusejp_469_:
{
v_a_420_ = v___x_470_;
goto v___jp_419_;
}
}
}
}
}
}
}
v___jp_419_:
{
size_t v___x_421_; size_t v___x_422_; 
v___x_421_ = ((size_t)1ULL);
v___x_422_ = lean_usize_add(v_i_417_, v___x_421_);
v_i_417_ = v___x_422_;
v_b_418_ = v_a_420_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg___boxed(lean_object* v_xs_475_, lean_object* v_ys_476_, lean_object* v_as_477_, lean_object* v_sz_478_, lean_object* v_i_479_, lean_object* v_b_480_){
_start:
{
size_t v_sz_boxed_481_; size_t v_i_boxed_482_; lean_object* v_res_483_; 
v_sz_boxed_481_ = lean_unbox_usize(v_sz_478_);
lean_dec(v_sz_478_);
v_i_boxed_482_ = lean_unbox_usize(v_i_479_);
lean_dec(v_i_479_);
v_res_483_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_475_, v_ys_476_, v_as_477_, v_sz_boxed_481_, v_i_boxed_482_, v_b_480_);
lean_dec_ref(v_as_477_);
lean_dec_ref(v_ys_476_);
lean_dec_ref(v_xs_475_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Array_zipMasked___redArg(lean_object* v_mask_490_, lean_object* v_xs_491_, lean_object* v_ys_492_){
_start:
{
lean_object* v___x_493_; size_t v_sz_494_; size_t v___x_495_; lean_object* v___x_496_; lean_object* v_snd_497_; lean_object* v_snd_498_; 
v___x_493_ = ((lean_object*)(l_Array_zipMasked___redArg___closed__1));
v_sz_494_ = lean_array_size(v_mask_490_);
v___x_495_ = ((size_t)0ULL);
v___x_496_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_491_, v_ys_492_, v_mask_490_, v_sz_494_, v___x_495_, v___x_493_);
v_snd_497_ = lean_ctor_get(v___x_496_, 1);
lean_inc(v_snd_497_);
lean_dec_ref(v___x_496_);
v_snd_498_ = lean_ctor_get(v_snd_497_, 1);
lean_inc(v_snd_498_);
lean_dec(v_snd_497_);
return v_snd_498_;
}
}
LEAN_EXPORT lean_object* l_Array_zipMasked___redArg___boxed(lean_object* v_mask_499_, lean_object* v_xs_500_, lean_object* v_ys_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Array_zipMasked___redArg(v_mask_499_, v_xs_500_, v_ys_501_);
lean_dec_ref(v_ys_501_);
lean_dec_ref(v_xs_500_);
lean_dec_ref(v_mask_499_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Array_zipMasked(lean_object* v_00_u03b1_503_, lean_object* v_mask_504_, lean_object* v_xs_505_, lean_object* v_ys_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l_Array_zipMasked___redArg(v_mask_504_, v_xs_505_, v_ys_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l_Array_zipMasked___boxed(lean_object* v_00_u03b1_508_, lean_object* v_mask_509_, lean_object* v_xs_510_, lean_object* v_ys_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Array_zipMasked(v_00_u03b1_508_, v_mask_509_, v_xs_510_, v_ys_511_);
lean_dec_ref(v_ys_511_);
lean_dec_ref(v_xs_510_);
lean_dec_ref(v_mask_509_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(lean_object* v_00_u03b1_513_, lean_object* v_xs_514_, lean_object* v_ys_515_, lean_object* v_as_516_, size_t v_sz_517_, size_t v_i_518_, lean_object* v_b_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___redArg(v_xs_514_, v_ys_515_, v_as_516_, v_sz_517_, v_i_518_, v_b_519_);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0___boxed(lean_object* v_00_u03b1_521_, lean_object* v_xs_522_, lean_object* v_ys_523_, lean_object* v_as_524_, lean_object* v_sz_525_, lean_object* v_i_526_, lean_object* v_b_527_){
_start:
{
size_t v_sz_boxed_528_; size_t v_i_boxed_529_; lean_object* v_res_530_; 
v_sz_boxed_528_ = lean_unbox_usize(v_sz_525_);
lean_dec(v_sz_525_);
v_i_boxed_529_ = lean_unbox_usize(v_i_526_);
lean_dec(v_i_526_);
v_res_530_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Array_zipMasked_spec__0(v_00_u03b1_521_, v_xs_522_, v_ys_523_, v_as_524_, v_sz_boxed_528_, v_i_boxed_529_, v_b_527_);
lean_dec_ref(v_as_524_);
lean_dec_ref(v_ys_523_);
lean_dec_ref(v_xs_522_);
return v_res_530_;
}
}
lean_object* runtime_initialize_Init_Data_Stream(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Nat(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_Iterators(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Lean_Data_Array(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
