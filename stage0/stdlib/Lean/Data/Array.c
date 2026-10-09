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
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__10(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__10___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__11(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* l_Lean_Array_filterPairsM___redArg___lam__4(lean_object* v___x_25_, lean_object* v_toPure_26_, lean_object* v_toBind_27_, lean_object* v___f_28_, uint8_t v___x_29_, lean_object* v_fst_30_, lean_object* v_a_31_, lean_object* v_next_32_, lean_object* v_acc_33_, lean_object* v_h_34_, lean_object* v_G_35_){
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
LEAN_EXPORT void l_Lean_Array_filterPairsM___redArg___lam__4_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_25_ = stack[0].m_obj;
lean_object* v_toPure_26_ = stack[1].m_obj;
lean_object* v_toBind_27_ = stack[2].m_obj;
lean_object* v___f_28_ = stack[3].m_obj;
uint8_t v___x_29_ = stack[4].m_num;
lean_object* v_fst_30_ = stack[5].m_obj;
lean_object* v_a_31_ = stack[6].m_obj;
lean_object* v_next_32_ = stack[7].m_obj;
lean_object* v_acc_33_ = stack[8].m_obj;
lean_object* v_G_35_ = stack[10].m_obj;
lean_object* v_res_52_;
v_res_52_ = l_Lean_Array_filterPairsM___redArg___lam__4(v___x_25_, v_toPure_26_, v_toBind_27_, v___f_28_, v___x_29_, v_fst_30_, v_a_31_, v_next_32_, v_acc_33_, lean_box(0), v_G_35_);
stack->m_obj
 = v_res_52_;
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__4___boxed(lean_object* v___x_53_, lean_object* v_toPure_54_, lean_object* v_toBind_55_, lean_object* v___f_56_, lean_object* v___x_57_, lean_object* v_fst_58_, lean_object* v_a_59_, lean_object* v_next_60_, lean_object* v_acc_61_, lean_object* v_h_62_, lean_object* v_G_63_){
_start:
{
uint8_t v___x_874__boxed_64_; lean_object* v_res_65_; 
v___x_874__boxed_64_ = lean_unbox(v___x_57_);
v_res_65_ = l_Lean_Array_filterPairsM___redArg___lam__4(v___x_53_, v_toPure_54_, v_toBind_55_, v___f_56_, v___x_874__boxed_64_, v_fst_58_, v_a_59_, v_next_60_, v_acc_61_, v_h_62_, v_G_63_);
lean_dec_ref(v_a_59_);
lean_dec(v_fst_58_);
lean_dec(v___x_53_);
return v_res_65_;
}
}
lean_object* l_Lean_Array_filterPairsM___redArg___lam__5(lean_object* v___x_66_, lean_object* v_toPure_67_, lean_object* v_toBind_68_, lean_object* v___f_69_, uint8_t v___x_70_, lean_object* v_a_71_, lean_object* v___f_72_, lean_object* v_____s_73_){
_start:
{
lean_object* v_fst_74_; lean_object* v_snd_75_; lean_object* v___x_76_; lean_object* v___x_77_; lean_object* v___f_78_; lean_object* v_a_x27_79_; lean_object* v___x_80_; lean_object* v___x_81_; 
v_fst_74_ = lean_ctor_get(v_____s_73_, 0);
lean_inc(v_fst_74_);
v_snd_75_ = lean_ctor_get(v_____s_73_, 1);
lean_inc(v_snd_75_);
lean_dec_ref(v_____s_73_);
v___x_76_ = lean_unsigned_to_nat(0u);
v___x_77_ = lean_box(v___x_70_);
lean_inc(v_toBind_68_);
v___f_78_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__4___boxed), 11, 7);
lean_closure_set(v___f_78_, 0, v___x_66_);
lean_closure_set(v___f_78_, 1, v_toPure_67_);
lean_closure_set(v___f_78_, 2, v_toBind_68_);
lean_closure_set(v___f_78_, 3, v___f_69_);
lean_closure_set(v___f_78_, 4, v___x_77_);
lean_closure_set(v___f_78_, 5, v_fst_74_);
lean_closure_set(v___f_78_, 6, v_a_71_);
v_a_x27_79_ = lean_mk_empty_array_with_capacity(v_snd_75_);
lean_dec(v_snd_75_);
v___x_80_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_78_, v___x_76_, v_a_x27_79_, lean_box(0));
v___x_81_ = lean_apply_4(v_toBind_68_, lean_box(0), lean_box(0), v___x_80_, v___f_72_);
return v___x_81_;
}
}
LEAN_EXPORT void l_Lean_Array_filterPairsM___redArg___lam__5_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_66_ = stack[0].m_obj;
lean_object* v_toPure_67_ = stack[1].m_obj;
lean_object* v_toBind_68_ = stack[2].m_obj;
lean_object* v___f_69_ = stack[3].m_obj;
uint8_t v___x_70_ = stack[4].m_num;
lean_object* v_a_71_ = stack[5].m_obj;
lean_object* v___f_72_ = stack[6].m_obj;
lean_object* v_____s_73_ = stack[7].m_obj;
lean_object* v_res_82_;
v_res_82_ = l_Lean_Array_filterPairsM___redArg___lam__5(v___x_66_, v_toPure_67_, v_toBind_68_, v___f_69_, v___x_70_, v_a_71_, v___f_72_, v_____s_73_);
stack->m_obj
 = v_res_82_;
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__5___boxed(lean_object* v___x_83_, lean_object* v_toPure_84_, lean_object* v_toBind_85_, lean_object* v___f_86_, lean_object* v___x_87_, lean_object* v_a_88_, lean_object* v___f_89_, lean_object* v_____s_90_){
_start:
{
uint8_t v___x_937__boxed_91_; lean_object* v_res_92_; 
v___x_937__boxed_91_ = lean_unbox(v___x_87_);
v_res_92_ = l_Lean_Array_filterPairsM___redArg___lam__5(v___x_83_, v_toPure_84_, v_toBind_85_, v___f_86_, v___x_937__boxed_91_, v_a_88_, v___f_89_, v_____s_90_);
return v_res_92_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__6(lean_object* v_toPure_93_, lean_object* v_____s_94_){
_start:
{
lean_object* v_fst_95_; lean_object* v_snd_96_; lean_object* v___x_98_; uint8_t v_isShared_99_; uint8_t v_isSharedCheck_105_; 
v_fst_95_ = lean_ctor_get(v_____s_94_, 0);
v_snd_96_ = lean_ctor_get(v_____s_94_, 1);
v_isSharedCheck_105_ = !lean_is_exclusive(v_____s_94_);
if (v_isSharedCheck_105_ == 0)
{
v___x_98_ = v_____s_94_;
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
else
{
lean_inc(v_snd_96_);
lean_inc(v_fst_95_);
lean_dec(v_____s_94_);
v___x_98_ = lean_box(0);
v_isShared_99_ = v_isSharedCheck_105_;
goto v_resetjp_97_;
}
v_resetjp_97_:
{
lean_object* v___x_101_; 
if (v_isShared_99_ == 0)
{
v___x_101_ = v___x_98_;
goto v_reusejp_100_;
}
else
{
lean_object* v_reuseFailAlloc_104_; 
v_reuseFailAlloc_104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_104_, 0, v_fst_95_);
lean_ctor_set(v_reuseFailAlloc_104_, 1, v_snd_96_);
v___x_101_ = v_reuseFailAlloc_104_;
goto v_reusejp_100_;
}
v_reusejp_100_:
{
lean_object* v___x_102_; lean_object* v___x_103_; 
v___x_102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_102_, 0, v___x_101_);
v___x_103_ = lean_apply_2(v_toPure_93_, lean_box(0), v___x_102_);
return v___x_103_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__7(lean_object* v_toPure_106_, lean_object* v_next_107_, lean_object* v_G_108_, lean_object* v_____do__lift_109_){
_start:
{
if (lean_obj_tag(v_____do__lift_109_) == 0)
{
lean_object* v_a_110_; lean_object* v___x_111_; 
lean_dec(v_G_108_);
v_a_110_ = lean_ctor_get(v_____do__lift_109_, 0);
lean_inc(v_a_110_);
lean_dec_ref_known(v_____do__lift_109_, 1);
v___x_111_ = lean_apply_2(v_toPure_106_, lean_box(0), v_a_110_);
return v___x_111_;
}
else
{
lean_object* v_a_112_; lean_object* v___x_113_; lean_object* v___x_114_; lean_object* v___x_115_; 
lean_dec(v_toPure_106_);
v_a_112_ = lean_ctor_get(v_____do__lift_109_, 0);
lean_inc(v_a_112_);
lean_dec_ref_known(v_____do__lift_109_, 1);
v___x_113_ = lean_unsigned_to_nat(1u);
v___x_114_ = lean_nat_add(v_next_107_, v___x_113_);
v___x_115_ = lean_apply_4(v_G_108_, v___x_114_, v_a_112_, lean_box(0), lean_box(0));
return v___x_115_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__7___boxed(lean_object* v_toPure_116_, lean_object* v_next_117_, lean_object* v_G_118_, lean_object* v_____do__lift_119_){
_start:
{
lean_object* v_res_120_; 
v_res_120_ = l_Lean_Array_filterPairsM___redArg___lam__7(v_toPure_116_, v_next_117_, v_G_118_, v_____do__lift_119_);
lean_dec(v_next_117_);
return v_res_120_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__8(lean_object* v_toPure_121_, lean_object* v_next_122_, lean_object* v___x_123_, lean_object* v_G_124_, lean_object* v_____do__lift_125_){
_start:
{
if (lean_obj_tag(v_____do__lift_125_) == 0)
{
lean_object* v_a_126_; lean_object* v___x_127_; 
lean_dec(v_G_124_);
v_a_126_ = lean_ctor_get(v_____do__lift_125_, 0);
lean_inc(v_a_126_);
lean_dec_ref_known(v_____do__lift_125_, 1);
v___x_127_ = lean_apply_2(v_toPure_121_, lean_box(0), v_a_126_);
return v___x_127_;
}
else
{
lean_object* v_a_128_; lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v_toPure_121_);
v_a_128_ = lean_ctor_get(v_____do__lift_125_, 0);
lean_inc(v_a_128_);
lean_dec_ref_known(v_____do__lift_125_, 1);
v___x_129_ = lean_nat_add(v_next_122_, v___x_123_);
v___x_130_ = lean_apply_4(v_G_124_, v___x_129_, v_a_128_, lean_box(0), lean_box(0));
return v___x_130_;
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__8___boxed(lean_object* v_toPure_131_, lean_object* v_next_132_, lean_object* v___x_133_, lean_object* v_G_134_, lean_object* v_____do__lift_135_){
_start:
{
lean_object* v_res_136_; 
v_res_136_ = l_Lean_Array_filterPairsM___redArg___lam__8(v_toPure_131_, v_next_132_, v___x_133_, v_G_134_, v_____do__lift_135_);
lean_dec(v___x_133_);
lean_dec(v_next_132_);
return v_res_136_;
}
}
lean_object* l_Lean_Array_filterPairsM___redArg___lam__9(lean_object* v___x_137_, lean_object* v_next_138_, uint8_t v___x_139_, lean_object* v_toPure_140_, lean_object* v_snd_141_, lean_object* v_fst_142_, lean_object* v_next_143_, lean_object* v_____x_144_){
_start:
{
lean_object* v_fst_145_; lean_object* v_snd_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_171_; 
v_fst_145_ = lean_ctor_get(v_____x_144_, 0);
v_snd_146_ = lean_ctor_get(v_____x_144_, 1);
v_isSharedCheck_171_ = !lean_is_exclusive(v_____x_144_);
if (v_isSharedCheck_171_ == 0)
{
v___x_148_ = v_____x_144_;
v_isShared_149_ = v_isSharedCheck_171_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_snd_146_);
lean_inc(v_fst_145_);
lean_dec(v_____x_144_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_171_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v_removed_151_; lean_object* v_numRemoved_152_; uint8_t v___x_167_; 
v___x_167_ = lean_unbox(v_fst_145_);
lean_dec(v_fst_145_);
if (v___x_167_ == 0)
{
lean_object* v___x_168_; lean_object* v___x_169_; lean_object* v___x_170_; 
v___x_168_ = lean_nat_add(v_snd_141_, v___x_137_);
lean_dec(v_snd_141_);
v___x_169_ = lean_box(v___x_139_);
v___x_170_ = lean_array_set(v_fst_142_, v_next_143_, v___x_169_);
v_removed_151_ = v___x_170_;
v_numRemoved_152_ = v___x_168_;
goto v___jp_150_;
}
else
{
v_removed_151_ = v_fst_142_;
v_numRemoved_152_ = v_snd_141_;
goto v___jp_150_;
}
v___jp_150_:
{
uint8_t v___x_153_; 
v___x_153_ = lean_unbox(v_snd_146_);
lean_dec(v_snd_146_);
if (v___x_153_ == 0)
{
lean_object* v___x_154_; lean_object* v___x_155_; lean_object* v___x_156_; lean_object* v___x_158_; 
v___x_154_ = lean_nat_add(v_numRemoved_152_, v___x_137_);
lean_dec(v_numRemoved_152_);
v___x_155_ = lean_box(v___x_139_);
v___x_156_ = lean_array_set(v_removed_151_, v_next_138_, v___x_155_);
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v___x_154_);
lean_ctor_set(v___x_148_, 0, v___x_156_);
v___x_158_ = v___x_148_;
goto v_reusejp_157_;
}
else
{
lean_object* v_reuseFailAlloc_161_; 
v_reuseFailAlloc_161_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_161_, 0, v___x_156_);
lean_ctor_set(v_reuseFailAlloc_161_, 1, v___x_154_);
v___x_158_ = v_reuseFailAlloc_161_;
goto v_reusejp_157_;
}
v_reusejp_157_:
{
lean_object* v___x_159_; lean_object* v___x_160_; 
v___x_159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_159_, 0, v___x_158_);
v___x_160_ = lean_apply_2(v_toPure_140_, lean_box(0), v___x_159_);
return v___x_160_;
}
}
else
{
lean_object* v___x_163_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v_numRemoved_152_);
lean_ctor_set(v___x_148_, 0, v_removed_151_);
v___x_163_ = v___x_148_;
goto v_reusejp_162_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_removed_151_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_numRemoved_152_);
v___x_163_ = v_reuseFailAlloc_166_;
goto v_reusejp_162_;
}
v_reusejp_162_:
{
lean_object* v___x_164_; lean_object* v___x_165_; 
v___x_164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_164_, 0, v___x_163_);
v___x_165_ = lean_apply_2(v_toPure_140_, lean_box(0), v___x_164_);
return v___x_165_;
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Array_filterPairsM___redArg___lam__9_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_137_ = stack[0].m_obj;
lean_object* v_next_138_ = stack[1].m_obj;
uint8_t v___x_139_ = stack[2].m_num;
lean_object* v_toPure_140_ = stack[3].m_obj;
lean_object* v_snd_141_ = stack[4].m_obj;
lean_object* v_fst_142_ = stack[5].m_obj;
lean_object* v_next_143_ = stack[6].m_obj;
lean_object* v_____x_144_ = stack[7].m_obj;
lean_object* v_res_172_;
v_res_172_ = l_Lean_Array_filterPairsM___redArg___lam__9(v___x_137_, v_next_138_, v___x_139_, v_toPure_140_, v_snd_141_, v_fst_142_, v_next_143_, v_____x_144_);
stack->m_obj
 = v_res_172_;
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__9___boxed(lean_object* v___x_173_, lean_object* v_next_174_, lean_object* v___x_175_, lean_object* v_toPure_176_, lean_object* v_snd_177_, lean_object* v_fst_178_, lean_object* v_next_179_, lean_object* v_____x_180_){
_start:
{
uint8_t v___x_1054__boxed_181_; lean_object* v_res_182_; 
v___x_1054__boxed_181_ = lean_unbox(v___x_175_);
v_res_182_ = l_Lean_Array_filterPairsM___redArg___lam__9(v___x_173_, v_next_174_, v___x_1054__boxed_181_, v_toPure_176_, v_snd_177_, v_fst_178_, v_next_179_, v_____x_180_);
lean_dec(v_next_179_);
lean_dec(v_next_174_);
lean_dec(v___x_173_);
return v_res_182_;
}
}
lean_object* l_Lean_Array_filterPairsM___redArg___lam__10(lean_object* v___x_183_, lean_object* v_toPure_184_, lean_object* v___x_185_, lean_object* v_toBind_186_, lean_object* v___f_187_, lean_object* v_next_188_, lean_object* v_a_189_, lean_object* v_f_190_, uint8_t v___x_191_, lean_object* v_next_192_, lean_object* v_acc_193_, lean_object* v_h_194_, lean_object* v_G_195_){
_start:
{
uint8_t v___x_196_; 
v___x_196_ = lean_nat_dec_lt(v_next_192_, v___x_183_);
if (v___x_196_ == 0)
{
lean_object* v___x_197_; 
lean_dec(v_G_195_);
lean_dec(v_next_192_);
lean_dec(v_f_190_);
lean_dec(v_next_188_);
lean_dec(v___f_187_);
lean_dec(v_toBind_186_);
lean_dec(v___x_185_);
v___x_197_ = lean_apply_2(v_toPure_184_, lean_box(0), v_acc_193_);
return v___x_197_;
}
else
{
lean_object* v_fst_198_; lean_object* v_snd_199_; lean_object* v___x_201_; uint8_t v_isShared_202_; uint8_t v_isSharedCheck_228_; 
v_fst_198_ = lean_ctor_get(v_acc_193_, 0);
v_snd_199_ = lean_ctor_get(v_acc_193_, 1);
v_isSharedCheck_228_ = !lean_is_exclusive(v_acc_193_);
if (v_isSharedCheck_228_ == 0)
{
v___x_201_ = v_acc_193_;
v_isShared_202_ = v_isSharedCheck_228_;
goto v_resetjp_200_;
}
else
{
lean_inc(v_snd_199_);
lean_inc(v_fst_198_);
lean_dec(v_acc_193_);
v___x_201_ = lean_box(0);
v_isShared_202_ = v_isSharedCheck_228_;
goto v_resetjp_200_;
}
v_resetjp_200_:
{
lean_object* v___f_203_; lean_object* v___y_205_; lean_object* v___x_208_; lean_object* v___f_209_; uint8_t v___y_211_; lean_object* v___x_221_; lean_object* v___x_222_; uint8_t v___x_223_; 
lean_inc(v___x_185_);
lean_inc_n(v_next_192_, 2);
lean_inc_n(v_toPure_184_, 2);
v___f_203_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__8___boxed), 5, 4);
lean_closure_set(v___f_203_, 0, v_toPure_184_);
lean_closure_set(v___f_203_, 1, v_next_192_);
lean_closure_set(v___f_203_, 2, v___x_185_);
lean_closure_set(v___f_203_, 3, v_G_195_);
v___x_208_ = lean_box(v___x_196_);
lean_inc(v_next_188_);
lean_inc(v_fst_198_);
lean_inc(v_snd_199_);
v___f_209_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__9___boxed), 8, 7);
lean_closure_set(v___f_209_, 0, v___x_185_);
lean_closure_set(v___f_209_, 1, v_next_192_);
lean_closure_set(v___f_209_, 2, v___x_208_);
lean_closure_set(v___f_209_, 3, v_toPure_184_);
lean_closure_set(v___f_209_, 4, v_snd_199_);
lean_closure_set(v___f_209_, 5, v_fst_198_);
lean_closure_set(v___f_209_, 6, v_next_188_);
v___x_221_ = lean_box(v___x_191_);
v___x_222_ = lean_array_get(v___x_221_, v_fst_198_, v_next_188_);
lean_dec(v___x_221_);
v___x_223_ = lean_unbox(v___x_222_);
if (v___x_223_ == 0)
{
lean_object* v___x_224_; lean_object* v___x_225_; uint8_t v___x_226_; 
lean_dec(v___x_222_);
v___x_224_ = lean_box(v___x_191_);
v___x_225_ = lean_array_get(v___x_224_, v_fst_198_, v_next_192_);
lean_dec(v___x_224_);
v___x_226_ = lean_unbox(v___x_225_);
lean_dec(v___x_225_);
v___y_211_ = v___x_226_;
goto v___jp_210_;
}
else
{
uint8_t v___x_227_; 
v___x_227_ = lean_unbox(v___x_222_);
lean_dec(v___x_222_);
v___y_211_ = v___x_227_;
goto v___jp_210_;
}
v___jp_204_:
{
lean_object* v___x_206_; lean_object* v___x_207_; 
lean_inc(v_toBind_186_);
v___x_206_ = lean_apply_4(v_toBind_186_, lean_box(0), lean_box(0), v___y_205_, v___f_187_);
v___x_207_ = lean_apply_4(v_toBind_186_, lean_box(0), lean_box(0), v___x_206_, v___f_203_);
return v___x_207_;
}
v___jp_210_:
{
if (v___y_211_ == 0)
{
lean_object* v___x_212_; lean_object* v___x_213_; lean_object* v___x_214_; lean_object* v___x_215_; 
lean_del_object(v___x_201_);
lean_dec(v_snd_199_);
lean_dec(v_fst_198_);
lean_dec(v_toPure_184_);
v___x_212_ = lean_array_fget_borrowed(v_a_189_, v_next_188_);
lean_dec(v_next_188_);
v___x_213_ = lean_array_fget_borrowed(v_a_189_, v_next_192_);
lean_dec(v_next_192_);
lean_inc(v___x_213_);
lean_inc(v___x_212_);
v___x_214_ = lean_apply_2(v_f_190_, v___x_212_, v___x_213_);
lean_inc(v_toBind_186_);
v___x_215_ = lean_apply_4(v_toBind_186_, lean_box(0), lean_box(0), v___x_214_, v___f_209_);
v___y_205_ = v___x_215_;
goto v___jp_204_;
}
else
{
lean_object* v___x_217_; 
lean_dec_ref(v___f_209_);
lean_dec(v_next_192_);
lean_dec(v_f_190_);
lean_dec(v_next_188_);
if (v_isShared_202_ == 0)
{
v___x_217_ = v___x_201_;
goto v_reusejp_216_;
}
else
{
lean_object* v_reuseFailAlloc_220_; 
v_reuseFailAlloc_220_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_220_, 0, v_fst_198_);
lean_ctor_set(v_reuseFailAlloc_220_, 1, v_snd_199_);
v___x_217_ = v_reuseFailAlloc_220_;
goto v_reusejp_216_;
}
v_reusejp_216_:
{
lean_object* v___x_218_; lean_object* v___x_219_; 
v___x_218_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_218_, 0, v___x_217_);
v___x_219_ = lean_apply_2(v_toPure_184_, lean_box(0), v___x_218_);
v___y_205_ = v___x_219_;
goto v___jp_204_;
}
}
}
}
}
}
}
LEAN_EXPORT void l_Lean_Array_filterPairsM___redArg___lam__10_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_183_ = stack[0].m_obj;
lean_object* v_toPure_184_ = stack[1].m_obj;
lean_object* v___x_185_ = stack[2].m_obj;
lean_object* v_toBind_186_ = stack[3].m_obj;
lean_object* v___f_187_ = stack[4].m_obj;
lean_object* v_next_188_ = stack[5].m_obj;
lean_object* v_a_189_ = stack[6].m_obj;
lean_object* v_f_190_ = stack[7].m_obj;
uint8_t v___x_191_ = stack[8].m_num;
lean_object* v_next_192_ = stack[9].m_obj;
lean_object* v_acc_193_ = stack[10].m_obj;
lean_object* v_G_195_ = stack[12].m_obj;
lean_object* v_res_229_;
v_res_229_ = l_Lean_Array_filterPairsM___redArg___lam__10(v___x_183_, v_toPure_184_, v___x_185_, v_toBind_186_, v___f_187_, v_next_188_, v_a_189_, v_f_190_, v___x_191_, v_next_192_, v_acc_193_, lean_box(0), v_G_195_);
stack->m_obj
 = v_res_229_;
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__10___boxed(lean_object* v___x_230_, lean_object* v_toPure_231_, lean_object* v___x_232_, lean_object* v_toBind_233_, lean_object* v___f_234_, lean_object* v_next_235_, lean_object* v_a_236_, lean_object* v_f_237_, lean_object* v___x_238_, lean_object* v_next_239_, lean_object* v_acc_240_, lean_object* v_h_241_, lean_object* v_G_242_){
_start:
{
uint8_t v___x_1146__boxed_243_; lean_object* v_res_244_; 
v___x_1146__boxed_243_ = lean_unbox(v___x_238_);
v_res_244_ = l_Lean_Array_filterPairsM___redArg___lam__10(v___x_230_, v_toPure_231_, v___x_232_, v_toBind_233_, v___f_234_, v_next_235_, v_a_236_, v_f_237_, v___x_1146__boxed_243_, v_next_239_, v_acc_240_, v_h_241_, v_G_242_);
lean_dec_ref(v_a_236_);
lean_dec(v___x_230_);
return v_res_244_;
}
}
lean_object* l_Lean_Array_filterPairsM___redArg___lam__11(lean_object* v___x_245_, lean_object* v_toPure_246_, lean_object* v_toBind_247_, lean_object* v___f_248_, lean_object* v_a_249_, lean_object* v_f_250_, uint8_t v___x_251_, lean_object* v___f_252_, lean_object* v___f_253_, lean_object* v_next_254_, lean_object* v_acc_255_, lean_object* v_h_256_, lean_object* v_G_257_){
_start:
{
uint8_t v___x_258_; 
v___x_258_ = lean_nat_dec_lt(v_next_254_, v___x_245_);
if (v___x_258_ == 0)
{
lean_object* v___x_259_; 
lean_dec(v_G_257_);
lean_dec(v_next_254_);
lean_dec(v___f_253_);
lean_dec(v___f_252_);
lean_dec(v_f_250_);
lean_dec_ref(v_a_249_);
lean_dec(v___f_248_);
lean_dec(v_toBind_247_);
lean_dec(v___x_245_);
v___x_259_ = lean_apply_2(v_toPure_246_, lean_box(0), v_acc_255_);
return v___x_259_;
}
else
{
lean_object* v_fst_260_; lean_object* v_snd_261_; lean_object* v___x_263_; uint8_t v_isShared_264_; uint8_t v_isSharedCheck_277_; 
v_fst_260_ = lean_ctor_get(v_acc_255_, 0);
v_snd_261_ = lean_ctor_get(v_acc_255_, 1);
v_isSharedCheck_277_ = !lean_is_exclusive(v_acc_255_);
if (v_isSharedCheck_277_ == 0)
{
v___x_263_ = v_acc_255_;
v_isShared_264_ = v_isSharedCheck_277_;
goto v_resetjp_262_;
}
else
{
lean_inc(v_snd_261_);
lean_inc(v_fst_260_);
lean_dec(v_acc_255_);
v___x_263_ = lean_box(0);
v_isShared_264_ = v_isSharedCheck_277_;
goto v_resetjp_262_;
}
v_resetjp_262_:
{
lean_object* v___f_265_; lean_object* v___x_266_; lean_object* v___x_267_; lean_object* v___f_268_; lean_object* v___x_269_; lean_object* v___x_271_; 
lean_inc_n(v_next_254_, 2);
lean_inc(v_toPure_246_);
v___f_265_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__7___boxed), 4, 3);
lean_closure_set(v___f_265_, 0, v_toPure_246_);
lean_closure_set(v___f_265_, 1, v_next_254_);
lean_closure_set(v___f_265_, 2, v_G_257_);
v___x_266_ = lean_unsigned_to_nat(1u);
v___x_267_ = lean_box(v___x_251_);
lean_inc(v_toBind_247_);
v___f_268_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__10___boxed), 13, 9);
lean_closure_set(v___f_268_, 0, v___x_245_);
lean_closure_set(v___f_268_, 1, v_toPure_246_);
lean_closure_set(v___f_268_, 2, v___x_266_);
lean_closure_set(v___f_268_, 3, v_toBind_247_);
lean_closure_set(v___f_268_, 4, v___f_248_);
lean_closure_set(v___f_268_, 5, v_next_254_);
lean_closure_set(v___f_268_, 6, v_a_249_);
lean_closure_set(v___f_268_, 7, v_f_250_);
lean_closure_set(v___f_268_, 8, v___x_267_);
v___x_269_ = lean_nat_add(v_next_254_, v___x_266_);
lean_dec(v_next_254_);
if (v_isShared_264_ == 0)
{
v___x_271_ = v___x_263_;
goto v_reusejp_270_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_fst_260_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_snd_261_);
v___x_271_ = v_reuseFailAlloc_276_;
goto v_reusejp_270_;
}
v_reusejp_270_:
{
lean_object* v___x_272_; lean_object* v___x_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v___x_272_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_268_, v___x_269_, v___x_271_, lean_box(0));
lean_inc_n(v_toBind_247_, 2);
v___x_273_ = lean_apply_4(v_toBind_247_, lean_box(0), lean_box(0), v___x_272_, v___f_252_);
v___x_274_ = lean_apply_4(v_toBind_247_, lean_box(0), lean_box(0), v___x_273_, v___f_253_);
v___x_275_ = lean_apply_4(v_toBind_247_, lean_box(0), lean_box(0), v___x_274_, v___f_265_);
return v___x_275_;
}
}
}
}
}
LEAN_EXPORT void l_Lean_Array_filterPairsM___redArg___lam__11_0interp(lean_interpreter_value* stack)
{
lean_object* v___x_245_ = stack[0].m_obj;
lean_object* v_toPure_246_ = stack[1].m_obj;
lean_object* v_toBind_247_ = stack[2].m_obj;
lean_object* v___f_248_ = stack[3].m_obj;
lean_object* v_a_249_ = stack[4].m_obj;
lean_object* v_f_250_ = stack[5].m_obj;
uint8_t v___x_251_ = stack[6].m_num;
lean_object* v___f_252_ = stack[7].m_obj;
lean_object* v___f_253_ = stack[8].m_obj;
lean_object* v_next_254_ = stack[9].m_obj;
lean_object* v_acc_255_ = stack[10].m_obj;
lean_object* v_G_257_ = stack[12].m_obj;
lean_object* v_res_278_;
v_res_278_ = l_Lean_Array_filterPairsM___redArg___lam__11(v___x_245_, v_toPure_246_, v_toBind_247_, v___f_248_, v_a_249_, v_f_250_, v___x_251_, v___f_252_, v___f_253_, v_next_254_, v_acc_255_, lean_box(0), v_G_257_);
stack->m_obj
 = v_res_278_;
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg___lam__11___boxed(lean_object* v___x_279_, lean_object* v_toPure_280_, lean_object* v_toBind_281_, lean_object* v___f_282_, lean_object* v_a_283_, lean_object* v_f_284_, lean_object* v___x_285_, lean_object* v___f_286_, lean_object* v___f_287_, lean_object* v_next_288_, lean_object* v_acc_289_, lean_object* v_h_290_, lean_object* v_G_291_){
_start:
{
uint8_t v___x_1258__boxed_292_; lean_object* v_res_293_; 
v___x_1258__boxed_292_ = lean_unbox(v___x_285_);
v_res_293_ = l_Lean_Array_filterPairsM___redArg___lam__11(v___x_279_, v_toPure_280_, v_toBind_281_, v___f_282_, v_a_283_, v_f_284_, v___x_1258__boxed_292_, v___f_286_, v___f_287_, v_next_288_, v_acc_289_, v_h_290_, v_G_291_);
return v_res_293_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM___redArg(lean_object* v_inst_294_, lean_object* v_a_295_, lean_object* v_f_296_){
_start:
{
lean_object* v_toApplicative_297_; lean_object* v_toBind_298_; lean_object* v___x_300_; uint8_t v_isShared_301_; uint8_t v_isSharedCheck_321_; 
v_toApplicative_297_ = lean_ctor_get(v_inst_294_, 0);
v_toBind_298_ = lean_ctor_get(v_inst_294_, 1);
v_isSharedCheck_321_ = !lean_is_exclusive(v_inst_294_);
if (v_isSharedCheck_321_ == 0)
{
v___x_300_ = v_inst_294_;
v_isShared_301_ = v_isSharedCheck_321_;
goto v_resetjp_299_;
}
else
{
lean_inc(v_toBind_298_);
lean_inc(v_toApplicative_297_);
lean_dec(v_inst_294_);
v___x_300_ = lean_box(0);
v_isShared_301_ = v_isSharedCheck_321_;
goto v_resetjp_299_;
}
v_resetjp_299_:
{
lean_object* v_toPure_302_; uint8_t v___x_303_; lean_object* v___x_304_; lean_object* v___x_305_; lean_object* v_removed_306_; lean_object* v___f_307_; lean_object* v___f_308_; lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___f_311_; lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v___f_314_; lean_object* v___x_315_; lean_object* v___x_317_; 
v_toPure_302_ = lean_ctor_get(v_toApplicative_297_, 1);
lean_inc_n(v_toPure_302_, 6);
lean_dec_ref(v_toApplicative_297_);
v___x_303_ = 0;
v___x_304_ = lean_array_get_size(v_a_295_);
v___x_305_ = lean_box(v___x_303_);
v_removed_306_ = lean_mk_array(v___x_304_, v___x_305_);
v___f_307_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__0), 2, 1);
lean_closure_set(v___f_307_, 0, v_toPure_302_);
v___f_308_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__2), 2, 1);
lean_closure_set(v___f_308_, 0, v_toPure_302_);
v___f_309_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__1), 2, 1);
lean_closure_set(v___f_309_, 0, v_toPure_302_);
v___x_310_ = lean_box(v___x_303_);
lean_inc_ref(v_a_295_);
lean_inc_n(v_toBind_298_, 2);
v___f_311_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__5___boxed), 8, 7);
lean_closure_set(v___f_311_, 0, v___x_304_);
lean_closure_set(v___f_311_, 1, v_toPure_302_);
lean_closure_set(v___f_311_, 2, v_toBind_298_);
lean_closure_set(v___f_311_, 3, v___f_308_);
lean_closure_set(v___f_311_, 4, v___x_310_);
lean_closure_set(v___f_311_, 5, v_a_295_);
lean_closure_set(v___f_311_, 6, v___f_309_);
v___f_312_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__6), 2, 1);
lean_closure_set(v___f_312_, 0, v_toPure_302_);
v___x_313_ = lean_box(v___x_303_);
lean_inc_ref(v___f_307_);
v___f_314_ = lean_alloc_closure((void*)(l_Lean_Array_filterPairsM___redArg___lam__11___boxed), 13, 9);
lean_closure_set(v___f_314_, 0, v___x_304_);
lean_closure_set(v___f_314_, 1, v_toPure_302_);
lean_closure_set(v___f_314_, 2, v_toBind_298_);
lean_closure_set(v___f_314_, 3, v___f_307_);
lean_closure_set(v___f_314_, 4, v_a_295_);
lean_closure_set(v___f_314_, 5, v_f_296_);
lean_closure_set(v___f_314_, 6, v___x_313_);
lean_closure_set(v___f_314_, 7, v___f_312_);
lean_closure_set(v___f_314_, 8, v___f_307_);
v___x_315_ = lean_unsigned_to_nat(0u);
if (v_isShared_301_ == 0)
{
lean_ctor_set(v___x_300_, 1, v___x_315_);
lean_ctor_set(v___x_300_, 0, v_removed_306_);
v___x_317_ = v___x_300_;
goto v_reusejp_316_;
}
else
{
lean_object* v_reuseFailAlloc_320_; 
v_reuseFailAlloc_320_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_320_, 0, v_removed_306_);
lean_ctor_set(v_reuseFailAlloc_320_, 1, v___x_315_);
v___x_317_ = v_reuseFailAlloc_320_;
goto v_reusejp_316_;
}
v_reusejp_316_:
{
lean_object* v___x_318_; lean_object* v___x_319_; 
v___x_318_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_314_, v___x_315_, v___x_317_, lean_box(0));
v___x_319_ = lean_apply_4(v_toBind_298_, lean_box(0), lean_box(0), v___x_318_, v___f_311_);
return v___x_319_;
}
}
}
}
LEAN_EXPORT lean_object* l_Lean_Array_filterPairsM(lean_object* v_m_322_, lean_object* v_inst_323_, lean_object* v_00_u03b1_324_, lean_object* v_a_325_, lean_object* v_f_326_){
_start:
{
lean_object* v___x_327_; 
v___x_327_ = l_Lean_Array_filterPairsM___redArg(v_inst_323_, v_a_325_, v_f_326_);
return v___x_327_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg(lean_object* v_as_328_, size_t v_sz_329_, size_t v_i_330_, lean_object* v_b_331_){
_start:
{
lean_object* v_a_333_; uint8_t v___x_337_; 
v___x_337_ = lean_usize_dec_lt(v_i_330_, v_sz_329_);
if (v___x_337_ == 0)
{
return v_b_331_;
}
else
{
lean_object* v_snd_338_; lean_object* v_fst_339_; lean_object* v___x_341_; uint8_t v_isShared_342_; uint8_t v_isSharedCheck_372_; 
v_snd_338_ = lean_ctor_get(v_b_331_, 1);
v_fst_339_ = lean_ctor_get(v_b_331_, 0);
v_isSharedCheck_372_ = !lean_is_exclusive(v_b_331_);
if (v_isSharedCheck_372_ == 0)
{
v___x_341_ = v_b_331_;
v_isShared_342_ = v_isSharedCheck_372_;
goto v_resetjp_340_;
}
else
{
lean_inc(v_snd_338_);
lean_inc(v_fst_339_);
lean_dec(v_b_331_);
v___x_341_ = lean_box(0);
v_isShared_342_ = v_isSharedCheck_372_;
goto v_resetjp_340_;
}
v_resetjp_340_:
{
lean_object* v_array_343_; lean_object* v_start_344_; lean_object* v_stop_345_; uint8_t v___x_346_; 
v_array_343_ = lean_ctor_get(v_snd_338_, 0);
v_start_344_ = lean_ctor_get(v_snd_338_, 1);
v_stop_345_ = lean_ctor_get(v_snd_338_, 2);
v___x_346_ = lean_nat_dec_lt(v_start_344_, v_stop_345_);
if (v___x_346_ == 0)
{
lean_object* v___x_348_; 
if (v_isShared_342_ == 0)
{
v___x_348_ = v___x_341_;
goto v_reusejp_347_;
}
else
{
lean_object* v_reuseFailAlloc_349_; 
v_reuseFailAlloc_349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_349_, 0, v_fst_339_);
lean_ctor_set(v_reuseFailAlloc_349_, 1, v_snd_338_);
v___x_348_ = v_reuseFailAlloc_349_;
goto v_reusejp_347_;
}
v_reusejp_347_:
{
return v___x_348_;
}
}
else
{
lean_object* v___x_351_; uint8_t v_isShared_352_; uint8_t v_isSharedCheck_368_; 
lean_inc(v_stop_345_);
lean_inc(v_start_344_);
lean_inc_ref(v_array_343_);
v_isSharedCheck_368_ = !lean_is_exclusive(v_snd_338_);
if (v_isSharedCheck_368_ == 0)
{
lean_object* v_unused_369_; lean_object* v_unused_370_; lean_object* v_unused_371_; 
v_unused_369_ = lean_ctor_get(v_snd_338_, 2);
lean_dec(v_unused_369_);
v_unused_370_ = lean_ctor_get(v_snd_338_, 1);
lean_dec(v_unused_370_);
v_unused_371_ = lean_ctor_get(v_snd_338_, 0);
lean_dec(v_unused_371_);
v___x_351_ = v_snd_338_;
v_isShared_352_ = v_isSharedCheck_368_;
goto v_resetjp_350_;
}
else
{
lean_dec(v_snd_338_);
v___x_351_ = lean_box(0);
v_isShared_352_ = v_isSharedCheck_368_;
goto v_resetjp_350_;
}
v_resetjp_350_:
{
lean_object* v_a_353_; lean_object* v___x_354_; lean_object* v___x_355_; lean_object* v___x_356_; lean_object* v___x_358_; 
v_a_353_ = lean_array_uget_borrowed(v_as_328_, v_i_330_);
v___x_354_ = lean_array_fget(v_array_343_, v_start_344_);
v___x_355_ = lean_unsigned_to_nat(1u);
v___x_356_ = lean_nat_add(v_start_344_, v___x_355_);
lean_dec(v_start_344_);
if (v_isShared_352_ == 0)
{
lean_ctor_set(v___x_351_, 1, v___x_356_);
v___x_358_ = v___x_351_;
goto v_reusejp_357_;
}
else
{
lean_object* v_reuseFailAlloc_367_; 
v_reuseFailAlloc_367_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_367_, 0, v_array_343_);
lean_ctor_set(v_reuseFailAlloc_367_, 1, v___x_356_);
lean_ctor_set(v_reuseFailAlloc_367_, 2, v_stop_345_);
v___x_358_ = v_reuseFailAlloc_367_;
goto v_reusejp_357_;
}
v_reusejp_357_:
{
uint8_t v___x_359_; 
v___x_359_ = lean_unbox(v_a_353_);
if (v___x_359_ == 0)
{
lean_object* v___x_361_; 
lean_dec(v___x_354_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v___x_358_);
v___x_361_ = v___x_341_;
goto v_reusejp_360_;
}
else
{
lean_object* v_reuseFailAlloc_362_; 
v_reuseFailAlloc_362_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_362_, 0, v_fst_339_);
lean_ctor_set(v_reuseFailAlloc_362_, 1, v___x_358_);
v___x_361_ = v_reuseFailAlloc_362_;
goto v_reusejp_360_;
}
v_reusejp_360_:
{
v_a_333_ = v___x_361_;
goto v___jp_332_;
}
}
else
{
lean_object* v___x_363_; lean_object* v___x_365_; 
v___x_363_ = lean_array_push(v_fst_339_, v___x_354_);
if (v_isShared_342_ == 0)
{
lean_ctor_set(v___x_341_, 1, v___x_358_);
lean_ctor_set(v___x_341_, 0, v___x_363_);
v___x_365_ = v___x_341_;
goto v_reusejp_364_;
}
else
{
lean_object* v_reuseFailAlloc_366_; 
v_reuseFailAlloc_366_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_366_, 0, v___x_363_);
lean_ctor_set(v_reuseFailAlloc_366_, 1, v___x_358_);
v___x_365_ = v_reuseFailAlloc_366_;
goto v_reusejp_364_;
}
v_reusejp_364_:
{
v_a_333_ = v___x_365_;
goto v___jp_332_;
}
}
}
}
}
}
}
v___jp_332_:
{
size_t v___x_334_; size_t v___x_335_; 
v___x_334_ = ((size_t)1ULL);
v___x_335_ = lean_usize_add(v_i_330_, v___x_334_);
v_i_330_ = v___x_335_;
v_b_331_ = v_a_333_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_328_ = stack[0].m_obj;
size_t v_sz_329_ = stack[1].m_num;
size_t v_i_330_ = stack[2].m_num;
lean_object* v_b_331_ = stack[3].m_obj;
lean_object* v_res_373_;
v_res_373_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg(v_as_328_, v_sz_329_, v_i_330_, v_b_331_);
stack->m_obj
 = v_res_373_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg___boxed(lean_object* v_as_374_, lean_object* v_sz_375_, lean_object* v_i_376_, lean_object* v_b_377_){
_start:
{
size_t v_sz_boxed_378_; size_t v_i_boxed_379_; lean_object* v_res_380_; 
v_sz_boxed_378_ = lean_unbox_usize(v_sz_375_);
lean_dec(v_sz_375_);
v_i_boxed_379_ = lean_unbox_usize(v_i_376_);
lean_dec(v_i_376_);
v_res_380_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg(v_as_374_, v_sz_boxed_378_, v_i_boxed_379_, v_b_377_);
lean_dec_ref(v_as_374_);
return v_res_380_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_mask___redArg(lean_object* v_mask_383_, lean_object* v_xs_384_){
_start:
{
lean_object* v___x_385_; lean_object* v_ys_386_; lean_object* v___x_387_; lean_object* v___x_388_; lean_object* v___x_389_; size_t v_sz_390_; size_t v___x_391_; lean_object* v___x_392_; lean_object* v_fst_393_; 
v___x_385_ = lean_unsigned_to_nat(0u);
v_ys_386_ = ((lean_object*)(l_Lean_Array_mask___redArg___closed__0));
v___x_387_ = lean_array_get_size(v_xs_384_);
v___x_388_ = l_Array_toSubarray___redArg(v_xs_384_, v___x_385_, v___x_387_);
v___x_389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_389_, 0, v_ys_386_);
lean_ctor_set(v___x_389_, 1, v___x_388_);
v_sz_390_ = lean_array_size(v_mask_383_);
v___x_391_ = ((size_t)0ULL);
v___x_392_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg(v_mask_383_, v_sz_390_, v___x_391_, v___x_389_);
v_fst_393_ = lean_ctor_get(v___x_392_, 0);
lean_inc(v_fst_393_);
lean_dec_ref(v___x_392_);
return v_fst_393_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_mask___redArg___boxed(lean_object* v_mask_394_, lean_object* v_xs_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l_Lean_Array_mask___redArg(v_mask_394_, v_xs_395_);
lean_dec_ref(v_mask_394_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_mask(lean_object* v_00_u03b1_397_, lean_object* v_mask_398_, lean_object* v_xs_399_){
_start:
{
lean_object* v___x_400_; 
v___x_400_ = l_Lean_Array_mask___redArg(v_mask_398_, v_xs_399_);
return v___x_400_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_mask___boxed(lean_object* v_00_u03b1_401_, lean_object* v_mask_402_, lean_object* v_xs_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l_Lean_Array_mask(v_00_u03b1_401_, v_mask_402_, v_xs_403_);
lean_dec_ref(v_mask_402_);
return v_res_404_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0(lean_object* v_00_u03b1_405_, lean_object* v_as_406_, size_t v_sz_407_, size_t v_i_408_, lean_object* v_b_409_){
_start:
{
lean_object* v___x_410_; 
v___x_410_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___redArg(v_as_406_, v_sz_407_, v_i_408_, v_b_409_);
return v___x_410_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_as_406_ = stack[1].m_obj;
size_t v_sz_407_ = stack[2].m_num;
size_t v_i_408_ = stack[3].m_num;
lean_object* v_b_409_ = stack[4].m_obj;
lean_object* v_res_411_;
v_res_411_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0(lean_box(0), v_as_406_, v_sz_407_, v_i_408_, v_b_409_);
stack->m_obj
 = v_res_411_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0___boxed(lean_object* v_00_u03b1_412_, lean_object* v_as_413_, lean_object* v_sz_414_, lean_object* v_i_415_, lean_object* v_b_416_){
_start:
{
size_t v_sz_boxed_417_; size_t v_i_boxed_418_; lean_object* v_res_419_; 
v_sz_boxed_417_ = lean_unbox_usize(v_sz_414_);
lean_dec(v_sz_414_);
v_i_boxed_418_ = lean_unbox_usize(v_i_415_);
lean_dec(v_i_415_);
v_res_419_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_mask_spec__0(v_00_u03b1_412_, v_as_413_, v_sz_boxed_417_, v_i_boxed_418_, v_b_416_);
lean_dec_ref(v_as_413_);
return v_res_419_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg(lean_object* v_xs_420_, lean_object* v_ys_421_, lean_object* v_as_422_, size_t v_sz_423_, size_t v_i_424_, lean_object* v_b_425_){
_start:
{
lean_object* v_a_427_; uint8_t v___x_431_; 
v___x_431_ = lean_usize_dec_lt(v_i_424_, v_sz_423_);
if (v___x_431_ == 0)
{
return v_b_425_;
}
else
{
lean_object* v_snd_432_; lean_object* v_fst_433_; lean_object* v___x_435_; uint8_t v_isShared_436_; uint8_t v_isSharedCheck_481_; 
v_snd_432_ = lean_ctor_get(v_b_425_, 1);
v_fst_433_ = lean_ctor_get(v_b_425_, 0);
v_isSharedCheck_481_ = !lean_is_exclusive(v_b_425_);
if (v_isSharedCheck_481_ == 0)
{
v___x_435_ = v_b_425_;
v_isShared_436_ = v_isSharedCheck_481_;
goto v_resetjp_434_;
}
else
{
lean_inc(v_snd_432_);
lean_inc(v_fst_433_);
lean_dec(v_b_425_);
v___x_435_ = lean_box(0);
v_isShared_436_ = v_isSharedCheck_481_;
goto v_resetjp_434_;
}
v_resetjp_434_:
{
lean_object* v_fst_437_; lean_object* v_snd_438_; lean_object* v___x_440_; uint8_t v_isShared_441_; uint8_t v_isSharedCheck_480_; 
v_fst_437_ = lean_ctor_get(v_snd_432_, 0);
v_snd_438_ = lean_ctor_get(v_snd_432_, 1);
v_isSharedCheck_480_ = !lean_is_exclusive(v_snd_432_);
if (v_isSharedCheck_480_ == 0)
{
v___x_440_ = v_snd_432_;
v_isShared_441_ = v_isSharedCheck_480_;
goto v_resetjp_439_;
}
else
{
lean_inc(v_snd_438_);
lean_inc(v_fst_437_);
lean_dec(v_snd_432_);
v___x_440_ = lean_box(0);
v_isShared_441_ = v_isSharedCheck_480_;
goto v_resetjp_439_;
}
v_resetjp_439_:
{
lean_object* v_a_442_; uint8_t v___x_443_; 
v_a_442_ = lean_array_uget_borrowed(v_as_422_, v_i_424_);
v___x_443_ = lean_unbox(v_a_442_);
if (v___x_443_ == 0)
{
lean_object* v___x_444_; uint8_t v___x_445_; 
v___x_444_ = lean_array_get_size(v_xs_420_);
v___x_445_ = lean_nat_dec_lt(v_fst_433_, v___x_444_);
if (v___x_445_ == 0)
{
lean_object* v___x_447_; 
if (v_isShared_441_ == 0)
{
v___x_447_ = v___x_440_;
goto v_reusejp_446_;
}
else
{
lean_object* v_reuseFailAlloc_451_; 
v_reuseFailAlloc_451_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_451_, 0, v_fst_437_);
lean_ctor_set(v_reuseFailAlloc_451_, 1, v_snd_438_);
v___x_447_ = v_reuseFailAlloc_451_;
goto v_reusejp_446_;
}
v_reusejp_446_:
{
lean_object* v___x_449_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_447_);
v___x_449_ = v___x_435_;
goto v_reusejp_448_;
}
else
{
lean_object* v_reuseFailAlloc_450_; 
v_reuseFailAlloc_450_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_450_, 0, v_fst_433_);
lean_ctor_set(v_reuseFailAlloc_450_, 1, v___x_447_);
v___x_449_ = v_reuseFailAlloc_450_;
goto v_reusejp_448_;
}
v_reusejp_448_:
{
v_a_427_ = v___x_449_;
goto v___jp_426_;
}
}
}
else
{
lean_object* v___x_452_; lean_object* v___x_453_; lean_object* v___x_454_; lean_object* v___x_455_; lean_object* v___x_457_; 
v___x_452_ = lean_array_fget_borrowed(v_xs_420_, v_fst_433_);
lean_inc(v___x_452_);
v___x_453_ = lean_array_push(v_snd_438_, v___x_452_);
v___x_454_ = lean_unsigned_to_nat(1u);
v___x_455_ = lean_nat_add(v_fst_433_, v___x_454_);
lean_dec(v_fst_433_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_453_);
v___x_457_ = v___x_440_;
goto v_reusejp_456_;
}
else
{
lean_object* v_reuseFailAlloc_461_; 
v_reuseFailAlloc_461_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_461_, 0, v_fst_437_);
lean_ctor_set(v_reuseFailAlloc_461_, 1, v___x_453_);
v___x_457_ = v_reuseFailAlloc_461_;
goto v_reusejp_456_;
}
v_reusejp_456_:
{
lean_object* v___x_459_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_457_);
lean_ctor_set(v___x_435_, 0, v___x_455_);
v___x_459_ = v___x_435_;
goto v_reusejp_458_;
}
else
{
lean_object* v_reuseFailAlloc_460_; 
v_reuseFailAlloc_460_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_460_, 0, v___x_455_);
lean_ctor_set(v_reuseFailAlloc_460_, 1, v___x_457_);
v___x_459_ = v_reuseFailAlloc_460_;
goto v_reusejp_458_;
}
v_reusejp_458_:
{
v_a_427_ = v___x_459_;
goto v___jp_426_;
}
}
}
}
else
{
lean_object* v___x_462_; uint8_t v___x_463_; 
v___x_462_ = lean_array_get_size(v_ys_421_);
v___x_463_ = lean_nat_dec_lt(v_fst_437_, v___x_462_);
if (v___x_463_ == 0)
{
lean_object* v___x_465_; 
if (v_isShared_441_ == 0)
{
v___x_465_ = v___x_440_;
goto v_reusejp_464_;
}
else
{
lean_object* v_reuseFailAlloc_469_; 
v_reuseFailAlloc_469_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_469_, 0, v_fst_437_);
lean_ctor_set(v_reuseFailAlloc_469_, 1, v_snd_438_);
v___x_465_ = v_reuseFailAlloc_469_;
goto v_reusejp_464_;
}
v_reusejp_464_:
{
lean_object* v___x_467_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_465_);
v___x_467_ = v___x_435_;
goto v_reusejp_466_;
}
else
{
lean_object* v_reuseFailAlloc_468_; 
v_reuseFailAlloc_468_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_468_, 0, v_fst_433_);
lean_ctor_set(v_reuseFailAlloc_468_, 1, v___x_465_);
v___x_467_ = v_reuseFailAlloc_468_;
goto v_reusejp_466_;
}
v_reusejp_466_:
{
v_a_427_ = v___x_467_;
goto v___jp_426_;
}
}
}
else
{
lean_object* v___x_470_; lean_object* v___x_471_; lean_object* v___x_472_; lean_object* v___x_473_; lean_object* v___x_475_; 
v___x_470_ = lean_array_fget_borrowed(v_ys_421_, v_fst_437_);
lean_inc(v___x_470_);
v___x_471_ = lean_array_push(v_snd_438_, v___x_470_);
v___x_472_ = lean_unsigned_to_nat(1u);
v___x_473_ = lean_nat_add(v_fst_437_, v___x_472_);
lean_dec(v_fst_437_);
if (v_isShared_441_ == 0)
{
lean_ctor_set(v___x_440_, 1, v___x_471_);
lean_ctor_set(v___x_440_, 0, v___x_473_);
v___x_475_ = v___x_440_;
goto v_reusejp_474_;
}
else
{
lean_object* v_reuseFailAlloc_479_; 
v_reuseFailAlloc_479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_479_, 0, v___x_473_);
lean_ctor_set(v_reuseFailAlloc_479_, 1, v___x_471_);
v___x_475_ = v_reuseFailAlloc_479_;
goto v_reusejp_474_;
}
v_reusejp_474_:
{
lean_object* v___x_477_; 
if (v_isShared_436_ == 0)
{
lean_ctor_set(v___x_435_, 1, v___x_475_);
v___x_477_ = v___x_435_;
goto v_reusejp_476_;
}
else
{
lean_object* v_reuseFailAlloc_478_; 
v_reuseFailAlloc_478_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_478_, 0, v_fst_433_);
lean_ctor_set(v_reuseFailAlloc_478_, 1, v___x_475_);
v___x_477_ = v_reuseFailAlloc_478_;
goto v_reusejp_476_;
}
v_reusejp_476_:
{
v_a_427_ = v___x_477_;
goto v___jp_426_;
}
}
}
}
}
}
}
v___jp_426_:
{
size_t v___x_428_; size_t v___x_429_; 
v___x_428_ = ((size_t)1ULL);
v___x_429_ = lean_usize_add(v_i_424_, v___x_428_);
v_i_424_ = v___x_429_;
v_b_425_ = v_a_427_;
goto _start;
}
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_420_ = stack[0].m_obj;
lean_object* v_ys_421_ = stack[1].m_obj;
lean_object* v_as_422_ = stack[2].m_obj;
size_t v_sz_423_ = stack[3].m_num;
size_t v_i_424_ = stack[4].m_num;
lean_object* v_b_425_ = stack[5].m_obj;
lean_object* v_res_482_;
v_res_482_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg(v_xs_420_, v_ys_421_, v_as_422_, v_sz_423_, v_i_424_, v_b_425_);
stack->m_obj
 = v_res_482_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg___boxed(lean_object* v_xs_483_, lean_object* v_ys_484_, lean_object* v_as_485_, lean_object* v_sz_486_, lean_object* v_i_487_, lean_object* v_b_488_){
_start:
{
size_t v_sz_boxed_489_; size_t v_i_boxed_490_; lean_object* v_res_491_; 
v_sz_boxed_489_ = lean_unbox_usize(v_sz_486_);
lean_dec(v_sz_486_);
v_i_boxed_490_ = lean_unbox_usize(v_i_487_);
lean_dec(v_i_487_);
v_res_491_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg(v_xs_483_, v_ys_484_, v_as_485_, v_sz_boxed_489_, v_i_boxed_490_, v_b_488_);
lean_dec_ref(v_as_485_);
lean_dec_ref(v_ys_484_);
lean_dec_ref(v_xs_483_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked___redArg(lean_object* v_mask_498_, lean_object* v_xs_499_, lean_object* v_ys_500_){
_start:
{
lean_object* v___x_501_; size_t v_sz_502_; size_t v___x_503_; lean_object* v___x_504_; lean_object* v_snd_505_; lean_object* v_snd_506_; 
v___x_501_ = ((lean_object*)(l_Lean_Array_zipMasked___redArg___closed__1));
v_sz_502_ = lean_array_size(v_mask_498_);
v___x_503_ = ((size_t)0ULL);
v___x_504_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg(v_xs_499_, v_ys_500_, v_mask_498_, v_sz_502_, v___x_503_, v___x_501_);
v_snd_505_ = lean_ctor_get(v___x_504_, 1);
lean_inc(v_snd_505_);
lean_dec_ref(v___x_504_);
v_snd_506_ = lean_ctor_get(v_snd_505_, 1);
lean_inc(v_snd_506_);
lean_dec(v_snd_505_);
return v_snd_506_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked___redArg___boxed(lean_object* v_mask_507_, lean_object* v_xs_508_, lean_object* v_ys_509_){
_start:
{
lean_object* v_res_510_; 
v_res_510_ = l_Lean_Array_zipMasked___redArg(v_mask_507_, v_xs_508_, v_ys_509_);
lean_dec_ref(v_ys_509_);
lean_dec_ref(v_xs_508_);
lean_dec_ref(v_mask_507_);
return v_res_510_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked(lean_object* v_00_u03b1_511_, lean_object* v_mask_512_, lean_object* v_xs_513_, lean_object* v_ys_514_){
_start:
{
lean_object* v___x_515_; 
v___x_515_ = l_Lean_Array_zipMasked___redArg(v_mask_512_, v_xs_513_, v_ys_514_);
return v___x_515_;
}
}
LEAN_EXPORT lean_object* l_Lean_Array_zipMasked___boxed(lean_object* v_00_u03b1_516_, lean_object* v_mask_517_, lean_object* v_xs_518_, lean_object* v_ys_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l_Lean_Array_zipMasked(v_00_u03b1_516_, v_mask_517_, v_xs_518_, v_ys_519_);
lean_dec_ref(v_ys_519_);
lean_dec_ref(v_xs_518_);
lean_dec_ref(v_mask_517_);
return v_res_520_;
}
}
lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0(lean_object* v_00_u03b1_521_, lean_object* v_xs_522_, lean_object* v_ys_523_, lean_object* v_as_524_, size_t v_sz_525_, size_t v_i_526_, lean_object* v_b_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___redArg(v_xs_522_, v_ys_523_, v_as_524_, v_sz_525_, v_i_526_, v_b_527_);
return v___x_528_;
}
}
LEAN_EXPORT void l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_xs_522_ = stack[1].m_obj;
lean_object* v_ys_523_ = stack[2].m_obj;
lean_object* v_as_524_ = stack[3].m_obj;
size_t v_sz_525_ = stack[4].m_num;
size_t v_i_526_ = stack[5].m_num;
lean_object* v_b_527_ = stack[6].m_obj;
lean_object* v_res_529_;
v_res_529_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0(lean_box(0), v_xs_522_, v_ys_523_, v_as_524_, v_sz_525_, v_i_526_, v_b_527_);
stack->m_obj
 = v_res_529_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0___boxed(lean_object* v_00_u03b1_530_, lean_object* v_xs_531_, lean_object* v_ys_532_, lean_object* v_as_533_, lean_object* v_sz_534_, lean_object* v_i_535_, lean_object* v_b_536_){
_start:
{
size_t v_sz_boxed_537_; size_t v_i_boxed_538_; lean_object* v_res_539_; 
v_sz_boxed_537_ = lean_unbox_usize(v_sz_534_);
lean_dec(v_sz_534_);
v_i_boxed_538_ = lean_unbox_usize(v_i_535_);
lean_dec(v_i_535_);
v_res_539_ = l___private_Init_Data_Array_Basic_0__Array_forIn_x27Unsafe_loop___at___00Lean_Array_zipMasked_spec__0(v_00_u03b1_530_, v_xs_531_, v_ys_532_, v_as_533_, v_sz_boxed_537_, v_i_boxed_538_, v_b_536_);
lean_dec_ref(v_as_533_);
lean_dec_ref(v_ys_532_);
lean_dec_ref(v_xs_531_);
return v_res_539_;
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
