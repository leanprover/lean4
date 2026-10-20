// Lean compiler output
// Module: Std.Data.Iterators.Producers.Monadic.Array
// Imports: public import Init.Data.Iterators.Consumers import Init.Omega
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* lean_array_fget(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdxM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Array_iterM(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterM___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___redArg(lean_object* v_array_1_, lean_object* v_pos_2_){
_start:
{
lean_object* v___x_3_; 
v___x_3_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3_, 0, v_array_1_);
lean_ctor_set(v___x_3_, 1, v_pos_2_);
return v___x_3_;
}
}
LEAN_EXPORT lean_object* l_Array_iterFromIdxM(lean_object* v_00_u03b1_4_, lean_object* v_array_5_, lean_object* v_m_6_, lean_object* v_pos_7_, lean_object* v_inst_8_){
_start:
{
lean_object* v___x_9_; 
v___x_9_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_9_, 0, v_array_5_);
lean_ctor_set(v___x_9_, 1, v_pos_7_);
return v___x_9_;
}
}
LEAN_EXPORT lean_object* l_Array_iterFromIdxM___boxed(lean_object* v_00_u03b1_10_, lean_object* v_array_11_, lean_object* v_m_12_, lean_object* v_pos_13_, lean_object* v_inst_14_){
_start:
{
lean_object* v_res_15_; 
v_res_15_ = l_Array_iterFromIdxM(v_00_u03b1_10_, v_array_11_, v_m_12_, v_pos_13_, v_inst_14_);
lean_dec(v_inst_14_);
return v_res_15_;
}
}
LEAN_EXPORT lean_object* l_Array_iterM___redArg(lean_object* v_array_16_){
_start:
{
lean_object* v___x_17_; lean_object* v___x_18_; 
v___x_17_ = lean_unsigned_to_nat(0u);
v___x_18_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_18_, 0, v_array_16_);
lean_ctor_set(v___x_18_, 1, v___x_17_);
return v___x_18_;
}
}
LEAN_EXPORT lean_object* l_Array_iterM(lean_object* v_00_u03b1_19_, lean_object* v_array_20_, lean_object* v_m_21_, lean_object* v_inst_22_){
_start:
{
lean_object* v___x_23_; lean_object* v___x_24_; 
v___x_23_ = lean_unsigned_to_nat(0u);
v___x_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_24_, 0, v_array_20_);
lean_ctor_set(v___x_24_, 1, v___x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_Array_iterM___boxed(lean_object* v_00_u03b1_25_, lean_object* v_array_26_, lean_object* v_m_27_, lean_object* v_inst_28_){
_start:
{
lean_object* v_res_29_; 
v_res_29_ = l_Array_iterM(v_00_u03b1_25_, v_array_26_, v_m_27_, v_inst_28_);
lean_dec(v_inst_28_);
return v_res_29_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator___redArg___lam__0(lean_object* v_inst_30_, lean_object* v_it_31_){
_start:
{
lean_object* v_array_32_; lean_object* v_pos_33_; lean_object* v___x_35_; uint8_t v_isShared_36_; uint8_t v_isSharedCheck_49_; 
v_array_32_ = lean_ctor_get(v_it_31_, 0);
v_pos_33_ = lean_ctor_get(v_it_31_, 1);
v_isSharedCheck_49_ = !lean_is_exclusive(v_it_31_);
if (v_isSharedCheck_49_ == 0)
{
v___x_35_ = v_it_31_;
v_isShared_36_ = v_isSharedCheck_49_;
goto v_resetjp_34_;
}
else
{
lean_inc(v_pos_33_);
lean_inc(v_array_32_);
lean_dec(v_it_31_);
v___x_35_ = lean_box(0);
v_isShared_36_ = v_isSharedCheck_49_;
goto v_resetjp_34_;
}
v_resetjp_34_:
{
lean_object* v___x_37_; uint8_t v___x_38_; 
v___x_37_ = lean_array_get_size(v_array_32_);
v___x_38_ = lean_nat_dec_lt(v_pos_33_, v___x_37_);
if (v___x_38_ == 0)
{
lean_object* v___x_39_; lean_object* v___x_40_; 
lean_del_object(v___x_35_);
lean_dec(v_pos_33_);
lean_dec_ref(v_array_32_);
v___x_39_ = lean_box(2);
v___x_40_ = lean_apply_2(v_inst_30_, lean_box(0), v___x_39_);
return v___x_40_;
}
else
{
lean_object* v___x_41_; lean_object* v___x_42_; lean_object* v___x_44_; 
v___x_41_ = lean_unsigned_to_nat(1u);
v___x_42_ = lean_nat_add(v_pos_33_, v___x_41_);
lean_inc_ref(v_array_32_);
if (v_isShared_36_ == 0)
{
lean_ctor_set(v___x_35_, 1, v___x_42_);
v___x_44_ = v___x_35_;
goto v_reusejp_43_;
}
else
{
lean_object* v_reuseFailAlloc_48_; 
v_reuseFailAlloc_48_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_48_, 0, v_array_32_);
lean_ctor_set(v_reuseFailAlloc_48_, 1, v___x_42_);
v___x_44_ = v_reuseFailAlloc_48_;
goto v_reusejp_43_;
}
v_reusejp_43_:
{
lean_object* v___x_45_; lean_object* v___x_46_; lean_object* v___x_47_; 
v___x_45_ = lean_array_fget(v_array_32_, v_pos_33_);
lean_dec(v_pos_33_);
lean_dec_ref(v_array_32_);
v___x_46_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_46_, 0, v___x_44_);
lean_ctor_set(v___x_46_, 1, v___x_45_);
v___x_47_ = lean_apply_2(v_inst_30_, lean_box(0), v___x_46_);
return v___x_47_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator___redArg(lean_object* v_inst_50_){
_start:
{
lean_object* v___f_51_; 
v___f_51_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_51_, 0, v_inst_50_);
return v___f_51_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIterator(lean_object* v_m_52_, lean_object* v_00_u03b1_53_, lean_object* v_inst_54_){
_start:
{
lean_object* v___f_55_; 
v___f_55_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIterator___redArg___lam__0), 2, 1);
lean_closure_set(v___f_55_, 0, v_inst_54_);
return v___f_55_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_57_; 
v___x_57_ = lean_box(0);
return v___x_57_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_58_){
_start:
{
lean_object* v_res_59_; 
v_res_59_ = l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation___redArg();
return v_res_59_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation(lean_object* v_00_u03b1_60_, lean_object* v_m_61_, lean_object* v_inst_62_){
_start:
{
lean_object* v___x_63_; 
v___x_63_ = lean_box(0);
return v___x_63_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_64_, lean_object* v_m_65_, lean_object* v_inst_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l___private_Std_Data_Iterators_Producers_Monadic_Array_0__Std_Iterators_Types_ArrayIterator_instFinitenessRelation(v_00_u03b1_64_, v_m_65_, v_inst_66_);
lean_dec(v_inst_66_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_68_, lean_object* v_recur_69_, lean_object* v_it_70_, lean_object* v_____do__lift_71_){
_start:
{
if (lean_obj_tag(v_____do__lift_71_) == 0)
{
lean_object* v_a_72_; lean_object* v___x_73_; 
lean_dec_ref(v_it_70_);
lean_dec(v_recur_69_);
v_a_72_ = lean_ctor_get(v_____do__lift_71_, 0);
lean_inc(v_a_72_);
lean_dec_ref_known(v_____do__lift_71_, 1);
v___x_73_ = lean_apply_2(v_toPure_68_, lean_box(0), v_a_72_);
return v___x_73_;
}
else
{
lean_object* v_a_74_; lean_object* v___x_75_; 
lean_dec(v_toPure_68_);
v_a_74_ = lean_ctor_get(v_____do__lift_71_, 0);
lean_inc(v_a_74_);
lean_dec_ref_known(v_____do__lift_71_, 1);
v___x_75_ = lean_apply_4(v_recur_69_, v_it_70_, v_a_74_, lean_box(0), lean_box(0));
return v___x_75_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_76_, lean_object* v_recur_77_, lean_object* v___y_78_, lean_object* v_acc_79_, lean_object* v_toBind_80_, lean_object* v_s_81_){
_start:
{
switch(lean_obj_tag(v_s_81_))
{
case 0:
{
lean_object* v_it_82_; lean_object* v_out_83_; lean_object* v___f_84_; lean_object* v___x_85_; lean_object* v___x_86_; 
v_it_82_ = lean_ctor_get(v_s_81_, 0);
lean_inc(v_it_82_);
v_out_83_ = lean_ctor_get(v_s_81_, 1);
lean_inc(v_out_83_);
lean_dec_ref_known(v_s_81_, 2);
v___f_84_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_84_, 0, v_toPure_76_);
lean_closure_set(v___f_84_, 1, v_recur_77_);
lean_closure_set(v___f_84_, 2, v_it_82_);
v___x_85_ = lean_apply_3(v___y_78_, v_out_83_, lean_box(0), v_acc_79_);
v___x_86_ = lean_apply_4(v_toBind_80_, lean_box(0), lean_box(0), v___x_85_, v___f_84_);
return v___x_86_;
}
case 1:
{
lean_object* v_it_87_; lean_object* v___x_88_; 
lean_dec(v_toBind_80_);
lean_dec(v___y_78_);
lean_dec(v_toPure_76_);
v_it_87_ = lean_ctor_get(v_s_81_, 0);
lean_inc(v_it_87_);
lean_dec_ref_known(v_s_81_, 1);
v___x_88_ = lean_apply_4(v_recur_77_, v_it_87_, v_acc_79_, lean_box(0), lean_box(0));
return v___x_88_;
}
default: 
{
lean_object* v___x_89_; 
lean_dec(v_toBind_80_);
lean_dec(v___y_78_);
lean_dec(v_recur_77_);
v___x_89_ = lean_apply_2(v_toPure_76_, lean_box(0), v_acc_79_);
return v___x_89_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_90_, lean_object* v___y_91_, lean_object* v_toBind_92_, lean_object* v_toPure_93_, lean_object* v_lift_94_, lean_object* v_it_95_, lean_object* v_acc_96_, lean_object* v_hP_97_, lean_object* v_recur_98_){
_start:
{
lean_object* v_array_99_; lean_object* v_pos_100_; lean_object* v___x_102_; uint8_t v_isShared_103_; uint8_t v_isSharedCheck_119_; 
v_array_99_ = lean_ctor_get(v_it_95_, 0);
v_pos_100_ = lean_ctor_get(v_it_95_, 1);
v_isSharedCheck_119_ = !lean_is_exclusive(v_it_95_);
if (v_isSharedCheck_119_ == 0)
{
v___x_102_ = v_it_95_;
v_isShared_103_ = v_isSharedCheck_119_;
goto v_resetjp_101_;
}
else
{
lean_inc(v_pos_100_);
lean_inc(v_array_99_);
lean_dec(v_it_95_);
v___x_102_ = lean_box(0);
v_isShared_103_ = v_isSharedCheck_119_;
goto v_resetjp_101_;
}
v_resetjp_101_:
{
lean_object* v___f_104_; lean_object* v___x_105_; uint8_t v___x_106_; 
v___f_104_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_104_, 0, v_toPure_90_);
lean_closure_set(v___f_104_, 1, v_recur_98_);
lean_closure_set(v___f_104_, 2, v___y_91_);
lean_closure_set(v___f_104_, 3, v_acc_96_);
lean_closure_set(v___f_104_, 4, v_toBind_92_);
v___x_105_ = lean_array_get_size(v_array_99_);
v___x_106_ = lean_nat_dec_lt(v_pos_100_, v___x_105_);
if (v___x_106_ == 0)
{
lean_object* v___x_107_; lean_object* v___x_108_; lean_object* v___x_109_; 
lean_del_object(v___x_102_);
lean_dec(v_pos_100_);
lean_dec_ref(v_array_99_);
v___x_107_ = lean_box(2);
v___x_108_ = lean_apply_2(v_toPure_93_, lean_box(0), v___x_107_);
v___x_109_ = lean_apply_4(v_lift_94_, lean_box(0), lean_box(0), v___f_104_, v___x_108_);
return v___x_109_;
}
else
{
lean_object* v___x_110_; lean_object* v___x_111_; lean_object* v___x_113_; 
v___x_110_ = lean_unsigned_to_nat(1u);
v___x_111_ = lean_nat_add(v_pos_100_, v___x_110_);
lean_inc_ref(v_array_99_);
if (v_isShared_103_ == 0)
{
lean_ctor_set(v___x_102_, 1, v___x_111_);
v___x_113_ = v___x_102_;
goto v_reusejp_112_;
}
else
{
lean_object* v_reuseFailAlloc_118_; 
v_reuseFailAlloc_118_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_118_, 0, v_array_99_);
lean_ctor_set(v_reuseFailAlloc_118_, 1, v___x_111_);
v___x_113_ = v_reuseFailAlloc_118_;
goto v_reusejp_112_;
}
v_reusejp_112_:
{
lean_object* v___x_114_; lean_object* v___x_115_; lean_object* v___x_116_; lean_object* v___x_117_; 
v___x_114_ = lean_array_fget(v_array_99_, v_pos_100_);
lean_dec(v_pos_100_);
lean_dec_ref(v_array_99_);
v___x_115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_115_, 0, v___x_113_);
lean_ctor_set(v___x_115_, 1, v___x_114_);
v___x_116_ = lean_apply_2(v_toPure_93_, lean_box(0), v___x_115_);
v___x_117_ = lean_apply_4(v_lift_94_, lean_box(0), lean_box(0), v___f_104_, v___x_116_);
return v___x_117_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__3(lean_object* v_inst_120_, lean_object* v_toPure_121_, lean_object* v_lift_122_, lean_object* v_00_u03b3_123_, lean_object* v_Pl_124_, lean_object* v_it_125_, lean_object* v_init_126_, lean_object* v___y_127_){
_start:
{
lean_object* v_toApplicative_128_; lean_object* v_toBind_129_; lean_object* v_toPure_130_; lean_object* v___f_131_; lean_object* v___x_132_; 
v_toApplicative_128_ = lean_ctor_get(v_inst_120_, 0);
lean_inc_ref(v_toApplicative_128_);
v_toBind_129_ = lean_ctor_get(v_inst_120_, 1);
lean_inc(v_toBind_129_);
lean_dec_ref(v_inst_120_);
v_toPure_130_ = lean_ctor_get(v_toApplicative_128_, 1);
lean_inc(v_toPure_130_);
lean_dec_ref(v_toApplicative_128_);
v___f_131_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__2), 9, 5);
lean_closure_set(v___f_131_, 0, v_toPure_130_);
lean_closure_set(v___f_131_, 1, v___y_127_);
lean_closure_set(v___f_131_, 2, v_toBind_129_);
lean_closure_set(v___f_131_, 3, v_toPure_121_);
lean_closure_set(v___f_131_, 4, v_lift_122_);
v___x_132_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_131_, v_it_125_, v_init_126_, lean_box(0));
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg(lean_object* v_inst_133_, lean_object* v_inst_134_){
_start:
{
lean_object* v_toApplicative_135_; lean_object* v_toPure_136_; lean_object* v___f_137_; 
v_toApplicative_135_ = lean_ctor_get(v_inst_133_, 0);
lean_inc_ref(v_toApplicative_135_);
lean_dec_ref(v_inst_133_);
v_toPure_136_ = lean_ctor_get(v_toApplicative_135_, 1);
lean_inc(v_toPure_136_);
lean_dec_ref(v_toApplicative_135_);
v___f_137_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_137_, 0, v_inst_134_);
lean_closure_set(v___f_137_, 1, v_toPure_136_);
return v___f_137_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_ArrayIterator_instIteratorLoop(lean_object* v_m_138_, lean_object* v_00_u03b1_139_, lean_object* v_inst_140_, lean_object* v_n_141_, lean_object* v_inst_142_){
_start:
{
lean_object* v_toApplicative_143_; lean_object* v_toPure_144_; lean_object* v___f_145_; 
v_toApplicative_143_ = lean_ctor_get(v_inst_140_, 0);
lean_inc_ref(v_toApplicative_143_);
lean_dec_ref(v_inst_140_);
v_toPure_144_ = lean_ctor_get(v_toApplicative_143_, 1);
lean_inc(v_toPure_144_);
lean_dec_ref(v_toApplicative_143_);
v___f_145_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_ArrayIterator_instIteratorLoop___redArg___lam__3), 8, 2);
lean_closure_set(v___f_145_, 0, v_inst_142_);
lean_closure_set(v___f_145_, 1, v_toPure_144_);
return v___f_145_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_Iterators_Producers_Monadic_Array(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Consumers(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_Iterators_Producers_Monadic_Array(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Consumers(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_Iterators_Producers_Monadic_Array(builtin);
}
#ifdef __cplusplus
}
#endif
