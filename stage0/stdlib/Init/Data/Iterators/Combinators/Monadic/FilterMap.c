// Lean compiler output
// Module: Init.Data.Iterators.Combinators.Monadic.FilterMap
// Imports: public import Init.Data.Iterators.PostconditionMonad public import Init.Data.Iterators.Consumers.Monadic.Loop import Init.PropLemmas
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
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_filterMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_filterMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_map___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_map___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMapWithPostcondition___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMapWithPostcondition___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMapWithPostcondition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMapWithPostcondition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Iterators_Types_Map_instIterator___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iterators_Types_Map_instIterator___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iterators_Types_Map_instIterator___redArg___closed__0 = (const lean_object*)&l_Std_Iterators_Types_Map_instIterator___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__4(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mapM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mapM___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mapM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_mapM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterM___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterM___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterM(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterM___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMap(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_map___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_map___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_map(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_map___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filter___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_filter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_filterMap___redArg(lean_object* v_it_1_){
_start:
{
lean_inc(v_it_1_);
return v_it_1_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_filterMap___redArg___boxed(lean_object* v_it_2_){
_start:
{
lean_object* v_res_3_; 
v_res_3_ = l_Std_IterM_InternalCombinators_filterMap___redArg(v_it_2_);
lean_dec(v_it_2_);
return v_res_3_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_filterMap(lean_object* v_00_u03b1_4_, lean_object* v_00_u03b2_5_, lean_object* v_00_u03b3_6_, lean_object* v_m_7_, lean_object* v_n_8_, lean_object* v_lift_9_, lean_object* v_inst_10_, lean_object* v_f_11_, lean_object* v_it_12_){
_start:
{
lean_inc(v_it_12_);
return v_it_12_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_filterMap___boxed(lean_object* v_00_u03b1_13_, lean_object* v_00_u03b2_14_, lean_object* v_00_u03b3_15_, lean_object* v_m_16_, lean_object* v_n_17_, lean_object* v_lift_18_, lean_object* v_inst_19_, lean_object* v_f_20_, lean_object* v_it_21_){
_start:
{
lean_object* v_res_22_; 
v_res_22_ = l_Std_IterM_InternalCombinators_filterMap(v_00_u03b1_13_, v_00_u03b2_14_, v_00_u03b3_15_, v_m_16_, v_n_17_, v_lift_18_, v_inst_19_, v_f_20_, v_it_21_);
lean_dec(v_it_21_);
lean_dec(v_f_20_);
lean_dec(v_inst_19_);
lean_dec(v_lift_18_);
return v_res_22_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_map___redArg(lean_object* v_it_23_){
_start:
{
lean_inc(v_it_23_);
return v_it_23_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_map___redArg___boxed(lean_object* v_it_24_){
_start:
{
lean_object* v_res_25_; 
v_res_25_ = l_Std_IterM_InternalCombinators_map___redArg(v_it_24_);
lean_dec(v_it_24_);
return v_res_25_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_map(lean_object* v_00_u03b1_26_, lean_object* v_00_u03b2_27_, lean_object* v_00_u03b3_28_, lean_object* v_m_29_, lean_object* v_n_30_, lean_object* v_inst_31_, lean_object* v_lift_32_, lean_object* v_inst_33_, lean_object* v_f_34_, lean_object* v_it_35_){
_start:
{
lean_inc(v_it_35_);
return v_it_35_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_InternalCombinators_map___boxed(lean_object* v_00_u03b1_36_, lean_object* v_00_u03b2_37_, lean_object* v_00_u03b3_38_, lean_object* v_m_39_, lean_object* v_n_40_, lean_object* v_inst_41_, lean_object* v_lift_42_, lean_object* v_inst_43_, lean_object* v_f_44_, lean_object* v_it_45_){
_start:
{
lean_object* v_res_46_; 
v_res_46_ = l_Std_IterM_InternalCombinators_map(v_00_u03b1_36_, v_00_u03b2_37_, v_00_u03b3_38_, v_m_39_, v_n_40_, v_inst_41_, v_lift_42_, v_inst_43_, v_f_44_, v_it_45_);
lean_dec(v_it_45_);
lean_dec(v_f_44_);
lean_dec(v_inst_43_);
lean_dec(v_lift_42_);
lean_dec_ref(v_inst_41_);
return v_res_46_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapWithPostcondition___redArg(lean_object* v_it_47_){
_start:
{
lean_inc(v_it_47_);
return v_it_47_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapWithPostcondition___redArg___boxed(lean_object* v_it_48_){
_start:
{
lean_object* v_res_49_; 
v_res_49_ = l_Std_IterM_filterMapWithPostcondition___redArg(v_it_48_);
lean_dec(v_it_48_);
return v_res_49_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapWithPostcondition(lean_object* v_00_u03b1_50_, lean_object* v_00_u03b2_51_, lean_object* v_00_u03b3_52_, lean_object* v_m_53_, lean_object* v_n_54_, lean_object* v_inst_55_, lean_object* v_inst_56_, lean_object* v_f_57_, lean_object* v_it_58_){
_start:
{
lean_inc(v_it_58_);
return v_it_58_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapWithPostcondition___boxed(lean_object* v_00_u03b1_59_, lean_object* v_00_u03b2_60_, lean_object* v_00_u03b3_61_, lean_object* v_m_62_, lean_object* v_n_63_, lean_object* v_inst_64_, lean_object* v_inst_65_, lean_object* v_f_66_, lean_object* v_it_67_){
_start:
{
lean_object* v_res_68_; 
v_res_68_ = l_Std_IterM_filterMapWithPostcondition(v_00_u03b1_59_, v_00_u03b2_60_, v_00_u03b3_61_, v_m_62_, v_n_63_, v_inst_64_, v_inst_65_, v_f_66_, v_it_67_);
lean_dec(v_it_67_);
lean_dec(v_f_66_);
lean_dec(v_inst_65_);
lean_dec(v_inst_64_);
return v_res_68_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0(lean_object* v_it_69_, lean_object* v_toPure_70_, lean_object* v_____do__lift_71_){
_start:
{
if (lean_obj_tag(v_____do__lift_71_) == 0)
{
lean_object* v___x_72_; lean_object* v___x_73_; 
v___x_72_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_72_, 0, v_it_69_);
v___x_73_ = lean_apply_2(v_toPure_70_, lean_box(0), v___x_72_);
return v___x_73_;
}
else
{
lean_object* v_val_74_; lean_object* v___x_75_; lean_object* v___x_76_; 
v_val_74_ = lean_ctor_get(v_____do__lift_71_, 0);
lean_inc(v_val_74_);
v___x_75_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_75_, 0, v_it_69_);
lean_ctor_set(v___x_75_, 1, v_val_74_);
v___x_76_ = lean_apply_2(v_toPure_70_, lean_box(0), v___x_75_);
return v___x_76_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0___boxed(lean_object* v_it_77_, lean_object* v_toPure_78_, lean_object* v_____do__lift_79_){
_start:
{
lean_object* v_res_80_; 
v_res_80_ = l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0(v_it_77_, v_toPure_78_, v_____do__lift_79_);
lean_dec(v_____do__lift_79_);
return v_res_80_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1(lean_object* v_toPure_81_, lean_object* v_f_82_, lean_object* v_toBind_83_, lean_object* v_____do__lift_84_){
_start:
{
switch(lean_obj_tag(v_____do__lift_84_))
{
case 0:
{
lean_object* v_it_85_; lean_object* v_out_86_; lean_object* v___f_87_; lean_object* v___x_88_; lean_object* v___x_89_; 
v_it_85_ = lean_ctor_get(v_____do__lift_84_, 0);
lean_inc(v_it_85_);
v_out_86_ = lean_ctor_get(v_____do__lift_84_, 1);
lean_inc(v_out_86_);
lean_dec_ref(v_____do__lift_84_);
v___f_87_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_87_, 0, v_it_85_);
lean_closure_set(v___f_87_, 1, v_toPure_81_);
v___x_88_ = lean_apply_1(v_f_82_, v_out_86_);
v___x_89_ = lean_apply_4(v_toBind_83_, lean_box(0), lean_box(0), v___x_88_, v___f_87_);
return v___x_89_;
}
case 1:
{
lean_object* v_it_90_; lean_object* v___x_92_; uint8_t v_isShared_93_; uint8_t v_isSharedCheck_98_; 
lean_dec(v_toBind_83_);
lean_dec(v_f_82_);
v_it_90_ = lean_ctor_get(v_____do__lift_84_, 0);
v_isSharedCheck_98_ = !lean_is_exclusive(v_____do__lift_84_);
if (v_isSharedCheck_98_ == 0)
{
v___x_92_ = v_____do__lift_84_;
v_isShared_93_ = v_isSharedCheck_98_;
goto v_resetjp_91_;
}
else
{
lean_inc(v_it_90_);
lean_dec(v_____do__lift_84_);
v___x_92_ = lean_box(0);
v_isShared_93_ = v_isSharedCheck_98_;
goto v_resetjp_91_;
}
v_resetjp_91_:
{
lean_object* v___x_95_; 
if (v_isShared_93_ == 0)
{
v___x_95_ = v___x_92_;
goto v_reusejp_94_;
}
else
{
lean_object* v_reuseFailAlloc_97_; 
v_reuseFailAlloc_97_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_97_, 0, v_it_90_);
v___x_95_ = v_reuseFailAlloc_97_;
goto v_reusejp_94_;
}
v_reusejp_94_:
{
lean_object* v___x_96_; 
v___x_96_ = lean_apply_2(v_toPure_81_, lean_box(0), v___x_95_);
return v___x_96_;
}
}
}
default: 
{
lean_object* v___x_99_; lean_object* v___x_100_; 
lean_dec(v_toBind_83_);
lean_dec(v_f_82_);
v___x_99_ = lean_box(2);
v___x_100_ = lean_apply_2(v_toPure_81_, lean_box(0), v___x_99_);
return v___x_100_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__2(lean_object* v_inst_101_, lean_object* v_lift_102_, lean_object* v_toBind_103_, lean_object* v___f_104_, lean_object* v_it_105_){
_start:
{
lean_object* v___x_106_; lean_object* v___x_107_; lean_object* v___x_108_; 
v___x_106_ = lean_apply_1(v_inst_101_, v_it_105_);
v___x_107_ = lean_apply_2(v_lift_102_, lean_box(0), v___x_106_);
v___x_108_ = lean_apply_4(v_toBind_103_, lean_box(0), lean_box(0), v___x_107_, v___f_104_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator___redArg(lean_object* v_lift_109_, lean_object* v_f_110_, lean_object* v_inst_111_, lean_object* v_inst_112_){
_start:
{
lean_object* v_toApplicative_113_; lean_object* v_toBind_114_; lean_object* v_toPure_115_; lean_object* v___f_116_; lean_object* v___f_117_; 
v_toApplicative_113_ = lean_ctor_get(v_inst_112_, 0);
lean_inc_ref(v_toApplicative_113_);
v_toBind_114_ = lean_ctor_get(v_inst_112_, 1);
lean_inc(v_toBind_114_);
lean_dec_ref(v_inst_112_);
v_toPure_115_ = lean_ctor_get(v_toApplicative_113_, 1);
lean_inc(v_toPure_115_);
lean_dec_ref(v_toApplicative_113_);
lean_inc(v_toBind_114_);
v___f_116_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_116_, 0, v_toPure_115_);
lean_closure_set(v___f_116_, 1, v_f_110_);
lean_closure_set(v___f_116_, 2, v_toBind_114_);
v___f_117_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__2), 5, 4);
lean_closure_set(v___f_117_, 0, v_inst_111_);
lean_closure_set(v___f_117_, 1, v_lift_109_);
lean_closure_set(v___f_117_, 2, v_toBind_114_);
lean_closure_set(v___f_117_, 3, v___f_116_);
return v___f_117_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIterator(lean_object* v_00_u03b1_118_, lean_object* v_00_u03b2_119_, lean_object* v_00_u03b3_120_, lean_object* v_m_121_, lean_object* v_n_122_, lean_object* v_lift_123_, lean_object* v_f_124_, lean_object* v_inst_125_, lean_object* v_inst_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = l_Std_Iterators_Types_FilterMap_instIterator___redArg(v_lift_123_, v_f_124_, v_inst_125_, v_inst_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___redArg___lam__0(lean_object* v_a_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v_a_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___redArg___lam__1(lean_object* v_toFunctor_130_, lean_object* v_f_131_, lean_object* v___f_132_, lean_object* v_b_133_){
_start:
{
lean_object* v_map_134_; lean_object* v___x_135_; lean_object* v___x_136_; 
v_map_134_ = lean_ctor_get(v_toFunctor_130_, 0);
lean_inc(v_map_134_);
lean_dec_ref(v_toFunctor_130_);
v___x_135_ = lean_apply_1(v_f_131_, v_b_133_);
v___x_136_ = lean_apply_4(v_map_134_, lean_box(0), lean_box(0), v___f_132_, v___x_135_);
return v___x_136_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___redArg(lean_object* v_inst_138_, lean_object* v_inst_139_, lean_object* v_lift_140_, lean_object* v_f_141_){
_start:
{
lean_object* v_toApplicative_142_; lean_object* v_toFunctor_143_; lean_object* v___f_144_; lean_object* v___f_145_; lean_object* v___x_146_; 
v_toApplicative_142_ = lean_ctor_get(v_inst_138_, 0);
v_toFunctor_143_ = lean_ctor_get(v_toApplicative_142_, 0);
v___f_144_ = ((lean_object*)(l_Std_Iterators_Types_Map_instIterator___redArg___closed__0));
lean_inc_ref(v_toFunctor_143_);
v___f_145_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_145_, 0, v_toFunctor_143_);
lean_closure_set(v___f_145_, 1, v_f_141_);
lean_closure_set(v___f_145_, 2, v___f_144_);
v___x_146_ = l_Std_Iterators_Types_FilterMap_instIterator___redArg(v_lift_140_, v___f_145_, v_inst_139_, v_inst_138_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator(lean_object* v_00_u03b1_147_, lean_object* v_00_u03b2_148_, lean_object* v_00_u03b3_149_, lean_object* v_m_150_, lean_object* v_n_151_, lean_object* v_inst_152_, lean_object* v_inst_153_, lean_object* v_lift_154_, lean_object* v_f_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_Std_Iterators_Types_Map_instIterator___redArg(v_inst_152_, v_inst_153_, v_lift_154_, v_f_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(lean_object* v_00_u03b1_157_, lean_object* v_00_u03b2_158_, lean_object* v_00_u03b3_159_, lean_object* v_m_160_, lean_object* v_n_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_lift_164_, lean_object* v_f_165_, lean_object* v_inst_166_){
_start:
{
lean_object* v___x_167_; 
v___x_167_ = lean_box(0);
return v___x_167_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___boxed(lean_object* v_00_u03b1_168_, lean_object* v_00_u03b2_169_, lean_object* v_00_u03b3_170_, lean_object* v_m_171_, lean_object* v_n_172_, lean_object* v_inst_173_, lean_object* v_inst_174_, lean_object* v_lift_175_, lean_object* v_f_176_, lean_object* v_inst_177_){
_start:
{
lean_object* v_res_178_; 
v_res_178_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(v_00_u03b1_168_, v_00_u03b2_169_, v_00_u03b3_170_, v_m_171_, v_n_172_, v_inst_173_, v_inst_174_, v_lift_175_, v_f_176_, v_inst_177_);
lean_dec(v_f_176_);
lean_dec(v_lift_175_);
lean_dec(v_inst_174_);
lean_dec_ref(v_inst_173_);
return v_res_178_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(lean_object* v_00_u03b1_179_, lean_object* v_00_u03b2_180_, lean_object* v_00_u03b3_181_, lean_object* v_m_182_, lean_object* v_n_183_, lean_object* v_inst_184_, lean_object* v_inst_185_, lean_object* v_lift_186_, lean_object* v_f_187_, lean_object* v_inst_188_){
_start:
{
lean_object* v___x_189_; 
v___x_189_ = lean_box(0);
return v___x_189_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___boxed(lean_object* v_00_u03b1_190_, lean_object* v_00_u03b2_191_, lean_object* v_00_u03b3_192_, lean_object* v_m_193_, lean_object* v_n_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_lift_197_, lean_object* v_f_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(v_00_u03b1_190_, v_00_u03b2_191_, v_00_u03b3_192_, v_m_193_, v_n_194_, v_inst_195_, v_inst_196_, v_lift_197_, v_f_198_, v_inst_199_);
lean_dec(v_f_198_);
lean_dec(v_lift_197_);
lean_dec(v_inst_196_);
lean_dec_ref(v_inst_195_);
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_201_, lean_object* v_recur_202_, lean_object* v_it_203_, lean_object* v_____do__lift_204_){
_start:
{
if (lean_obj_tag(v_____do__lift_204_) == 0)
{
lean_object* v_a_205_; lean_object* v___x_206_; 
lean_dec(v_it_203_);
lean_dec(v_recur_202_);
v_a_205_ = lean_ctor_get(v_____do__lift_204_, 0);
lean_inc(v_a_205_);
lean_dec_ref(v_____do__lift_204_);
v___x_206_ = lean_apply_2(v_toPure_201_, lean_box(0), v_a_205_);
return v___x_206_;
}
else
{
lean_object* v_a_207_; lean_object* v___x_208_; 
lean_dec(v_toPure_201_);
v_a_207_ = lean_ctor_get(v_____do__lift_204_, 0);
lean_inc(v_a_207_);
lean_dec_ref(v_____do__lift_204_);
v___x_208_ = lean_apply_4(v_recur_202_, v_it_203_, v_a_207_, lean_box(0), lean_box(0));
return v___x_208_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_209_, lean_object* v_recur_210_, lean_object* v___y_211_, lean_object* v_acc_212_, lean_object* v_toBind_213_, lean_object* v_s_214_){
_start:
{
switch(lean_obj_tag(v_s_214_))
{
case 0:
{
lean_object* v_it_215_; lean_object* v_out_216_; lean_object* v___f_217_; lean_object* v___x_218_; lean_object* v___x_219_; 
v_it_215_ = lean_ctor_get(v_s_214_, 0);
lean_inc(v_it_215_);
v_out_216_ = lean_ctor_get(v_s_214_, 1);
lean_inc(v_out_216_);
lean_dec_ref(v_s_214_);
v___f_217_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_217_, 0, v_toPure_209_);
lean_closure_set(v___f_217_, 1, v_recur_210_);
lean_closure_set(v___f_217_, 2, v_it_215_);
v___x_218_ = lean_apply_3(v___y_211_, v_out_216_, lean_box(0), v_acc_212_);
v___x_219_ = lean_apply_4(v_toBind_213_, lean_box(0), lean_box(0), v___x_218_, v___f_217_);
return v___x_219_;
}
case 1:
{
lean_object* v_it_220_; lean_object* v___x_221_; 
lean_dec(v_toBind_213_);
lean_dec(v___y_211_);
lean_dec(v_toPure_209_);
v_it_220_ = lean_ctor_get(v_s_214_, 0);
lean_inc(v_it_220_);
lean_dec_ref(v_s_214_);
v___x_221_ = lean_apply_4(v_recur_210_, v_it_220_, v_acc_212_, lean_box(0), lean_box(0));
return v___x_221_;
}
default: 
{
lean_object* v___x_222_; 
lean_dec(v_toBind_213_);
lean_dec(v___y_211_);
lean_dec(v_recur_210_);
v___x_222_ = lean_apply_2(v_toPure_209_, lean_box(0), v_acc_212_);
return v___x_222_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4(lean_object* v_inst_223_, lean_object* v_toPure_224_, lean_object* v___y_225_, lean_object* v_toBind_226_, lean_object* v_f_227_, lean_object* v_inst_228_, lean_object* v_lift_229_, lean_object* v_lift_230_, lean_object* v_it_231_, lean_object* v_acc_232_, lean_object* v_hP_233_, lean_object* v_recur_234_){
_start:
{
lean_object* v_toApplicative_235_; lean_object* v_toBind_236_; lean_object* v_toPure_237_; lean_object* v___f_238_; lean_object* v___f_239_; lean_object* v___x_240_; lean_object* v___x_241_; lean_object* v___x_242_; lean_object* v___x_243_; 
v_toApplicative_235_ = lean_ctor_get(v_inst_223_, 0);
lean_inc_ref(v_toApplicative_235_);
v_toBind_236_ = lean_ctor_get(v_inst_223_, 1);
lean_inc(v_toBind_236_);
lean_dec_ref(v_inst_223_);
v_toPure_237_ = lean_ctor_get(v_toApplicative_235_, 1);
lean_inc(v_toPure_237_);
lean_dec_ref(v_toApplicative_235_);
v___f_238_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_238_, 0, v_toPure_224_);
lean_closure_set(v___f_238_, 1, v_recur_234_);
lean_closure_set(v___f_238_, 2, v___y_225_);
lean_closure_set(v___f_238_, 3, v_acc_232_);
lean_closure_set(v___f_238_, 4, v_toBind_226_);
lean_inc(v_toBind_236_);
v___f_239_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_239_, 0, v_toPure_237_);
lean_closure_set(v___f_239_, 1, v_f_227_);
lean_closure_set(v___f_239_, 2, v_toBind_236_);
v___x_240_ = lean_apply_1(v_inst_228_, v_it_231_);
v___x_241_ = lean_apply_2(v_lift_229_, lean_box(0), v___x_240_);
v___x_242_ = lean_apply_4(v_toBind_236_, lean_box(0), lean_box(0), v___x_241_, v___f_239_);
v___x_243_ = lean_apply_4(v_lift_230_, lean_box(0), lean_box(0), v___f_238_, v___x_242_);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2(lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_f_246_, lean_object* v_inst_247_, lean_object* v_lift_248_, lean_object* v_lift_249_, lean_object* v_00_u03b3_250_, lean_object* v_Pl_251_, lean_object* v_it_252_, lean_object* v_init_253_, lean_object* v___y_254_){
_start:
{
lean_object* v_toApplicative_255_; lean_object* v_toBind_256_; lean_object* v_toPure_257_; lean_object* v___f_258_; lean_object* v___x_259_; 
v_toApplicative_255_ = lean_ctor_get(v_inst_244_, 0);
lean_inc_ref(v_toApplicative_255_);
v_toBind_256_ = lean_ctor_get(v_inst_244_, 1);
lean_inc(v_toBind_256_);
lean_dec_ref(v_inst_244_);
v_toPure_257_ = lean_ctor_get(v_toApplicative_255_, 1);
lean_inc(v_toPure_257_);
lean_dec_ref(v_toApplicative_255_);
v___f_258_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4), 12, 8);
lean_closure_set(v___f_258_, 0, v_inst_245_);
lean_closure_set(v___f_258_, 1, v_toPure_257_);
lean_closure_set(v___f_258_, 2, v___y_254_);
lean_closure_set(v___f_258_, 3, v_toBind_256_);
lean_closure_set(v___f_258_, 4, v_f_246_);
lean_closure_set(v___f_258_, 5, v_inst_247_);
lean_closure_set(v___f_258_, 6, v_lift_248_);
lean_closure_set(v___f_258_, 7, v_lift_249_);
v___x_259_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_258_, v_it_252_, v_init_253_, lean_box(0));
return v___x_259_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg(lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_lift_263_, lean_object* v_f_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2), 11, 5);
lean_closure_set(v___f_265_, 0, v_inst_261_);
lean_closure_set(v___f_265_, 1, v_inst_260_);
lean_closure_set(v___f_265_, 2, v_f_264_);
lean_closure_set(v___f_265_, 3, v_inst_262_);
lean_closure_set(v___f_265_, 4, v_lift_263_);
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop(lean_object* v_00_u03b1_266_, lean_object* v_00_u03b2_267_, lean_object* v_00_u03b3_268_, lean_object* v_m_269_, lean_object* v_n_270_, lean_object* v_o_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_lift_275_, lean_object* v_f_276_){
_start:
{
lean_object* v___f_277_; 
v___f_277_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2), 11, 5);
lean_closure_set(v___f_277_, 0, v_inst_273_);
lean_closure_set(v___f_277_, 1, v_inst_272_);
lean_closure_set(v___f_277_, 2, v_f_276_);
lean_closure_set(v___f_277_, 3, v_inst_274_);
lean_closure_set(v___f_277_, 4, v_lift_275_);
return v___f_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__4(lean_object* v_toFunctor_278_, lean_object* v_toPure_279_, lean_object* v_f_280_, lean_object* v___f_281_, lean_object* v_toBind_282_, lean_object* v_____do__lift_283_){
_start:
{
switch(lean_obj_tag(v_____do__lift_283_))
{
case 0:
{
lean_object* v_it_284_; lean_object* v_out_285_; lean_object* v_map_286_; lean_object* v___f_287_; lean_object* v___x_288_; lean_object* v___x_289_; lean_object* v___x_290_; 
v_it_284_ = lean_ctor_get(v_____do__lift_283_, 0);
lean_inc(v_it_284_);
v_out_285_ = lean_ctor_get(v_____do__lift_283_, 1);
lean_inc(v_out_285_);
lean_dec_ref(v_____do__lift_283_);
v_map_286_ = lean_ctor_get(v_toFunctor_278_, 0);
lean_inc(v_map_286_);
lean_dec_ref(v_toFunctor_278_);
v___f_287_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_287_, 0, v_it_284_);
lean_closure_set(v___f_287_, 1, v_toPure_279_);
v___x_288_ = lean_apply_1(v_f_280_, v_out_285_);
v___x_289_ = lean_apply_4(v_map_286_, lean_box(0), lean_box(0), v___f_281_, v___x_288_);
v___x_290_ = lean_apply_4(v_toBind_282_, lean_box(0), lean_box(0), v___x_289_, v___f_287_);
return v___x_290_;
}
case 1:
{
lean_object* v_it_291_; lean_object* v___x_293_; uint8_t v_isShared_294_; uint8_t v_isSharedCheck_299_; 
lean_dec(v_toBind_282_);
lean_dec_ref(v___f_281_);
lean_dec(v_f_280_);
lean_dec_ref(v_toFunctor_278_);
v_it_291_ = lean_ctor_get(v_____do__lift_283_, 0);
v_isSharedCheck_299_ = !lean_is_exclusive(v_____do__lift_283_);
if (v_isSharedCheck_299_ == 0)
{
v___x_293_ = v_____do__lift_283_;
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
else
{
lean_inc(v_it_291_);
lean_dec(v_____do__lift_283_);
v___x_293_ = lean_box(0);
v_isShared_294_ = v_isSharedCheck_299_;
goto v_resetjp_292_;
}
v_resetjp_292_:
{
lean_object* v___x_296_; 
if (v_isShared_294_ == 0)
{
v___x_296_ = v___x_293_;
goto v_reusejp_295_;
}
else
{
lean_object* v_reuseFailAlloc_298_; 
v_reuseFailAlloc_298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_298_, 0, v_it_291_);
v___x_296_ = v_reuseFailAlloc_298_;
goto v_reusejp_295_;
}
v_reusejp_295_:
{
lean_object* v___x_297_; 
v___x_297_ = lean_apply_2(v_toPure_279_, lean_box(0), v___x_296_);
return v___x_297_;
}
}
}
default: 
{
lean_object* v___x_300_; lean_object* v___x_301_; 
lean_dec(v_toBind_282_);
lean_dec_ref(v___f_281_);
lean_dec(v_f_280_);
lean_dec_ref(v_toFunctor_278_);
v___x_300_ = lean_box(2);
v___x_301_ = lean_apply_2(v_toPure_279_, lean_box(0), v___x_300_);
return v___x_301_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0(lean_object* v_inst_302_, lean_object* v_toPure_303_, lean_object* v___y_304_, lean_object* v_toBind_305_, lean_object* v_f_306_, lean_object* v___f_307_, lean_object* v_inst_308_, lean_object* v_lift_309_, lean_object* v_lift_310_, lean_object* v_it_311_, lean_object* v_acc_312_, lean_object* v_hP_313_, lean_object* v_recur_314_){
_start:
{
lean_object* v_toApplicative_315_; lean_object* v_toBind_316_; lean_object* v_toFunctor_317_; lean_object* v_toPure_318_; lean_object* v___f_319_; lean_object* v___f_320_; lean_object* v___x_321_; lean_object* v___x_322_; lean_object* v___x_323_; lean_object* v___x_324_; 
v_toApplicative_315_ = lean_ctor_get(v_inst_302_, 0);
lean_inc_ref(v_toApplicative_315_);
v_toBind_316_ = lean_ctor_get(v_inst_302_, 1);
lean_inc(v_toBind_316_);
lean_dec_ref(v_inst_302_);
v_toFunctor_317_ = lean_ctor_get(v_toApplicative_315_, 0);
lean_inc_ref(v_toFunctor_317_);
v_toPure_318_ = lean_ctor_get(v_toApplicative_315_, 1);
lean_inc(v_toPure_318_);
lean_dec_ref(v_toApplicative_315_);
v___f_319_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_319_, 0, v_toPure_303_);
lean_closure_set(v___f_319_, 1, v_recur_314_);
lean_closure_set(v___f_319_, 2, v___y_304_);
lean_closure_set(v___f_319_, 3, v_acc_312_);
lean_closure_set(v___f_319_, 4, v_toBind_305_);
lean_inc(v_toBind_316_);
v___f_320_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__4), 6, 5);
lean_closure_set(v___f_320_, 0, v_toFunctor_317_);
lean_closure_set(v___f_320_, 1, v_toPure_318_);
lean_closure_set(v___f_320_, 2, v_f_306_);
lean_closure_set(v___f_320_, 3, v___f_307_);
lean_closure_set(v___f_320_, 4, v_toBind_316_);
v___x_321_ = lean_apply_1(v_inst_308_, v_it_311_);
v___x_322_ = lean_apply_2(v_lift_309_, lean_box(0), v___x_321_);
v___x_323_ = lean_apply_4(v_toBind_316_, lean_box(0), lean_box(0), v___x_322_, v___f_320_);
v___x_324_ = lean_apply_4(v_lift_310_, lean_box(0), lean_box(0), v___f_319_, v___x_323_);
return v___x_324_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__1(lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_f_327_, lean_object* v___f_328_, lean_object* v_inst_329_, lean_object* v_lift_330_, lean_object* v_lift_331_, lean_object* v_00_u03b3_332_, lean_object* v_Pl_333_, lean_object* v_it_334_, lean_object* v_init_335_, lean_object* v___y_336_){
_start:
{
lean_object* v_toApplicative_337_; lean_object* v_toBind_338_; lean_object* v_toPure_339_; lean_object* v___f_340_; lean_object* v___x_341_; 
v_toApplicative_337_ = lean_ctor_get(v_inst_325_, 0);
lean_inc_ref(v_toApplicative_337_);
v_toBind_338_ = lean_ctor_get(v_inst_325_, 1);
lean_inc(v_toBind_338_);
lean_dec_ref(v_inst_325_);
v_toPure_339_ = lean_ctor_get(v_toApplicative_337_, 1);
lean_inc(v_toPure_339_);
lean_dec_ref(v_toApplicative_337_);
v___f_340_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0), 13, 9);
lean_closure_set(v___f_340_, 0, v_inst_326_);
lean_closure_set(v___f_340_, 1, v_toPure_339_);
lean_closure_set(v___f_340_, 2, v___y_336_);
lean_closure_set(v___f_340_, 3, v_toBind_338_);
lean_closure_set(v___f_340_, 4, v_f_327_);
lean_closure_set(v___f_340_, 5, v___f_328_);
lean_closure_set(v___f_340_, 6, v_inst_329_);
lean_closure_set(v___f_340_, 7, v_lift_330_);
lean_closure_set(v___f_340_, 8, v_lift_331_);
v___x_341_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_340_, v_it_334_, v_init_335_, lean_box(0));
return v___x_341_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg(lean_object* v_inst_342_, lean_object* v_inst_343_, lean_object* v_inst_344_, lean_object* v_lift_345_, lean_object* v_f_346_){
_start:
{
lean_object* v___f_347_; lean_object* v___f_348_; 
v___f_347_ = ((lean_object*)(l_Std_Iterators_Types_Map_instIterator___redArg___closed__0));
v___f_348_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__1), 12, 6);
lean_closure_set(v___f_348_, 0, v_inst_343_);
lean_closure_set(v___f_348_, 1, v_inst_342_);
lean_closure_set(v___f_348_, 2, v_f_346_);
lean_closure_set(v___f_348_, 3, v___f_347_);
lean_closure_set(v___f_348_, 4, v_inst_344_);
lean_closure_set(v___f_348_, 5, v_lift_345_);
return v___f_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop(lean_object* v_00_u03b1_349_, lean_object* v_00_u03b2_350_, lean_object* v_00_u03b3_351_, lean_object* v_m_352_, lean_object* v_n_353_, lean_object* v_o_354_, lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_lift_358_, lean_object* v_f_359_){
_start:
{
lean_object* v___x_360_; 
v___x_360_ = l_Std_Iterators_Types_Map_instIteratorLoop___redArg(v_inst_355_, v_inst_356_, v_inst_357_, v_lift_358_, v_f_359_);
return v___x_360_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___redArg(lean_object* v_it_361_){
_start:
{
lean_inc(v_it_361_);
return v_it_361_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___redArg___boxed(lean_object* v_it_362_){
_start:
{
lean_object* v_res_363_; 
v_res_363_ = l_Std_IterM_mapWithPostcondition___redArg(v_it_362_);
lean_dec(v_it_362_);
return v_res_363_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition(lean_object* v_00_u03b1_364_, lean_object* v_00_u03b2_365_, lean_object* v_00_u03b3_366_, lean_object* v_m_367_, lean_object* v_n_368_, lean_object* v_inst_369_, lean_object* v_inst_370_, lean_object* v_inst_371_, lean_object* v_f_372_, lean_object* v_it_373_){
_start:
{
lean_inc(v_it_373_);
return v_it_373_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___boxed(lean_object* v_00_u03b1_374_, lean_object* v_00_u03b2_375_, lean_object* v_00_u03b3_376_, lean_object* v_m_377_, lean_object* v_n_378_, lean_object* v_inst_379_, lean_object* v_inst_380_, lean_object* v_inst_381_, lean_object* v_f_382_, lean_object* v_it_383_){
_start:
{
lean_object* v_res_384_; 
v_res_384_ = l_Std_IterM_mapWithPostcondition(v_00_u03b1_374_, v_00_u03b2_375_, v_00_u03b3_376_, v_m_377_, v_n_378_, v_inst_379_, v_inst_380_, v_inst_381_, v_f_382_, v_it_383_);
lean_dec(v_it_383_);
lean_dec(v_f_382_);
lean_dec(v_inst_381_);
lean_dec(v_inst_380_);
lean_dec_ref(v_inst_379_);
return v_res_384_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___redArg(lean_object* v_it_385_){
_start:
{
lean_inc(v_it_385_);
return v_it_385_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___redArg___boxed(lean_object* v_it_386_){
_start:
{
lean_object* v_res_387_; 
v_res_387_ = l_Std_IterM_filterWithPostcondition___redArg(v_it_386_);
lean_dec(v_it_386_);
return v_res_387_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition(lean_object* v_00_u03b1_388_, lean_object* v_00_u03b2_389_, lean_object* v_m_390_, lean_object* v_n_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_inst_394_, lean_object* v_f_395_, lean_object* v_it_396_){
_start:
{
lean_inc(v_it_396_);
return v_it_396_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___boxed(lean_object* v_00_u03b1_397_, lean_object* v_00_u03b2_398_, lean_object* v_m_399_, lean_object* v_n_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_f_404_, lean_object* v_it_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_IterM_filterWithPostcondition(v_00_u03b1_397_, v_00_u03b2_398_, v_m_399_, v_n_400_, v_inst_401_, v_inst_402_, v_inst_403_, v_f_404_, v_it_405_);
lean_dec(v_it_405_);
lean_dec(v_f_404_);
lean_dec(v_inst_403_);
lean_dec(v_inst_402_);
lean_dec_ref(v_inst_401_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___redArg(lean_object* v_it_407_){
_start:
{
lean_inc(v_it_407_);
return v_it_407_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___redArg___boxed(lean_object* v_it_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_IterM_filterMapM___redArg(v_it_408_);
lean_dec(v_it_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM(lean_object* v_00_u03b1_410_, lean_object* v_00_u03b2_411_, lean_object* v_00_u03b3_412_, lean_object* v_m_413_, lean_object* v_n_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_inst_417_, lean_object* v_inst_418_, lean_object* v_f_419_, lean_object* v_it_420_){
_start:
{
lean_inc(v_it_420_);
return v_it_420_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___boxed(lean_object* v_00_u03b1_421_, lean_object* v_00_u03b2_422_, lean_object* v_00_u03b3_423_, lean_object* v_m_424_, lean_object* v_n_425_, lean_object* v_inst_426_, lean_object* v_inst_427_, lean_object* v_inst_428_, lean_object* v_inst_429_, lean_object* v_f_430_, lean_object* v_it_431_){
_start:
{
lean_object* v_res_432_; 
v_res_432_ = l_Std_IterM_filterMapM(v_00_u03b1_421_, v_00_u03b2_422_, v_00_u03b3_423_, v_m_424_, v_n_425_, v_inst_426_, v_inst_427_, v_inst_428_, v_inst_429_, v_f_430_, v_it_431_);
lean_dec(v_it_431_);
lean_dec(v_f_430_);
lean_dec(v_inst_429_);
lean_dec(v_inst_428_);
lean_dec_ref(v_inst_427_);
lean_dec(v_inst_426_);
return v_res_432_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___redArg(lean_object* v_it_433_){
_start:
{
lean_inc(v_it_433_);
return v_it_433_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___redArg___boxed(lean_object* v_it_434_){
_start:
{
lean_object* v_res_435_; 
v_res_435_ = l_Std_IterM_mapM___redArg(v_it_434_);
lean_dec(v_it_434_);
return v_res_435_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b2_437_, lean_object* v_00_u03b3_438_, lean_object* v_m_439_, lean_object* v_n_440_, lean_object* v_inst_441_, lean_object* v_inst_442_, lean_object* v_inst_443_, lean_object* v_inst_444_, lean_object* v_f_445_, lean_object* v_it_446_){
_start:
{
lean_inc(v_it_446_);
return v_it_446_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___boxed(lean_object* v_00_u03b1_447_, lean_object* v_00_u03b2_448_, lean_object* v_00_u03b3_449_, lean_object* v_m_450_, lean_object* v_n_451_, lean_object* v_inst_452_, lean_object* v_inst_453_, lean_object* v_inst_454_, lean_object* v_inst_455_, lean_object* v_f_456_, lean_object* v_it_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l_Std_IterM_mapM(v_00_u03b1_447_, v_00_u03b2_448_, v_00_u03b3_449_, v_m_450_, v_n_451_, v_inst_452_, v_inst_453_, v_inst_454_, v_inst_455_, v_f_456_, v_it_457_);
lean_dec(v_it_457_);
lean_dec(v_f_456_);
lean_dec(v_inst_455_);
lean_dec(v_inst_454_);
lean_dec_ref(v_inst_453_);
lean_dec(v_inst_452_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___redArg(lean_object* v_it_459_){
_start:
{
lean_inc(v_it_459_);
return v_it_459_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___redArg___boxed(lean_object* v_it_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l_Std_IterM_filterM___redArg(v_it_460_);
lean_dec(v_it_460_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM(lean_object* v_00_u03b1_462_, lean_object* v_00_u03b2_463_, lean_object* v_m_464_, lean_object* v_n_465_, lean_object* v_inst_466_, lean_object* v_inst_467_, lean_object* v_inst_468_, lean_object* v_inst_469_, lean_object* v_f_470_, lean_object* v_it_471_){
_start:
{
lean_inc(v_it_471_);
return v_it_471_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___boxed(lean_object* v_00_u03b1_472_, lean_object* v_00_u03b2_473_, lean_object* v_m_474_, lean_object* v_n_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_inst_478_, lean_object* v_inst_479_, lean_object* v_f_480_, lean_object* v_it_481_){
_start:
{
lean_object* v_res_482_; 
v_res_482_ = l_Std_IterM_filterM(v_00_u03b1_472_, v_00_u03b2_473_, v_m_474_, v_n_475_, v_inst_476_, v_inst_477_, v_inst_478_, v_inst_479_, v_f_480_, v_it_481_);
lean_dec(v_it_481_);
lean_dec(v_f_480_);
lean_dec(v_inst_479_);
lean_dec(v_inst_478_);
lean_dec_ref(v_inst_477_);
lean_dec(v_inst_476_);
return v_res_482_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___redArg(lean_object* v_it_483_){
_start:
{
lean_inc(v_it_483_);
return v_it_483_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___redArg___boxed(lean_object* v_it_484_){
_start:
{
lean_object* v_res_485_; 
v_res_485_ = l_Std_IterM_filterMap___redArg(v_it_484_);
lean_dec(v_it_484_);
return v_res_485_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap(lean_object* v_00_u03b1_486_, lean_object* v_00_u03b2_487_, lean_object* v_00_u03b3_488_, lean_object* v_m_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_f_492_, lean_object* v_it_493_){
_start:
{
lean_inc(v_it_493_);
return v_it_493_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___boxed(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_00_u03b3_496_, lean_object* v_m_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_f_500_, lean_object* v_it_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l_Std_IterM_filterMap(v_00_u03b1_494_, v_00_u03b2_495_, v_00_u03b3_496_, v_m_497_, v_inst_498_, v_inst_499_, v_f_500_, v_it_501_);
lean_dec(v_it_501_);
lean_dec_ref(v_f_500_);
lean_dec_ref(v_inst_499_);
lean_dec(v_inst_498_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___redArg(lean_object* v_it_503_){
_start:
{
lean_inc(v_it_503_);
return v_it_503_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___redArg___boxed(lean_object* v_it_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l_Std_IterM_map___redArg(v_it_504_);
lean_dec(v_it_504_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map(lean_object* v_00_u03b1_506_, lean_object* v_00_u03b2_507_, lean_object* v_00_u03b3_508_, lean_object* v_m_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_f_512_, lean_object* v_it_513_){
_start:
{
lean_inc(v_it_513_);
return v_it_513_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___boxed(lean_object* v_00_u03b1_514_, lean_object* v_00_u03b2_515_, lean_object* v_00_u03b3_516_, lean_object* v_m_517_, lean_object* v_inst_518_, lean_object* v_inst_519_, lean_object* v_f_520_, lean_object* v_it_521_){
_start:
{
lean_object* v_res_522_; 
v_res_522_ = l_Std_IterM_map(v_00_u03b1_514_, v_00_u03b2_515_, v_00_u03b3_516_, v_m_517_, v_inst_518_, v_inst_519_, v_f_520_, v_it_521_);
lean_dec(v_it_521_);
lean_dec(v_f_520_);
lean_dec_ref(v_inst_519_);
lean_dec(v_inst_518_);
return v_res_522_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___redArg(lean_object* v_it_523_){
_start:
{
lean_inc(v_it_523_);
return v_it_523_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___redArg___boxed(lean_object* v_it_524_){
_start:
{
lean_object* v_res_525_; 
v_res_525_ = l_Std_IterM_filter___redArg(v_it_524_);
lean_dec(v_it_524_);
return v_res_525_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b2_527_, lean_object* v_m_528_, lean_object* v_inst_529_, lean_object* v_inst_530_, lean_object* v_f_531_, lean_object* v_it_532_){
_start:
{
lean_inc(v_it_532_);
return v_it_532_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___boxed(lean_object* v_00_u03b1_533_, lean_object* v_00_u03b2_534_, lean_object* v_m_535_, lean_object* v_inst_536_, lean_object* v_inst_537_, lean_object* v_f_538_, lean_object* v_it_539_){
_start:
{
lean_object* v_res_540_; 
v_res_540_ = l_Std_IterM_filter(v_00_u03b1_533_, v_00_u03b2_534_, v_m_535_, v_inst_536_, v_inst_537_, v_f_538_, v_it_539_);
lean_dec(v_it_539_);
lean_dec_ref(v_f_538_);
lean_dec_ref(v_inst_537_);
lean_dec(v_inst_536_);
return v_res_540_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_Iterators_PostconditionMonad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_PropLemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_PostconditionMonad(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_PropLemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(builtin);
}
#ifdef __cplusplus
}
#endif
