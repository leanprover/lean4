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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0 = (const lean_object*)&l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___aux__3___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___aux__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__5(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc_n(v_toBind_114_, 2);
lean_dec_ref(v_inst_112_);
v_toPure_115_ = lean_ctor_get(v_toApplicative_113_, 1);
lean_inc(v_toPure_115_);
lean_dec_ref(v_toApplicative_113_);
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
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__0(lean_object* v_a_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_129_, 0, v_a_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2(lean_object* v_toFunctor_130_, lean_object* v_toPure_131_, lean_object* v_f_132_, lean_object* v___f_133_, lean_object* v_toBind_134_, lean_object* v_____do__lift_135_){
_start:
{
switch(lean_obj_tag(v_____do__lift_135_))
{
case 0:
{
lean_object* v_it_136_; lean_object* v_out_137_; lean_object* v_map_138_; lean_object* v___f_139_; lean_object* v___x_140_; lean_object* v___x_141_; lean_object* v___x_142_; 
v_it_136_ = lean_ctor_get(v_____do__lift_135_, 0);
lean_inc(v_it_136_);
v_out_137_ = lean_ctor_get(v_____do__lift_135_, 1);
lean_inc(v_out_137_);
lean_dec_ref(v_____do__lift_135_);
v_map_138_ = lean_ctor_get(v_toFunctor_130_, 0);
lean_inc(v_map_138_);
lean_dec_ref(v_toFunctor_130_);
v___f_139_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__0___boxed), 3, 2);
lean_closure_set(v___f_139_, 0, v_it_136_);
lean_closure_set(v___f_139_, 1, v_toPure_131_);
v___x_140_ = lean_apply_1(v_f_132_, v_out_137_);
v___x_141_ = lean_apply_4(v_map_138_, lean_box(0), lean_box(0), v___f_133_, v___x_140_);
v___x_142_ = lean_apply_4(v_toBind_134_, lean_box(0), lean_box(0), v___x_141_, v___f_139_);
return v___x_142_;
}
case 1:
{
lean_object* v_it_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_151_; 
lean_dec(v_toBind_134_);
lean_dec_ref(v___f_133_);
lean_dec(v_f_132_);
lean_dec_ref(v_toFunctor_130_);
v_it_143_ = lean_ctor_get(v_____do__lift_135_, 0);
v_isSharedCheck_151_ = !lean_is_exclusive(v_____do__lift_135_);
if (v_isSharedCheck_151_ == 0)
{
v___x_145_ = v_____do__lift_135_;
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_it_143_);
lean_dec(v_____do__lift_135_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_151_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_148_; 
if (v_isShared_146_ == 0)
{
v___x_148_ = v___x_145_;
goto v_reusejp_147_;
}
else
{
lean_object* v_reuseFailAlloc_150_; 
v_reuseFailAlloc_150_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_150_, 0, v_it_143_);
v___x_148_ = v_reuseFailAlloc_150_;
goto v_reusejp_147_;
}
v_reusejp_147_:
{
lean_object* v___x_149_; 
v___x_149_ = lean_apply_2(v_toPure_131_, lean_box(0), v___x_148_);
return v___x_149_;
}
}
}
default: 
{
lean_object* v___x_152_; lean_object* v___x_153_; 
lean_dec(v_toBind_134_);
lean_dec_ref(v___f_133_);
lean_dec(v_f_132_);
lean_dec_ref(v_toFunctor_130_);
v___x_152_ = lean_box(2);
v___x_153_ = lean_apply_2(v_toPure_131_, lean_box(0), v___x_152_);
return v___x_153_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___aux__3___redArg(lean_object* v_inst_155_, lean_object* v_inst_156_, lean_object* v_lift_157_, lean_object* v_f_158_, lean_object* v_it_159_){
_start:
{
lean_object* v_toApplicative_160_; lean_object* v_toBind_161_; lean_object* v_toFunctor_162_; lean_object* v_toPure_163_; lean_object* v___f_164_; lean_object* v___x_165_; lean_object* v___x_166_; lean_object* v___f_167_; lean_object* v___x_168_; 
v_toApplicative_160_ = lean_ctor_get(v_inst_155_, 0);
lean_inc_ref(v_toApplicative_160_);
v_toBind_161_ = lean_ctor_get(v_inst_155_, 1);
lean_inc_n(v_toBind_161_, 2);
lean_dec_ref(v_inst_155_);
v_toFunctor_162_ = lean_ctor_get(v_toApplicative_160_, 0);
lean_inc_ref(v_toFunctor_162_);
v_toPure_163_ = lean_ctor_get(v_toApplicative_160_, 1);
lean_inc(v_toPure_163_);
lean_dec_ref(v_toApplicative_160_);
v___f_164_ = ((lean_object*)(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0));
v___x_165_ = lean_apply_1(v_inst_156_, v_it_159_);
v___x_166_ = lean_apply_2(v_lift_157_, lean_box(0), v___x_165_);
v___f_167_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2), 6, 5);
lean_closure_set(v___f_167_, 0, v_toFunctor_162_);
lean_closure_set(v___f_167_, 1, v_toPure_163_);
lean_closure_set(v___f_167_, 2, v_f_158_);
lean_closure_set(v___f_167_, 3, v___f_164_);
lean_closure_set(v___f_167_, 4, v_toBind_161_);
v___x_168_ = lean_apply_4(v_toBind_161_, lean_box(0), lean_box(0), v___x_166_, v___f_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___aux__3(lean_object* v_00_u03b1_169_, lean_object* v_00_u03b2_170_, lean_object* v_00_u03b3_171_, lean_object* v_m_172_, lean_object* v_n_173_, lean_object* v_inst_174_, lean_object* v_inst_175_, lean_object* v_lift_176_, lean_object* v_f_177_, lean_object* v_it_178_){
_start:
{
lean_object* v_toApplicative_179_; lean_object* v_toBind_180_; lean_object* v_toFunctor_181_; lean_object* v_toPure_182_; lean_object* v___f_183_; lean_object* v___x_184_; lean_object* v___x_185_; lean_object* v___f_186_; lean_object* v___x_187_; 
v_toApplicative_179_ = lean_ctor_get(v_inst_174_, 0);
lean_inc_ref(v_toApplicative_179_);
v_toBind_180_ = lean_ctor_get(v_inst_174_, 1);
lean_inc_n(v_toBind_180_, 2);
lean_dec_ref(v_inst_174_);
v_toFunctor_181_ = lean_ctor_get(v_toApplicative_179_, 0);
lean_inc_ref(v_toFunctor_181_);
v_toPure_182_ = lean_ctor_get(v_toApplicative_179_, 1);
lean_inc(v_toPure_182_);
lean_dec_ref(v_toApplicative_179_);
v___f_183_ = ((lean_object*)(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0));
v___x_184_ = lean_apply_1(v_inst_175_, v_it_178_);
v___x_185_ = lean_apply_2(v_lift_176_, lean_box(0), v___x_184_);
v___f_186_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2), 6, 5);
lean_closure_set(v___f_186_, 0, v_toFunctor_181_);
lean_closure_set(v___f_186_, 1, v_toPure_182_);
lean_closure_set(v___f_186_, 2, v_f_177_);
lean_closure_set(v___f_186_, 3, v___f_183_);
lean_closure_set(v___f_186_, 4, v_toBind_180_);
v___x_187_ = lean_apply_4(v_toBind_180_, lean_box(0), lean_box(0), v___x_185_, v___f_186_);
return v___x_187_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator___redArg(lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_lift_190_, lean_object* v_f_191_){
_start:
{
lean_object* v___x_192_; 
v___x_192_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIterator___aux__3), 10, 9);
lean_closure_set(v___x_192_, 0, lean_box(0));
lean_closure_set(v___x_192_, 1, lean_box(0));
lean_closure_set(v___x_192_, 2, lean_box(0));
lean_closure_set(v___x_192_, 3, lean_box(0));
lean_closure_set(v___x_192_, 4, lean_box(0));
lean_closure_set(v___x_192_, 5, v_inst_188_);
lean_closure_set(v___x_192_, 6, v_inst_189_);
lean_closure_set(v___x_192_, 7, v_lift_190_);
lean_closure_set(v___x_192_, 8, v_f_191_);
return v___x_192_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIterator(lean_object* v_00_u03b1_193_, lean_object* v_00_u03b2_194_, lean_object* v_00_u03b3_195_, lean_object* v_m_196_, lean_object* v_n_197_, lean_object* v_inst_198_, lean_object* v_inst_199_, lean_object* v_lift_200_, lean_object* v_f_201_){
_start:
{
lean_object* v___x_202_; 
v___x_202_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIterator___aux__3), 10, 9);
lean_closure_set(v___x_202_, 0, lean_box(0));
lean_closure_set(v___x_202_, 1, lean_box(0));
lean_closure_set(v___x_202_, 2, lean_box(0));
lean_closure_set(v___x_202_, 3, lean_box(0));
lean_closure_set(v___x_202_, 4, lean_box(0));
lean_closure_set(v___x_202_, 5, v_inst_198_);
lean_closure_set(v___x_202_, 6, v_inst_199_);
lean_closure_set(v___x_202_, 7, v_lift_200_);
lean_closure_set(v___x_202_, 8, v_f_201_);
return v___x_202_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(lean_object* v_00_u03b1_203_, lean_object* v_00_u03b2_204_, lean_object* v_00_u03b3_205_, lean_object* v_m_206_, lean_object* v_n_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_lift_210_, lean_object* v_f_211_, lean_object* v_inst_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_box(0);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___boxed(lean_object* v_00_u03b1_214_, lean_object* v_00_u03b2_215_, lean_object* v_00_u03b3_216_, lean_object* v_m_217_, lean_object* v_n_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_lift_221_, lean_object* v_f_222_, lean_object* v_inst_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(v_00_u03b1_214_, v_00_u03b2_215_, v_00_u03b3_216_, v_m_217_, v_n_218_, v_inst_219_, v_inst_220_, v_lift_221_, v_f_222_, v_inst_223_);
lean_dec(v_f_222_);
lean_dec(v_lift_221_);
lean_dec(v_inst_220_);
lean_dec_ref(v_inst_219_);
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(lean_object* v_00_u03b1_225_, lean_object* v_00_u03b2_226_, lean_object* v_00_u03b3_227_, lean_object* v_m_228_, lean_object* v_n_229_, lean_object* v_inst_230_, lean_object* v_inst_231_, lean_object* v_lift_232_, lean_object* v_f_233_, lean_object* v_inst_234_){
_start:
{
lean_object* v___x_235_; 
v___x_235_ = lean_box(0);
return v___x_235_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___boxed(lean_object* v_00_u03b1_236_, lean_object* v_00_u03b2_237_, lean_object* v_00_u03b3_238_, lean_object* v_m_239_, lean_object* v_n_240_, lean_object* v_inst_241_, lean_object* v_inst_242_, lean_object* v_lift_243_, lean_object* v_f_244_, lean_object* v_inst_245_){
_start:
{
lean_object* v_res_246_; 
v_res_246_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(v_00_u03b1_236_, v_00_u03b2_237_, v_00_u03b3_238_, v_m_239_, v_n_240_, v_inst_241_, v_inst_242_, v_lift_243_, v_f_244_, v_inst_245_);
lean_dec(v_f_244_);
lean_dec(v_lift_243_);
lean_dec(v_inst_242_);
lean_dec_ref(v_inst_241_);
return v_res_246_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_247_, lean_object* v_recur_248_, lean_object* v_it_249_, lean_object* v_____do__lift_250_){
_start:
{
if (lean_obj_tag(v_____do__lift_250_) == 0)
{
lean_object* v_a_251_; lean_object* v___x_252_; 
lean_dec(v_it_249_);
lean_dec(v_recur_248_);
v_a_251_ = lean_ctor_get(v_____do__lift_250_, 0);
lean_inc(v_a_251_);
lean_dec_ref(v_____do__lift_250_);
v___x_252_ = lean_apply_2(v_toPure_247_, lean_box(0), v_a_251_);
return v___x_252_;
}
else
{
lean_object* v_a_253_; lean_object* v___x_254_; 
lean_dec(v_toPure_247_);
v_a_253_ = lean_ctor_get(v_____do__lift_250_, 0);
lean_inc(v_a_253_);
lean_dec_ref(v_____do__lift_250_);
v___x_254_ = lean_apply_4(v_recur_248_, v_it_249_, v_a_253_, lean_box(0), lean_box(0));
return v___x_254_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_255_, lean_object* v_recur_256_, lean_object* v___y_257_, lean_object* v_acc_258_, lean_object* v_toBind_259_, lean_object* v_s_260_){
_start:
{
switch(lean_obj_tag(v_s_260_))
{
case 0:
{
lean_object* v_it_261_; lean_object* v_out_262_; lean_object* v___f_263_; lean_object* v___x_264_; lean_object* v___x_265_; 
v_it_261_ = lean_ctor_get(v_s_260_, 0);
lean_inc(v_it_261_);
v_out_262_ = lean_ctor_get(v_s_260_, 1);
lean_inc(v_out_262_);
lean_dec_ref(v_s_260_);
v___f_263_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_263_, 0, v_toPure_255_);
lean_closure_set(v___f_263_, 1, v_recur_256_);
lean_closure_set(v___f_263_, 2, v_it_261_);
v___x_264_ = lean_apply_3(v___y_257_, v_out_262_, lean_box(0), v_acc_258_);
v___x_265_ = lean_apply_4(v_toBind_259_, lean_box(0), lean_box(0), v___x_264_, v___f_263_);
return v___x_265_;
}
case 1:
{
lean_object* v_it_266_; lean_object* v___x_267_; 
lean_dec(v_toBind_259_);
lean_dec(v___y_257_);
lean_dec(v_toPure_255_);
v_it_266_ = lean_ctor_get(v_s_260_, 0);
lean_inc(v_it_266_);
lean_dec_ref(v_s_260_);
v___x_267_ = lean_apply_4(v_recur_256_, v_it_266_, v_acc_258_, lean_box(0), lean_box(0));
return v___x_267_;
}
default: 
{
lean_object* v___x_268_; 
lean_dec(v_toBind_259_);
lean_dec(v___y_257_);
lean_dec(v_recur_256_);
v___x_268_ = lean_apply_2(v_toPure_255_, lean_box(0), v_acc_258_);
return v___x_268_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4(lean_object* v_inst_269_, lean_object* v_toPure_270_, lean_object* v___y_271_, lean_object* v_toBind_272_, lean_object* v_f_273_, lean_object* v_inst_274_, lean_object* v_lift_275_, lean_object* v_lift_276_, lean_object* v_it_277_, lean_object* v_acc_278_, lean_object* v_hP_279_, lean_object* v_recur_280_){
_start:
{
lean_object* v_toApplicative_281_; lean_object* v_toBind_282_; lean_object* v_toPure_283_; lean_object* v___f_284_; lean_object* v___f_285_; lean_object* v___x_286_; lean_object* v___x_287_; lean_object* v___x_288_; lean_object* v___x_289_; 
v_toApplicative_281_ = lean_ctor_get(v_inst_269_, 0);
lean_inc_ref(v_toApplicative_281_);
v_toBind_282_ = lean_ctor_get(v_inst_269_, 1);
lean_inc_n(v_toBind_282_, 2);
lean_dec_ref(v_inst_269_);
v_toPure_283_ = lean_ctor_get(v_toApplicative_281_, 1);
lean_inc(v_toPure_283_);
lean_dec_ref(v_toApplicative_281_);
v___f_284_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_284_, 0, v_toPure_270_);
lean_closure_set(v___f_284_, 1, v_recur_280_);
lean_closure_set(v___f_284_, 2, v___y_271_);
lean_closure_set(v___f_284_, 3, v_acc_278_);
lean_closure_set(v___f_284_, 4, v_toBind_272_);
v___f_285_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_285_, 0, v_toPure_283_);
lean_closure_set(v___f_285_, 1, v_f_273_);
lean_closure_set(v___f_285_, 2, v_toBind_282_);
v___x_286_ = lean_apply_1(v_inst_274_, v_it_277_);
v___x_287_ = lean_apply_2(v_lift_275_, lean_box(0), v___x_286_);
v___x_288_ = lean_apply_4(v_toBind_282_, lean_box(0), lean_box(0), v___x_287_, v___f_285_);
v___x_289_ = lean_apply_4(v_lift_276_, lean_box(0), lean_box(0), v___f_284_, v___x_288_);
return v___x_289_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2(lean_object* v_inst_290_, lean_object* v_inst_291_, lean_object* v_f_292_, lean_object* v_inst_293_, lean_object* v_lift_294_, lean_object* v_lift_295_, lean_object* v_00_u03b3_296_, lean_object* v_Pl_297_, lean_object* v_it_298_, lean_object* v_init_299_, lean_object* v___y_300_){
_start:
{
lean_object* v_toApplicative_301_; lean_object* v_toBind_302_; lean_object* v_toPure_303_; lean_object* v___f_304_; lean_object* v___x_305_; 
v_toApplicative_301_ = lean_ctor_get(v_inst_290_, 0);
lean_inc_ref(v_toApplicative_301_);
v_toBind_302_ = lean_ctor_get(v_inst_290_, 1);
lean_inc(v_toBind_302_);
lean_dec_ref(v_inst_290_);
v_toPure_303_ = lean_ctor_get(v_toApplicative_301_, 1);
lean_inc(v_toPure_303_);
lean_dec_ref(v_toApplicative_301_);
v___f_304_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4), 12, 8);
lean_closure_set(v___f_304_, 0, v_inst_291_);
lean_closure_set(v___f_304_, 1, v_toPure_303_);
lean_closure_set(v___f_304_, 2, v___y_300_);
lean_closure_set(v___f_304_, 3, v_toBind_302_);
lean_closure_set(v___f_304_, 4, v_f_292_);
lean_closure_set(v___f_304_, 5, v_inst_293_);
lean_closure_set(v___f_304_, 6, v_lift_294_);
lean_closure_set(v___f_304_, 7, v_lift_295_);
v___x_305_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_304_, v_it_298_, v_init_299_, lean_box(0));
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg(lean_object* v_inst_306_, lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_lift_309_, lean_object* v_f_310_){
_start:
{
lean_object* v___f_311_; 
v___f_311_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2), 11, 5);
lean_closure_set(v___f_311_, 0, v_inst_307_);
lean_closure_set(v___f_311_, 1, v_inst_306_);
lean_closure_set(v___f_311_, 2, v_f_310_);
lean_closure_set(v___f_311_, 3, v_inst_308_);
lean_closure_set(v___f_311_, 4, v_lift_309_);
return v___f_311_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop(lean_object* v_00_u03b1_312_, lean_object* v_00_u03b2_313_, lean_object* v_00_u03b3_314_, lean_object* v_m_315_, lean_object* v_n_316_, lean_object* v_o_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_inst_320_, lean_object* v_lift_321_, lean_object* v_f_322_){
_start:
{
lean_object* v___f_323_; 
v___f_323_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2), 11, 5);
lean_closure_set(v___f_323_, 0, v_inst_319_);
lean_closure_set(v___f_323_, 1, v_inst_318_);
lean_closure_set(v___f_323_, 2, v_f_322_);
lean_closure_set(v___f_323_, 3, v_inst_320_);
lean_closure_set(v___f_323_, 4, v_lift_321_);
return v___f_323_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__5(lean_object* v_inst_324_, lean_object* v_toPure_325_, lean_object* v___y_326_, lean_object* v_toBind_327_, lean_object* v_inst_328_, lean_object* v_lift_329_, lean_object* v_f_330_, lean_object* v___f_331_, lean_object* v_lift_332_, lean_object* v_it_333_, lean_object* v_acc_334_, lean_object* v_hP_335_, lean_object* v_recur_336_){
_start:
{
lean_object* v_toApplicative_337_; lean_object* v_toBind_338_; lean_object* v_toFunctor_339_; lean_object* v_toPure_340_; lean_object* v___f_341_; lean_object* v___x_342_; lean_object* v___x_343_; lean_object* v___f_344_; lean_object* v___x_345_; lean_object* v___x_346_; 
v_toApplicative_337_ = lean_ctor_get(v_inst_324_, 0);
lean_inc_ref(v_toApplicative_337_);
v_toBind_338_ = lean_ctor_get(v_inst_324_, 1);
lean_inc_n(v_toBind_338_, 2);
lean_dec_ref(v_inst_324_);
v_toFunctor_339_ = lean_ctor_get(v_toApplicative_337_, 0);
lean_inc_ref(v_toFunctor_339_);
v_toPure_340_ = lean_ctor_get(v_toApplicative_337_, 1);
lean_inc(v_toPure_340_);
lean_dec_ref(v_toApplicative_337_);
v___f_341_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_341_, 0, v_toPure_325_);
lean_closure_set(v___f_341_, 1, v_recur_336_);
lean_closure_set(v___f_341_, 2, v___y_326_);
lean_closure_set(v___f_341_, 3, v_acc_334_);
lean_closure_set(v___f_341_, 4, v_toBind_327_);
v___x_342_ = lean_apply_1(v_inst_328_, v_it_333_);
v___x_343_ = lean_apply_2(v_lift_329_, lean_box(0), v___x_342_);
v___f_344_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2), 6, 5);
lean_closure_set(v___f_344_, 0, v_toFunctor_339_);
lean_closure_set(v___f_344_, 1, v_toPure_340_);
lean_closure_set(v___f_344_, 2, v_f_330_);
lean_closure_set(v___f_344_, 3, v___f_331_);
lean_closure_set(v___f_344_, 4, v_toBind_338_);
v___x_345_ = lean_apply_4(v_toBind_338_, lean_box(0), lean_box(0), v___x_343_, v___f_344_);
v___x_346_ = lean_apply_4(v_lift_332_, lean_box(0), lean_box(0), v___f_341_, v___x_345_);
return v___x_346_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0(lean_object* v_inst_347_, lean_object* v_inst_348_, lean_object* v_inst_349_, lean_object* v_lift_350_, lean_object* v_f_351_, lean_object* v___f_352_, lean_object* v_lift_353_, lean_object* v_00_u03b3_354_, lean_object* v_Pl_355_, lean_object* v_it_356_, lean_object* v_init_357_, lean_object* v___y_358_){
_start:
{
lean_object* v_toApplicative_359_; lean_object* v_toBind_360_; lean_object* v_toPure_361_; lean_object* v___f_362_; lean_object* v___x_363_; 
v_toApplicative_359_ = lean_ctor_get(v_inst_347_, 0);
lean_inc_ref(v_toApplicative_359_);
v_toBind_360_ = lean_ctor_get(v_inst_347_, 1);
lean_inc(v_toBind_360_);
lean_dec_ref(v_inst_347_);
v_toPure_361_ = lean_ctor_get(v_toApplicative_359_, 1);
lean_inc(v_toPure_361_);
lean_dec_ref(v_toApplicative_359_);
v___f_362_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__5), 13, 9);
lean_closure_set(v___f_362_, 0, v_inst_348_);
lean_closure_set(v___f_362_, 1, v_toPure_361_);
lean_closure_set(v___f_362_, 2, v___y_358_);
lean_closure_set(v___f_362_, 3, v_toBind_360_);
lean_closure_set(v___f_362_, 4, v_inst_349_);
lean_closure_set(v___f_362_, 5, v_lift_350_);
lean_closure_set(v___f_362_, 6, v_f_351_);
lean_closure_set(v___f_362_, 7, v___f_352_);
lean_closure_set(v___f_362_, 8, v_lift_353_);
v___x_363_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_362_, v_it_356_, v_init_357_, lean_box(0));
return v___x_363_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg(lean_object* v_inst_364_, lean_object* v_inst_365_, lean_object* v_inst_366_, lean_object* v_lift_367_, lean_object* v_f_368_){
_start:
{
lean_object* v___f_369_; lean_object* v___f_370_; 
v___f_369_ = ((lean_object*)(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0));
v___f_370_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0), 12, 6);
lean_closure_set(v___f_370_, 0, v_inst_365_);
lean_closure_set(v___f_370_, 1, v_inst_364_);
lean_closure_set(v___f_370_, 2, v_inst_366_);
lean_closure_set(v___f_370_, 3, v_lift_367_);
lean_closure_set(v___f_370_, 4, v_f_368_);
lean_closure_set(v___f_370_, 5, v___f_369_);
return v___f_370_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop(lean_object* v_00_u03b1_371_, lean_object* v_00_u03b2_372_, lean_object* v_00_u03b3_373_, lean_object* v_m_374_, lean_object* v_n_375_, lean_object* v_o_376_, lean_object* v_inst_377_, lean_object* v_inst_378_, lean_object* v_inst_379_, lean_object* v_lift_380_, lean_object* v_f_381_){
_start:
{
lean_object* v___x_382_; 
v___x_382_ = l_Std_Iterators_Types_Map_instIteratorLoop___redArg(v_inst_377_, v_inst_378_, v_inst_379_, v_lift_380_, v_f_381_);
return v___x_382_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___redArg(lean_object* v_it_383_){
_start:
{
lean_inc(v_it_383_);
return v_it_383_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___redArg___boxed(lean_object* v_it_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l_Std_IterM_mapWithPostcondition___redArg(v_it_384_);
lean_dec(v_it_384_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition(lean_object* v_00_u03b1_386_, lean_object* v_00_u03b2_387_, lean_object* v_00_u03b3_388_, lean_object* v_m_389_, lean_object* v_n_390_, lean_object* v_inst_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_f_394_, lean_object* v_it_395_){
_start:
{
lean_inc(v_it_395_);
return v_it_395_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___boxed(lean_object* v_00_u03b1_396_, lean_object* v_00_u03b2_397_, lean_object* v_00_u03b3_398_, lean_object* v_m_399_, lean_object* v_n_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_f_404_, lean_object* v_it_405_){
_start:
{
lean_object* v_res_406_; 
v_res_406_ = l_Std_IterM_mapWithPostcondition(v_00_u03b1_396_, v_00_u03b2_397_, v_00_u03b3_398_, v_m_399_, v_n_400_, v_inst_401_, v_inst_402_, v_inst_403_, v_f_404_, v_it_405_);
lean_dec(v_it_405_);
lean_dec(v_f_404_);
lean_dec(v_inst_403_);
lean_dec(v_inst_402_);
lean_dec_ref(v_inst_401_);
return v_res_406_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___redArg(lean_object* v_it_407_){
_start:
{
lean_inc(v_it_407_);
return v_it_407_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___redArg___boxed(lean_object* v_it_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_IterM_filterWithPostcondition___redArg(v_it_408_);
lean_dec(v_it_408_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition(lean_object* v_00_u03b1_410_, lean_object* v_00_u03b2_411_, lean_object* v_m_412_, lean_object* v_n_413_, lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_inst_416_, lean_object* v_f_417_, lean_object* v_it_418_){
_start:
{
lean_inc(v_it_418_);
return v_it_418_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___boxed(lean_object* v_00_u03b1_419_, lean_object* v_00_u03b2_420_, lean_object* v_m_421_, lean_object* v_n_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_f_426_, lean_object* v_it_427_){
_start:
{
lean_object* v_res_428_; 
v_res_428_ = l_Std_IterM_filterWithPostcondition(v_00_u03b1_419_, v_00_u03b2_420_, v_m_421_, v_n_422_, v_inst_423_, v_inst_424_, v_inst_425_, v_f_426_, v_it_427_);
lean_dec(v_it_427_);
lean_dec(v_f_426_);
lean_dec(v_inst_425_);
lean_dec(v_inst_424_);
lean_dec_ref(v_inst_423_);
return v_res_428_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___redArg(lean_object* v_it_429_){
_start:
{
lean_inc(v_it_429_);
return v_it_429_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___redArg___boxed(lean_object* v_it_430_){
_start:
{
lean_object* v_res_431_; 
v_res_431_ = l_Std_IterM_filterMapM___redArg(v_it_430_);
lean_dec(v_it_430_);
return v_res_431_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM(lean_object* v_00_u03b1_432_, lean_object* v_00_u03b2_433_, lean_object* v_00_u03b3_434_, lean_object* v_m_435_, lean_object* v_n_436_, lean_object* v_inst_437_, lean_object* v_inst_438_, lean_object* v_inst_439_, lean_object* v_inst_440_, lean_object* v_f_441_, lean_object* v_it_442_){
_start:
{
lean_inc(v_it_442_);
return v_it_442_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___boxed(lean_object* v_00_u03b1_443_, lean_object* v_00_u03b2_444_, lean_object* v_00_u03b3_445_, lean_object* v_m_446_, lean_object* v_n_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_inst_451_, lean_object* v_f_452_, lean_object* v_it_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l_Std_IterM_filterMapM(v_00_u03b1_443_, v_00_u03b2_444_, v_00_u03b3_445_, v_m_446_, v_n_447_, v_inst_448_, v_inst_449_, v_inst_450_, v_inst_451_, v_f_452_, v_it_453_);
lean_dec(v_it_453_);
lean_dec(v_f_452_);
lean_dec(v_inst_451_);
lean_dec(v_inst_450_);
lean_dec_ref(v_inst_449_);
lean_dec(v_inst_448_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___redArg(lean_object* v_it_455_){
_start:
{
lean_inc(v_it_455_);
return v_it_455_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___redArg___boxed(lean_object* v_it_456_){
_start:
{
lean_object* v_res_457_; 
v_res_457_ = l_Std_IterM_mapM___redArg(v_it_456_);
lean_dec(v_it_456_);
return v_res_457_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM(lean_object* v_00_u03b1_458_, lean_object* v_00_u03b2_459_, lean_object* v_00_u03b3_460_, lean_object* v_m_461_, lean_object* v_n_462_, lean_object* v_inst_463_, lean_object* v_inst_464_, lean_object* v_inst_465_, lean_object* v_inst_466_, lean_object* v_f_467_, lean_object* v_it_468_){
_start:
{
lean_inc(v_it_468_);
return v_it_468_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___boxed(lean_object* v_00_u03b1_469_, lean_object* v_00_u03b2_470_, lean_object* v_00_u03b3_471_, lean_object* v_m_472_, lean_object* v_n_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_inst_477_, lean_object* v_f_478_, lean_object* v_it_479_){
_start:
{
lean_object* v_res_480_; 
v_res_480_ = l_Std_IterM_mapM(v_00_u03b1_469_, v_00_u03b2_470_, v_00_u03b3_471_, v_m_472_, v_n_473_, v_inst_474_, v_inst_475_, v_inst_476_, v_inst_477_, v_f_478_, v_it_479_);
lean_dec(v_it_479_);
lean_dec(v_f_478_);
lean_dec(v_inst_477_);
lean_dec(v_inst_476_);
lean_dec_ref(v_inst_475_);
lean_dec(v_inst_474_);
return v_res_480_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___redArg(lean_object* v_it_481_){
_start:
{
lean_inc(v_it_481_);
return v_it_481_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___redArg___boxed(lean_object* v_it_482_){
_start:
{
lean_object* v_res_483_; 
v_res_483_ = l_Std_IterM_filterM___redArg(v_it_482_);
lean_dec(v_it_482_);
return v_res_483_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b2_485_, lean_object* v_m_486_, lean_object* v_n_487_, lean_object* v_inst_488_, lean_object* v_inst_489_, lean_object* v_inst_490_, lean_object* v_inst_491_, lean_object* v_f_492_, lean_object* v_it_493_){
_start:
{
lean_inc(v_it_493_);
return v_it_493_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___boxed(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_m_496_, lean_object* v_n_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_f_502_, lean_object* v_it_503_){
_start:
{
lean_object* v_res_504_; 
v_res_504_ = l_Std_IterM_filterM(v_00_u03b1_494_, v_00_u03b2_495_, v_m_496_, v_n_497_, v_inst_498_, v_inst_499_, v_inst_500_, v_inst_501_, v_f_502_, v_it_503_);
lean_dec(v_it_503_);
lean_dec(v_f_502_);
lean_dec(v_inst_501_);
lean_dec(v_inst_500_);
lean_dec_ref(v_inst_499_);
lean_dec(v_inst_498_);
return v_res_504_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___redArg(lean_object* v_it_505_){
_start:
{
lean_inc(v_it_505_);
return v_it_505_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___redArg___boxed(lean_object* v_it_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l_Std_IterM_filterMap___redArg(v_it_506_);
lean_dec(v_it_506_);
return v_res_507_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_, lean_object* v_00_u03b3_510_, lean_object* v_m_511_, lean_object* v_inst_512_, lean_object* v_inst_513_, lean_object* v_f_514_, lean_object* v_it_515_){
_start:
{
lean_inc(v_it_515_);
return v_it_515_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___boxed(lean_object* v_00_u03b1_516_, lean_object* v_00_u03b2_517_, lean_object* v_00_u03b3_518_, lean_object* v_m_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_f_522_, lean_object* v_it_523_){
_start:
{
lean_object* v_res_524_; 
v_res_524_ = l_Std_IterM_filterMap(v_00_u03b1_516_, v_00_u03b2_517_, v_00_u03b3_518_, v_m_519_, v_inst_520_, v_inst_521_, v_f_522_, v_it_523_);
lean_dec(v_it_523_);
lean_dec_ref(v_f_522_);
lean_dec_ref(v_inst_521_);
lean_dec(v_inst_520_);
return v_res_524_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___redArg(lean_object* v_it_525_){
_start:
{
lean_inc(v_it_525_);
return v_it_525_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___redArg___boxed(lean_object* v_it_526_){
_start:
{
lean_object* v_res_527_; 
v_res_527_ = l_Std_IterM_map___redArg(v_it_526_);
lean_dec(v_it_526_);
return v_res_527_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map(lean_object* v_00_u03b1_528_, lean_object* v_00_u03b2_529_, lean_object* v_00_u03b3_530_, lean_object* v_m_531_, lean_object* v_inst_532_, lean_object* v_inst_533_, lean_object* v_f_534_, lean_object* v_it_535_){
_start:
{
lean_inc(v_it_535_);
return v_it_535_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___boxed(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_00_u03b3_538_, lean_object* v_m_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_f_542_, lean_object* v_it_543_){
_start:
{
lean_object* v_res_544_; 
v_res_544_ = l_Std_IterM_map(v_00_u03b1_536_, v_00_u03b2_537_, v_00_u03b3_538_, v_m_539_, v_inst_540_, v_inst_541_, v_f_542_, v_it_543_);
lean_dec(v_it_543_);
lean_dec(v_f_542_);
lean_dec_ref(v_inst_541_);
lean_dec(v_inst_540_);
return v_res_544_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___redArg(lean_object* v_it_545_){
_start:
{
lean_inc(v_it_545_);
return v_it_545_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___redArg___boxed(lean_object* v_it_546_){
_start:
{
lean_object* v_res_547_; 
v_res_547_ = l_Std_IterM_filter___redArg(v_it_546_);
lean_dec(v_it_546_);
return v_res_547_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter(lean_object* v_00_u03b1_548_, lean_object* v_00_u03b2_549_, lean_object* v_m_550_, lean_object* v_inst_551_, lean_object* v_inst_552_, lean_object* v_f_553_, lean_object* v_it_554_){
_start:
{
lean_inc(v_it_554_);
return v_it_554_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___boxed(lean_object* v_00_u03b1_555_, lean_object* v_00_u03b2_556_, lean_object* v_m_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_f_560_, lean_object* v_it_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_Std_IterM_filter(v_00_u03b1_555_, v_00_u03b2_556_, v_m_557_, v_inst_558_, v_inst_559_, v_f_560_, v_it_561_);
lean_dec(v_it_561_);
lean_dec_ref(v_f_560_);
lean_dec_ref(v_inst_559_);
lean_dec(v_inst_558_);
return v_res_562_;
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
