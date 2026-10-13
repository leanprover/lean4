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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___redArg___boxed(lean_object*);
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
lean_dec_ref_known(v_____do__lift_84_, 2);
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
lean_dec_ref_known(v_____do__lift_135_, 2);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(0);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_205_){
_start:
{
lean_object* v_res_206_; 
v_res_206_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___redArg();
return v_res_206_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(lean_object* v_00_u03b1_207_, lean_object* v_00_u03b2_208_, lean_object* v_00_u03b3_209_, lean_object* v_m_210_, lean_object* v_n_211_, lean_object* v_inst_212_, lean_object* v_inst_213_, lean_object* v_lift_214_, lean_object* v_f_215_, lean_object* v_inst_216_){
_start:
{
lean_object* v___x_217_; 
v___x_217_ = lean_box(0);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___boxed(lean_object* v_00_u03b1_218_, lean_object* v_00_u03b2_219_, lean_object* v_00_u03b3_220_, lean_object* v_m_221_, lean_object* v_n_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_lift_225_, lean_object* v_f_226_, lean_object* v_inst_227_){
_start:
{
lean_object* v_res_228_; 
v_res_228_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(v_00_u03b1_218_, v_00_u03b2_219_, v_00_u03b3_220_, v_m_221_, v_n_222_, v_inst_223_, v_inst_224_, v_lift_225_, v_f_226_, v_inst_227_);
lean_dec(v_f_226_);
lean_dec(v_lift_225_);
lean_dec(v_inst_224_);
lean_dec_ref(v_inst_223_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = lean_box(0);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_231_){
_start:
{
lean_object* v_res_232_; 
v_res_232_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___redArg();
return v_res_232_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(lean_object* v_00_u03b1_233_, lean_object* v_00_u03b2_234_, lean_object* v_00_u03b3_235_, lean_object* v_m_236_, lean_object* v_n_237_, lean_object* v_inst_238_, lean_object* v_inst_239_, lean_object* v_lift_240_, lean_object* v_f_241_, lean_object* v_inst_242_){
_start:
{
lean_object* v___x_243_; 
v___x_243_ = lean_box(0);
return v___x_243_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___boxed(lean_object* v_00_u03b1_244_, lean_object* v_00_u03b2_245_, lean_object* v_00_u03b3_246_, lean_object* v_m_247_, lean_object* v_n_248_, lean_object* v_inst_249_, lean_object* v_inst_250_, lean_object* v_lift_251_, lean_object* v_f_252_, lean_object* v_inst_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(v_00_u03b1_244_, v_00_u03b2_245_, v_00_u03b3_246_, v_m_247_, v_n_248_, v_inst_249_, v_inst_250_, v_lift_251_, v_f_252_, v_inst_253_);
lean_dec(v_f_252_);
lean_dec(v_lift_251_);
lean_dec(v_inst_250_);
lean_dec_ref(v_inst_249_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_255_, lean_object* v_recur_256_, lean_object* v_it_257_, lean_object* v_____do__lift_258_){
_start:
{
if (lean_obj_tag(v_____do__lift_258_) == 0)
{
lean_object* v_a_259_; lean_object* v___x_260_; 
lean_dec(v_it_257_);
lean_dec(v_recur_256_);
v_a_259_ = lean_ctor_get(v_____do__lift_258_, 0);
lean_inc(v_a_259_);
lean_dec_ref_known(v_____do__lift_258_, 1);
v___x_260_ = lean_apply_2(v_toPure_255_, lean_box(0), v_a_259_);
return v___x_260_;
}
else
{
lean_object* v_a_261_; lean_object* v___x_262_; 
lean_dec(v_toPure_255_);
v_a_261_ = lean_ctor_get(v_____do__lift_258_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v_____do__lift_258_, 1);
v___x_262_ = lean_apply_4(v_recur_256_, v_it_257_, v_a_261_, lean_box(0), lean_box(0));
return v___x_262_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_263_, lean_object* v_recur_264_, lean_object* v___y_265_, lean_object* v_acc_266_, lean_object* v_toBind_267_, lean_object* v_s_268_){
_start:
{
switch(lean_obj_tag(v_s_268_))
{
case 0:
{
lean_object* v_it_269_; lean_object* v_out_270_; lean_object* v___f_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
v_it_269_ = lean_ctor_get(v_s_268_, 0);
lean_inc(v_it_269_);
v_out_270_ = lean_ctor_get(v_s_268_, 1);
lean_inc(v_out_270_);
lean_dec_ref_known(v_s_268_, 2);
v___f_271_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_271_, 0, v_toPure_263_);
lean_closure_set(v___f_271_, 1, v_recur_264_);
lean_closure_set(v___f_271_, 2, v_it_269_);
v___x_272_ = lean_apply_3(v___y_265_, v_out_270_, lean_box(0), v_acc_266_);
v___x_273_ = lean_apply_4(v_toBind_267_, lean_box(0), lean_box(0), v___x_272_, v___f_271_);
return v___x_273_;
}
case 1:
{
lean_object* v_it_274_; lean_object* v___x_275_; 
lean_dec(v_toBind_267_);
lean_dec(v___y_265_);
lean_dec(v_toPure_263_);
v_it_274_ = lean_ctor_get(v_s_268_, 0);
lean_inc(v_it_274_);
lean_dec_ref_known(v_s_268_, 1);
v___x_275_ = lean_apply_4(v_recur_264_, v_it_274_, v_acc_266_, lean_box(0), lean_box(0));
return v___x_275_;
}
default: 
{
lean_object* v___x_276_; 
lean_dec(v_toBind_267_);
lean_dec(v___y_265_);
lean_dec(v_recur_264_);
v___x_276_ = lean_apply_2(v_toPure_263_, lean_box(0), v_acc_266_);
return v___x_276_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4(lean_object* v_inst_277_, lean_object* v_toPure_278_, lean_object* v___y_279_, lean_object* v_toBind_280_, lean_object* v_f_281_, lean_object* v_inst_282_, lean_object* v_lift_283_, lean_object* v_lift_284_, lean_object* v_it_285_, lean_object* v_acc_286_, lean_object* v_hP_287_, lean_object* v_recur_288_){
_start:
{
lean_object* v_toApplicative_289_; lean_object* v_toBind_290_; lean_object* v_toPure_291_; lean_object* v___f_292_; lean_object* v___f_293_; lean_object* v___x_294_; lean_object* v___x_295_; lean_object* v___x_296_; lean_object* v___x_297_; 
v_toApplicative_289_ = lean_ctor_get(v_inst_277_, 0);
lean_inc_ref(v_toApplicative_289_);
v_toBind_290_ = lean_ctor_get(v_inst_277_, 1);
lean_inc_n(v_toBind_290_, 2);
lean_dec_ref(v_inst_277_);
v_toPure_291_ = lean_ctor_get(v_toApplicative_289_, 1);
lean_inc(v_toPure_291_);
lean_dec_ref(v_toApplicative_289_);
v___f_292_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_292_, 0, v_toPure_278_);
lean_closure_set(v___f_292_, 1, v_recur_288_);
lean_closure_set(v___f_292_, 2, v___y_279_);
lean_closure_set(v___f_292_, 3, v_acc_286_);
lean_closure_set(v___f_292_, 4, v_toBind_280_);
v___f_293_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_293_, 0, v_toPure_291_);
lean_closure_set(v___f_293_, 1, v_f_281_);
lean_closure_set(v___f_293_, 2, v_toBind_290_);
v___x_294_ = lean_apply_1(v_inst_282_, v_it_285_);
v___x_295_ = lean_apply_2(v_lift_283_, lean_box(0), v___x_294_);
v___x_296_ = lean_apply_4(v_toBind_290_, lean_box(0), lean_box(0), v___x_295_, v___f_293_);
v___x_297_ = lean_apply_4(v_lift_284_, lean_box(0), lean_box(0), v___f_292_, v___x_296_);
return v___x_297_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2(lean_object* v_inst_298_, lean_object* v_inst_299_, lean_object* v_f_300_, lean_object* v_inst_301_, lean_object* v_lift_302_, lean_object* v_lift_303_, lean_object* v_00_u03b3_304_, lean_object* v_Pl_305_, lean_object* v_it_306_, lean_object* v_init_307_, lean_object* v___y_308_){
_start:
{
lean_object* v_toApplicative_309_; lean_object* v_toBind_310_; lean_object* v_toPure_311_; lean_object* v___f_312_; lean_object* v___x_313_; 
v_toApplicative_309_ = lean_ctor_get(v_inst_298_, 0);
lean_inc_ref(v_toApplicative_309_);
v_toBind_310_ = lean_ctor_get(v_inst_298_, 1);
lean_inc(v_toBind_310_);
lean_dec_ref(v_inst_298_);
v_toPure_311_ = lean_ctor_get(v_toApplicative_309_, 1);
lean_inc(v_toPure_311_);
lean_dec_ref(v_toApplicative_309_);
v___f_312_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4), 12, 8);
lean_closure_set(v___f_312_, 0, v_inst_299_);
lean_closure_set(v___f_312_, 1, v_toPure_311_);
lean_closure_set(v___f_312_, 2, v___y_308_);
lean_closure_set(v___f_312_, 3, v_toBind_310_);
lean_closure_set(v___f_312_, 4, v_f_300_);
lean_closure_set(v___f_312_, 5, v_inst_301_);
lean_closure_set(v___f_312_, 6, v_lift_302_);
lean_closure_set(v___f_312_, 7, v_lift_303_);
v___x_313_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_312_, v_it_306_, v_init_307_, lean_box(0));
return v___x_313_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg(lean_object* v_inst_314_, lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_lift_317_, lean_object* v_f_318_){
_start:
{
lean_object* v___f_319_; 
v___f_319_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2), 11, 5);
lean_closure_set(v___f_319_, 0, v_inst_315_);
lean_closure_set(v___f_319_, 1, v_inst_314_);
lean_closure_set(v___f_319_, 2, v_f_318_);
lean_closure_set(v___f_319_, 3, v_inst_316_);
lean_closure_set(v___f_319_, 4, v_lift_317_);
return v___f_319_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop(lean_object* v_00_u03b1_320_, lean_object* v_00_u03b2_321_, lean_object* v_00_u03b3_322_, lean_object* v_m_323_, lean_object* v_n_324_, lean_object* v_o_325_, lean_object* v_inst_326_, lean_object* v_inst_327_, lean_object* v_inst_328_, lean_object* v_lift_329_, lean_object* v_f_330_){
_start:
{
lean_object* v___f_331_; 
v___f_331_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2), 11, 5);
lean_closure_set(v___f_331_, 0, v_inst_327_);
lean_closure_set(v___f_331_, 1, v_inst_326_);
lean_closure_set(v___f_331_, 2, v_f_330_);
lean_closure_set(v___f_331_, 3, v_inst_328_);
lean_closure_set(v___f_331_, 4, v_lift_329_);
return v___f_331_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__5(lean_object* v_inst_332_, lean_object* v_toPure_333_, lean_object* v___y_334_, lean_object* v_toBind_335_, lean_object* v_inst_336_, lean_object* v_lift_337_, lean_object* v_f_338_, lean_object* v___f_339_, lean_object* v_lift_340_, lean_object* v_it_341_, lean_object* v_acc_342_, lean_object* v_hP_343_, lean_object* v_recur_344_){
_start:
{
lean_object* v_toApplicative_345_; lean_object* v_toBind_346_; lean_object* v_toFunctor_347_; lean_object* v_toPure_348_; lean_object* v___f_349_; lean_object* v___x_350_; lean_object* v___x_351_; lean_object* v___f_352_; lean_object* v___x_353_; lean_object* v___x_354_; 
v_toApplicative_345_ = lean_ctor_get(v_inst_332_, 0);
lean_inc_ref(v_toApplicative_345_);
v_toBind_346_ = lean_ctor_get(v_inst_332_, 1);
lean_inc_n(v_toBind_346_, 2);
lean_dec_ref(v_inst_332_);
v_toFunctor_347_ = lean_ctor_get(v_toApplicative_345_, 0);
lean_inc_ref(v_toFunctor_347_);
v_toPure_348_ = lean_ctor_get(v_toApplicative_345_, 1);
lean_inc(v_toPure_348_);
lean_dec_ref(v_toApplicative_345_);
v___f_349_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_349_, 0, v_toPure_333_);
lean_closure_set(v___f_349_, 1, v_recur_344_);
lean_closure_set(v___f_349_, 2, v___y_334_);
lean_closure_set(v___f_349_, 3, v_acc_342_);
lean_closure_set(v___f_349_, 4, v_toBind_335_);
v___x_350_ = lean_apply_1(v_inst_336_, v_it_341_);
v___x_351_ = lean_apply_2(v_lift_337_, lean_box(0), v___x_350_);
v___f_352_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2), 6, 5);
lean_closure_set(v___f_352_, 0, v_toFunctor_347_);
lean_closure_set(v___f_352_, 1, v_toPure_348_);
lean_closure_set(v___f_352_, 2, v_f_338_);
lean_closure_set(v___f_352_, 3, v___f_339_);
lean_closure_set(v___f_352_, 4, v_toBind_346_);
v___x_353_ = lean_apply_4(v_toBind_346_, lean_box(0), lean_box(0), v___x_351_, v___f_352_);
v___x_354_ = lean_apply_4(v_lift_340_, lean_box(0), lean_box(0), v___f_349_, v___x_353_);
return v___x_354_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0(lean_object* v_inst_355_, lean_object* v_inst_356_, lean_object* v_inst_357_, lean_object* v_lift_358_, lean_object* v_f_359_, lean_object* v___f_360_, lean_object* v_lift_361_, lean_object* v_00_u03b3_362_, lean_object* v_Pl_363_, lean_object* v_it_364_, lean_object* v_init_365_, lean_object* v___y_366_){
_start:
{
lean_object* v_toApplicative_367_; lean_object* v_toBind_368_; lean_object* v_toPure_369_; lean_object* v___f_370_; lean_object* v___x_371_; 
v_toApplicative_367_ = lean_ctor_get(v_inst_355_, 0);
lean_inc_ref(v_toApplicative_367_);
v_toBind_368_ = lean_ctor_get(v_inst_355_, 1);
lean_inc(v_toBind_368_);
lean_dec_ref(v_inst_355_);
v_toPure_369_ = lean_ctor_get(v_toApplicative_367_, 1);
lean_inc(v_toPure_369_);
lean_dec_ref(v_toApplicative_367_);
v___f_370_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__5), 13, 9);
lean_closure_set(v___f_370_, 0, v_inst_356_);
lean_closure_set(v___f_370_, 1, v_toPure_369_);
lean_closure_set(v___f_370_, 2, v___y_366_);
lean_closure_set(v___f_370_, 3, v_toBind_368_);
lean_closure_set(v___f_370_, 4, v_inst_357_);
lean_closure_set(v___f_370_, 5, v_lift_358_);
lean_closure_set(v___f_370_, 6, v_f_359_);
lean_closure_set(v___f_370_, 7, v___f_360_);
lean_closure_set(v___f_370_, 8, v_lift_361_);
v___x_371_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_370_, v_it_364_, v_init_365_, lean_box(0));
return v___x_371_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg(lean_object* v_inst_372_, lean_object* v_inst_373_, lean_object* v_inst_374_, lean_object* v_lift_375_, lean_object* v_f_376_){
_start:
{
lean_object* v___f_377_; lean_object* v___f_378_; 
v___f_377_ = ((lean_object*)(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0));
v___f_378_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0), 12, 6);
lean_closure_set(v___f_378_, 0, v_inst_373_);
lean_closure_set(v___f_378_, 1, v_inst_372_);
lean_closure_set(v___f_378_, 2, v_inst_374_);
lean_closure_set(v___f_378_, 3, v_lift_375_);
lean_closure_set(v___f_378_, 4, v_f_376_);
lean_closure_set(v___f_378_, 5, v___f_377_);
return v___f_378_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop(lean_object* v_00_u03b1_379_, lean_object* v_00_u03b2_380_, lean_object* v_00_u03b3_381_, lean_object* v_m_382_, lean_object* v_n_383_, lean_object* v_o_384_, lean_object* v_inst_385_, lean_object* v_inst_386_, lean_object* v_inst_387_, lean_object* v_lift_388_, lean_object* v_f_389_){
_start:
{
lean_object* v___x_390_; 
v___x_390_ = l_Std_Iterators_Types_Map_instIteratorLoop___redArg(v_inst_385_, v_inst_386_, v_inst_387_, v_lift_388_, v_f_389_);
return v___x_390_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___redArg(lean_object* v_it_391_){
_start:
{
lean_inc(v_it_391_);
return v_it_391_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___redArg___boxed(lean_object* v_it_392_){
_start:
{
lean_object* v_res_393_; 
v_res_393_ = l_Std_IterM_mapWithPostcondition___redArg(v_it_392_);
lean_dec(v_it_392_);
return v_res_393_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition(lean_object* v_00_u03b1_394_, lean_object* v_00_u03b2_395_, lean_object* v_00_u03b3_396_, lean_object* v_m_397_, lean_object* v_n_398_, lean_object* v_inst_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_f_402_, lean_object* v_it_403_){
_start:
{
lean_inc(v_it_403_);
return v_it_403_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___boxed(lean_object* v_00_u03b1_404_, lean_object* v_00_u03b2_405_, lean_object* v_00_u03b3_406_, lean_object* v_m_407_, lean_object* v_n_408_, lean_object* v_inst_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_f_412_, lean_object* v_it_413_){
_start:
{
lean_object* v_res_414_; 
v_res_414_ = l_Std_IterM_mapWithPostcondition(v_00_u03b1_404_, v_00_u03b2_405_, v_00_u03b3_406_, v_m_407_, v_n_408_, v_inst_409_, v_inst_410_, v_inst_411_, v_f_412_, v_it_413_);
lean_dec(v_it_413_);
lean_dec(v_f_412_);
lean_dec(v_inst_411_);
lean_dec(v_inst_410_);
lean_dec_ref(v_inst_409_);
return v_res_414_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___redArg(lean_object* v_it_415_){
_start:
{
lean_inc(v_it_415_);
return v_it_415_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___redArg___boxed(lean_object* v_it_416_){
_start:
{
lean_object* v_res_417_; 
v_res_417_ = l_Std_IterM_filterWithPostcondition___redArg(v_it_416_);
lean_dec(v_it_416_);
return v_res_417_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition(lean_object* v_00_u03b1_418_, lean_object* v_00_u03b2_419_, lean_object* v_m_420_, lean_object* v_n_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_f_425_, lean_object* v_it_426_){
_start:
{
lean_inc(v_it_426_);
return v_it_426_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___boxed(lean_object* v_00_u03b1_427_, lean_object* v_00_u03b2_428_, lean_object* v_m_429_, lean_object* v_n_430_, lean_object* v_inst_431_, lean_object* v_inst_432_, lean_object* v_inst_433_, lean_object* v_f_434_, lean_object* v_it_435_){
_start:
{
lean_object* v_res_436_; 
v_res_436_ = l_Std_IterM_filterWithPostcondition(v_00_u03b1_427_, v_00_u03b2_428_, v_m_429_, v_n_430_, v_inst_431_, v_inst_432_, v_inst_433_, v_f_434_, v_it_435_);
lean_dec(v_it_435_);
lean_dec(v_f_434_);
lean_dec(v_inst_433_);
lean_dec(v_inst_432_);
lean_dec_ref(v_inst_431_);
return v_res_436_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___redArg(lean_object* v_it_437_){
_start:
{
lean_inc(v_it_437_);
return v_it_437_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___redArg___boxed(lean_object* v_it_438_){
_start:
{
lean_object* v_res_439_; 
v_res_439_ = l_Std_IterM_filterMapM___redArg(v_it_438_);
lean_dec(v_it_438_);
return v_res_439_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b2_441_, lean_object* v_00_u03b3_442_, lean_object* v_m_443_, lean_object* v_n_444_, lean_object* v_inst_445_, lean_object* v_inst_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_f_449_, lean_object* v_it_450_){
_start:
{
lean_inc(v_it_450_);
return v_it_450_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___boxed(lean_object* v_00_u03b1_451_, lean_object* v_00_u03b2_452_, lean_object* v_00_u03b3_453_, lean_object* v_m_454_, lean_object* v_n_455_, lean_object* v_inst_456_, lean_object* v_inst_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_f_460_, lean_object* v_it_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l_Std_IterM_filterMapM(v_00_u03b1_451_, v_00_u03b2_452_, v_00_u03b3_453_, v_m_454_, v_n_455_, v_inst_456_, v_inst_457_, v_inst_458_, v_inst_459_, v_f_460_, v_it_461_);
lean_dec(v_it_461_);
lean_dec(v_f_460_);
lean_dec(v_inst_459_);
lean_dec(v_inst_458_);
lean_dec_ref(v_inst_457_);
lean_dec(v_inst_456_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___redArg(lean_object* v_it_463_){
_start:
{
lean_inc(v_it_463_);
return v_it_463_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___redArg___boxed(lean_object* v_it_464_){
_start:
{
lean_object* v_res_465_; 
v_res_465_ = l_Std_IterM_mapM___redArg(v_it_464_);
lean_dec(v_it_464_);
return v_res_465_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM(lean_object* v_00_u03b1_466_, lean_object* v_00_u03b2_467_, lean_object* v_00_u03b3_468_, lean_object* v_m_469_, lean_object* v_n_470_, lean_object* v_inst_471_, lean_object* v_inst_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_f_475_, lean_object* v_it_476_){
_start:
{
lean_inc(v_it_476_);
return v_it_476_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___boxed(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b2_478_, lean_object* v_00_u03b3_479_, lean_object* v_m_480_, lean_object* v_n_481_, lean_object* v_inst_482_, lean_object* v_inst_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_f_486_, lean_object* v_it_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l_Std_IterM_mapM(v_00_u03b1_477_, v_00_u03b2_478_, v_00_u03b3_479_, v_m_480_, v_n_481_, v_inst_482_, v_inst_483_, v_inst_484_, v_inst_485_, v_f_486_, v_it_487_);
lean_dec(v_it_487_);
lean_dec(v_f_486_);
lean_dec(v_inst_485_);
lean_dec(v_inst_484_);
lean_dec_ref(v_inst_483_);
lean_dec(v_inst_482_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___redArg(lean_object* v_it_489_){
_start:
{
lean_inc(v_it_489_);
return v_it_489_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___redArg___boxed(lean_object* v_it_490_){
_start:
{
lean_object* v_res_491_; 
v_res_491_ = l_Std_IterM_filterM___redArg(v_it_490_);
lean_dec(v_it_490_);
return v_res_491_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM(lean_object* v_00_u03b1_492_, lean_object* v_00_u03b2_493_, lean_object* v_m_494_, lean_object* v_n_495_, lean_object* v_inst_496_, lean_object* v_inst_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_f_500_, lean_object* v_it_501_){
_start:
{
lean_inc(v_it_501_);
return v_it_501_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___boxed(lean_object* v_00_u03b1_502_, lean_object* v_00_u03b2_503_, lean_object* v_m_504_, lean_object* v_n_505_, lean_object* v_inst_506_, lean_object* v_inst_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_f_510_, lean_object* v_it_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l_Std_IterM_filterM(v_00_u03b1_502_, v_00_u03b2_503_, v_m_504_, v_n_505_, v_inst_506_, v_inst_507_, v_inst_508_, v_inst_509_, v_f_510_, v_it_511_);
lean_dec(v_it_511_);
lean_dec(v_f_510_);
lean_dec(v_inst_509_);
lean_dec(v_inst_508_);
lean_dec_ref(v_inst_507_);
lean_dec(v_inst_506_);
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___redArg(lean_object* v_it_513_){
_start:
{
lean_inc(v_it_513_);
return v_it_513_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___redArg___boxed(lean_object* v_it_514_){
_start:
{
lean_object* v_res_515_; 
v_res_515_ = l_Std_IterM_filterMap___redArg(v_it_514_);
lean_dec(v_it_514_);
return v_res_515_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap(lean_object* v_00_u03b1_516_, lean_object* v_00_u03b2_517_, lean_object* v_00_u03b3_518_, lean_object* v_m_519_, lean_object* v_inst_520_, lean_object* v_inst_521_, lean_object* v_f_522_, lean_object* v_it_523_){
_start:
{
lean_inc(v_it_523_);
return v_it_523_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___boxed(lean_object* v_00_u03b1_524_, lean_object* v_00_u03b2_525_, lean_object* v_00_u03b3_526_, lean_object* v_m_527_, lean_object* v_inst_528_, lean_object* v_inst_529_, lean_object* v_f_530_, lean_object* v_it_531_){
_start:
{
lean_object* v_res_532_; 
v_res_532_ = l_Std_IterM_filterMap(v_00_u03b1_524_, v_00_u03b2_525_, v_00_u03b3_526_, v_m_527_, v_inst_528_, v_inst_529_, v_f_530_, v_it_531_);
lean_dec(v_it_531_);
lean_dec_ref(v_f_530_);
lean_dec_ref(v_inst_529_);
lean_dec(v_inst_528_);
return v_res_532_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___redArg(lean_object* v_it_533_){
_start:
{
lean_inc(v_it_533_);
return v_it_533_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___redArg___boxed(lean_object* v_it_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l_Std_IterM_map___redArg(v_it_534_);
lean_dec(v_it_534_);
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map(lean_object* v_00_u03b1_536_, lean_object* v_00_u03b2_537_, lean_object* v_00_u03b3_538_, lean_object* v_m_539_, lean_object* v_inst_540_, lean_object* v_inst_541_, lean_object* v_f_542_, lean_object* v_it_543_){
_start:
{
lean_inc(v_it_543_);
return v_it_543_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___boxed(lean_object* v_00_u03b1_544_, lean_object* v_00_u03b2_545_, lean_object* v_00_u03b3_546_, lean_object* v_m_547_, lean_object* v_inst_548_, lean_object* v_inst_549_, lean_object* v_f_550_, lean_object* v_it_551_){
_start:
{
lean_object* v_res_552_; 
v_res_552_ = l_Std_IterM_map(v_00_u03b1_544_, v_00_u03b2_545_, v_00_u03b3_546_, v_m_547_, v_inst_548_, v_inst_549_, v_f_550_, v_it_551_);
lean_dec(v_it_551_);
lean_dec(v_f_550_);
lean_dec_ref(v_inst_549_);
lean_dec(v_inst_548_);
return v_res_552_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___redArg(lean_object* v_it_553_){
_start:
{
lean_inc(v_it_553_);
return v_it_553_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___redArg___boxed(lean_object* v_it_554_){
_start:
{
lean_object* v_res_555_; 
v_res_555_ = l_Std_IterM_filter___redArg(v_it_554_);
lean_dec(v_it_554_);
return v_res_555_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter(lean_object* v_00_u03b1_556_, lean_object* v_00_u03b2_557_, lean_object* v_m_558_, lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_f_561_, lean_object* v_it_562_){
_start:
{
lean_inc(v_it_562_);
return v_it_562_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___boxed(lean_object* v_00_u03b1_563_, lean_object* v_00_u03b2_564_, lean_object* v_m_565_, lean_object* v_inst_566_, lean_object* v_inst_567_, lean_object* v_f_568_, lean_object* v_it_569_){
_start:
{
lean_object* v_res_570_; 
v_res_570_ = l_Std_IterM_filter(v_00_u03b1_563_, v_00_u03b2_564_, v_m_565_, v_inst_566_, v_inst_567_, v_f_568_, v_it_569_);
lean_dec(v_it_569_);
lean_dec_ref(v_f_568_);
lean_dec_ref(v_inst_567_);
lean_dec(v_inst_566_);
return v_res_570_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_PostconditionMonad(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_PropLemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Iterators_Combinators_Monadic_FilterMap(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
