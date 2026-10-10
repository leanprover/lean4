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
lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(0);
return v___x_204_;
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_205_;
v_res_205_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___redArg();
stack->m_obj
 = v_res_205_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___redArg();
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(lean_object* v_00_u03b1_208_, lean_object* v_00_u03b2_209_, lean_object* v_00_u03b3_210_, lean_object* v_m_211_, lean_object* v_n_212_, lean_object* v_inst_213_, lean_object* v_inst_214_, lean_object* v_lift_215_, lean_object* v_f_216_, lean_object* v_inst_217_){
_start:
{
lean_object* v___x_218_; 
v___x_218_ = lean_box(0);
return v___x_218_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation___boxed(lean_object* v_00_u03b1_219_, lean_object* v_00_u03b2_220_, lean_object* v_00_u03b3_221_, lean_object* v_m_222_, lean_object* v_n_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_lift_226_, lean_object* v_f_227_, lean_object* v_inst_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_FilterMap_instFinitenessRelation(v_00_u03b1_219_, v_00_u03b2_220_, v_00_u03b3_221_, v_m_222_, v_n_223_, v_inst_224_, v_inst_225_, v_lift_226_, v_f_227_, v_inst_228_);
lean_dec(v_f_227_);
lean_dec(v_lift_226_);
lean_dec(v_inst_225_);
lean_dec_ref(v_inst_224_);
return v_res_229_;
}
}
lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_231_; 
v___x_231_ = lean_box(0);
return v___x_231_;
}
}
LEAN_EXPORT void l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_232_;
v_res_232_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___redArg();
stack->m_obj
 = v_res_232_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_233_){
_start:
{
lean_object* v_res_234_; 
v_res_234_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___redArg();
return v_res_234_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(lean_object* v_00_u03b1_235_, lean_object* v_00_u03b2_236_, lean_object* v_00_u03b3_237_, lean_object* v_m_238_, lean_object* v_n_239_, lean_object* v_inst_240_, lean_object* v_inst_241_, lean_object* v_lift_242_, lean_object* v_f_243_, lean_object* v_inst_244_){
_start:
{
lean_object* v___x_245_; 
v___x_245_ = lean_box(0);
return v___x_245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation___boxed(lean_object* v_00_u03b1_246_, lean_object* v_00_u03b2_247_, lean_object* v_00_u03b3_248_, lean_object* v_m_249_, lean_object* v_n_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_lift_253_, lean_object* v_f_254_, lean_object* v_inst_255_){
_start:
{
lean_object* v_res_256_; 
v_res_256_ = l___private_Init_Data_Iterators_Combinators_Monadic_FilterMap_0__Std_Iterators_Types_Map_instProductivenessRelation(v_00_u03b1_246_, v_00_u03b2_247_, v_00_u03b3_248_, v_m_249_, v_n_250_, v_inst_251_, v_inst_252_, v_lift_253_, v_f_254_, v_inst_255_);
lean_dec(v_f_254_);
lean_dec(v_lift_253_);
lean_dec(v_inst_252_);
lean_dec_ref(v_inst_251_);
return v_res_256_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_257_, lean_object* v_recur_258_, lean_object* v_it_259_, lean_object* v_____do__lift_260_){
_start:
{
if (lean_obj_tag(v_____do__lift_260_) == 0)
{
lean_object* v_a_261_; lean_object* v___x_262_; 
lean_dec(v_it_259_);
lean_dec(v_recur_258_);
v_a_261_ = lean_ctor_get(v_____do__lift_260_, 0);
lean_inc(v_a_261_);
lean_dec_ref_known(v_____do__lift_260_, 1);
v___x_262_ = lean_apply_2(v_toPure_257_, lean_box(0), v_a_261_);
return v___x_262_;
}
else
{
lean_object* v_a_263_; lean_object* v___x_264_; 
lean_dec(v_toPure_257_);
v_a_263_ = lean_ctor_get(v_____do__lift_260_, 0);
lean_inc(v_a_263_);
lean_dec_ref_known(v_____do__lift_260_, 1);
v___x_264_ = lean_apply_4(v_recur_258_, v_it_259_, v_a_263_, lean_box(0), lean_box(0));
return v___x_264_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1(lean_object* v_toPure_265_, lean_object* v_recur_266_, lean_object* v___y_267_, lean_object* v_acc_268_, lean_object* v_toBind_269_, lean_object* v_s_270_){
_start:
{
switch(lean_obj_tag(v_s_270_))
{
case 0:
{
lean_object* v_it_271_; lean_object* v_out_272_; lean_object* v___f_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
v_it_271_ = lean_ctor_get(v_s_270_, 0);
lean_inc(v_it_271_);
v_out_272_ = lean_ctor_get(v_s_270_, 1);
lean_inc(v_out_272_);
lean_dec_ref_known(v_s_270_, 2);
v___f_273_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__0), 4, 3);
lean_closure_set(v___f_273_, 0, v_toPure_265_);
lean_closure_set(v___f_273_, 1, v_recur_266_);
lean_closure_set(v___f_273_, 2, v_it_271_);
v___x_274_ = lean_apply_3(v___y_267_, v_out_272_, lean_box(0), v_acc_268_);
v___x_275_ = lean_apply_4(v_toBind_269_, lean_box(0), lean_box(0), v___x_274_, v___f_273_);
return v___x_275_;
}
case 1:
{
lean_object* v_it_276_; lean_object* v___x_277_; 
lean_dec(v_toBind_269_);
lean_dec(v___y_267_);
lean_dec(v_toPure_265_);
v_it_276_ = lean_ctor_get(v_s_270_, 0);
lean_inc(v_it_276_);
lean_dec_ref_known(v_s_270_, 1);
v___x_277_ = lean_apply_4(v_recur_266_, v_it_276_, v_acc_268_, lean_box(0), lean_box(0));
return v___x_277_;
}
default: 
{
lean_object* v___x_278_; 
lean_dec(v_toBind_269_);
lean_dec(v___y_267_);
lean_dec(v_recur_266_);
v___x_278_ = lean_apply_2(v_toPure_265_, lean_box(0), v_acc_268_);
return v___x_278_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4(lean_object* v_inst_279_, lean_object* v_toPure_280_, lean_object* v___y_281_, lean_object* v_toBind_282_, lean_object* v_f_283_, lean_object* v_inst_284_, lean_object* v_lift_285_, lean_object* v_lift_286_, lean_object* v_it_287_, lean_object* v_acc_288_, lean_object* v_hP_289_, lean_object* v_recur_290_){
_start:
{
lean_object* v_toApplicative_291_; lean_object* v_toBind_292_; lean_object* v_toPure_293_; lean_object* v___f_294_; lean_object* v___f_295_; lean_object* v___x_296_; lean_object* v___x_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_toApplicative_291_ = lean_ctor_get(v_inst_279_, 0);
lean_inc_ref(v_toApplicative_291_);
v_toBind_292_ = lean_ctor_get(v_inst_279_, 1);
lean_inc_n(v_toBind_292_, 2);
lean_dec_ref(v_inst_279_);
v_toPure_293_ = lean_ctor_get(v_toApplicative_291_, 1);
lean_inc(v_toPure_293_);
lean_dec_ref(v_toApplicative_291_);
v___f_294_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_294_, 0, v_toPure_280_);
lean_closure_set(v___f_294_, 1, v_recur_290_);
lean_closure_set(v___f_294_, 2, v___y_281_);
lean_closure_set(v___f_294_, 3, v_acc_288_);
lean_closure_set(v___f_294_, 4, v_toBind_282_);
v___f_295_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIterator___redArg___lam__1), 4, 3);
lean_closure_set(v___f_295_, 0, v_toPure_293_);
lean_closure_set(v___f_295_, 1, v_f_283_);
lean_closure_set(v___f_295_, 2, v_toBind_292_);
v___x_296_ = lean_apply_1(v_inst_284_, v_it_287_);
v___x_297_ = lean_apply_2(v_lift_285_, lean_box(0), v___x_296_);
v___x_298_ = lean_apply_4(v_toBind_292_, lean_box(0), lean_box(0), v___x_297_, v___f_295_);
v___x_299_ = lean_apply_4(v_lift_286_, lean_box(0), lean_box(0), v___f_294_, v___x_298_);
return v___x_299_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2(lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_f_302_, lean_object* v_inst_303_, lean_object* v_lift_304_, lean_object* v_lift_305_, lean_object* v_00_u03b3_306_, lean_object* v_Pl_307_, lean_object* v_it_308_, lean_object* v_init_309_, lean_object* v___y_310_){
_start:
{
lean_object* v_toApplicative_311_; lean_object* v_toBind_312_; lean_object* v_toPure_313_; lean_object* v___f_314_; lean_object* v___x_315_; 
v_toApplicative_311_ = lean_ctor_get(v_inst_300_, 0);
lean_inc_ref(v_toApplicative_311_);
v_toBind_312_ = lean_ctor_get(v_inst_300_, 1);
lean_inc(v_toBind_312_);
lean_dec_ref(v_inst_300_);
v_toPure_313_ = lean_ctor_get(v_toApplicative_311_, 1);
lean_inc(v_toPure_313_);
lean_dec_ref(v_toApplicative_311_);
v___f_314_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__4), 12, 8);
lean_closure_set(v___f_314_, 0, v_inst_301_);
lean_closure_set(v___f_314_, 1, v_toPure_313_);
lean_closure_set(v___f_314_, 2, v___y_310_);
lean_closure_set(v___f_314_, 3, v_toBind_312_);
lean_closure_set(v___f_314_, 4, v_f_302_);
lean_closure_set(v___f_314_, 5, v_inst_303_);
lean_closure_set(v___f_314_, 6, v_lift_304_);
lean_closure_set(v___f_314_, 7, v_lift_305_);
v___x_315_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_314_, v_it_308_, v_init_309_, lean_box(0));
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg(lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_lift_319_, lean_object* v_f_320_){
_start:
{
lean_object* v___f_321_; 
v___f_321_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2), 11, 5);
lean_closure_set(v___f_321_, 0, v_inst_317_);
lean_closure_set(v___f_321_, 1, v_inst_316_);
lean_closure_set(v___f_321_, 2, v_f_320_);
lean_closure_set(v___f_321_, 3, v_inst_318_);
lean_closure_set(v___f_321_, 4, v_lift_319_);
return v___f_321_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_FilterMap_instIteratorLoop(lean_object* v_00_u03b1_322_, lean_object* v_00_u03b2_323_, lean_object* v_00_u03b3_324_, lean_object* v_m_325_, lean_object* v_n_326_, lean_object* v_o_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_lift_331_, lean_object* v_f_332_){
_start:
{
lean_object* v___f_333_; 
v___f_333_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__2), 11, 5);
lean_closure_set(v___f_333_, 0, v_inst_329_);
lean_closure_set(v___f_333_, 1, v_inst_328_);
lean_closure_set(v___f_333_, 2, v_f_332_);
lean_closure_set(v___f_333_, 3, v_inst_330_);
lean_closure_set(v___f_333_, 4, v_lift_331_);
return v___f_333_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__5(lean_object* v_inst_334_, lean_object* v_toPure_335_, lean_object* v___y_336_, lean_object* v_toBind_337_, lean_object* v_inst_338_, lean_object* v_lift_339_, lean_object* v_f_340_, lean_object* v___f_341_, lean_object* v_lift_342_, lean_object* v_it_343_, lean_object* v_acc_344_, lean_object* v_hP_345_, lean_object* v_recur_346_){
_start:
{
lean_object* v_toApplicative_347_; lean_object* v_toBind_348_; lean_object* v_toFunctor_349_; lean_object* v_toPure_350_; lean_object* v___f_351_; lean_object* v___x_352_; lean_object* v___x_353_; lean_object* v___f_354_; lean_object* v___x_355_; lean_object* v___x_356_; 
v_toApplicative_347_ = lean_ctor_get(v_inst_334_, 0);
lean_inc_ref(v_toApplicative_347_);
v_toBind_348_ = lean_ctor_get(v_inst_334_, 1);
lean_inc_n(v_toBind_348_, 2);
lean_dec_ref(v_inst_334_);
v_toFunctor_349_ = lean_ctor_get(v_toApplicative_347_, 0);
lean_inc_ref(v_toFunctor_349_);
v_toPure_350_ = lean_ctor_get(v_toApplicative_347_, 1);
lean_inc(v_toPure_350_);
lean_dec_ref(v_toApplicative_347_);
v___f_351_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_FilterMap_instIteratorLoop___redArg___lam__1), 6, 5);
lean_closure_set(v___f_351_, 0, v_toPure_335_);
lean_closure_set(v___f_351_, 1, v_recur_346_);
lean_closure_set(v___f_351_, 2, v___y_336_);
lean_closure_set(v___f_351_, 3, v_acc_344_);
lean_closure_set(v___f_351_, 4, v_toBind_337_);
v___x_352_ = lean_apply_1(v_inst_338_, v_it_343_);
v___x_353_ = lean_apply_2(v_lift_339_, lean_box(0), v___x_352_);
v___f_354_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___lam__2), 6, 5);
lean_closure_set(v___f_354_, 0, v_toFunctor_349_);
lean_closure_set(v___f_354_, 1, v_toPure_350_);
lean_closure_set(v___f_354_, 2, v_f_340_);
lean_closure_set(v___f_354_, 3, v___f_341_);
lean_closure_set(v___f_354_, 4, v_toBind_348_);
v___x_355_ = lean_apply_4(v_toBind_348_, lean_box(0), lean_box(0), v___x_353_, v___f_354_);
v___x_356_ = lean_apply_4(v_lift_342_, lean_box(0), lean_box(0), v___f_351_, v___x_355_);
return v___x_356_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0(lean_object* v_inst_357_, lean_object* v_inst_358_, lean_object* v_inst_359_, lean_object* v_lift_360_, lean_object* v_f_361_, lean_object* v___f_362_, lean_object* v_lift_363_, lean_object* v_00_u03b3_364_, lean_object* v_Pl_365_, lean_object* v_it_366_, lean_object* v_init_367_, lean_object* v___y_368_){
_start:
{
lean_object* v_toApplicative_369_; lean_object* v_toBind_370_; lean_object* v_toPure_371_; lean_object* v___f_372_; lean_object* v___x_373_; 
v_toApplicative_369_ = lean_ctor_get(v_inst_357_, 0);
lean_inc_ref(v_toApplicative_369_);
v_toBind_370_ = lean_ctor_get(v_inst_357_, 1);
lean_inc(v_toBind_370_);
lean_dec_ref(v_inst_357_);
v_toPure_371_ = lean_ctor_get(v_toApplicative_369_, 1);
lean_inc(v_toPure_371_);
lean_dec_ref(v_toApplicative_369_);
v___f_372_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__5), 13, 9);
lean_closure_set(v___f_372_, 0, v_inst_358_);
lean_closure_set(v___f_372_, 1, v_toPure_371_);
lean_closure_set(v___f_372_, 2, v___y_368_);
lean_closure_set(v___f_372_, 3, v_toBind_370_);
lean_closure_set(v___f_372_, 4, v_inst_359_);
lean_closure_set(v___f_372_, 5, v_lift_360_);
lean_closure_set(v___f_372_, 6, v_f_361_);
lean_closure_set(v___f_372_, 7, v___f_362_);
lean_closure_set(v___f_372_, 8, v_lift_363_);
v___x_373_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_372_, v_it_366_, v_init_367_, lean_box(0));
return v___x_373_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop___redArg(lean_object* v_inst_374_, lean_object* v_inst_375_, lean_object* v_inst_376_, lean_object* v_lift_377_, lean_object* v_f_378_){
_start:
{
lean_object* v___f_379_; lean_object* v___f_380_; 
v___f_379_ = ((lean_object*)(l_Std_Iterators_Types_Map_instIterator___aux__3___redArg___closed__0));
v___f_380_ = lean_alloc_closure((void*)(l_Std_Iterators_Types_Map_instIteratorLoop___redArg___lam__0), 12, 6);
lean_closure_set(v___f_380_, 0, v_inst_375_);
lean_closure_set(v___f_380_, 1, v_inst_374_);
lean_closure_set(v___f_380_, 2, v_inst_376_);
lean_closure_set(v___f_380_, 3, v_lift_377_);
lean_closure_set(v___f_380_, 4, v_f_378_);
lean_closure_set(v___f_380_, 5, v___f_379_);
return v___f_380_;
}
}
LEAN_EXPORT lean_object* l_Std_Iterators_Types_Map_instIteratorLoop(lean_object* v_00_u03b1_381_, lean_object* v_00_u03b2_382_, lean_object* v_00_u03b3_383_, lean_object* v_m_384_, lean_object* v_n_385_, lean_object* v_o_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_lift_390_, lean_object* v_f_391_){
_start:
{
lean_object* v___x_392_; 
v___x_392_ = l_Std_Iterators_Types_Map_instIteratorLoop___redArg(v_inst_387_, v_inst_388_, v_inst_389_, v_lift_390_, v_f_391_);
return v___x_392_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___redArg(lean_object* v_it_393_){
_start:
{
lean_inc(v_it_393_);
return v_it_393_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___redArg___boxed(lean_object* v_it_394_){
_start:
{
lean_object* v_res_395_; 
v_res_395_ = l_Std_IterM_mapWithPostcondition___redArg(v_it_394_);
lean_dec(v_it_394_);
return v_res_395_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition(lean_object* v_00_u03b1_396_, lean_object* v_00_u03b2_397_, lean_object* v_00_u03b3_398_, lean_object* v_m_399_, lean_object* v_n_400_, lean_object* v_inst_401_, lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_f_404_, lean_object* v_it_405_){
_start:
{
lean_inc(v_it_405_);
return v_it_405_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapWithPostcondition___boxed(lean_object* v_00_u03b1_406_, lean_object* v_00_u03b2_407_, lean_object* v_00_u03b3_408_, lean_object* v_m_409_, lean_object* v_n_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_f_414_, lean_object* v_it_415_){
_start:
{
lean_object* v_res_416_; 
v_res_416_ = l_Std_IterM_mapWithPostcondition(v_00_u03b1_406_, v_00_u03b2_407_, v_00_u03b3_408_, v_m_409_, v_n_410_, v_inst_411_, v_inst_412_, v_inst_413_, v_f_414_, v_it_415_);
lean_dec(v_it_415_);
lean_dec(v_f_414_);
lean_dec(v_inst_413_);
lean_dec(v_inst_412_);
lean_dec_ref(v_inst_411_);
return v_res_416_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___redArg(lean_object* v_it_417_){
_start:
{
lean_inc(v_it_417_);
return v_it_417_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___redArg___boxed(lean_object* v_it_418_){
_start:
{
lean_object* v_res_419_; 
v_res_419_ = l_Std_IterM_filterWithPostcondition___redArg(v_it_418_);
lean_dec(v_it_418_);
return v_res_419_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition(lean_object* v_00_u03b1_420_, lean_object* v_00_u03b2_421_, lean_object* v_m_422_, lean_object* v_n_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_f_427_, lean_object* v_it_428_){
_start:
{
lean_inc(v_it_428_);
return v_it_428_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterWithPostcondition___boxed(lean_object* v_00_u03b1_429_, lean_object* v_00_u03b2_430_, lean_object* v_m_431_, lean_object* v_n_432_, lean_object* v_inst_433_, lean_object* v_inst_434_, lean_object* v_inst_435_, lean_object* v_f_436_, lean_object* v_it_437_){
_start:
{
lean_object* v_res_438_; 
v_res_438_ = l_Std_IterM_filterWithPostcondition(v_00_u03b1_429_, v_00_u03b2_430_, v_m_431_, v_n_432_, v_inst_433_, v_inst_434_, v_inst_435_, v_f_436_, v_it_437_);
lean_dec(v_it_437_);
lean_dec(v_f_436_);
lean_dec(v_inst_435_);
lean_dec(v_inst_434_);
lean_dec_ref(v_inst_433_);
return v_res_438_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___redArg(lean_object* v_it_439_){
_start:
{
lean_inc(v_it_439_);
return v_it_439_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___redArg___boxed(lean_object* v_it_440_){
_start:
{
lean_object* v_res_441_; 
v_res_441_ = l_Std_IterM_filterMapM___redArg(v_it_440_);
lean_dec(v_it_440_);
return v_res_441_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM(lean_object* v_00_u03b1_442_, lean_object* v_00_u03b2_443_, lean_object* v_00_u03b3_444_, lean_object* v_m_445_, lean_object* v_n_446_, lean_object* v_inst_447_, lean_object* v_inst_448_, lean_object* v_inst_449_, lean_object* v_inst_450_, lean_object* v_f_451_, lean_object* v_it_452_){
_start:
{
lean_inc(v_it_452_);
return v_it_452_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMapM___boxed(lean_object* v_00_u03b1_453_, lean_object* v_00_u03b2_454_, lean_object* v_00_u03b3_455_, lean_object* v_m_456_, lean_object* v_n_457_, lean_object* v_inst_458_, lean_object* v_inst_459_, lean_object* v_inst_460_, lean_object* v_inst_461_, lean_object* v_f_462_, lean_object* v_it_463_){
_start:
{
lean_object* v_res_464_; 
v_res_464_ = l_Std_IterM_filterMapM(v_00_u03b1_453_, v_00_u03b2_454_, v_00_u03b3_455_, v_m_456_, v_n_457_, v_inst_458_, v_inst_459_, v_inst_460_, v_inst_461_, v_f_462_, v_it_463_);
lean_dec(v_it_463_);
lean_dec(v_f_462_);
lean_dec(v_inst_461_);
lean_dec(v_inst_460_);
lean_dec_ref(v_inst_459_);
lean_dec(v_inst_458_);
return v_res_464_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___redArg(lean_object* v_it_465_){
_start:
{
lean_inc(v_it_465_);
return v_it_465_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___redArg___boxed(lean_object* v_it_466_){
_start:
{
lean_object* v_res_467_; 
v_res_467_ = l_Std_IterM_mapM___redArg(v_it_466_);
lean_dec(v_it_466_);
return v_res_467_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM(lean_object* v_00_u03b1_468_, lean_object* v_00_u03b2_469_, lean_object* v_00_u03b3_470_, lean_object* v_m_471_, lean_object* v_n_472_, lean_object* v_inst_473_, lean_object* v_inst_474_, lean_object* v_inst_475_, lean_object* v_inst_476_, lean_object* v_f_477_, lean_object* v_it_478_){
_start:
{
lean_inc(v_it_478_);
return v_it_478_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_mapM___boxed(lean_object* v_00_u03b1_479_, lean_object* v_00_u03b2_480_, lean_object* v_00_u03b3_481_, lean_object* v_m_482_, lean_object* v_n_483_, lean_object* v_inst_484_, lean_object* v_inst_485_, lean_object* v_inst_486_, lean_object* v_inst_487_, lean_object* v_f_488_, lean_object* v_it_489_){
_start:
{
lean_object* v_res_490_; 
v_res_490_ = l_Std_IterM_mapM(v_00_u03b1_479_, v_00_u03b2_480_, v_00_u03b3_481_, v_m_482_, v_n_483_, v_inst_484_, v_inst_485_, v_inst_486_, v_inst_487_, v_f_488_, v_it_489_);
lean_dec(v_it_489_);
lean_dec(v_f_488_);
lean_dec(v_inst_487_);
lean_dec(v_inst_486_);
lean_dec_ref(v_inst_485_);
lean_dec(v_inst_484_);
return v_res_490_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___redArg(lean_object* v_it_491_){
_start:
{
lean_inc(v_it_491_);
return v_it_491_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___redArg___boxed(lean_object* v_it_492_){
_start:
{
lean_object* v_res_493_; 
v_res_493_ = l_Std_IterM_filterM___redArg(v_it_492_);
lean_dec(v_it_492_);
return v_res_493_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM(lean_object* v_00_u03b1_494_, lean_object* v_00_u03b2_495_, lean_object* v_m_496_, lean_object* v_n_497_, lean_object* v_inst_498_, lean_object* v_inst_499_, lean_object* v_inst_500_, lean_object* v_inst_501_, lean_object* v_f_502_, lean_object* v_it_503_){
_start:
{
lean_inc(v_it_503_);
return v_it_503_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterM___boxed(lean_object* v_00_u03b1_504_, lean_object* v_00_u03b2_505_, lean_object* v_m_506_, lean_object* v_n_507_, lean_object* v_inst_508_, lean_object* v_inst_509_, lean_object* v_inst_510_, lean_object* v_inst_511_, lean_object* v_f_512_, lean_object* v_it_513_){
_start:
{
lean_object* v_res_514_; 
v_res_514_ = l_Std_IterM_filterM(v_00_u03b1_504_, v_00_u03b2_505_, v_m_506_, v_n_507_, v_inst_508_, v_inst_509_, v_inst_510_, v_inst_511_, v_f_512_, v_it_513_);
lean_dec(v_it_513_);
lean_dec(v_f_512_);
lean_dec(v_inst_511_);
lean_dec(v_inst_510_);
lean_dec_ref(v_inst_509_);
lean_dec(v_inst_508_);
return v_res_514_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___redArg(lean_object* v_it_515_){
_start:
{
lean_inc(v_it_515_);
return v_it_515_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___redArg___boxed(lean_object* v_it_516_){
_start:
{
lean_object* v_res_517_; 
v_res_517_ = l_Std_IterM_filterMap___redArg(v_it_516_);
lean_dec(v_it_516_);
return v_res_517_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap(lean_object* v_00_u03b1_518_, lean_object* v_00_u03b2_519_, lean_object* v_00_u03b3_520_, lean_object* v_m_521_, lean_object* v_inst_522_, lean_object* v_inst_523_, lean_object* v_f_524_, lean_object* v_it_525_){
_start:
{
lean_inc(v_it_525_);
return v_it_525_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filterMap___boxed(lean_object* v_00_u03b1_526_, lean_object* v_00_u03b2_527_, lean_object* v_00_u03b3_528_, lean_object* v_m_529_, lean_object* v_inst_530_, lean_object* v_inst_531_, lean_object* v_f_532_, lean_object* v_it_533_){
_start:
{
lean_object* v_res_534_; 
v_res_534_ = l_Std_IterM_filterMap(v_00_u03b1_526_, v_00_u03b2_527_, v_00_u03b3_528_, v_m_529_, v_inst_530_, v_inst_531_, v_f_532_, v_it_533_);
lean_dec(v_it_533_);
lean_dec_ref(v_f_532_);
lean_dec_ref(v_inst_531_);
lean_dec(v_inst_530_);
return v_res_534_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___redArg(lean_object* v_it_535_){
_start:
{
lean_inc(v_it_535_);
return v_it_535_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___redArg___boxed(lean_object* v_it_536_){
_start:
{
lean_object* v_res_537_; 
v_res_537_ = l_Std_IterM_map___redArg(v_it_536_);
lean_dec(v_it_536_);
return v_res_537_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map(lean_object* v_00_u03b1_538_, lean_object* v_00_u03b2_539_, lean_object* v_00_u03b3_540_, lean_object* v_m_541_, lean_object* v_inst_542_, lean_object* v_inst_543_, lean_object* v_f_544_, lean_object* v_it_545_){
_start:
{
lean_inc(v_it_545_);
return v_it_545_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_map___boxed(lean_object* v_00_u03b1_546_, lean_object* v_00_u03b2_547_, lean_object* v_00_u03b3_548_, lean_object* v_m_549_, lean_object* v_inst_550_, lean_object* v_inst_551_, lean_object* v_f_552_, lean_object* v_it_553_){
_start:
{
lean_object* v_res_554_; 
v_res_554_ = l_Std_IterM_map(v_00_u03b1_546_, v_00_u03b2_547_, v_00_u03b3_548_, v_m_549_, v_inst_550_, v_inst_551_, v_f_552_, v_it_553_);
lean_dec(v_it_553_);
lean_dec(v_f_552_);
lean_dec_ref(v_inst_551_);
lean_dec(v_inst_550_);
return v_res_554_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___redArg(lean_object* v_it_555_){
_start:
{
lean_inc(v_it_555_);
return v_it_555_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___redArg___boxed(lean_object* v_it_556_){
_start:
{
lean_object* v_res_557_; 
v_res_557_ = l_Std_IterM_filter___redArg(v_it_556_);
lean_dec(v_it_556_);
return v_res_557_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter(lean_object* v_00_u03b1_558_, lean_object* v_00_u03b2_559_, lean_object* v_m_560_, lean_object* v_inst_561_, lean_object* v_inst_562_, lean_object* v_f_563_, lean_object* v_it_564_){
_start:
{
lean_inc(v_it_564_);
return v_it_564_;
}
}
LEAN_EXPORT lean_object* l_Std_IterM_filter___boxed(lean_object* v_00_u03b1_565_, lean_object* v_00_u03b2_566_, lean_object* v_m_567_, lean_object* v_inst_568_, lean_object* v_inst_569_, lean_object* v_f_570_, lean_object* v_it_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l_Std_IterM_filter(v_00_u03b1_565_, v_00_u03b2_566_, v_m_567_, v_inst_568_, v_inst_569_, v_f_570_, v_it_571_);
lean_dec(v_it_571_);
lean_dec_ref(v_f_570_);
lean_dec_ref(v_inst_569_);
lean_dec(v_inst_568_);
return v_res_572_;
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
