// Lean compiler output
// Module: Std.Data.DHashMap.Iterator
// Imports: public import Std.Data.Iterators.Producers.Array public import Init.Data.Iterators.Combinators.FlatMap public import Std.Data.DHashMap.Basic public import Std.Data.DHashMap.Internal.AssocList.Iterator import Init.Data.Iterators.Combinators.FilterMap import all Std.Data.DHashMap.Internal.AssocList.Basic import all Std.Data.DHashMap.Internal.Defs import Init.Data.Iterators.Lemmas.Combinators import Init.Data.Iterators.Lemmas.Consumers.Collect import Std.Data.Iterators.Lemmas.Producers.Array import Init.Omega
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
lean_object* lean_array_get_size(lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* lean_array_fget_borrowed(lean_object*, lean_object*);
uint8_t lean_noption_is_some(lean_object*);
lean_object* lean_noption_get(lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorRawIteratorIdSigma___lam__0(lean_object*);
static const lean_closure_object l_Std_DHashMap_Raw_instIteratorRawIteratorIdSigma___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Std_DHashMap_Raw_instIteratorRawIteratorIdSigma___lam__0, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_Std_DHashMap_Raw_instIteratorRawIteratorIdSigma___closed__0 = (const lean_object*)&l_Std_DHashMap_Raw_instIteratorRawIteratorIdSigma___closed__0_value;
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorRawIteratorIdSigma(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_DHashMap_Raw_RawIterator_finitenessRelation(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_iterFrom___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_iterFrom(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_DHashMap_Raw_instIteratorRawIteratorIdSigma_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_DHashMap_Raw_instIteratorRawIteratorIdSigma_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_RawIterator_iterStartImpl(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_RawIterator_iterStartImpl___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_iter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysIter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesIter(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_iter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_iter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_iter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_keysIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_keysIter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_keysIter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_valuesIter___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_valuesIter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_valuesIter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorRawIteratorIdSigma___lam__0(lean_object* v_it_1_){
_start:
{
lean_object* v_map_2_; lean_object* v_pos_3_; lean_object* v___x_5_; uint8_t v_isShared_6_; uint8_t v_isSharedCheck_30_; 
v_map_2_ = lean_ctor_get(v_it_1_, 0);
v_pos_3_ = lean_ctor_get(v_it_1_, 1);
v_isSharedCheck_30_ = !lean_is_exclusive(v_it_1_);
if (v_isSharedCheck_30_ == 0)
{
v___x_5_ = v_it_1_;
v_isShared_6_ = v_isSharedCheck_30_;
goto v_resetjp_4_;
}
else
{
lean_inc(v_pos_3_);
lean_inc(v_map_2_);
lean_dec(v_it_1_);
v___x_5_ = lean_box(0);
v_isShared_6_ = v_isSharedCheck_30_;
goto v_resetjp_4_;
}
v_resetjp_4_:
{
lean_object* v_keyArray_14_; lean_object* v_valueArray_15_; lean_object* v___x_16_; uint8_t v___x_17_; 
v_keyArray_14_ = lean_ctor_get(v_map_2_, 1);
v_valueArray_15_ = lean_ctor_get(v_map_2_, 2);
v___x_16_ = lean_array_get_size(v_keyArray_14_);
v___x_17_ = lean_nat_dec_lt(v_pos_3_, v___x_16_);
if (v___x_17_ == 0)
{
lean_object* v___x_18_; 
lean_del_object(v___x_5_);
lean_dec(v_pos_3_);
lean_dec_ref(v_map_2_);
v___x_18_ = lean_box(2);
return v___x_18_;
}
else
{
lean_object* v___x_19_; uint8_t v_isSome_20_; 
v___x_19_ = lean_array_fget_borrowed(v_keyArray_14_, v_pos_3_);
v_isSome_20_ = lean_noption_is_some(v___x_19_);
if (v_isSome_20_ == 0)
{
goto v___jp_7_;
}
else
{
lean_object* v___x_21_; uint8_t v_isSome_22_; 
v___x_21_ = lean_array_fget_borrowed(v_valueArray_15_, v_pos_3_);
v_isSome_22_ = lean_noption_is_some(v___x_21_);
if (v_isSome_22_ == 0)
{
goto v___jp_7_;
}
else
{
lean_object* v_val_23_; lean_object* v_val_24_; lean_object* v___x_25_; lean_object* v___x_26_; lean_object* v___x_27_; lean_object* v___x_28_; lean_object* v___x_29_; 
lean_del_object(v___x_5_);
lean_inc(v___x_19_);
v_val_23_ = lean_noption_get(v___x_19_);
lean_inc(v___x_21_);
v_val_24_ = lean_noption_get(v___x_21_);
v___x_25_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_25_, 0, v_val_23_);
lean_ctor_set(v___x_25_, 1, v_val_24_);
v___x_26_ = lean_unsigned_to_nat(1u);
v___x_27_ = lean_nat_add(v_pos_3_, v___x_26_);
lean_dec(v_pos_3_);
v___x_28_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_28_, 0, v_map_2_);
lean_ctor_set(v___x_28_, 1, v___x_27_);
v___x_29_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_29_, 0, v___x_28_);
lean_ctor_set(v___x_29_, 1, v___x_25_);
return v___x_29_;
}
}
}
v___jp_7_:
{
lean_object* v___x_8_; lean_object* v___x_9_; lean_object* v___x_11_; 
v___x_8_ = lean_unsigned_to_nat(1u);
v___x_9_ = lean_nat_add(v_pos_3_, v___x_8_);
lean_dec(v_pos_3_);
if (v_isShared_6_ == 0)
{
lean_ctor_set(v___x_5_, 1, v___x_9_);
v___x_11_ = v___x_5_;
goto v_reusejp_10_;
}
else
{
lean_object* v_reuseFailAlloc_13_; 
v_reuseFailAlloc_13_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_13_, 0, v_map_2_);
lean_ctor_set(v_reuseFailAlloc_13_, 1, v___x_9_);
v___x_11_ = v_reuseFailAlloc_13_;
goto v_reusejp_10_;
}
v_reusejp_10_:
{
lean_object* v___x_12_; 
v___x_12_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_12_, 0, v___x_11_);
return v___x_12_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorRawIteratorIdSigma(lean_object* v_00_u03b1_32_, lean_object* v_00_u03b2_33_){
_start:
{
lean_object* v___f_34_; 
v___f_34_ = ((lean_object*)(l_Std_DHashMap_Raw_instIteratorRawIteratorIdSigma___closed__0));
return v___f_34_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_DHashMap_Raw_RawIterator_finitenessRelation(lean_object* v_00_u03b1_35_, lean_object* v_00_u03b2_36_){
_start:
{
lean_object* v___x_37_; 
v___x_37_ = lean_box(0);
return v___x_37_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__0(lean_object* v_toPure_38_, lean_object* v_recur_39_, lean_object* v_it_40_, lean_object* v_____do__lift_41_){
_start:
{
if (lean_obj_tag(v_____do__lift_41_) == 0)
{
lean_object* v_a_42_; lean_object* v___x_43_; 
lean_dec_ref(v_it_40_);
lean_dec(v_recur_39_);
v_a_42_ = lean_ctor_get(v_____do__lift_41_, 0);
lean_inc(v_a_42_);
lean_dec_ref_known(v_____do__lift_41_, 1);
v___x_43_ = lean_apply_2(v_toPure_38_, lean_box(0), v_a_42_);
return v___x_43_;
}
else
{
lean_object* v_a_44_; lean_object* v___x_45_; 
lean_dec(v_toPure_38_);
v_a_44_ = lean_ctor_get(v_____do__lift_41_, 0);
lean_inc(v_a_44_);
lean_dec_ref_known(v_____do__lift_41_, 1);
v___x_45_ = lean_apply_4(v_recur_39_, v_it_40_, v_a_44_, lean_box(0), lean_box(0));
return v___x_45_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__1(lean_object* v_toPure_46_, lean_object* v_recur_47_, lean_object* v___y_48_, lean_object* v_acc_49_, lean_object* v_toBind_50_, lean_object* v_s_51_){
_start:
{
switch(lean_obj_tag(v_s_51_))
{
case 0:
{
lean_object* v_it_52_; lean_object* v_out_53_; lean_object* v___f_54_; lean_object* v___x_55_; lean_object* v___x_56_; 
v_it_52_ = lean_ctor_get(v_s_51_, 0);
lean_inc(v_it_52_);
v_out_53_ = lean_ctor_get(v_s_51_, 1);
lean_inc(v_out_53_);
lean_dec_ref_known(v_s_51_, 2);
v___f_54_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_54_, 0, v_toPure_46_);
lean_closure_set(v___f_54_, 1, v_recur_47_);
lean_closure_set(v___f_54_, 2, v_it_52_);
v___x_55_ = lean_apply_3(v___y_48_, v_out_53_, lean_box(0), v_acc_49_);
v___x_56_ = lean_apply_4(v_toBind_50_, lean_box(0), lean_box(0), v___x_55_, v___f_54_);
return v___x_56_;
}
case 1:
{
lean_object* v_it_57_; lean_object* v___x_58_; 
lean_dec(v_toBind_50_);
lean_dec(v___y_48_);
lean_dec(v_toPure_46_);
v_it_57_ = lean_ctor_get(v_s_51_, 0);
lean_inc(v_it_57_);
lean_dec_ref_known(v_s_51_, 1);
v___x_58_ = lean_apply_4(v_recur_47_, v_it_57_, v_acc_49_, lean_box(0), lean_box(0));
return v___x_58_;
}
default: 
{
lean_object* v___x_59_; 
lean_dec(v_toBind_50_);
lean_dec(v___y_48_);
lean_dec(v_recur_47_);
v___x_59_ = lean_apply_2(v_toPure_46_, lean_box(0), v_acc_49_);
return v___x_59_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__2(lean_object* v_toPure_60_, lean_object* v___y_61_, lean_object* v_toBind_62_, lean_object* v_lift_63_, lean_object* v_it_64_, lean_object* v_acc_65_, lean_object* v_hP_66_, lean_object* v_recur_67_){
_start:
{
lean_object* v_map_68_; lean_object* v_pos_69_; lean_object* v___x_71_; uint8_t v_isShared_72_; uint8_t v_isSharedCheck_100_; 
v_map_68_ = lean_ctor_get(v_it_64_, 0);
v_pos_69_ = lean_ctor_get(v_it_64_, 1);
v_isSharedCheck_100_ = !lean_is_exclusive(v_it_64_);
if (v_isSharedCheck_100_ == 0)
{
v___x_71_ = v_it_64_;
v_isShared_72_ = v_isSharedCheck_100_;
goto v_resetjp_70_;
}
else
{
lean_inc(v_pos_69_);
lean_inc(v_map_68_);
lean_dec(v_it_64_);
v___x_71_ = lean_box(0);
v_isShared_72_ = v_isSharedCheck_100_;
goto v_resetjp_70_;
}
v_resetjp_70_:
{
lean_object* v_keyArray_73_; lean_object* v_valueArray_74_; lean_object* v___f_75_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_keyArray_73_ = lean_ctor_get(v_map_68_, 1);
v_valueArray_74_ = lean_ctor_get(v_map_68_, 2);
v___f_75_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_75_, 0, v_toPure_60_);
lean_closure_set(v___f_75_, 1, v_recur_67_);
lean_closure_set(v___f_75_, 2, v___y_61_);
lean_closure_set(v___f_75_, 3, v_acc_65_);
lean_closure_set(v___f_75_, 4, v_toBind_62_);
v___x_84_ = lean_array_get_size(v_keyArray_73_);
v___x_85_ = lean_nat_dec_lt(v_pos_69_, v___x_84_);
if (v___x_85_ == 0)
{
lean_object* v___x_86_; lean_object* v___x_87_; 
lean_del_object(v___x_71_);
lean_dec(v_pos_69_);
lean_dec_ref(v_map_68_);
v___x_86_ = lean_box(2);
v___x_87_ = lean_apply_4(v_lift_63_, lean_box(0), lean_box(0), v___f_75_, v___x_86_);
return v___x_87_;
}
else
{
lean_object* v___x_88_; uint8_t v_isSome_89_; 
v___x_88_ = lean_array_fget_borrowed(v_keyArray_73_, v_pos_69_);
v_isSome_89_ = lean_noption_is_some(v___x_88_);
if (v_isSome_89_ == 0)
{
goto v___jp_76_;
}
else
{
lean_object* v___x_90_; uint8_t v_isSome_91_; 
v___x_90_ = lean_array_fget_borrowed(v_valueArray_74_, v_pos_69_);
v_isSome_91_ = lean_noption_is_some(v___x_90_);
if (v_isSome_91_ == 0)
{
goto v___jp_76_;
}
else
{
lean_object* v_val_92_; lean_object* v_val_93_; lean_object* v___x_94_; lean_object* v___x_95_; lean_object* v___x_96_; lean_object* v___x_97_; lean_object* v___x_98_; lean_object* v___x_99_; 
lean_del_object(v___x_71_);
lean_inc(v___x_88_);
v_val_92_ = lean_noption_get(v___x_88_);
lean_inc(v___x_90_);
v_val_93_ = lean_noption_get(v___x_90_);
v___x_94_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_94_, 0, v_val_92_);
lean_ctor_set(v___x_94_, 1, v_val_93_);
v___x_95_ = lean_unsigned_to_nat(1u);
v___x_96_ = lean_nat_add(v_pos_69_, v___x_95_);
lean_dec(v_pos_69_);
v___x_97_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_97_, 0, v_map_68_);
lean_ctor_set(v___x_97_, 1, v___x_96_);
v___x_98_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_98_, 0, v___x_97_);
lean_ctor_set(v___x_98_, 1, v___x_94_);
v___x_99_ = lean_apply_4(v_lift_63_, lean_box(0), lean_box(0), v___f_75_, v___x_98_);
return v___x_99_;
}
}
}
v___jp_76_:
{
lean_object* v___x_77_; lean_object* v___x_78_; lean_object* v___x_80_; 
v___x_77_ = lean_unsigned_to_nat(1u);
v___x_78_ = lean_nat_add(v_pos_69_, v___x_77_);
lean_dec(v_pos_69_);
if (v_isShared_72_ == 0)
{
lean_ctor_set(v___x_71_, 1, v___x_78_);
v___x_80_ = v___x_71_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_83_; 
v_reuseFailAlloc_83_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_83_, 0, v_map_68_);
lean_ctor_set(v_reuseFailAlloc_83_, 1, v___x_78_);
v___x_80_ = v_reuseFailAlloc_83_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
lean_object* v___x_81_; lean_object* v___x_82_; 
v___x_81_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_81_, 0, v___x_80_);
v___x_82_ = lean_apply_4(v_lift_63_, lean_box(0), lean_box(0), v___f_75_, v___x_81_);
return v___x_82_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__3(lean_object* v_inst_101_, lean_object* v_lift_102_, lean_object* v_00_u03b3_103_, lean_object* v_Pl_104_, lean_object* v_it_105_, lean_object* v_init_106_, lean_object* v___y_107_){
_start:
{
lean_object* v_toApplicative_108_; lean_object* v_toBind_109_; lean_object* v_toPure_110_; lean_object* v___f_111_; lean_object* v___x_112_; 
v_toApplicative_108_ = lean_ctor_get(v_inst_101_, 0);
lean_inc_ref(v_toApplicative_108_);
v_toBind_109_ = lean_ctor_get(v_inst_101_, 1);
lean_inc(v_toBind_109_);
lean_dec_ref(v_inst_101_);
v_toPure_110_ = lean_ctor_get(v_toApplicative_108_, 1);
lean_inc(v_toPure_110_);
lean_dec_ref(v_toApplicative_108_);
v___f_111_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__2), 8, 4);
lean_closure_set(v___f_111_, 0, v_toPure_110_);
lean_closure_set(v___f_111_, 1, v___y_107_);
lean_closure_set(v___f_111_, 2, v_toBind_109_);
lean_closure_set(v___f_111_, 3, v_lift_102_);
v___x_112_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_111_, v_it_105_, v_init_106_, lean_box(0));
return v___x_112_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg(lean_object* v_inst_113_){
_start:
{
lean_object* v___f_114_; 
v___f_114_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_114_, 0, v_inst_113_);
return v___f_114_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad(lean_object* v_00_u03b1_115_, lean_object* v_00_u03b2_116_, lean_object* v_m_117_, lean_object* v_inst_118_){
_start:
{
lean_object* v___f_119_; 
v___f_119_ = lean_alloc_closure((void*)(l_Std_DHashMap_Raw_instIteratorLoopRawIteratorIdSigmaOfMonad___redArg___lam__3), 7, 1);
lean_closure_set(v___f_119_, 0, v_inst_118_);
return v___f_119_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_iterFrom___redArg(lean_object* v_m_120_, lean_object* v_pos_121_){
_start:
{
lean_object* v___x_122_; 
v___x_122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_122_, 0, v_m_120_);
lean_ctor_set(v___x_122_, 1, v_pos_121_);
return v___x_122_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_iterFrom(lean_object* v_00_u03b1_123_, lean_object* v_00_u03b2_124_, lean_object* v_m_125_, lean_object* v_pos_126_){
_start:
{
lean_object* v___x_127_; 
v___x_127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_127_, 0, v_m_125_);
lean_ctor_set(v___x_127_, 1, v_pos_126_);
return v___x_127_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_DHashMap_Raw_instIteratorRawIteratorIdSigma_match__3_splitter___redArg(lean_object* v_x_128_, lean_object* v_h__1_129_, lean_object* v_h__2_130_){
_start:
{
if (lean_obj_tag(v_x_128_) == 0)
{
lean_object* v___x_131_; lean_object* v___x_132_; 
lean_dec(v_h__2_130_);
v___x_131_ = lean_box(0);
v___x_132_ = lean_apply_1(v_h__1_129_, v___x_131_);
return v___x_132_;
}
else
{
lean_object* v_val_133_; lean_object* v___x_134_; 
lean_dec(v_h__1_129_);
v_val_133_ = lean_ctor_get(v_x_128_, 0);
lean_inc(v_val_133_);
lean_dec_ref_known(v_x_128_, 1);
v___x_134_ = lean_apply_1(v_h__2_130_, v_val_133_);
return v___x_134_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_DHashMap_Raw_instIteratorRawIteratorIdSigma_match__3_splitter(lean_object* v_00_u03b1_135_, lean_object* v_00_u03b2_136_, lean_object* v_motive_137_, lean_object* v_x_138_, lean_object* v_h__1_139_, lean_object* v_h__2_140_){
_start:
{
if (lean_obj_tag(v_x_138_) == 0)
{
lean_object* v___x_141_; lean_object* v___x_142_; 
lean_dec(v_h__2_140_);
v___x_141_ = lean_box(0);
v___x_142_ = lean_apply_1(v_h__1_139_, v___x_141_);
return v___x_142_;
}
else
{
lean_object* v_val_143_; lean_object* v___x_144_; 
lean_dec(v_h__1_139_);
v_val_143_ = lean_ctor_get(v_x_138_, 0);
lean_inc(v_val_143_);
lean_dec_ref_known(v_x_138_, 1);
v___x_144_ = lean_apply_1(v_h__2_140_, v_val_143_);
return v___x_144_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_Iter_toArray__eq__match__step_match__1_splitter___redArg(lean_object* v_x_145_, lean_object* v_h__1_146_, lean_object* v_h__2_147_, lean_object* v_h__3_148_){
_start:
{
switch(lean_obj_tag(v_x_145_))
{
case 0:
{
lean_object* v_it_149_; lean_object* v_out_150_; lean_object* v___x_151_; 
lean_dec(v_h__3_148_);
lean_dec(v_h__2_147_);
v_it_149_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_it_149_);
v_out_150_ = lean_ctor_get(v_x_145_, 1);
lean_inc(v_out_150_);
lean_dec_ref_known(v_x_145_, 2);
v___x_151_ = lean_apply_2(v_h__1_146_, v_it_149_, v_out_150_);
return v___x_151_;
}
case 1:
{
lean_object* v_it_152_; lean_object* v___x_153_; 
lean_dec(v_h__3_148_);
lean_dec(v_h__1_146_);
v_it_152_ = lean_ctor_get(v_x_145_, 0);
lean_inc(v_it_152_);
lean_dec_ref_known(v_x_145_, 1);
v___x_153_ = lean_apply_1(v_h__2_147_, v_it_152_);
return v___x_153_;
}
default: 
{
lean_object* v___x_154_; lean_object* v___x_155_; 
lean_dec(v_h__2_147_);
lean_dec(v_h__1_146_);
v___x_154_ = lean_box(0);
v___x_155_ = lean_apply_1(v_h__3_148_, v___x_154_);
return v___x_155_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_Iter_toArray__eq__match__step_match__1_splitter(lean_object* v_00_u03b1_156_, lean_object* v_00_u03b2_157_, lean_object* v_motive_158_, lean_object* v_x_159_, lean_object* v_h__1_160_, lean_object* v_h__2_161_, lean_object* v_h__3_162_){
_start:
{
switch(lean_obj_tag(v_x_159_))
{
case 0:
{
lean_object* v_it_163_; lean_object* v_out_164_; lean_object* v___x_165_; 
lean_dec(v_h__3_162_);
lean_dec(v_h__2_161_);
v_it_163_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_it_163_);
v_out_164_ = lean_ctor_get(v_x_159_, 1);
lean_inc(v_out_164_);
lean_dec_ref_known(v_x_159_, 2);
v___x_165_ = lean_apply_2(v_h__1_160_, v_it_163_, v_out_164_);
return v___x_165_;
}
case 1:
{
lean_object* v_it_166_; lean_object* v___x_167_; 
lean_dec(v_h__3_162_);
lean_dec(v_h__1_160_);
v_it_166_ = lean_ctor_get(v_x_159_, 0);
lean_inc(v_it_166_);
lean_dec_ref_known(v_x_159_, 1);
v___x_167_ = lean_apply_1(v_h__2_161_, v_it_166_);
return v___x_167_;
}
default: 
{
lean_object* v___x_168_; lean_object* v___x_169_; 
lean_dec(v_h__2_161_);
lean_dec(v_h__1_160_);
v___x_168_ = lean_box(0);
v___x_169_ = lean_apply_1(v_h__3_162_, v___x_168_);
return v___x_169_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_RawIterator_iterStartImpl(lean_object* v_00_u03b1_170_, lean_object* v_00_u03b2_171_, lean_object* v___m_172_){
_start:
{
lean_object* v___x_173_; 
v___x_173_ = lean_unsigned_to_nat(0u);
return v___x_173_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_RawIterator_iterStartImpl___boxed(lean_object* v_00_u03b1_174_, lean_object* v_00_u03b2_175_, lean_object* v___m_176_){
_start:
{
lean_object* v_res_177_; 
v_res_177_ = l_Std_DHashMap_Raw_RawIterator_iterStartImpl(v_00_u03b1_174_, v_00_u03b2_175_, v___m_176_);
lean_dec_ref(v___m_176_);
return v_res_177_;
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter___redArg(lean_object* v_x_178_, lean_object* v_h__1_179_, lean_object* v_h__2_180_){
_start:
{
if (lean_obj_tag(v_x_178_) == 0)
{
lean_object* v___x_181_; lean_object* v___x_182_; 
lean_dec(v_h__2_180_);
v___x_181_ = lean_box(0);
v___x_182_ = lean_apply_1(v_h__1_179_, v___x_181_);
return v___x_182_;
}
else
{
lean_object* v_key_183_; lean_object* v_value_184_; lean_object* v_tail_185_; lean_object* v___x_186_; 
lean_dec(v_h__1_179_);
v_key_183_ = lean_ctor_get(v_x_178_, 0);
lean_inc(v_key_183_);
v_value_184_ = lean_ctor_get(v_x_178_, 1);
lean_inc(v_value_184_);
v_tail_185_ = lean_ctor_get(v_x_178_, 2);
lean_inc(v_tail_185_);
lean_dec_ref_known(v_x_178_, 3);
v___x_186_ = lean_apply_3(v_h__2_180_, v_key_183_, v_value_184_, v_tail_185_);
return v___x_186_;
}
}
}
LEAN_EXPORT lean_object* l___private_Std_Data_DHashMap_Iterator_0__Std_DHashMap_Internal_AssocList_toList_match__1_splitter(lean_object* v_00_u03b1_187_, lean_object* v_00_u03b2_188_, lean_object* v_motive_189_, lean_object* v_x_190_, lean_object* v_h__1_191_, lean_object* v_h__2_192_){
_start:
{
if (lean_obj_tag(v_x_190_) == 0)
{
lean_object* v___x_193_; lean_object* v___x_194_; 
lean_dec(v_h__2_192_);
v___x_193_ = lean_box(0);
v___x_194_ = lean_apply_1(v_h__1_191_, v___x_193_);
return v___x_194_;
}
else
{
lean_object* v_key_195_; lean_object* v_value_196_; lean_object* v_tail_197_; lean_object* v___x_198_; 
lean_dec(v_h__1_191_);
v_key_195_ = lean_ctor_get(v_x_190_, 0);
lean_inc(v_key_195_);
v_value_196_ = lean_ctor_get(v_x_190_, 1);
lean_inc(v_value_196_);
v_tail_197_ = lean_ctor_get(v_x_190_, 2);
lean_inc(v_tail_197_);
lean_dec_ref_known(v_x_190_, 3);
v___x_198_ = lean_apply_3(v_h__2_192_, v_key_195_, v_value_196_, v_tail_197_);
return v___x_198_;
}
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_iter___redArg(lean_object* v_m_199_){
_start:
{
lean_object* v___x_200_; lean_object* v___x_201_; 
v___x_200_ = lean_unsigned_to_nat(0u);
v___x_201_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_201_, 0, v_m_199_);
lean_ctor_set(v___x_201_, 1, v___x_200_);
return v___x_201_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_iter(lean_object* v_00_u03b1_202_, lean_object* v_00_u03b2_203_, lean_object* v_m_204_){
_start:
{
lean_object* v___x_205_; lean_object* v___x_206_; 
v___x_205_ = lean_unsigned_to_nat(0u);
v___x_206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_206_, 0, v_m_204_);
lean_ctor_set(v___x_206_, 1, v___x_205_);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysIter___redArg(lean_object* v_m_207_){
_start:
{
lean_object* v___x_208_; lean_object* v___x_209_; 
v___x_208_ = lean_unsigned_to_nat(0u);
v___x_209_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_209_, 0, v_m_207_);
lean_ctor_set(v___x_209_, 1, v___x_208_);
return v___x_209_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_keysIter(lean_object* v_00_u03b1_210_, lean_object* v_00_u03b2_211_, lean_object* v_m_212_){
_start:
{
lean_object* v___x_213_; lean_object* v___x_214_; 
v___x_213_ = lean_unsigned_to_nat(0u);
v___x_214_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_214_, 0, v_m_212_);
lean_ctor_set(v___x_214_, 1, v___x_213_);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesIter___redArg(lean_object* v_m_215_){
_start:
{
lean_object* v___x_216_; lean_object* v___x_217_; 
v___x_216_ = lean_unsigned_to_nat(0u);
v___x_217_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_217_, 0, v_m_215_);
lean_ctor_set(v___x_217_, 1, v___x_216_);
return v___x_217_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_Raw_valuesIter(lean_object* v_00_u03b1_218_, lean_object* v_00_u03b2_219_, lean_object* v_m_220_){
_start:
{
lean_object* v___x_221_; lean_object* v___x_222_; 
v___x_221_ = lean_unsigned_to_nat(0u);
v___x_222_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_222_, 0, v_m_220_);
lean_ctor_set(v___x_222_, 1, v___x_221_);
return v___x_222_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_iter___redArg(lean_object* v_m_223_){
_start:
{
lean_object* v___x_224_; lean_object* v___x_225_; 
v___x_224_ = lean_unsigned_to_nat(0u);
v___x_225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_225_, 0, v_m_223_);
lean_ctor_set(v___x_225_, 1, v___x_224_);
return v___x_225_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_iter(lean_object* v_00_u03b1_226_, lean_object* v_00_u03b2_227_, lean_object* v_inst_228_, lean_object* v_inst_229_, lean_object* v_m_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_unsigned_to_nat(0u);
v___x_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_232_, 0, v_m_230_);
lean_ctor_set(v___x_232_, 1, v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_iter___boxed(lean_object* v_00_u03b1_233_, lean_object* v_00_u03b2_234_, lean_object* v_inst_235_, lean_object* v_inst_236_, lean_object* v_m_237_){
_start:
{
lean_object* v_res_238_; 
v_res_238_ = l_Std_DHashMap_iter(v_00_u03b1_233_, v_00_u03b2_234_, v_inst_235_, v_inst_236_, v_m_237_);
lean_dec_ref(v_inst_236_);
lean_dec_ref(v_inst_235_);
return v_res_238_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_keysIter___redArg(lean_object* v_m_239_){
_start:
{
lean_object* v___x_240_; lean_object* v___x_241_; 
v___x_240_ = lean_unsigned_to_nat(0u);
v___x_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_241_, 0, v_m_239_);
lean_ctor_set(v___x_241_, 1, v___x_240_);
return v___x_241_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_keysIter(lean_object* v_00_u03b1_242_, lean_object* v_00_u03b2_243_, lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_m_246_){
_start:
{
lean_object* v___x_247_; lean_object* v___x_248_; 
v___x_247_ = lean_unsigned_to_nat(0u);
v___x_248_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_248_, 0, v_m_246_);
lean_ctor_set(v___x_248_, 1, v___x_247_);
return v___x_248_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_keysIter___boxed(lean_object* v_00_u03b1_249_, lean_object* v_00_u03b2_250_, lean_object* v_inst_251_, lean_object* v_inst_252_, lean_object* v_m_253_){
_start:
{
lean_object* v_res_254_; 
v_res_254_ = l_Std_DHashMap_keysIter(v_00_u03b1_249_, v_00_u03b2_250_, v_inst_251_, v_inst_252_, v_m_253_);
lean_dec_ref(v_inst_252_);
lean_dec_ref(v_inst_251_);
return v_res_254_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_valuesIter___redArg(lean_object* v_m_255_){
_start:
{
lean_object* v___x_256_; lean_object* v___x_257_; 
v___x_256_ = lean_unsigned_to_nat(0u);
v___x_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_257_, 0, v_m_255_);
lean_ctor_set(v___x_257_, 1, v___x_256_);
return v___x_257_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_valuesIter(lean_object* v_00_u03b1_258_, lean_object* v_00_u03b2_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_m_262_){
_start:
{
lean_object* v___x_263_; lean_object* v___x_264_; 
v___x_263_ = lean_unsigned_to_nat(0u);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v_m_262_);
lean_ctor_set(v___x_264_, 1, v___x_263_);
return v___x_264_;
}
}
LEAN_EXPORT lean_object* l_Std_DHashMap_valuesIter___boxed(lean_object* v_00_u03b1_265_, lean_object* v_00_u03b2_266_, lean_object* v_inst_267_, lean_object* v_inst_268_, lean_object* v_m_269_){
_start:
{
lean_object* v_res_270_; 
v_res_270_ = l_Std_DHashMap_valuesIter(v_00_u03b1_265_, v_00_u03b2_266_, v_inst_267_, v_inst_268_, v_m_269_);
lean_dec_ref(v_inst_268_);
lean_dec_ref(v_inst_267_);
return v_res_270_;
}
}
lean_object* runtime_initialize_Std_Data_Iterators_Producers_Array(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FlatMap(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Combinators(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Array(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Std_Data_DHashMap_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Std_Data_Iterators_Producers_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Combinators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_Iterators_Lemmas_Producers_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Std_Data_DHashMap_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Std_Data_Iterators_Producers_Array(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_FlatMap(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_AssocList_Basic(uint8_t builtin);
lean_object* initialize_Std_Data_DHashMap_Internal_Defs(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Combinators(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Std_Data_Iterators_Lemmas_Producers_Array(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Std_Data_DHashMap_Iterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Std_Data_Iterators_Producers_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FlatMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_AssocList_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_AssocList_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_DHashMap_Internal_Defs(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Combinators(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Std_Data_Iterators_Lemmas_Producers_Array(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Std_Data_DHashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Std_Data_DHashMap_Iterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Std_Data_DHashMap_Iterator(builtin);
}
#ifdef __cplusplus
}
#endif
