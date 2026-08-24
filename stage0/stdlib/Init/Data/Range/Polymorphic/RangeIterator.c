// Lean compiler output
// Module: Init.Data.Range.Polymorphic.RangeIterator
// Imports: import Init.Data.Iterators.Lemmas.Consumers.Monadic.Loop public import Init.Data.Range.Polymorphic.PRange public import Init.Data.Iterators.Consumers.Monadic.Access public import Init.Data.Iterators.Consumers.Monadic.Loop import Init.ByCases import Init.Data.Bool import Init.Data.List.Lemmas import Init.Data.List.Sublist import Init.Data.Option.Lemmas
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
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_Monadic_step___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_Monadic_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_step___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterStep_successor_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg(lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_Monadic_step___redArg(lean_object* v_inst_1_, lean_object* v_inst_2_, lean_object* v_it_3_){
_start:
{
lean_object* v_next_4_; 
v_next_4_ = lean_ctor_get(v_it_3_, 0);
lean_inc(v_next_4_);
if (lean_obj_tag(v_next_4_) == 0)
{
lean_object* v___x_5_; 
lean_dec_ref(v_it_3_);
lean_dec_ref(v_inst_2_);
lean_dec_ref(v_inst_1_);
v___x_5_ = lean_box(2);
return v___x_5_;
}
else
{
lean_object* v_upperBound_6_; lean_object* v___x_8_; uint8_t v_isShared_9_; uint8_t v_isSharedCheck_27_; 
v_upperBound_6_ = lean_ctor_get(v_it_3_, 1);
v_isSharedCheck_27_ = !lean_is_exclusive(v_it_3_);
if (v_isSharedCheck_27_ == 0)
{
lean_object* v_unused_28_; 
v_unused_28_ = lean_ctor_get(v_it_3_, 0);
lean_dec(v_unused_28_);
v___x_8_ = v_it_3_;
v_isShared_9_ = v_isSharedCheck_27_;
goto v_resetjp_7_;
}
else
{
lean_inc(v_upperBound_6_);
lean_dec(v_it_3_);
v___x_8_ = lean_box(0);
v_isShared_9_ = v_isSharedCheck_27_;
goto v_resetjp_7_;
}
v_resetjp_7_:
{
lean_object* v_val_10_; lean_object* v___x_11_; uint8_t v___x_12_; 
v_val_10_ = lean_ctor_get(v_next_4_, 0);
lean_inc_n(v_val_10_, 2);
lean_dec_ref_known(v_next_4_, 1);
lean_inc(v_upperBound_6_);
v___x_11_ = lean_apply_2(v_inst_2_, v_val_10_, v_upperBound_6_);
v___x_12_ = lean_unbox(v___x_11_);
if (v___x_12_ == 0)
{
lean_object* v___x_13_; 
lean_dec(v_val_10_);
lean_del_object(v___x_8_);
lean_dec(v_upperBound_6_);
lean_dec_ref(v_inst_1_);
v___x_13_ = lean_box(2);
return v___x_13_;
}
else
{
lean_object* v_succ_x3f_14_; lean_object* v___x_16_; uint8_t v_isShared_17_; uint8_t v_isSharedCheck_25_; 
v_succ_x3f_14_ = lean_ctor_get(v_inst_1_, 0);
v_isSharedCheck_25_ = !lean_is_exclusive(v_inst_1_);
if (v_isSharedCheck_25_ == 0)
{
lean_object* v_unused_26_; 
v_unused_26_ = lean_ctor_get(v_inst_1_, 1);
lean_dec(v_unused_26_);
v___x_16_ = v_inst_1_;
v_isShared_17_ = v_isSharedCheck_25_;
goto v_resetjp_15_;
}
else
{
lean_inc(v_succ_x3f_14_);
lean_dec(v_inst_1_);
v___x_16_ = lean_box(0);
v_isShared_17_ = v_isSharedCheck_25_;
goto v_resetjp_15_;
}
v_resetjp_15_:
{
lean_object* v___x_18_; lean_object* v___x_20_; 
lean_inc(v_val_10_);
v___x_18_ = lean_apply_1(v_succ_x3f_14_, v_val_10_);
if (v_isShared_9_ == 0)
{
lean_ctor_set(v___x_8_, 0, v___x_18_);
v___x_20_ = v___x_8_;
goto v_reusejp_19_;
}
else
{
lean_object* v_reuseFailAlloc_24_; 
v_reuseFailAlloc_24_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_24_, 0, v___x_18_);
lean_ctor_set(v_reuseFailAlloc_24_, 1, v_upperBound_6_);
v___x_20_ = v_reuseFailAlloc_24_;
goto v_reusejp_19_;
}
v_reusejp_19_:
{
lean_object* v___x_22_; 
if (v_isShared_17_ == 0)
{
lean_ctor_set(v___x_16_, 1, v_val_10_);
lean_ctor_set(v___x_16_, 0, v___x_20_);
v___x_22_ = v___x_16_;
goto v_reusejp_21_;
}
else
{
lean_object* v_reuseFailAlloc_23_; 
v_reuseFailAlloc_23_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_23_, 0, v___x_20_);
lean_ctor_set(v_reuseFailAlloc_23_, 1, v_val_10_);
v___x_22_ = v_reuseFailAlloc_23_;
goto v_reusejp_21_;
}
v_reusejp_21_:
{
return v___x_22_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_Monadic_step(lean_object* v_00_u03b1_29_, lean_object* v_inst_30_, lean_object* v_inst_31_, lean_object* v_inst_32_, lean_object* v_it_33_){
_start:
{
lean_object* v_next_34_; 
v_next_34_ = lean_ctor_get(v_it_33_, 0);
lean_inc(v_next_34_);
if (lean_obj_tag(v_next_34_) == 0)
{
lean_object* v___x_35_; 
lean_dec_ref(v_it_33_);
lean_dec_ref(v_inst_32_);
lean_dec_ref(v_inst_30_);
v___x_35_ = lean_box(2);
return v___x_35_;
}
else
{
lean_object* v_upperBound_36_; lean_object* v___x_38_; uint8_t v_isShared_39_; uint8_t v_isSharedCheck_57_; 
v_upperBound_36_ = lean_ctor_get(v_it_33_, 1);
v_isSharedCheck_57_ = !lean_is_exclusive(v_it_33_);
if (v_isSharedCheck_57_ == 0)
{
lean_object* v_unused_58_; 
v_unused_58_ = lean_ctor_get(v_it_33_, 0);
lean_dec(v_unused_58_);
v___x_38_ = v_it_33_;
v_isShared_39_ = v_isSharedCheck_57_;
goto v_resetjp_37_;
}
else
{
lean_inc(v_upperBound_36_);
lean_dec(v_it_33_);
v___x_38_ = lean_box(0);
v_isShared_39_ = v_isSharedCheck_57_;
goto v_resetjp_37_;
}
v_resetjp_37_:
{
lean_object* v_val_40_; lean_object* v___x_41_; uint8_t v___x_42_; 
v_val_40_ = lean_ctor_get(v_next_34_, 0);
lean_inc_n(v_val_40_, 2);
lean_dec_ref_known(v_next_34_, 1);
lean_inc(v_upperBound_36_);
v___x_41_ = lean_apply_2(v_inst_32_, v_val_40_, v_upperBound_36_);
v___x_42_ = lean_unbox(v___x_41_);
if (v___x_42_ == 0)
{
lean_object* v___x_43_; 
lean_dec(v_val_40_);
lean_del_object(v___x_38_);
lean_dec(v_upperBound_36_);
lean_dec_ref(v_inst_30_);
v___x_43_ = lean_box(2);
return v___x_43_;
}
else
{
lean_object* v_succ_x3f_44_; lean_object* v___x_46_; uint8_t v_isShared_47_; uint8_t v_isSharedCheck_55_; 
v_succ_x3f_44_ = lean_ctor_get(v_inst_30_, 0);
v_isSharedCheck_55_ = !lean_is_exclusive(v_inst_30_);
if (v_isSharedCheck_55_ == 0)
{
lean_object* v_unused_56_; 
v_unused_56_ = lean_ctor_get(v_inst_30_, 1);
lean_dec(v_unused_56_);
v___x_46_ = v_inst_30_;
v_isShared_47_ = v_isSharedCheck_55_;
goto v_resetjp_45_;
}
else
{
lean_inc(v_succ_x3f_44_);
lean_dec(v_inst_30_);
v___x_46_ = lean_box(0);
v_isShared_47_ = v_isSharedCheck_55_;
goto v_resetjp_45_;
}
v_resetjp_45_:
{
lean_object* v___x_48_; lean_object* v___x_50_; 
lean_inc(v_val_40_);
v___x_48_ = lean_apply_1(v_succ_x3f_44_, v_val_40_);
if (v_isShared_39_ == 0)
{
lean_ctor_set(v___x_38_, 0, v___x_48_);
v___x_50_ = v___x_38_;
goto v_reusejp_49_;
}
else
{
lean_object* v_reuseFailAlloc_54_; 
v_reuseFailAlloc_54_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_54_, 0, v___x_48_);
lean_ctor_set(v_reuseFailAlloc_54_, 1, v_upperBound_36_);
v___x_50_ = v_reuseFailAlloc_54_;
goto v_reusejp_49_;
}
v_reusejp_49_:
{
lean_object* v___x_52_; 
if (v_isShared_47_ == 0)
{
lean_ctor_set(v___x_46_, 1, v_val_40_);
lean_ctor_set(v___x_46_, 0, v___x_50_);
v___x_52_ = v___x_46_;
goto v_reusejp_51_;
}
else
{
lean_object* v_reuseFailAlloc_53_; 
v_reuseFailAlloc_53_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_53_, 0, v___x_50_);
lean_ctor_set(v_reuseFailAlloc_53_, 1, v_val_40_);
v___x_52_ = v_reuseFailAlloc_53_;
goto v_reusejp_51_;
}
v_reusejp_51_:
{
return v___x_52_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_step___redArg(lean_object* v_inst_59_, lean_object* v_inst_60_, lean_object* v_it_61_){
_start:
{
lean_object* v_next_62_; 
v_next_62_ = lean_ctor_get(v_it_61_, 0);
lean_inc(v_next_62_);
if (lean_obj_tag(v_next_62_) == 0)
{
lean_object* v___x_63_; 
lean_dec_ref(v_it_61_);
lean_dec_ref(v_inst_60_);
lean_dec_ref(v_inst_59_);
v___x_63_ = lean_box(2);
return v___x_63_;
}
else
{
lean_object* v_upperBound_64_; lean_object* v___x_66_; uint8_t v_isShared_67_; uint8_t v_isSharedCheck_85_; 
v_upperBound_64_ = lean_ctor_get(v_it_61_, 1);
v_isSharedCheck_85_ = !lean_is_exclusive(v_it_61_);
if (v_isSharedCheck_85_ == 0)
{
lean_object* v_unused_86_; 
v_unused_86_ = lean_ctor_get(v_it_61_, 0);
lean_dec(v_unused_86_);
v___x_66_ = v_it_61_;
v_isShared_67_ = v_isSharedCheck_85_;
goto v_resetjp_65_;
}
else
{
lean_inc(v_upperBound_64_);
lean_dec(v_it_61_);
v___x_66_ = lean_box(0);
v_isShared_67_ = v_isSharedCheck_85_;
goto v_resetjp_65_;
}
v_resetjp_65_:
{
lean_object* v_val_68_; lean_object* v___x_69_; uint8_t v___x_70_; 
v_val_68_ = lean_ctor_get(v_next_62_, 0);
lean_inc_n(v_val_68_, 2);
lean_dec_ref_known(v_next_62_, 1);
lean_inc(v_upperBound_64_);
v___x_69_ = lean_apply_2(v_inst_60_, v_val_68_, v_upperBound_64_);
v___x_70_ = lean_unbox(v___x_69_);
if (v___x_70_ == 0)
{
lean_object* v___x_71_; 
lean_dec(v_val_68_);
lean_del_object(v___x_66_);
lean_dec(v_upperBound_64_);
lean_dec_ref(v_inst_59_);
v___x_71_ = lean_box(2);
return v___x_71_;
}
else
{
lean_object* v_succ_x3f_72_; lean_object* v___x_74_; uint8_t v_isShared_75_; uint8_t v_isSharedCheck_83_; 
v_succ_x3f_72_ = lean_ctor_get(v_inst_59_, 0);
v_isSharedCheck_83_ = !lean_is_exclusive(v_inst_59_);
if (v_isSharedCheck_83_ == 0)
{
lean_object* v_unused_84_; 
v_unused_84_ = lean_ctor_get(v_inst_59_, 1);
lean_dec(v_unused_84_);
v___x_74_ = v_inst_59_;
v_isShared_75_ = v_isSharedCheck_83_;
goto v_resetjp_73_;
}
else
{
lean_inc(v_succ_x3f_72_);
lean_dec(v_inst_59_);
v___x_74_ = lean_box(0);
v_isShared_75_ = v_isSharedCheck_83_;
goto v_resetjp_73_;
}
v_resetjp_73_:
{
lean_object* v___x_76_; lean_object* v___x_78_; 
lean_inc(v_val_68_);
v___x_76_ = lean_apply_1(v_succ_x3f_72_, v_val_68_);
if (v_isShared_67_ == 0)
{
lean_ctor_set(v___x_66_, 0, v___x_76_);
v___x_78_ = v___x_66_;
goto v_reusejp_77_;
}
else
{
lean_object* v_reuseFailAlloc_82_; 
v_reuseFailAlloc_82_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_82_, 0, v___x_76_);
lean_ctor_set(v_reuseFailAlloc_82_, 1, v_upperBound_64_);
v___x_78_ = v_reuseFailAlloc_82_;
goto v_reusejp_77_;
}
v_reusejp_77_:
{
lean_object* v___x_80_; 
if (v_isShared_75_ == 0)
{
lean_ctor_set(v___x_74_, 1, v_val_68_);
lean_ctor_set(v___x_74_, 0, v___x_78_);
v___x_80_ = v___x_74_;
goto v_reusejp_79_;
}
else
{
lean_object* v_reuseFailAlloc_81_; 
v_reuseFailAlloc_81_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_81_, 0, v___x_78_);
lean_ctor_set(v_reuseFailAlloc_81_, 1, v_val_68_);
v___x_80_ = v_reuseFailAlloc_81_;
goto v_reusejp_79_;
}
v_reusejp_79_:
{
return v___x_80_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_step(lean_object* v_00_u03b1_87_, lean_object* v_inst_88_, lean_object* v_inst_89_, lean_object* v_inst_90_, lean_object* v_it_91_){
_start:
{
lean_object* v_next_92_; 
v_next_92_ = lean_ctor_get(v_it_91_, 0);
lean_inc(v_next_92_);
if (lean_obj_tag(v_next_92_) == 0)
{
lean_object* v___x_93_; 
lean_dec_ref(v_it_91_);
lean_dec_ref(v_inst_90_);
lean_dec_ref(v_inst_88_);
v___x_93_ = lean_box(2);
return v___x_93_;
}
else
{
lean_object* v_upperBound_94_; lean_object* v___x_96_; uint8_t v_isShared_97_; uint8_t v_isSharedCheck_115_; 
v_upperBound_94_ = lean_ctor_get(v_it_91_, 1);
v_isSharedCheck_115_ = !lean_is_exclusive(v_it_91_);
if (v_isSharedCheck_115_ == 0)
{
lean_object* v_unused_116_; 
v_unused_116_ = lean_ctor_get(v_it_91_, 0);
lean_dec(v_unused_116_);
v___x_96_ = v_it_91_;
v_isShared_97_ = v_isSharedCheck_115_;
goto v_resetjp_95_;
}
else
{
lean_inc(v_upperBound_94_);
lean_dec(v_it_91_);
v___x_96_ = lean_box(0);
v_isShared_97_ = v_isSharedCheck_115_;
goto v_resetjp_95_;
}
v_resetjp_95_:
{
lean_object* v_val_98_; lean_object* v___x_99_; uint8_t v___x_100_; 
v_val_98_ = lean_ctor_get(v_next_92_, 0);
lean_inc_n(v_val_98_, 2);
lean_dec_ref_known(v_next_92_, 1);
lean_inc(v_upperBound_94_);
v___x_99_ = lean_apply_2(v_inst_90_, v_val_98_, v_upperBound_94_);
v___x_100_ = lean_unbox(v___x_99_);
if (v___x_100_ == 0)
{
lean_object* v___x_101_; 
lean_dec(v_val_98_);
lean_del_object(v___x_96_);
lean_dec(v_upperBound_94_);
lean_dec_ref(v_inst_88_);
v___x_101_ = lean_box(2);
return v___x_101_;
}
else
{
lean_object* v_succ_x3f_102_; lean_object* v___x_104_; uint8_t v_isShared_105_; uint8_t v_isSharedCheck_113_; 
v_succ_x3f_102_ = lean_ctor_get(v_inst_88_, 0);
v_isSharedCheck_113_ = !lean_is_exclusive(v_inst_88_);
if (v_isSharedCheck_113_ == 0)
{
lean_object* v_unused_114_; 
v_unused_114_ = lean_ctor_get(v_inst_88_, 1);
lean_dec(v_unused_114_);
v___x_104_ = v_inst_88_;
v_isShared_105_ = v_isSharedCheck_113_;
goto v_resetjp_103_;
}
else
{
lean_inc(v_succ_x3f_102_);
lean_dec(v_inst_88_);
v___x_104_ = lean_box(0);
v_isShared_105_ = v_isSharedCheck_113_;
goto v_resetjp_103_;
}
v_resetjp_103_:
{
lean_object* v___x_106_; lean_object* v___x_108_; 
lean_inc(v_val_98_);
v___x_106_ = lean_apply_1(v_succ_x3f_102_, v_val_98_);
if (v_isShared_97_ == 0)
{
lean_ctor_set(v___x_96_, 0, v___x_106_);
v___x_108_ = v___x_96_;
goto v_reusejp_107_;
}
else
{
lean_object* v_reuseFailAlloc_112_; 
v_reuseFailAlloc_112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_112_, 0, v___x_106_);
lean_ctor_set(v_reuseFailAlloc_112_, 1, v_upperBound_94_);
v___x_108_ = v_reuseFailAlloc_112_;
goto v_reusejp_107_;
}
v_reusejp_107_:
{
lean_object* v___x_110_; 
if (v_isShared_105_ == 0)
{
lean_ctor_set(v___x_104_, 1, v_val_98_);
lean_ctor_set(v___x_104_, 0, v___x_108_);
v___x_110_ = v___x_104_;
goto v_reusejp_109_;
}
else
{
lean_object* v_reuseFailAlloc_111_; 
v_reuseFailAlloc_111_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_111_, 0, v___x_108_);
lean_ctor_set(v_reuseFailAlloc_111_, 1, v_val_98_);
v___x_110_ = v_reuseFailAlloc_111_;
goto v_reusejp_109_;
}
v_reusejp_109_:
{
return v___x_110_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter___redArg(lean_object* v_x_117_, lean_object* v_h__1_118_, lean_object* v_h__2_119_){
_start:
{
if (lean_obj_tag(v_x_117_) == 0)
{
lean_object* v___x_120_; lean_object* v___x_121_; 
lean_dec(v_h__2_119_);
v___x_120_ = lean_box(0);
v___x_121_ = lean_apply_1(v_h__1_118_, v___x_120_);
return v___x_121_;
}
else
{
lean_object* v_val_122_; lean_object* v___x_123_; 
lean_dec(v_h__1_118_);
v_val_122_ = lean_ctor_get(v_x_117_, 0);
lean_inc(v_val_122_);
lean_dec_ref_known(v_x_117_, 1);
v___x_123_ = lean_apply_1(v_h__2_119_, v_val_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter(lean_object* v_00_u03b1_124_, lean_object* v_motive_125_, lean_object* v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_){
_start:
{
if (lean_obj_tag(v_x_126_) == 0)
{
lean_object* v___x_129_; lean_object* v___x_130_; 
lean_dec(v_h__2_128_);
v___x_129_ = lean_box(0);
v___x_130_ = lean_apply_1(v_h__1_127_, v___x_129_);
return v___x_130_;
}
else
{
lean_object* v_val_131_; lean_object* v___x_132_; 
lean_dec(v_h__1_127_);
v_val_131_ = lean_ctor_get(v_x_126_, 0);
lean_inc(v_val_131_);
lean_dec_ref_known(v_x_126_, 1);
v___x_132_ = lean_apply_1(v_h__2_128_, v_val_131_);
return v___x_132_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0(lean_object* v_inst_133_, lean_object* v_inst_134_, lean_object* v_it_135_){
_start:
{
lean_object* v_next_136_; 
v_next_136_ = lean_ctor_get(v_it_135_, 0);
lean_inc(v_next_136_);
if (lean_obj_tag(v_next_136_) == 0)
{
lean_object* v___x_137_; 
lean_dec_ref(v_it_135_);
lean_dec_ref(v_inst_134_);
lean_dec_ref(v_inst_133_);
v___x_137_ = lean_box(2);
return v___x_137_;
}
else
{
lean_object* v_upperBound_138_; lean_object* v___x_140_; uint8_t v_isShared_141_; uint8_t v_isSharedCheck_159_; 
v_upperBound_138_ = lean_ctor_get(v_it_135_, 1);
v_isSharedCheck_159_ = !lean_is_exclusive(v_it_135_);
if (v_isSharedCheck_159_ == 0)
{
lean_object* v_unused_160_; 
v_unused_160_ = lean_ctor_get(v_it_135_, 0);
lean_dec(v_unused_160_);
v___x_140_ = v_it_135_;
v_isShared_141_ = v_isSharedCheck_159_;
goto v_resetjp_139_;
}
else
{
lean_inc(v_upperBound_138_);
lean_dec(v_it_135_);
v___x_140_ = lean_box(0);
v_isShared_141_ = v_isSharedCheck_159_;
goto v_resetjp_139_;
}
v_resetjp_139_:
{
lean_object* v_val_142_; lean_object* v___x_143_; uint8_t v___x_144_; 
v_val_142_ = lean_ctor_get(v_next_136_, 0);
lean_inc_n(v_val_142_, 2);
lean_dec_ref_known(v_next_136_, 1);
lean_inc(v_upperBound_138_);
v___x_143_ = lean_apply_2(v_inst_133_, v_val_142_, v_upperBound_138_);
v___x_144_ = lean_unbox(v___x_143_);
if (v___x_144_ == 0)
{
lean_object* v___x_145_; 
lean_dec(v_val_142_);
lean_del_object(v___x_140_);
lean_dec(v_upperBound_138_);
lean_dec_ref(v_inst_134_);
v___x_145_ = lean_box(2);
return v___x_145_;
}
else
{
lean_object* v_succ_x3f_146_; lean_object* v___x_148_; uint8_t v_isShared_149_; uint8_t v_isSharedCheck_157_; 
v_succ_x3f_146_ = lean_ctor_get(v_inst_134_, 0);
v_isSharedCheck_157_ = !lean_is_exclusive(v_inst_134_);
if (v_isSharedCheck_157_ == 0)
{
lean_object* v_unused_158_; 
v_unused_158_ = lean_ctor_get(v_inst_134_, 1);
lean_dec(v_unused_158_);
v___x_148_ = v_inst_134_;
v_isShared_149_ = v_isSharedCheck_157_;
goto v_resetjp_147_;
}
else
{
lean_inc(v_succ_x3f_146_);
lean_dec(v_inst_134_);
v___x_148_ = lean_box(0);
v_isShared_149_ = v_isSharedCheck_157_;
goto v_resetjp_147_;
}
v_resetjp_147_:
{
lean_object* v___x_150_; lean_object* v___x_152_; 
lean_inc(v_val_142_);
v___x_150_ = lean_apply_1(v_succ_x3f_146_, v_val_142_);
if (v_isShared_141_ == 0)
{
lean_ctor_set(v___x_140_, 0, v___x_150_);
v___x_152_ = v___x_140_;
goto v_reusejp_151_;
}
else
{
lean_object* v_reuseFailAlloc_156_; 
v_reuseFailAlloc_156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_156_, 0, v___x_150_);
lean_ctor_set(v_reuseFailAlloc_156_, 1, v_upperBound_138_);
v___x_152_ = v_reuseFailAlloc_156_;
goto v_reusejp_151_;
}
v_reusejp_151_:
{
lean_object* v___x_154_; 
if (v_isShared_149_ == 0)
{
lean_ctor_set(v___x_148_, 1, v_val_142_);
lean_ctor_set(v___x_148_, 0, v___x_152_);
v___x_154_ = v___x_148_;
goto v_reusejp_153_;
}
else
{
lean_object* v_reuseFailAlloc_155_; 
v_reuseFailAlloc_155_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_155_, 0, v___x_152_);
lean_ctor_set(v_reuseFailAlloc_155_, 1, v_val_142_);
v___x_154_ = v_reuseFailAlloc_155_;
goto v_reusejp_153_;
}
v_reusejp_153_:
{
return v___x_154_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg(lean_object* v_inst_161_, lean_object* v_inst_162_){
_start:
{
lean_object* v___f_163_; 
v___f_163_ = lean_alloc_closure((void*)(l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0), 3, 2);
lean_closure_set(v___f_163_, 0, v_inst_162_);
lean_closure_set(v___f_163_, 1, v_inst_161_);
return v___f_163_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE(lean_object* v_00_u03b1_164_, lean_object* v_inst_165_, lean_object* v_inst_166_, lean_object* v_inst_167_){
_start:
{
lean_object* v___f_168_; 
v___f_168_ = lean_alloc_closure((void*)(l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0), 3, 2);
lean_closure_set(v___f_168_, 0, v_inst_167_);
lean_closure_set(v___f_168_, 1, v_inst_165_);
return v___f_168_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object* v_x_169_, lean_object* v_h__1_170_, lean_object* v_h__2_171_, lean_object* v_h__3_172_){
_start:
{
switch(lean_obj_tag(v_x_169_))
{
case 0:
{
lean_object* v_it_173_; lean_object* v_out_174_; lean_object* v___x_175_; 
lean_dec(v_h__3_172_);
lean_dec(v_h__2_171_);
v_it_173_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_it_173_);
v_out_174_ = lean_ctor_get(v_x_169_, 1);
lean_inc(v_out_174_);
lean_dec_ref_known(v_x_169_, 2);
v___x_175_ = lean_apply_2(v_h__1_170_, v_it_173_, v_out_174_);
return v___x_175_;
}
case 1:
{
lean_object* v_it_176_; lean_object* v___x_177_; 
lean_dec(v_h__3_172_);
lean_dec(v_h__1_170_);
v_it_176_ = lean_ctor_get(v_x_169_, 0);
lean_inc(v_it_176_);
lean_dec_ref_known(v_x_169_, 1);
v___x_177_ = lean_apply_1(v_h__2_171_, v_it_176_);
return v___x_177_;
}
default: 
{
lean_object* v___x_178_; lean_object* v___x_179_; 
lean_dec(v_h__2_171_);
lean_dec(v_h__1_170_);
v___x_178_ = lean_box(0);
v___x_179_ = lean_apply_1(v_h__3_172_, v___x_178_);
return v___x_179_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterStep_successor_match__1_splitter(lean_object* v_00_u03b1_180_, lean_object* v_00_u03b2_181_, lean_object* v_motive_182_, lean_object* v_x_183_, lean_object* v_h__1_184_, lean_object* v_h__2_185_, lean_object* v_h__3_186_){
_start:
{
switch(lean_obj_tag(v_x_183_))
{
case 0:
{
lean_object* v_it_187_; lean_object* v_out_188_; lean_object* v___x_189_; 
lean_dec(v_h__3_186_);
lean_dec(v_h__2_185_);
v_it_187_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_it_187_);
v_out_188_ = lean_ctor_get(v_x_183_, 1);
lean_inc(v_out_188_);
lean_dec_ref_known(v_x_183_, 2);
v___x_189_ = lean_apply_2(v_h__1_184_, v_it_187_, v_out_188_);
return v___x_189_;
}
case 1:
{
lean_object* v_it_190_; lean_object* v___x_191_; 
lean_dec(v_h__3_186_);
lean_dec(v_h__1_184_);
v_it_190_ = lean_ctor_get(v_x_183_, 0);
lean_inc(v_it_190_);
lean_dec_ref_known(v_x_183_, 1);
v___x_191_ = lean_apply_1(v_h__2_185_, v_it_190_);
return v___x_191_;
}
default: 
{
lean_object* v___x_192_; lean_object* v___x_193_; 
lean_dec(v_h__2_185_);
lean_dec(v_h__1_184_);
v___x_192_ = lean_box(0);
v___x_193_ = lean_apply_1(v_h__3_186_, v___x_192_);
return v___x_193_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_, lean_object* v_inst_198_, lean_object* v_inst_199_){
_start:
{
lean_object* v___x_200_; 
v___x_200_ = lean_box(0);
return v___x_200_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_inst_204_, lean_object* v_inst_205_, lean_object* v_inst_206_){
_start:
{
lean_object* v_res_207_; 
v_res_207_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(v_00_u03b1_201_, v_inst_202_, v_inst_203_, v_inst_204_, v_inst_205_, v_inst_206_);
lean_dec_ref(v_inst_204_);
lean_dec_ref(v_inst_202_);
return v_res_207_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_inst_211_, lean_object* v_inst_212_){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_box(0);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_214_, lean_object* v_inst_215_, lean_object* v_inst_216_, lean_object* v_inst_217_, lean_object* v_inst_218_){
_start:
{
lean_object* v_res_219_; 
v_res_219_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(v_00_u03b1_214_, v_inst_215_, v_inst_216_, v_inst_217_, v_inst_218_);
lean_dec_ref(v_inst_217_);
lean_dec_ref(v_inst_215_);
return v_res_219_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter___redArg(lean_object* v_x_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
lean_object* v___x_223_; lean_object* v___x_224_; 
lean_dec(v_h__2_222_);
v___x_223_ = lean_box(0);
v___x_224_ = lean_apply_1(v_h__1_221_, v___x_223_);
return v___x_224_;
}
else
{
lean_object* v_val_225_; lean_object* v___x_226_; 
lean_dec(v_h__1_221_);
v_val_225_ = lean_ctor_get(v_x_220_, 0);
lean_inc(v_val_225_);
lean_dec_ref_known(v_x_220_, 1);
v___x_226_ = lean_apply_1(v_h__2_222_, v_val_225_);
return v___x_226_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter(lean_object* v_00_u03b1_227_, lean_object* v_motive_228_, lean_object* v_x_229_, lean_object* v_h__1_230_, lean_object* v_h__2_231_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v___x_232_; lean_object* v___x_233_; 
lean_dec(v_h__2_231_);
v___x_232_ = lean_box(0);
v___x_233_ = lean_apply_1(v_h__1_230_, v___x_232_);
return v___x_233_;
}
else
{
lean_object* v_val_234_; lean_object* v___x_235_; 
lean_dec(v_h__1_230_);
v_val_234_ = lean_ctor_get(v_x_229_, 0);
lean_inc(v_val_234_);
lean_dec_ref_known(v_x_229_, 1);
v___x_235_ = lean_apply_1(v_h__2_231_, v_val_234_);
return v___x_235_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_236_, lean_object* v_inst_237_, lean_object* v_it_238_, lean_object* v_n_239_){
_start:
{
lean_object* v_next_240_; 
v_next_240_ = lean_ctor_get(v_it_238_, 0);
lean_inc(v_next_240_);
if (lean_obj_tag(v_next_240_) == 0)
{
lean_object* v___x_241_; 
lean_dec(v_n_239_);
lean_dec_ref(v_it_238_);
lean_dec_ref(v_inst_237_);
lean_dec_ref(v_inst_236_);
v___x_241_ = lean_box(2);
return v___x_241_;
}
else
{
lean_object* v_upperBound_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_266_; 
v_upperBound_242_ = lean_ctor_get(v_it_238_, 1);
v_isSharedCheck_266_ = !lean_is_exclusive(v_it_238_);
if (v_isSharedCheck_266_ == 0)
{
lean_object* v_unused_267_; 
v_unused_267_ = lean_ctor_get(v_it_238_, 0);
lean_dec(v_unused_267_);
v___x_244_ = v_it_238_;
v_isShared_245_ = v_isSharedCheck_266_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_upperBound_242_);
lean_dec(v_it_238_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_266_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_succ_x3f_246_; lean_object* v_succMany_x3f_247_; lean_object* v___x_249_; uint8_t v_isShared_250_; uint8_t v_isSharedCheck_265_; 
v_succ_x3f_246_ = lean_ctor_get(v_inst_236_, 0);
v_succMany_x3f_247_ = lean_ctor_get(v_inst_236_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_inst_236_);
if (v_isSharedCheck_265_ == 0)
{
v___x_249_ = v_inst_236_;
v_isShared_250_ = v_isSharedCheck_265_;
goto v_resetjp_248_;
}
else
{
lean_inc(v_succMany_x3f_247_);
lean_inc(v_succ_x3f_246_);
lean_dec(v_inst_236_);
v___x_249_ = lean_box(0);
v_isShared_250_ = v_isSharedCheck_265_;
goto v_resetjp_248_;
}
v_resetjp_248_:
{
lean_object* v_val_251_; lean_object* v___x_252_; 
v_val_251_ = lean_ctor_get(v_next_240_, 0);
lean_inc(v_val_251_);
lean_dec_ref_known(v_next_240_, 1);
v___x_252_ = lean_apply_2(v_succMany_x3f_247_, v_n_239_, v_val_251_);
if (lean_obj_tag(v___x_252_) == 0)
{
lean_object* v___x_253_; 
lean_del_object(v___x_249_);
lean_dec_ref(v_succ_x3f_246_);
lean_del_object(v___x_244_);
lean_dec(v_upperBound_242_);
lean_dec_ref(v_inst_237_);
v___x_253_ = lean_box(2);
return v___x_253_;
}
else
{
lean_object* v_val_254_; lean_object* v___x_255_; uint8_t v___x_256_; 
v_val_254_ = lean_ctor_get(v___x_252_, 0);
lean_inc_n(v_val_254_, 2);
lean_dec_ref_known(v___x_252_, 1);
lean_inc(v_upperBound_242_);
v___x_255_ = lean_apply_2(v_inst_237_, v_val_254_, v_upperBound_242_);
v___x_256_ = lean_unbox(v___x_255_);
if (v___x_256_ == 0)
{
lean_object* v___x_257_; 
lean_dec(v_val_254_);
lean_del_object(v___x_249_);
lean_dec_ref(v_succ_x3f_246_);
lean_del_object(v___x_244_);
lean_dec(v_upperBound_242_);
v___x_257_ = lean_box(2);
return v___x_257_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_260_; 
lean_inc(v_val_254_);
v___x_258_ = lean_apply_1(v_succ_x3f_246_, v_val_254_);
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 0, v___x_258_);
v___x_260_ = v___x_244_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v___x_258_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_upperBound_242_);
v___x_260_ = v_reuseFailAlloc_264_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_262_; 
if (v_isShared_250_ == 0)
{
lean_ctor_set(v___x_249_, 1, v_val_254_);
lean_ctor_set(v___x_249_, 0, v___x_260_);
v___x_262_ = v___x_249_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v___x_260_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_val_254_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess___redArg(lean_object* v_inst_268_, lean_object* v_inst_269_){
_start:
{
lean_object* v___f_270_; 
v___f_270_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_270_, 0, v_inst_268_);
lean_closure_set(v___f_270_, 1, v_inst_269_);
return v___f_270_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess(lean_object* v_00_u03b1_271_, lean_object* v_inst_272_, lean_object* v_inst_273_, lean_object* v_inst_274_, lean_object* v_inst_275_, lean_object* v_inst_276_){
_start:
{
lean_object* v___f_277_; 
v___f_277_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_277_, 0, v_inst_272_);
lean_closure_set(v___f_277_, 1, v_inst_274_);
return v___f_277_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0(lean_object* v_toPure_278_, lean_object* v_inst_279_, lean_object* v_next_280_, lean_object* v_G_281_, lean_object* v_____do__lift_282_){
_start:
{
if (lean_obj_tag(v_____do__lift_282_) == 0)
{
lean_object* v_a_283_; lean_object* v___x_284_; 
lean_dec(v_G_281_);
lean_dec(v_next_280_);
lean_dec_ref(v_inst_279_);
v_a_283_ = lean_ctor_get(v_____do__lift_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref_known(v_____do__lift_282_, 1);
v___x_284_ = lean_apply_2(v_toPure_278_, lean_box(0), v_a_283_);
return v___x_284_;
}
else
{
lean_object* v_a_285_; lean_object* v_succ_x3f_286_; lean_object* v___x_287_; 
v_a_285_ = lean_ctor_get(v_____do__lift_282_, 0);
lean_inc(v_a_285_);
lean_dec_ref_known(v_____do__lift_282_, 1);
v_succ_x3f_286_ = lean_ctor_get(v_inst_279_, 0);
lean_inc_ref(v_succ_x3f_286_);
lean_dec_ref(v_inst_279_);
v___x_287_ = lean_apply_1(v_succ_x3f_286_, v_next_280_);
if (lean_obj_tag(v___x_287_) == 0)
{
lean_object* v___x_288_; 
lean_dec(v_G_281_);
v___x_288_ = lean_apply_2(v_toPure_278_, lean_box(0), v_a_285_);
return v___x_288_;
}
else
{
lean_object* v_val_289_; lean_object* v___x_290_; 
lean_dec(v_toPure_278_);
v_val_289_ = lean_ctor_get(v___x_287_, 0);
lean_inc(v_val_289_);
lean_dec_ref_known(v___x_287_, 1);
v___x_290_ = lean_apply_4(v_G_281_, v_val_289_, v_a_285_, lean_box(0), lean_box(0));
return v___x_290_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object* v_inst_291_, lean_object* v_upperBound_292_, lean_object* v_toPure_293_, lean_object* v_inst_294_, lean_object* v_f_295_, lean_object* v_toBind_296_, lean_object* v_next_297_, lean_object* v_acc_298_, lean_object* v_h_299_, lean_object* v_G_300_){
_start:
{
lean_object* v___x_301_; uint8_t v___x_302_; 
lean_inc(v_next_297_);
v___x_301_ = lean_apply_2(v_inst_291_, v_next_297_, v_upperBound_292_);
v___x_302_ = lean_unbox(v___x_301_);
if (v___x_302_ == 0)
{
lean_object* v___x_303_; 
lean_dec(v_G_300_);
lean_dec(v_next_297_);
lean_dec(v_toBind_296_);
lean_dec(v_f_295_);
lean_dec_ref(v_inst_294_);
v___x_303_ = lean_apply_2(v_toPure_293_, lean_box(0), v_acc_298_);
return v___x_303_;
}
else
{
lean_object* v___f_304_; lean_object* v___x_305_; lean_object* v___x_306_; 
lean_inc(v_next_297_);
v___f_304_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_304_, 0, v_toPure_293_);
lean_closure_set(v___f_304_, 1, v_inst_294_);
lean_closure_set(v___f_304_, 2, v_next_297_);
lean_closure_set(v___f_304_, 3, v_G_300_);
v___x_305_ = lean_apply_4(v_f_295_, v_next_297_, lean_box(0), lean_box(0), v_acc_298_);
v___x_306_ = lean_apply_4(v_toBind_296_, lean_box(0), lean_box(0), v___x_305_, v___f_304_);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_307_, lean_object* v_inst_308_, lean_object* v_inst_309_, lean_object* v_upperBound_310_, lean_object* v_acc_311_, lean_object* v_next_312_, lean_object* v_f_313_){
_start:
{
lean_object* v_toApplicative_314_; lean_object* v_toBind_315_; lean_object* v_toPure_316_; lean_object* v___f_317_; lean_object* v___x_318_; 
v_toApplicative_314_ = lean_ctor_get(v_inst_309_, 0);
lean_inc_ref(v_toApplicative_314_);
v_toBind_315_ = lean_ctor_get(v_inst_309_, 1);
lean_inc(v_toBind_315_);
lean_dec_ref(v_inst_309_);
v_toPure_316_ = lean_ctor_get(v_toApplicative_314_, 1);
lean_inc(v_toPure_316_);
lean_dec_ref(v_toApplicative_314_);
v___f_317_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_317_, 0, v_inst_308_);
lean_closure_set(v___f_317_, 1, v_upperBound_310_);
lean_closure_set(v___f_317_, 2, v_toPure_316_);
lean_closure_set(v___f_317_, 3, v_inst_307_);
lean_closure_set(v___f_317_, 4, v_f_313_);
lean_closure_set(v___f_317_, 5, v_toBind_315_);
v___x_318_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_317_, v_next_312_, v_acc_311_, lean_box(0));
return v___x_318_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_319_, lean_object* v_inst_320_, lean_object* v_inst_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_n_325_, lean_object* v_inst_326_, lean_object* v_00_u03b3_327_, lean_object* v_Pl_328_, lean_object* v_LargeEnough_329_, lean_object* v_hl_330_, lean_object* v_upperBound_331_, lean_object* v_acc_332_, lean_object* v_next_333_, lean_object* v_h_334_, lean_object* v_f_335_){
_start:
{
lean_object* v_toApplicative_336_; lean_object* v_toBind_337_; lean_object* v_toPure_338_; lean_object* v___f_339_; lean_object* v___x_340_; 
v_toApplicative_336_ = lean_ctor_get(v_inst_326_, 0);
lean_inc_ref(v_toApplicative_336_);
v_toBind_337_ = lean_ctor_get(v_inst_326_, 1);
lean_inc(v_toBind_337_);
lean_dec_ref(v_inst_326_);
v_toPure_338_ = lean_ctor_get(v_toApplicative_336_, 1);
lean_inc(v_toPure_338_);
lean_dec_ref(v_toApplicative_336_);
v___f_339_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_339_, 0, v_inst_322_);
lean_closure_set(v___f_339_, 1, v_upperBound_331_);
lean_closure_set(v___f_339_, 2, v_toPure_338_);
lean_closure_set(v___f_339_, 3, v_inst_320_);
lean_closure_set(v___f_339_, 4, v_f_335_);
lean_closure_set(v___f_339_, 5, v_toBind_337_);
v___x_340_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_339_, v_next_333_, v_acc_332_, lean_box(0));
return v___x_340_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_341_ = _args[0];
lean_object* v_inst_342_ = _args[1];
lean_object* v_inst_343_ = _args[2];
lean_object* v_inst_344_ = _args[3];
lean_object* v_inst_345_ = _args[4];
lean_object* v_inst_346_ = _args[5];
lean_object* v_n_347_ = _args[6];
lean_object* v_inst_348_ = _args[7];
lean_object* v_00_u03b3_349_ = _args[8];
lean_object* v_Pl_350_ = _args[9];
lean_object* v_LargeEnough_351_ = _args[10];
lean_object* v_hl_352_ = _args[11];
lean_object* v_upperBound_353_ = _args[12];
lean_object* v_acc_354_ = _args[13];
lean_object* v_next_355_ = _args[14];
lean_object* v_h_356_ = _args[15];
lean_object* v_f_357_ = _args[16];
_start:
{
lean_object* v_res_358_; 
v_res_358_ = l_Std_Rxc_Iterator_instIteratorLoop_loop(v_00_u03b1_341_, v_inst_342_, v_inst_343_, v_inst_344_, v_inst_345_, v_inst_346_, v_n_347_, v_inst_348_, v_00_u03b3_349_, v_Pl_350_, v_LargeEnough_351_, v_hl_352_, v_upperBound_353_, v_acc_354_, v_next_355_, v_h_356_, v_f_357_);
return v_res_358_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1(lean_object* v_inst_359_, lean_object* v_upperBound_360_, lean_object* v_toPure_361_, lean_object* v_inst_362_, lean_object* v_f_363_, lean_object* v_toBind_364_, lean_object* v_next_365_, lean_object* v_acc_366_, lean_object* v_h_367_, lean_object* v_G_368_){
_start:
{
lean_object* v___x_369_; uint8_t v___x_370_; 
lean_inc(v_next_365_);
v___x_369_ = lean_apply_2(v_inst_359_, v_next_365_, v_upperBound_360_);
v___x_370_ = lean_unbox(v___x_369_);
if (v___x_370_ == 0)
{
lean_object* v___x_371_; 
lean_dec(v_G_368_);
lean_dec(v_next_365_);
lean_dec(v_toBind_364_);
lean_dec(v_f_363_);
lean_dec_ref(v_inst_362_);
v___x_371_ = lean_apply_2(v_toPure_361_, lean_box(0), v_acc_366_);
return v___x_371_;
}
else
{
lean_object* v___f_372_; lean_object* v___x_373_; lean_object* v___x_374_; 
lean_inc(v_next_365_);
v___f_372_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_372_, 0, v_toPure_361_);
lean_closure_set(v___f_372_, 1, v_inst_362_);
lean_closure_set(v___f_372_, 2, v_next_365_);
lean_closure_set(v___f_372_, 3, v_G_368_);
v___x_373_ = lean_apply_3(v_f_363_, v_next_365_, lean_box(0), v_acc_366_);
v___x_374_ = lean_apply_4(v_toBind_364_, lean_box(0), lean_box(0), v___x_373_, v___f_372_);
return v___x_374_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_toBind_378_, lean_object* v_x_379_, lean_object* v_00_u03b3_380_, lean_object* v_Pl_381_, lean_object* v_it_382_, lean_object* v_init_383_, lean_object* v_f_384_){
_start:
{
lean_object* v_next_385_; 
v_next_385_ = lean_ctor_get(v_it_382_, 0);
lean_inc(v_next_385_);
if (lean_obj_tag(v_next_385_) == 0)
{
lean_object* v___x_386_; 
lean_dec(v_f_384_);
lean_dec_ref(v_it_382_);
lean_dec(v_toBind_378_);
lean_dec_ref(v_inst_377_);
lean_dec_ref(v_inst_376_);
v___x_386_ = lean_apply_2(v_toPure_375_, lean_box(0), v_init_383_);
return v___x_386_;
}
else
{
lean_object* v_upperBound_387_; lean_object* v_val_388_; lean_object* v___f_389_; lean_object* v___x_390_; 
v_upperBound_387_ = lean_ctor_get(v_it_382_, 1);
lean_inc(v_upperBound_387_);
lean_dec_ref(v_it_382_);
v_val_388_ = lean_ctor_get(v_next_385_, 0);
lean_inc(v_val_388_);
lean_dec_ref_known(v_next_385_, 1);
v___f_389_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_389_, 0, v_inst_376_);
lean_closure_set(v___f_389_, 1, v_upperBound_387_);
lean_closure_set(v___f_389_, 2, v_toPure_375_);
lean_closure_set(v___f_389_, 3, v_inst_377_);
lean_closure_set(v___f_389_, 4, v_f_384_);
lean_closure_set(v___f_389_, 5, v_toBind_378_);
v___x_390_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_389_, v_val_388_, v_init_383_, lean_box(0));
return v___x_390_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0___boxed(lean_object* v_toPure_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_toBind_394_, lean_object* v_x_395_, lean_object* v_00_u03b3_396_, lean_object* v_Pl_397_, lean_object* v_it_398_, lean_object* v_init_399_, lean_object* v_f_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0(v_toPure_391_, v_inst_392_, v_inst_393_, v_toBind_394_, v_x_395_, v_00_u03b3_396_, v_Pl_397_, v_it_398_, v_init_399_, v_f_400_);
lean_dec(v_x_395_);
return v_res_401_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg(lean_object* v_inst_402_, lean_object* v_inst_403_, lean_object* v_inst_404_){
_start:
{
lean_object* v_toApplicative_405_; lean_object* v_toBind_406_; lean_object* v_toPure_407_; lean_object* v___f_408_; 
v_toApplicative_405_ = lean_ctor_get(v_inst_404_, 0);
lean_inc_ref(v_toApplicative_405_);
v_toBind_406_ = lean_ctor_get(v_inst_404_, 1);
lean_inc(v_toBind_406_);
lean_dec_ref(v_inst_404_);
v_toPure_407_ = lean_ctor_get(v_toApplicative_405_, 1);
lean_inc(v_toPure_407_);
lean_dec_ref(v_toApplicative_405_);
v___f_408_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_408_, 0, v_toPure_407_);
lean_closure_set(v___f_408_, 1, v_inst_403_);
lean_closure_set(v___f_408_, 2, v_inst_402_);
lean_closure_set(v___f_408_, 3, v_toBind_406_);
return v___f_408_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop(lean_object* v_00_u03b1_409_, lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_, lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_n_415_, lean_object* v_inst_416_){
_start:
{
lean_object* v_toApplicative_417_; lean_object* v_toBind_418_; lean_object* v_toPure_419_; lean_object* v___f_420_; 
v_toApplicative_417_ = lean_ctor_get(v_inst_416_, 0);
lean_inc_ref(v_toApplicative_417_);
v_toBind_418_ = lean_ctor_get(v_inst_416_, 1);
lean_inc(v_toBind_418_);
lean_dec_ref(v_inst_416_);
v_toPure_419_ = lean_ctor_get(v_toApplicative_417_, 1);
lean_inc(v_toPure_419_);
lean_dec_ref(v_toApplicative_417_);
v___f_420_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_420_, 0, v_toPure_419_);
lean_closure_set(v___f_420_, 1, v_inst_412_);
lean_closure_set(v___f_420_, 2, v_inst_410_);
lean_closure_set(v___f_420_, 3, v_toBind_418_);
return v___f_420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___redArg(lean_object* v_____do__lift_421_, lean_object* v_h__1_422_, lean_object* v_h__2_423_){
_start:
{
if (lean_obj_tag(v_____do__lift_421_) == 0)
{
lean_object* v_a_424_; lean_object* v___x_425_; 
lean_dec(v_h__1_422_);
v_a_424_ = lean_ctor_get(v_____do__lift_421_, 0);
lean_inc(v_a_424_);
lean_dec_ref_known(v_____do__lift_421_, 1);
v___x_425_ = lean_apply_2(v_h__2_423_, v_a_424_, lean_box(0));
return v___x_425_;
}
else
{
lean_object* v_a_426_; lean_object* v___x_427_; 
lean_dec(v_h__2_423_);
v_a_426_ = lean_ctor_get(v_____do__lift_421_, 0);
lean_inc(v_a_426_);
lean_dec_ref_known(v_____do__lift_421_, 1);
v___x_427_ = lean_apply_2(v_h__1_422_, v_a_426_, lean_box(0));
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(lean_object* v_00_u03b1_428_, lean_object* v_00_u03b3_429_, lean_object* v_Pl_430_, lean_object* v_acc_431_, lean_object* v_next_432_, lean_object* v_motive_433_, lean_object* v_____do__lift_434_, lean_object* v_h__1_435_, lean_object* v_h__2_436_){
_start:
{
if (lean_obj_tag(v_____do__lift_434_) == 0)
{
lean_object* v_a_437_; lean_object* v___x_438_; 
lean_dec(v_h__1_435_);
v_a_437_ = lean_ctor_get(v_____do__lift_434_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v_____do__lift_434_, 1);
v___x_438_ = lean_apply_2(v_h__2_436_, v_a_437_, lean_box(0));
return v___x_438_;
}
else
{
lean_object* v_a_439_; lean_object* v___x_440_; 
lean_dec(v_h__2_436_);
v_a_439_ = lean_ctor_get(v_____do__lift_434_, 0);
lean_inc(v_a_439_);
lean_dec_ref_known(v_____do__lift_434_, 1);
v___x_440_ = lean_apply_2(v_h__1_435_, v_a_439_, lean_box(0));
return v___x_440_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___boxed(lean_object* v_00_u03b1_441_, lean_object* v_00_u03b3_442_, lean_object* v_Pl_443_, lean_object* v_acc_444_, lean_object* v_next_445_, lean_object* v_motive_446_, lean_object* v_____do__lift_447_, lean_object* v_h__1_448_, lean_object* v_h__2_449_){
_start:
{
lean_object* v_res_450_; 
v_res_450_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(v_00_u03b1_441_, v_00_u03b3_442_, v_Pl_443_, v_acc_444_, v_next_445_, v_motive_446_, v_____do__lift_447_, v_h__1_448_, v_h__2_449_);
lean_dec(v_next_445_);
lean_dec(v_acc_444_);
return v_res_450_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter___redArg(lean_object* v_x_451_, lean_object* v_h__1_452_, lean_object* v_h__2_453_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_object* v___x_454_; 
lean_dec(v_h__1_452_);
v___x_454_ = lean_apply_1(v_h__2_453_, lean_box(0));
return v___x_454_;
}
else
{
lean_object* v_val_455_; lean_object* v___x_456_; 
lean_dec(v_h__2_453_);
v_val_455_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_val_455_);
lean_dec_ref_known(v_x_451_, 1);
v___x_456_ = lean_apply_2(v_h__1_452_, v_val_455_, lean_box(0));
return v___x_456_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter(lean_object* v_00_u03b1_457_, lean_object* v_motive_458_, lean_object* v_x_459_, lean_object* v_h__1_460_, lean_object* v_h__2_461_){
_start:
{
if (lean_obj_tag(v_x_459_) == 0)
{
lean_object* v___x_462_; 
lean_dec(v_h__1_460_);
v___x_462_ = lean_apply_1(v_h__2_461_, lean_box(0));
return v___x_462_;
}
else
{
lean_object* v_val_463_; lean_object* v___x_464_; 
lean_dec(v_h__2_461_);
v_val_463_ = lean_ctor_get(v_x_459_, 0);
lean_inc(v_val_463_);
lean_dec_ref_known(v_x_459_, 1);
v___x_464_ = lean_apply_2(v_h__1_460_, v_val_463_, lean_box(0));
return v___x_464_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___redArg(lean_object* v_____do__lift_465_, lean_object* v_h__1_466_, lean_object* v_h__2_467_){
_start:
{
if (lean_obj_tag(v_____do__lift_465_) == 0)
{
lean_object* v_a_468_; lean_object* v___x_469_; 
lean_dec(v_h__1_466_);
v_a_468_ = lean_ctor_get(v_____do__lift_465_, 0);
lean_inc(v_a_468_);
lean_dec_ref_known(v_____do__lift_465_, 1);
v___x_469_ = lean_apply_2(v_h__2_467_, v_a_468_, lean_box(0));
return v___x_469_;
}
else
{
lean_object* v_a_470_; lean_object* v___x_471_; 
lean_dec(v_h__2_467_);
v_a_470_ = lean_ctor_get(v_____do__lift_465_, 0);
lean_inc(v_a_470_);
lean_dec_ref_known(v_____do__lift_465_, 1);
v___x_471_ = lean_apply_2(v_h__1_466_, v_a_470_, lean_box(0));
return v___x_471_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(lean_object* v_00_u03b1_472_, lean_object* v_00_u03b3_473_, lean_object* v_Pl_474_, lean_object* v_next_475_, lean_object* v_acc_476_, lean_object* v_motive_477_, lean_object* v_____do__lift_478_, lean_object* v_h__1_479_, lean_object* v_h__2_480_){
_start:
{
if (lean_obj_tag(v_____do__lift_478_) == 0)
{
lean_object* v_a_481_; lean_object* v___x_482_; 
lean_dec(v_h__1_479_);
v_a_481_ = lean_ctor_get(v_____do__lift_478_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_____do__lift_478_, 1);
v___x_482_ = lean_apply_2(v_h__2_480_, v_a_481_, lean_box(0));
return v___x_482_;
}
else
{
lean_object* v_a_483_; lean_object* v___x_484_; 
lean_dec(v_h__2_480_);
v_a_483_ = lean_ctor_get(v_____do__lift_478_, 0);
lean_inc(v_a_483_);
lean_dec_ref_known(v_____do__lift_478_, 1);
v___x_484_ = lean_apply_2(v_h__1_479_, v_a_483_, lean_box(0));
return v___x_484_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_485_, lean_object* v_00_u03b3_486_, lean_object* v_Pl_487_, lean_object* v_next_488_, lean_object* v_acc_489_, lean_object* v_motive_490_, lean_object* v_____do__lift_491_, lean_object* v_h__1_492_, lean_object* v_h__2_493_){
_start:
{
lean_object* v_res_494_; 
v_res_494_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(v_00_u03b1_485_, v_00_u03b3_486_, v_Pl_487_, v_next_488_, v_acc_489_, v_motive_490_, v_____do__lift_491_, v_h__1_492_, v_h__2_493_);
lean_dec(v_acc_489_);
lean_dec(v_next_488_);
return v_res_494_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_495_, lean_object* v_h__1_496_, lean_object* v_h__2_497_, lean_object* v_h__3_498_){
_start:
{
switch(lean_obj_tag(v_x_495_))
{
case 0:
{
lean_object* v_it_499_; lean_object* v_out_500_; lean_object* v___x_501_; 
lean_dec(v_h__3_498_);
lean_dec(v_h__2_497_);
v_it_499_ = lean_ctor_get(v_x_495_, 0);
lean_inc(v_it_499_);
v_out_500_ = lean_ctor_get(v_x_495_, 1);
lean_inc(v_out_500_);
lean_dec_ref_known(v_x_495_, 2);
v___x_501_ = lean_apply_3(v_h__1_496_, v_it_499_, v_out_500_, lean_box(0));
return v___x_501_;
}
case 1:
{
lean_object* v_it_502_; lean_object* v___x_503_; 
lean_dec(v_h__3_498_);
lean_dec(v_h__1_496_);
v_it_502_ = lean_ctor_get(v_x_495_, 0);
lean_inc(v_it_502_);
lean_dec_ref_known(v_x_495_, 1);
v___x_503_ = lean_apply_2(v_h__2_497_, v_it_502_, lean_box(0));
return v___x_503_;
}
default: 
{
lean_object* v___x_504_; 
lean_dec(v_h__2_497_);
lean_dec(v_h__1_496_);
v___x_504_ = lean_apply_1(v_h__3_498_, lean_box(0));
return v___x_504_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_505_, lean_object* v_00_u03b2_506_, lean_object* v_m_507_, lean_object* v_inst_508_, lean_object* v_it_509_, lean_object* v_motive_510_, lean_object* v_x_511_, lean_object* v_h__1_512_, lean_object* v_h__2_513_, lean_object* v_h__3_514_){
_start:
{
switch(lean_obj_tag(v_x_511_))
{
case 0:
{
lean_object* v_it_515_; lean_object* v_out_516_; lean_object* v___x_517_; 
lean_dec(v_h__3_514_);
lean_dec(v_h__2_513_);
v_it_515_ = lean_ctor_get(v_x_511_, 0);
lean_inc(v_it_515_);
v_out_516_ = lean_ctor_get(v_x_511_, 1);
lean_inc(v_out_516_);
lean_dec_ref_known(v_x_511_, 2);
v___x_517_ = lean_apply_3(v_h__1_512_, v_it_515_, v_out_516_, lean_box(0));
return v___x_517_;
}
case 1:
{
lean_object* v_it_518_; lean_object* v___x_519_; 
lean_dec(v_h__3_514_);
lean_dec(v_h__1_512_);
v_it_518_ = lean_ctor_get(v_x_511_, 0);
lean_inc(v_it_518_);
lean_dec_ref_known(v_x_511_, 1);
v___x_519_ = lean_apply_2(v_h__2_513_, v_it_518_, lean_box(0));
return v___x_519_;
}
default: 
{
lean_object* v___x_520_; 
lean_dec(v_h__2_513_);
lean_dec(v_h__1_512_);
v___x_520_ = lean_apply_1(v_h__3_514_, lean_box(0));
return v___x_520_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_521_, lean_object* v_00_u03b2_522_, lean_object* v_m_523_, lean_object* v_inst_524_, lean_object* v_it_525_, lean_object* v_motive_526_, lean_object* v_x_527_, lean_object* v_h__1_528_, lean_object* v_h__2_529_, lean_object* v_h__3_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_521_, v_00_u03b2_522_, v_m_523_, v_inst_524_, v_it_525_, v_motive_526_, v_x_527_, v_h__1_528_, v_h__2_529_, v_h__3_530_);
lean_dec(v_it_525_);
lean_dec(v_inst_524_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
if (lean_obj_tag(v_____do__lift_532_) == 0)
{
lean_object* v_a_535_; lean_object* v___x_536_; 
lean_dec(v_h__1_533_);
v_a_535_ = lean_ctor_get(v_____do__lift_532_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v_____do__lift_532_, 1);
v___x_536_ = lean_apply_2(v_h__2_534_, v_a_535_, lean_box(0));
return v___x_536_;
}
else
{
lean_object* v_a_537_; lean_object* v___x_538_; 
lean_dec(v_h__2_534_);
v_a_537_ = lean_ctor_get(v_____do__lift_532_, 0);
lean_inc(v_a_537_);
lean_dec_ref_known(v_____do__lift_532_, 1);
v___x_538_ = lean_apply_2(v_h__1_533_, v_a_537_, lean_box(0));
return v___x_538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b2_539_, lean_object* v_00_u03b3_540_, lean_object* v_init_541_, lean_object* v_PlausibleForInStep_542_, lean_object* v_out_543_, lean_object* v_motive_544_, lean_object* v_____do__lift_545_, lean_object* v_h__1_546_, lean_object* v_h__2_547_){
_start:
{
if (lean_obj_tag(v_____do__lift_545_) == 0)
{
lean_object* v_a_548_; lean_object* v___x_549_; 
lean_dec(v_h__1_546_);
v_a_548_ = lean_ctor_get(v_____do__lift_545_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v_____do__lift_545_, 1);
v___x_549_ = lean_apply_2(v_h__2_547_, v_a_548_, lean_box(0));
return v___x_549_;
}
else
{
lean_object* v_a_550_; lean_object* v___x_551_; 
lean_dec(v_h__2_547_);
v_a_550_ = lean_ctor_get(v_____do__lift_545_, 0);
lean_inc(v_a_550_);
lean_dec_ref_known(v_____do__lift_545_, 1);
v___x_551_ = lean_apply_2(v_h__1_546_, v_a_550_, lean_box(0));
return v___x_551_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(lean_object* v_00_u03b2_552_, lean_object* v_00_u03b3_553_, lean_object* v_init_554_, lean_object* v_PlausibleForInStep_555_, lean_object* v_out_556_, lean_object* v_motive_557_, lean_object* v_____do__lift_558_, lean_object* v_h__1_559_, lean_object* v_h__2_560_){
_start:
{
lean_object* v_res_561_; 
v_res_561_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_552_, v_00_u03b3_553_, v_init_554_, v_PlausibleForInStep_555_, v_out_556_, v_motive_557_, v_____do__lift_558_, v_h__1_559_, v_h__2_560_);
lean_dec(v_out_556_);
lean_dec(v_init_554_);
return v_res_561_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_562_, lean_object* v_f_563_, lean_object* v_h__1_564_, lean_object* v_h__2_565_){
_start:
{
lean_object* v_next_566_; 
v_next_566_ = lean_ctor_get(v_it_562_, 0);
if (lean_obj_tag(v_next_566_) == 0)
{
lean_object* v_upperBound_567_; lean_object* v___x_568_; 
lean_dec(v_h__1_564_);
v_upperBound_567_ = lean_ctor_get(v_it_562_, 1);
lean_inc(v_upperBound_567_);
lean_dec_ref(v_it_562_);
v___x_568_ = lean_apply_2(v_h__2_565_, v_upperBound_567_, v_f_563_);
return v___x_568_;
}
else
{
lean_object* v_upperBound_569_; lean_object* v_val_570_; lean_object* v___x_571_; 
lean_inc_ref(v_next_566_);
lean_dec(v_h__2_565_);
v_upperBound_569_ = lean_ctor_get(v_it_562_, 1);
lean_inc(v_upperBound_569_);
lean_dec_ref(v_it_562_);
v_val_570_ = lean_ctor_get(v_next_566_, 0);
lean_inc(v_val_570_);
lean_dec_ref_known(v_next_566_, 1);
v___x_571_ = lean_apply_3(v_h__1_564_, v_val_570_, v_upperBound_569_, v_f_563_);
return v___x_571_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_572_, lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_inst_575_, lean_object* v_n_576_, lean_object* v_00_u03b3_577_, lean_object* v_Pl_578_, lean_object* v_motive_579_, lean_object* v_it_580_, lean_object* v_f_581_, lean_object* v_h__1_582_, lean_object* v_h__2_583_){
_start:
{
lean_object* v_next_584_; 
v_next_584_ = lean_ctor_get(v_it_580_, 0);
if (lean_obj_tag(v_next_584_) == 0)
{
lean_object* v_upperBound_585_; lean_object* v___x_586_; 
lean_dec(v_h__1_582_);
v_upperBound_585_ = lean_ctor_get(v_it_580_, 1);
lean_inc(v_upperBound_585_);
lean_dec_ref(v_it_580_);
v___x_586_ = lean_apply_2(v_h__2_583_, v_upperBound_585_, v_f_581_);
return v___x_586_;
}
else
{
lean_object* v_upperBound_587_; lean_object* v_val_588_; lean_object* v___x_589_; 
lean_inc_ref(v_next_584_);
lean_dec(v_h__2_583_);
v_upperBound_587_ = lean_ctor_get(v_it_580_, 1);
lean_inc(v_upperBound_587_);
lean_dec_ref(v_it_580_);
v_val_588_ = lean_ctor_get(v_next_584_, 0);
lean_inc(v_val_588_);
lean_dec_ref_known(v_next_584_, 1);
v___x_589_ = lean_apply_3(v_h__1_582_, v_val_588_, v_upperBound_587_, v_f_581_);
return v___x_589_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_590_, lean_object* v_inst_591_, lean_object* v_inst_592_, lean_object* v_inst_593_, lean_object* v_n_594_, lean_object* v_00_u03b3_595_, lean_object* v_Pl_596_, lean_object* v_motive_597_, lean_object* v_it_598_, lean_object* v_f_599_, lean_object* v_h__1_600_, lean_object* v_h__2_601_){
_start:
{
lean_object* v_res_602_; 
v_res_602_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_590_, v_inst_591_, v_inst_592_, v_inst_593_, v_n_594_, v_00_u03b3_595_, v_Pl_596_, v_motive_597_, v_it_598_, v_f_599_, v_h__1_600_, v_h__2_601_);
lean_dec_ref(v_inst_593_);
lean_dec_ref(v_inst_591_);
return v_res_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object* v_x_603_, lean_object* v_h__1_604_, lean_object* v_h__2_605_, lean_object* v_h__3_606_){
_start:
{
switch(lean_obj_tag(v_x_603_))
{
case 0:
{
lean_object* v_it_607_; lean_object* v_out_608_; lean_object* v___x_609_; 
lean_dec(v_h__3_606_);
lean_dec(v_h__2_605_);
v_it_607_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_it_607_);
v_out_608_ = lean_ctor_get(v_x_603_, 1);
lean_inc(v_out_608_);
lean_dec_ref_known(v_x_603_, 2);
v___x_609_ = lean_apply_3(v_h__1_604_, v_it_607_, v_out_608_, lean_box(0));
return v___x_609_;
}
case 1:
{
lean_object* v_it_610_; lean_object* v___x_611_; 
lean_dec(v_h__3_606_);
lean_dec(v_h__1_604_);
v_it_610_ = lean_ctor_get(v_x_603_, 0);
lean_inc(v_it_610_);
lean_dec_ref_known(v_x_603_, 1);
v___x_611_ = lean_apply_2(v_h__2_605_, v_it_610_, lean_box(0));
return v___x_611_;
}
default: 
{
lean_object* v___x_612_; 
lean_dec(v_h__2_605_);
lean_dec(v_h__1_604_);
v___x_612_ = lean_apply_1(v_h__3_606_, lean_box(0));
return v___x_612_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object* v_m_613_, lean_object* v_00_u03b1_614_, lean_object* v_00_u03b2_615_, lean_object* v_inst_616_, lean_object* v_it_617_, lean_object* v_motive_618_, lean_object* v_x_619_, lean_object* v_h__1_620_, lean_object* v_h__2_621_, lean_object* v_h__3_622_){
_start:
{
switch(lean_obj_tag(v_x_619_))
{
case 0:
{
lean_object* v_it_623_; lean_object* v_out_624_; lean_object* v___x_625_; 
lean_dec(v_h__3_622_);
lean_dec(v_h__2_621_);
v_it_623_ = lean_ctor_get(v_x_619_, 0);
lean_inc(v_it_623_);
v_out_624_ = lean_ctor_get(v_x_619_, 1);
lean_inc(v_out_624_);
lean_dec_ref_known(v_x_619_, 2);
v___x_625_ = lean_apply_3(v_h__1_620_, v_it_623_, v_out_624_, lean_box(0));
return v___x_625_;
}
case 1:
{
lean_object* v_it_626_; lean_object* v___x_627_; 
lean_dec(v_h__3_622_);
lean_dec(v_h__1_620_);
v_it_626_ = lean_ctor_get(v_x_619_, 0);
lean_inc(v_it_626_);
lean_dec_ref_known(v_x_619_, 1);
v___x_627_ = lean_apply_2(v_h__2_621_, v_it_626_, lean_box(0));
return v___x_627_;
}
default: 
{
lean_object* v___x_628_; 
lean_dec(v_h__2_621_);
lean_dec(v_h__1_620_);
v___x_628_ = lean_apply_1(v_h__3_622_, lean_box(0));
return v___x_628_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object* v_m_629_, lean_object* v_00_u03b1_630_, lean_object* v_00_u03b2_631_, lean_object* v_inst_632_, lean_object* v_it_633_, lean_object* v_motive_634_, lean_object* v_x_635_, lean_object* v_h__1_636_, lean_object* v_h__2_637_, lean_object* v_h__3_638_){
_start:
{
lean_object* v_res_639_; 
v_res_639_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_629_, v_00_u03b1_630_, v_00_u03b2_631_, v_inst_632_, v_it_633_, v_motive_634_, v_x_635_, v_h__1_636_, v_h__2_637_, v_h__3_638_);
lean_dec(v_it_633_);
lean_dec(v_inst_632_);
return v_res_639_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object* v_____do__lift_640_, lean_object* v_h__1_641_, lean_object* v_h__2_642_){
_start:
{
if (lean_obj_tag(v_____do__lift_640_) == 0)
{
lean_object* v_a_643_; lean_object* v___x_644_; 
lean_dec(v_h__1_641_);
v_a_643_ = lean_ctor_get(v_____do__lift_640_, 0);
lean_inc(v_a_643_);
lean_dec_ref_known(v_____do__lift_640_, 1);
v___x_644_ = lean_apply_2(v_h__2_642_, v_a_643_, lean_box(0));
return v___x_644_;
}
else
{
lean_object* v_a_645_; lean_object* v___x_646_; 
lean_dec(v_h__2_642_);
v_a_645_ = lean_ctor_get(v_____do__lift_640_, 0);
lean_inc(v_a_645_);
lean_dec_ref_known(v_____do__lift_640_, 1);
v___x_646_ = lean_apply_2(v_h__1_641_, v_a_645_, lean_box(0));
return v___x_646_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object* v_00_u03b2_647_, lean_object* v_00_u03b3_648_, lean_object* v_PlausibleForInStep_649_, lean_object* v_acc_650_, lean_object* v_out_651_, lean_object* v_motive_652_, lean_object* v_____do__lift_653_, lean_object* v_h__1_654_, lean_object* v_h__2_655_){
_start:
{
if (lean_obj_tag(v_____do__lift_653_) == 0)
{
lean_object* v_a_656_; lean_object* v___x_657_; 
lean_dec(v_h__1_654_);
v_a_656_ = lean_ctor_get(v_____do__lift_653_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v_____do__lift_653_, 1);
v___x_657_ = lean_apply_2(v_h__2_655_, v_a_656_, lean_box(0));
return v___x_657_;
}
else
{
lean_object* v_a_658_; lean_object* v___x_659_; 
lean_dec(v_h__2_655_);
v_a_658_ = lean_ctor_get(v_____do__lift_653_, 0);
lean_inc(v_a_658_);
lean_dec_ref_known(v_____do__lift_653_, 1);
v___x_659_ = lean_apply_2(v_h__1_654_, v_a_658_, lean_box(0));
return v___x_659_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object* v_00_u03b2_660_, lean_object* v_00_u03b3_661_, lean_object* v_PlausibleForInStep_662_, lean_object* v_acc_663_, lean_object* v_out_664_, lean_object* v_motive_665_, lean_object* v_____do__lift_666_, lean_object* v_h__1_667_, lean_object* v_h__2_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_660_, v_00_u03b3_661_, v_PlausibleForInStep_662_, v_acc_663_, v_out_664_, v_motive_665_, v_____do__lift_666_, v_h__1_667_, v_h__2_668_);
lean_dec(v_out_664_);
lean_dec(v_acc_663_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step___redArg(lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_it_672_){
_start:
{
lean_object* v_next_673_; 
v_next_673_ = lean_ctor_get(v_it_672_, 0);
lean_inc(v_next_673_);
if (lean_obj_tag(v_next_673_) == 0)
{
lean_object* v___x_674_; 
lean_dec_ref(v_it_672_);
lean_dec_ref(v_inst_671_);
lean_dec_ref(v_inst_670_);
v___x_674_ = lean_box(2);
return v___x_674_;
}
else
{
lean_object* v_upperBound_675_; lean_object* v___x_677_; uint8_t v_isShared_678_; uint8_t v_isSharedCheck_696_; 
v_upperBound_675_ = lean_ctor_get(v_it_672_, 1);
v_isSharedCheck_696_ = !lean_is_exclusive(v_it_672_);
if (v_isSharedCheck_696_ == 0)
{
lean_object* v_unused_697_; 
v_unused_697_ = lean_ctor_get(v_it_672_, 0);
lean_dec(v_unused_697_);
v___x_677_ = v_it_672_;
v_isShared_678_ = v_isSharedCheck_696_;
goto v_resetjp_676_;
}
else
{
lean_inc(v_upperBound_675_);
lean_dec(v_it_672_);
v___x_677_ = lean_box(0);
v_isShared_678_ = v_isSharedCheck_696_;
goto v_resetjp_676_;
}
v_resetjp_676_:
{
lean_object* v_val_679_; lean_object* v___x_680_; uint8_t v___x_681_; 
v_val_679_ = lean_ctor_get(v_next_673_, 0);
lean_inc_n(v_val_679_, 2);
lean_dec_ref_known(v_next_673_, 1);
lean_inc(v_upperBound_675_);
v___x_680_ = lean_apply_2(v_inst_671_, v_val_679_, v_upperBound_675_);
v___x_681_ = lean_unbox(v___x_680_);
if (v___x_681_ == 0)
{
lean_object* v___x_682_; 
lean_dec(v_val_679_);
lean_del_object(v___x_677_);
lean_dec(v_upperBound_675_);
lean_dec_ref(v_inst_670_);
v___x_682_ = lean_box(2);
return v___x_682_;
}
else
{
lean_object* v_succ_x3f_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_694_; 
v_succ_x3f_683_ = lean_ctor_get(v_inst_670_, 0);
v_isSharedCheck_694_ = !lean_is_exclusive(v_inst_670_);
if (v_isSharedCheck_694_ == 0)
{
lean_object* v_unused_695_; 
v_unused_695_ = lean_ctor_get(v_inst_670_, 1);
lean_dec(v_unused_695_);
v___x_685_ = v_inst_670_;
v_isShared_686_ = v_isSharedCheck_694_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_succ_x3f_683_);
lean_dec(v_inst_670_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_694_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v___x_687_; lean_object* v___x_689_; 
lean_inc(v_val_679_);
v___x_687_ = lean_apply_1(v_succ_x3f_683_, v_val_679_);
if (v_isShared_678_ == 0)
{
lean_ctor_set(v___x_677_, 0, v___x_687_);
v___x_689_ = v___x_677_;
goto v_reusejp_688_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_687_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_upperBound_675_);
v___x_689_ = v_reuseFailAlloc_693_;
goto v_reusejp_688_;
}
v_reusejp_688_:
{
lean_object* v___x_691_; 
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 1, v_val_679_);
lean_ctor_set(v___x_685_, 0, v___x_689_);
v___x_691_ = v___x_685_;
goto v_reusejp_690_;
}
else
{
lean_object* v_reuseFailAlloc_692_; 
v_reuseFailAlloc_692_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_692_, 0, v___x_689_);
lean_ctor_set(v_reuseFailAlloc_692_, 1, v_val_679_);
v___x_691_ = v_reuseFailAlloc_692_;
goto v_reusejp_690_;
}
v_reusejp_690_:
{
return v___x_691_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step(lean_object* v_00_u03b1_698_, lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_inst_701_, lean_object* v_it_702_){
_start:
{
lean_object* v_next_703_; 
v_next_703_ = lean_ctor_get(v_it_702_, 0);
lean_inc(v_next_703_);
if (lean_obj_tag(v_next_703_) == 0)
{
lean_object* v___x_704_; 
lean_dec_ref(v_it_702_);
lean_dec_ref(v_inst_701_);
lean_dec_ref(v_inst_699_);
v___x_704_ = lean_box(2);
return v___x_704_;
}
else
{
lean_object* v_upperBound_705_; lean_object* v___x_707_; uint8_t v_isShared_708_; uint8_t v_isSharedCheck_726_; 
v_upperBound_705_ = lean_ctor_get(v_it_702_, 1);
v_isSharedCheck_726_ = !lean_is_exclusive(v_it_702_);
if (v_isSharedCheck_726_ == 0)
{
lean_object* v_unused_727_; 
v_unused_727_ = lean_ctor_get(v_it_702_, 0);
lean_dec(v_unused_727_);
v___x_707_ = v_it_702_;
v_isShared_708_ = v_isSharedCheck_726_;
goto v_resetjp_706_;
}
else
{
lean_inc(v_upperBound_705_);
lean_dec(v_it_702_);
v___x_707_ = lean_box(0);
v_isShared_708_ = v_isSharedCheck_726_;
goto v_resetjp_706_;
}
v_resetjp_706_:
{
lean_object* v_val_709_; lean_object* v___x_710_; uint8_t v___x_711_; 
v_val_709_ = lean_ctor_get(v_next_703_, 0);
lean_inc_n(v_val_709_, 2);
lean_dec_ref_known(v_next_703_, 1);
lean_inc(v_upperBound_705_);
v___x_710_ = lean_apply_2(v_inst_701_, v_val_709_, v_upperBound_705_);
v___x_711_ = lean_unbox(v___x_710_);
if (v___x_711_ == 0)
{
lean_object* v___x_712_; 
lean_dec(v_val_709_);
lean_del_object(v___x_707_);
lean_dec(v_upperBound_705_);
lean_dec_ref(v_inst_699_);
v___x_712_ = lean_box(2);
return v___x_712_;
}
else
{
lean_object* v_succ_x3f_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_724_; 
v_succ_x3f_713_ = lean_ctor_get(v_inst_699_, 0);
v_isSharedCheck_724_ = !lean_is_exclusive(v_inst_699_);
if (v_isSharedCheck_724_ == 0)
{
lean_object* v_unused_725_; 
v_unused_725_ = lean_ctor_get(v_inst_699_, 1);
lean_dec(v_unused_725_);
v___x_715_ = v_inst_699_;
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_succ_x3f_713_);
lean_dec(v_inst_699_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_724_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v___x_717_; lean_object* v___x_719_; 
lean_inc(v_val_709_);
v___x_717_ = lean_apply_1(v_succ_x3f_713_, v_val_709_);
if (v_isShared_708_ == 0)
{
lean_ctor_set(v___x_707_, 0, v___x_717_);
v___x_719_ = v___x_707_;
goto v_reusejp_718_;
}
else
{
lean_object* v_reuseFailAlloc_723_; 
v_reuseFailAlloc_723_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_723_, 0, v___x_717_);
lean_ctor_set(v_reuseFailAlloc_723_, 1, v_upperBound_705_);
v___x_719_ = v_reuseFailAlloc_723_;
goto v_reusejp_718_;
}
v_reusejp_718_:
{
lean_object* v___x_721_; 
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 1, v_val_709_);
lean_ctor_set(v___x_715_, 0, v___x_719_);
v___x_721_ = v___x_715_;
goto v_reusejp_720_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_719_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_val_709_);
v___x_721_ = v_reuseFailAlloc_722_;
goto v_reusejp_720_;
}
v_reusejp_720_:
{
return v___x_721_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step___redArg(lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_it_730_){
_start:
{
lean_object* v_next_731_; 
v_next_731_ = lean_ctor_get(v_it_730_, 0);
lean_inc(v_next_731_);
if (lean_obj_tag(v_next_731_) == 0)
{
lean_object* v___x_732_; 
lean_dec_ref(v_it_730_);
lean_dec_ref(v_inst_729_);
lean_dec_ref(v_inst_728_);
v___x_732_ = lean_box(2);
return v___x_732_;
}
else
{
lean_object* v_upperBound_733_; lean_object* v___x_735_; uint8_t v_isShared_736_; uint8_t v_isSharedCheck_754_; 
v_upperBound_733_ = lean_ctor_get(v_it_730_, 1);
v_isSharedCheck_754_ = !lean_is_exclusive(v_it_730_);
if (v_isSharedCheck_754_ == 0)
{
lean_object* v_unused_755_; 
v_unused_755_ = lean_ctor_get(v_it_730_, 0);
lean_dec(v_unused_755_);
v___x_735_ = v_it_730_;
v_isShared_736_ = v_isSharedCheck_754_;
goto v_resetjp_734_;
}
else
{
lean_inc(v_upperBound_733_);
lean_dec(v_it_730_);
v___x_735_ = lean_box(0);
v_isShared_736_ = v_isSharedCheck_754_;
goto v_resetjp_734_;
}
v_resetjp_734_:
{
lean_object* v_val_737_; lean_object* v___x_738_; uint8_t v___x_739_; 
v_val_737_ = lean_ctor_get(v_next_731_, 0);
lean_inc_n(v_val_737_, 2);
lean_dec_ref_known(v_next_731_, 1);
lean_inc(v_upperBound_733_);
v___x_738_ = lean_apply_2(v_inst_729_, v_val_737_, v_upperBound_733_);
v___x_739_ = lean_unbox(v___x_738_);
if (v___x_739_ == 0)
{
lean_object* v___x_740_; 
lean_dec(v_val_737_);
lean_del_object(v___x_735_);
lean_dec(v_upperBound_733_);
lean_dec_ref(v_inst_728_);
v___x_740_ = lean_box(2);
return v___x_740_;
}
else
{
lean_object* v_succ_x3f_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_752_; 
v_succ_x3f_741_ = lean_ctor_get(v_inst_728_, 0);
v_isSharedCheck_752_ = !lean_is_exclusive(v_inst_728_);
if (v_isSharedCheck_752_ == 0)
{
lean_object* v_unused_753_; 
v_unused_753_ = lean_ctor_get(v_inst_728_, 1);
lean_dec(v_unused_753_);
v___x_743_ = v_inst_728_;
v_isShared_744_ = v_isSharedCheck_752_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_succ_x3f_741_);
lean_dec(v_inst_728_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_752_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v___x_745_; lean_object* v___x_747_; 
lean_inc(v_val_737_);
v___x_745_ = lean_apply_1(v_succ_x3f_741_, v_val_737_);
if (v_isShared_736_ == 0)
{
lean_ctor_set(v___x_735_, 0, v___x_745_);
v___x_747_ = v___x_735_;
goto v_reusejp_746_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_745_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_upperBound_733_);
v___x_747_ = v_reuseFailAlloc_751_;
goto v_reusejp_746_;
}
v_reusejp_746_:
{
lean_object* v___x_749_; 
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 1, v_val_737_);
lean_ctor_set(v___x_743_, 0, v___x_747_);
v___x_749_ = v___x_743_;
goto v_reusejp_748_;
}
else
{
lean_object* v_reuseFailAlloc_750_; 
v_reuseFailAlloc_750_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_750_, 0, v___x_747_);
lean_ctor_set(v_reuseFailAlloc_750_, 1, v_val_737_);
v___x_749_ = v_reuseFailAlloc_750_;
goto v_reusejp_748_;
}
v_reusejp_748_:
{
return v___x_749_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step(lean_object* v_00_u03b1_756_, lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_inst_759_, lean_object* v_it_760_){
_start:
{
lean_object* v_next_761_; 
v_next_761_ = lean_ctor_get(v_it_760_, 0);
lean_inc(v_next_761_);
if (lean_obj_tag(v_next_761_) == 0)
{
lean_object* v___x_762_; 
lean_dec_ref(v_it_760_);
lean_dec_ref(v_inst_759_);
lean_dec_ref(v_inst_757_);
v___x_762_ = lean_box(2);
return v___x_762_;
}
else
{
lean_object* v_upperBound_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_784_; 
v_upperBound_763_ = lean_ctor_get(v_it_760_, 1);
v_isSharedCheck_784_ = !lean_is_exclusive(v_it_760_);
if (v_isSharedCheck_784_ == 0)
{
lean_object* v_unused_785_; 
v_unused_785_ = lean_ctor_get(v_it_760_, 0);
lean_dec(v_unused_785_);
v___x_765_ = v_it_760_;
v_isShared_766_ = v_isSharedCheck_784_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_upperBound_763_);
lean_dec(v_it_760_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_784_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v_val_767_; lean_object* v___x_768_; uint8_t v___x_769_; 
v_val_767_ = lean_ctor_get(v_next_761_, 0);
lean_inc_n(v_val_767_, 2);
lean_dec_ref_known(v_next_761_, 1);
lean_inc(v_upperBound_763_);
v___x_768_ = lean_apply_2(v_inst_759_, v_val_767_, v_upperBound_763_);
v___x_769_ = lean_unbox(v___x_768_);
if (v___x_769_ == 0)
{
lean_object* v___x_770_; 
lean_dec(v_val_767_);
lean_del_object(v___x_765_);
lean_dec(v_upperBound_763_);
lean_dec_ref(v_inst_757_);
v___x_770_ = lean_box(2);
return v___x_770_;
}
else
{
lean_object* v_succ_x3f_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_782_; 
v_succ_x3f_771_ = lean_ctor_get(v_inst_757_, 0);
v_isSharedCheck_782_ = !lean_is_exclusive(v_inst_757_);
if (v_isSharedCheck_782_ == 0)
{
lean_object* v_unused_783_; 
v_unused_783_ = lean_ctor_get(v_inst_757_, 1);
lean_dec(v_unused_783_);
v___x_773_ = v_inst_757_;
v_isShared_774_ = v_isSharedCheck_782_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_succ_x3f_771_);
lean_dec(v_inst_757_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_782_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v___x_775_; lean_object* v___x_777_; 
lean_inc(v_val_767_);
v___x_775_ = lean_apply_1(v_succ_x3f_771_, v_val_767_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 0, v___x_775_);
v___x_777_ = v___x_765_;
goto v_reusejp_776_;
}
else
{
lean_object* v_reuseFailAlloc_781_; 
v_reuseFailAlloc_781_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_781_, 0, v___x_775_);
lean_ctor_set(v_reuseFailAlloc_781_, 1, v_upperBound_763_);
v___x_777_ = v_reuseFailAlloc_781_;
goto v_reusejp_776_;
}
v_reusejp_776_:
{
lean_object* v___x_779_; 
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 1, v_val_767_);
lean_ctor_set(v___x_773_, 0, v___x_777_);
v___x_779_ = v___x_773_;
goto v_reusejp_778_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_777_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_val_767_);
v___x_779_ = v_reuseFailAlloc_780_;
goto v_reusejp_778_;
}
v_reusejp_778_:
{
return v___x_779_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0(lean_object* v_inst_786_, lean_object* v_inst_787_, lean_object* v_it_788_){
_start:
{
lean_object* v_next_789_; 
v_next_789_ = lean_ctor_get(v_it_788_, 0);
lean_inc(v_next_789_);
if (lean_obj_tag(v_next_789_) == 0)
{
lean_object* v___x_790_; 
lean_dec_ref(v_it_788_);
lean_dec_ref(v_inst_787_);
lean_dec_ref(v_inst_786_);
v___x_790_ = lean_box(2);
return v___x_790_;
}
else
{
lean_object* v_upperBound_791_; lean_object* v___x_793_; uint8_t v_isShared_794_; uint8_t v_isSharedCheck_812_; 
v_upperBound_791_ = lean_ctor_get(v_it_788_, 1);
v_isSharedCheck_812_ = !lean_is_exclusive(v_it_788_);
if (v_isSharedCheck_812_ == 0)
{
lean_object* v_unused_813_; 
v_unused_813_ = lean_ctor_get(v_it_788_, 0);
lean_dec(v_unused_813_);
v___x_793_ = v_it_788_;
v_isShared_794_ = v_isSharedCheck_812_;
goto v_resetjp_792_;
}
else
{
lean_inc(v_upperBound_791_);
lean_dec(v_it_788_);
v___x_793_ = lean_box(0);
v_isShared_794_ = v_isSharedCheck_812_;
goto v_resetjp_792_;
}
v_resetjp_792_:
{
lean_object* v_val_795_; lean_object* v___x_796_; uint8_t v___x_797_; 
v_val_795_ = lean_ctor_get(v_next_789_, 0);
lean_inc_n(v_val_795_, 2);
lean_dec_ref_known(v_next_789_, 1);
lean_inc(v_upperBound_791_);
v___x_796_ = lean_apply_2(v_inst_786_, v_val_795_, v_upperBound_791_);
v___x_797_ = lean_unbox(v___x_796_);
if (v___x_797_ == 0)
{
lean_object* v___x_798_; 
lean_dec(v_val_795_);
lean_del_object(v___x_793_);
lean_dec(v_upperBound_791_);
lean_dec_ref(v_inst_787_);
v___x_798_ = lean_box(2);
return v___x_798_;
}
else
{
lean_object* v_succ_x3f_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_810_; 
v_succ_x3f_799_ = lean_ctor_get(v_inst_787_, 0);
v_isSharedCheck_810_ = !lean_is_exclusive(v_inst_787_);
if (v_isSharedCheck_810_ == 0)
{
lean_object* v_unused_811_; 
v_unused_811_ = lean_ctor_get(v_inst_787_, 1);
lean_dec(v_unused_811_);
v___x_801_ = v_inst_787_;
v_isShared_802_ = v_isSharedCheck_810_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_succ_x3f_799_);
lean_dec(v_inst_787_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_810_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v___x_803_; lean_object* v___x_805_; 
lean_inc(v_val_795_);
v___x_803_ = lean_apply_1(v_succ_x3f_799_, v_val_795_);
if (v_isShared_794_ == 0)
{
lean_ctor_set(v___x_793_, 0, v___x_803_);
v___x_805_ = v___x_793_;
goto v_reusejp_804_;
}
else
{
lean_object* v_reuseFailAlloc_809_; 
v_reuseFailAlloc_809_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_809_, 0, v___x_803_);
lean_ctor_set(v_reuseFailAlloc_809_, 1, v_upperBound_791_);
v___x_805_ = v_reuseFailAlloc_809_;
goto v_reusejp_804_;
}
v_reusejp_804_:
{
lean_object* v___x_807_; 
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 1, v_val_795_);
lean_ctor_set(v___x_801_, 0, v___x_805_);
v___x_807_ = v___x_801_;
goto v_reusejp_806_;
}
else
{
lean_object* v_reuseFailAlloc_808_; 
v_reuseFailAlloc_808_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_808_, 0, v___x_805_);
lean_ctor_set(v_reuseFailAlloc_808_, 1, v_val_795_);
v___x_807_ = v_reuseFailAlloc_808_;
goto v_reusejp_806_;
}
v_reusejp_806_:
{
return v___x_807_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg(lean_object* v_inst_814_, lean_object* v_inst_815_){
_start:
{
lean_object* v___f_816_; 
v___f_816_ = lean_alloc_closure((void*)(l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_816_, 0, v_inst_815_);
lean_closure_set(v___f_816_, 1, v_inst_814_);
return v___f_816_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT(lean_object* v_00_u03b1_817_, lean_object* v_inst_818_, lean_object* v_inst_819_, lean_object* v_inst_820_){
_start:
{
lean_object* v___f_821_; 
v___f_821_ = lean_alloc_closure((void*)(l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_821_, 0, v_inst_820_);
lean_closure_set(v___f_821_, 1, v_inst_818_);
return v___f_821_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_822_, lean_object* v_inst_823_, lean_object* v_inst_824_, lean_object* v_inst_825_, lean_object* v_inst_826_, lean_object* v_inst_827_){
_start:
{
lean_object* v___x_828_; 
v___x_828_ = lean_box(0);
return v___x_828_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_inst_832_, lean_object* v_inst_833_, lean_object* v_inst_834_){
_start:
{
lean_object* v_res_835_; 
v_res_835_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(v_00_u03b1_829_, v_inst_830_, v_inst_831_, v_inst_832_, v_inst_833_, v_inst_834_);
lean_dec_ref(v_inst_832_);
lean_dec_ref(v_inst_830_);
return v_res_835_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_836_, lean_object* v_inst_837_, lean_object* v_inst_838_, lean_object* v_inst_839_, lean_object* v_inst_840_){
_start:
{
lean_object* v___x_841_; 
v___x_841_ = lean_box(0);
return v___x_841_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_inst_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(v_00_u03b1_842_, v_inst_843_, v_inst_844_, v_inst_845_, v_inst_846_);
lean_dec_ref(v_inst_845_);
lean_dec_ref(v_inst_843_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v_it_850_, lean_object* v_n_851_){
_start:
{
lean_object* v_next_852_; 
v_next_852_ = lean_ctor_get(v_it_850_, 0);
lean_inc(v_next_852_);
if (lean_obj_tag(v_next_852_) == 0)
{
lean_object* v___x_853_; 
lean_dec(v_n_851_);
lean_dec_ref(v_it_850_);
lean_dec_ref(v_inst_849_);
lean_dec_ref(v_inst_848_);
v___x_853_ = lean_box(2);
return v___x_853_;
}
else
{
lean_object* v_upperBound_854_; lean_object* v___x_856_; uint8_t v_isShared_857_; uint8_t v_isSharedCheck_878_; 
v_upperBound_854_ = lean_ctor_get(v_it_850_, 1);
v_isSharedCheck_878_ = !lean_is_exclusive(v_it_850_);
if (v_isSharedCheck_878_ == 0)
{
lean_object* v_unused_879_; 
v_unused_879_ = lean_ctor_get(v_it_850_, 0);
lean_dec(v_unused_879_);
v___x_856_ = v_it_850_;
v_isShared_857_ = v_isSharedCheck_878_;
goto v_resetjp_855_;
}
else
{
lean_inc(v_upperBound_854_);
lean_dec(v_it_850_);
v___x_856_ = lean_box(0);
v_isShared_857_ = v_isSharedCheck_878_;
goto v_resetjp_855_;
}
v_resetjp_855_:
{
lean_object* v_succ_x3f_858_; lean_object* v_succMany_x3f_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_877_; 
v_succ_x3f_858_ = lean_ctor_get(v_inst_848_, 0);
v_succMany_x3f_859_ = lean_ctor_get(v_inst_848_, 1);
v_isSharedCheck_877_ = !lean_is_exclusive(v_inst_848_);
if (v_isSharedCheck_877_ == 0)
{
v___x_861_ = v_inst_848_;
v_isShared_862_ = v_isSharedCheck_877_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_succMany_x3f_859_);
lean_inc(v_succ_x3f_858_);
lean_dec(v_inst_848_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_877_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v_val_863_; lean_object* v___x_864_; 
v_val_863_ = lean_ctor_get(v_next_852_, 0);
lean_inc(v_val_863_);
lean_dec_ref_known(v_next_852_, 1);
v___x_864_ = lean_apply_2(v_succMany_x3f_859_, v_n_851_, v_val_863_);
if (lean_obj_tag(v___x_864_) == 0)
{
lean_object* v___x_865_; 
lean_del_object(v___x_861_);
lean_dec_ref(v_succ_x3f_858_);
lean_del_object(v___x_856_);
lean_dec(v_upperBound_854_);
lean_dec_ref(v_inst_849_);
v___x_865_ = lean_box(2);
return v___x_865_;
}
else
{
lean_object* v_val_866_; lean_object* v___x_867_; uint8_t v___x_868_; 
v_val_866_ = lean_ctor_get(v___x_864_, 0);
lean_inc_n(v_val_866_, 2);
lean_dec_ref_known(v___x_864_, 1);
lean_inc(v_upperBound_854_);
v___x_867_ = lean_apply_2(v_inst_849_, v_val_866_, v_upperBound_854_);
v___x_868_ = lean_unbox(v___x_867_);
if (v___x_868_ == 0)
{
lean_object* v___x_869_; 
lean_dec(v_val_866_);
lean_del_object(v___x_861_);
lean_dec_ref(v_succ_x3f_858_);
lean_del_object(v___x_856_);
lean_dec(v_upperBound_854_);
v___x_869_ = lean_box(2);
return v___x_869_;
}
else
{
lean_object* v___x_870_; lean_object* v___x_872_; 
lean_inc(v_val_866_);
v___x_870_ = lean_apply_1(v_succ_x3f_858_, v_val_866_);
if (v_isShared_857_ == 0)
{
lean_ctor_set(v___x_856_, 0, v___x_870_);
v___x_872_ = v___x_856_;
goto v_reusejp_871_;
}
else
{
lean_object* v_reuseFailAlloc_876_; 
v_reuseFailAlloc_876_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_876_, 0, v___x_870_);
lean_ctor_set(v_reuseFailAlloc_876_, 1, v_upperBound_854_);
v___x_872_ = v_reuseFailAlloc_876_;
goto v_reusejp_871_;
}
v_reusejp_871_:
{
lean_object* v___x_874_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 1, v_val_866_);
lean_ctor_set(v___x_861_, 0, v___x_872_);
v___x_874_ = v___x_861_;
goto v_reusejp_873_;
}
else
{
lean_object* v_reuseFailAlloc_875_; 
v_reuseFailAlloc_875_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_875_, 0, v___x_872_);
lean_ctor_set(v_reuseFailAlloc_875_, 1, v_val_866_);
v___x_874_ = v_reuseFailAlloc_875_;
goto v_reusejp_873_;
}
v_reusejp_873_:
{
return v___x_874_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg(lean_object* v_inst_880_, lean_object* v_inst_881_){
_start:
{
lean_object* v___f_882_; 
v___f_882_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_882_, 0, v_inst_880_);
lean_closure_set(v___f_882_, 1, v_inst_881_);
return v___f_882_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess(lean_object* v_00_u03b1_883_, lean_object* v_inst_884_, lean_object* v_inst_885_, lean_object* v_inst_886_, lean_object* v_inst_887_, lean_object* v_inst_888_){
_start:
{
lean_object* v___f_889_; 
v___f_889_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_889_, 0, v_inst_884_);
lean_closure_set(v___f_889_, 1, v_inst_886_);
return v___f_889_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_890_, lean_object* v_inst_891_, lean_object* v_inst_892_, lean_object* v_upperBound_893_, lean_object* v_acc_894_, lean_object* v_next_895_, lean_object* v_f_896_){
_start:
{
lean_object* v_toApplicative_897_; lean_object* v_toBind_898_; lean_object* v_toPure_899_; lean_object* v___f_900_; lean_object* v___x_901_; 
v_toApplicative_897_ = lean_ctor_get(v_inst_892_, 0);
lean_inc_ref(v_toApplicative_897_);
v_toBind_898_ = lean_ctor_get(v_inst_892_, 1);
lean_inc(v_toBind_898_);
lean_dec_ref(v_inst_892_);
v_toPure_899_ = lean_ctor_get(v_toApplicative_897_, 1);
lean_inc(v_toPure_899_);
lean_dec_ref(v_toApplicative_897_);
v___f_900_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_900_, 0, v_inst_891_);
lean_closure_set(v___f_900_, 1, v_upperBound_893_);
lean_closure_set(v___f_900_, 2, v_toPure_899_);
lean_closure_set(v___f_900_, 3, v_inst_890_);
lean_closure_set(v___f_900_, 4, v_f_896_);
lean_closure_set(v___f_900_, 5, v_toBind_898_);
v___x_901_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_900_, v_next_895_, v_acc_894_, lean_box(0));
return v___x_901_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_902_, lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_n_907_, lean_object* v_inst_908_, lean_object* v_00_u03b3_909_, lean_object* v_Pl_910_, lean_object* v_LargeEnough_911_, lean_object* v_hl_912_, lean_object* v_upperBound_913_, lean_object* v_acc_914_, lean_object* v_next_915_, lean_object* v_h_916_, lean_object* v_f_917_){
_start:
{
lean_object* v_toApplicative_918_; lean_object* v_toBind_919_; lean_object* v_toPure_920_; lean_object* v___f_921_; lean_object* v___x_922_; 
v_toApplicative_918_ = lean_ctor_get(v_inst_908_, 0);
lean_inc_ref(v_toApplicative_918_);
v_toBind_919_ = lean_ctor_get(v_inst_908_, 1);
lean_inc(v_toBind_919_);
lean_dec_ref(v_inst_908_);
v_toPure_920_ = lean_ctor_get(v_toApplicative_918_, 1);
lean_inc(v_toPure_920_);
lean_dec_ref(v_toApplicative_918_);
v___f_921_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_921_, 0, v_inst_905_);
lean_closure_set(v___f_921_, 1, v_upperBound_913_);
lean_closure_set(v___f_921_, 2, v_toPure_920_);
lean_closure_set(v___f_921_, 3, v_inst_903_);
lean_closure_set(v___f_921_, 4, v_f_917_);
lean_closure_set(v___f_921_, 5, v_toBind_919_);
v___x_922_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_921_, v_next_915_, v_acc_914_, lean_box(0));
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_toBind_926_, lean_object* v_x_927_, lean_object* v_00_u03b3_928_, lean_object* v_Pl_929_, lean_object* v_it_930_, lean_object* v_init_931_, lean_object* v_f_932_){
_start:
{
lean_object* v_next_933_; 
v_next_933_ = lean_ctor_get(v_it_930_, 0);
lean_inc(v_next_933_);
if (lean_obj_tag(v_next_933_) == 0)
{
lean_object* v___x_934_; 
lean_dec(v_f_932_);
lean_dec_ref(v_it_930_);
lean_dec(v_toBind_926_);
lean_dec_ref(v_inst_925_);
lean_dec_ref(v_inst_924_);
v___x_934_ = lean_apply_2(v_toPure_923_, lean_box(0), v_init_931_);
return v___x_934_;
}
else
{
lean_object* v_upperBound_935_; lean_object* v_val_936_; lean_object* v___f_937_; lean_object* v___x_938_; 
v_upperBound_935_ = lean_ctor_get(v_it_930_, 1);
lean_inc(v_upperBound_935_);
lean_dec_ref(v_it_930_);
v_val_936_ = lean_ctor_get(v_next_933_, 0);
lean_inc(v_val_936_);
lean_dec_ref_known(v_next_933_, 1);
v___f_937_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_937_, 0, v_inst_924_);
lean_closure_set(v___f_937_, 1, v_upperBound_935_);
lean_closure_set(v___f_937_, 2, v_toPure_923_);
lean_closure_set(v___f_937_, 3, v_inst_925_);
lean_closure_set(v___f_937_, 4, v_f_932_);
lean_closure_set(v___f_937_, 5, v_toBind_926_);
v___x_938_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_937_, v_val_936_, v_init_931_, lean_box(0));
return v___x_938_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_939_, lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_toBind_942_, lean_object* v_x_943_, lean_object* v_00_u03b3_944_, lean_object* v_Pl_945_, lean_object* v_it_946_, lean_object* v_init_947_, lean_object* v_f_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_939_, v_inst_940_, v_inst_941_, v_toBind_942_, v_x_943_, v_00_u03b3_944_, v_Pl_945_, v_it_946_, v_init_947_, v_f_948_);
lean_dec(v_x_943_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg(lean_object* v_inst_950_, lean_object* v_inst_951_, lean_object* v_inst_952_){
_start:
{
lean_object* v_toApplicative_953_; lean_object* v_toBind_954_; lean_object* v_toPure_955_; lean_object* v___f_956_; 
v_toApplicative_953_ = lean_ctor_get(v_inst_952_, 0);
lean_inc_ref(v_toApplicative_953_);
v_toBind_954_ = lean_ctor_get(v_inst_952_, 1);
lean_inc(v_toBind_954_);
lean_dec_ref(v_inst_952_);
v_toPure_955_ = lean_ctor_get(v_toApplicative_953_, 1);
lean_inc(v_toPure_955_);
lean_dec_ref(v_toApplicative_953_);
v___f_956_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_956_, 0, v_toPure_955_);
lean_closure_set(v___f_956_, 1, v_inst_951_);
lean_closure_set(v___f_956_, 2, v_inst_950_);
lean_closure_set(v___f_956_, 3, v_toBind_954_);
return v___f_956_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop(lean_object* v_00_u03b1_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_n_963_, lean_object* v_inst_964_){
_start:
{
lean_object* v_toApplicative_965_; lean_object* v_toBind_966_; lean_object* v_toPure_967_; lean_object* v___f_968_; 
v_toApplicative_965_ = lean_ctor_get(v_inst_964_, 0);
lean_inc_ref(v_toApplicative_965_);
v_toBind_966_ = lean_ctor_get(v_inst_964_, 1);
lean_inc(v_toBind_966_);
lean_dec_ref(v_inst_964_);
v_toPure_967_ = lean_ctor_get(v_toApplicative_965_, 1);
lean_inc(v_toPure_967_);
lean_dec_ref(v_toApplicative_965_);
v___f_968_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_968_, 0, v_toPure_967_);
lean_closure_set(v___f_968_, 1, v_inst_960_);
lean_closure_set(v___f_968_, 2, v_inst_958_);
lean_closure_set(v___f_968_, 3, v_toBind_966_);
return v___f_968_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_969_, lean_object* v_f_970_, lean_object* v_h__1_971_, lean_object* v_h__2_972_){
_start:
{
lean_object* v_next_973_; 
v_next_973_ = lean_ctor_get(v_it_969_, 0);
if (lean_obj_tag(v_next_973_) == 0)
{
lean_object* v_upperBound_974_; lean_object* v___x_975_; 
lean_dec(v_h__1_971_);
v_upperBound_974_ = lean_ctor_get(v_it_969_, 1);
lean_inc(v_upperBound_974_);
lean_dec_ref(v_it_969_);
v___x_975_ = lean_apply_2(v_h__2_972_, v_upperBound_974_, v_f_970_);
return v___x_975_;
}
else
{
lean_object* v_upperBound_976_; lean_object* v_val_977_; lean_object* v___x_978_; 
lean_inc_ref(v_next_973_);
lean_dec(v_h__2_972_);
v_upperBound_976_ = lean_ctor_get(v_it_969_, 1);
lean_inc(v_upperBound_976_);
lean_dec_ref(v_it_969_);
v_val_977_ = lean_ctor_get(v_next_973_, 0);
lean_inc(v_val_977_);
lean_dec_ref_known(v_next_973_, 1);
v___x_978_ = lean_apply_3(v_h__1_971_, v_val_977_, v_upperBound_976_, v_f_970_);
return v___x_978_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_979_, lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_n_983_, lean_object* v_00_u03b3_984_, lean_object* v_Pl_985_, lean_object* v_motive_986_, lean_object* v_it_987_, lean_object* v_f_988_, lean_object* v_h__1_989_, lean_object* v_h__2_990_){
_start:
{
lean_object* v_next_991_; 
v_next_991_ = lean_ctor_get(v_it_987_, 0);
if (lean_obj_tag(v_next_991_) == 0)
{
lean_object* v_upperBound_992_; lean_object* v___x_993_; 
lean_dec(v_h__1_989_);
v_upperBound_992_ = lean_ctor_get(v_it_987_, 1);
lean_inc(v_upperBound_992_);
lean_dec_ref(v_it_987_);
v___x_993_ = lean_apply_2(v_h__2_990_, v_upperBound_992_, v_f_988_);
return v___x_993_;
}
else
{
lean_object* v_upperBound_994_; lean_object* v_val_995_; lean_object* v___x_996_; 
lean_inc_ref(v_next_991_);
lean_dec(v_h__2_990_);
v_upperBound_994_ = lean_ctor_get(v_it_987_, 1);
lean_inc(v_upperBound_994_);
lean_dec_ref(v_it_987_);
v_val_995_ = lean_ctor_get(v_next_991_, 0);
lean_inc(v_val_995_);
lean_dec_ref_known(v_next_991_, 1);
v___x_996_ = lean_apply_3(v_h__1_989_, v_val_995_, v_upperBound_994_, v_f_988_);
return v___x_996_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_997_, lean_object* v_inst_998_, lean_object* v_inst_999_, lean_object* v_inst_1000_, lean_object* v_n_1001_, lean_object* v_00_u03b3_1002_, lean_object* v_Pl_1003_, lean_object* v_motive_1004_, lean_object* v_it_1005_, lean_object* v_f_1006_, lean_object* v_h__1_1007_, lean_object* v_h__2_1008_){
_start:
{
lean_object* v_res_1009_; 
v_res_1009_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_997_, v_inst_998_, v_inst_999_, v_inst_1000_, v_n_1001_, v_00_u03b3_1002_, v_Pl_1003_, v_motive_1004_, v_it_1005_, v_f_1006_, v_h__1_1007_, v_h__2_1008_);
lean_dec_ref(v_inst_1000_);
lean_dec_ref(v_inst_998_);
return v_res_1009_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step___redArg(lean_object* v_inst_1010_, lean_object* v_it_1011_){
_start:
{
if (lean_obj_tag(v_it_1011_) == 0)
{
lean_object* v___x_1012_; 
lean_dec_ref(v_inst_1010_);
v___x_1012_ = lean_box(2);
return v___x_1012_;
}
else
{
lean_object* v_val_1013_; lean_object* v_succ_x3f_1014_; lean_object* v___x_1016_; uint8_t v_isShared_1017_; uint8_t v_isSharedCheck_1022_; 
v_val_1013_ = lean_ctor_get(v_it_1011_, 0);
lean_inc(v_val_1013_);
lean_dec_ref_known(v_it_1011_, 1);
v_succ_x3f_1014_ = lean_ctor_get(v_inst_1010_, 0);
v_isSharedCheck_1022_ = !lean_is_exclusive(v_inst_1010_);
if (v_isSharedCheck_1022_ == 0)
{
lean_object* v_unused_1023_; 
v_unused_1023_ = lean_ctor_get(v_inst_1010_, 1);
lean_dec(v_unused_1023_);
v___x_1016_ = v_inst_1010_;
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
else
{
lean_inc(v_succ_x3f_1014_);
lean_dec(v_inst_1010_);
v___x_1016_ = lean_box(0);
v_isShared_1017_ = v_isSharedCheck_1022_;
goto v_resetjp_1015_;
}
v_resetjp_1015_:
{
lean_object* v___x_1018_; lean_object* v___x_1020_; 
lean_inc(v_val_1013_);
v___x_1018_ = lean_apply_1(v_succ_x3f_1014_, v_val_1013_);
if (v_isShared_1017_ == 0)
{
lean_ctor_set(v___x_1016_, 1, v_val_1013_);
lean_ctor_set(v___x_1016_, 0, v___x_1018_);
v___x_1020_ = v___x_1016_;
goto v_reusejp_1019_;
}
else
{
lean_object* v_reuseFailAlloc_1021_; 
v_reuseFailAlloc_1021_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1021_, 0, v___x_1018_);
lean_ctor_set(v_reuseFailAlloc_1021_, 1, v_val_1013_);
v___x_1020_ = v_reuseFailAlloc_1021_;
goto v_reusejp_1019_;
}
v_reusejp_1019_:
{
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step(lean_object* v_00_u03b1_1024_, lean_object* v_inst_1025_, lean_object* v_it_1026_){
_start:
{
if (lean_obj_tag(v_it_1026_) == 0)
{
lean_object* v___x_1027_; 
lean_dec_ref(v_inst_1025_);
v___x_1027_ = lean_box(2);
return v___x_1027_;
}
else
{
lean_object* v_val_1028_; lean_object* v_succ_x3f_1029_; lean_object* v___x_1031_; uint8_t v_isShared_1032_; uint8_t v_isSharedCheck_1037_; 
v_val_1028_ = lean_ctor_get(v_it_1026_, 0);
lean_inc(v_val_1028_);
lean_dec_ref_known(v_it_1026_, 1);
v_succ_x3f_1029_ = lean_ctor_get(v_inst_1025_, 0);
v_isSharedCheck_1037_ = !lean_is_exclusive(v_inst_1025_);
if (v_isSharedCheck_1037_ == 0)
{
lean_object* v_unused_1038_; 
v_unused_1038_ = lean_ctor_get(v_inst_1025_, 1);
lean_dec(v_unused_1038_);
v___x_1031_ = v_inst_1025_;
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
else
{
lean_inc(v_succ_x3f_1029_);
lean_dec(v_inst_1025_);
v___x_1031_ = lean_box(0);
v_isShared_1032_ = v_isSharedCheck_1037_;
goto v_resetjp_1030_;
}
v_resetjp_1030_:
{
lean_object* v___x_1033_; lean_object* v___x_1035_; 
lean_inc(v_val_1028_);
v___x_1033_ = lean_apply_1(v_succ_x3f_1029_, v_val_1028_);
if (v_isShared_1032_ == 0)
{
lean_ctor_set(v___x_1031_, 1, v_val_1028_);
lean_ctor_set(v___x_1031_, 0, v___x_1033_);
v___x_1035_ = v___x_1031_;
goto v_reusejp_1034_;
}
else
{
lean_object* v_reuseFailAlloc_1036_; 
v_reuseFailAlloc_1036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1036_, 0, v___x_1033_);
lean_ctor_set(v_reuseFailAlloc_1036_, 1, v_val_1028_);
v___x_1035_ = v_reuseFailAlloc_1036_;
goto v_reusejp_1034_;
}
v_reusejp_1034_:
{
return v___x_1035_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step___redArg(lean_object* v_inst_1039_, lean_object* v_it_1040_){
_start:
{
if (lean_obj_tag(v_it_1040_) == 0)
{
lean_object* v___x_1041_; 
lean_dec_ref(v_inst_1039_);
v___x_1041_ = lean_box(2);
return v___x_1041_;
}
else
{
lean_object* v_val_1042_; lean_object* v_succ_x3f_1043_; lean_object* v___x_1045_; uint8_t v_isShared_1046_; uint8_t v_isSharedCheck_1051_; 
v_val_1042_ = lean_ctor_get(v_it_1040_, 0);
lean_inc(v_val_1042_);
lean_dec_ref_known(v_it_1040_, 1);
v_succ_x3f_1043_ = lean_ctor_get(v_inst_1039_, 0);
v_isSharedCheck_1051_ = !lean_is_exclusive(v_inst_1039_);
if (v_isSharedCheck_1051_ == 0)
{
lean_object* v_unused_1052_; 
v_unused_1052_ = lean_ctor_get(v_inst_1039_, 1);
lean_dec(v_unused_1052_);
v___x_1045_ = v_inst_1039_;
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
else
{
lean_inc(v_succ_x3f_1043_);
lean_dec(v_inst_1039_);
v___x_1045_ = lean_box(0);
v_isShared_1046_ = v_isSharedCheck_1051_;
goto v_resetjp_1044_;
}
v_resetjp_1044_:
{
lean_object* v___x_1047_; lean_object* v___x_1049_; 
lean_inc(v_val_1042_);
v___x_1047_ = lean_apply_1(v_succ_x3f_1043_, v_val_1042_);
if (v_isShared_1046_ == 0)
{
lean_ctor_set(v___x_1045_, 1, v_val_1042_);
lean_ctor_set(v___x_1045_, 0, v___x_1047_);
v___x_1049_ = v___x_1045_;
goto v_reusejp_1048_;
}
else
{
lean_object* v_reuseFailAlloc_1050_; 
v_reuseFailAlloc_1050_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1050_, 0, v___x_1047_);
lean_ctor_set(v_reuseFailAlloc_1050_, 1, v_val_1042_);
v___x_1049_ = v_reuseFailAlloc_1050_;
goto v_reusejp_1048_;
}
v_reusejp_1048_:
{
return v___x_1049_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step(lean_object* v_00_u03b1_1053_, lean_object* v_inst_1054_, lean_object* v_it_1055_){
_start:
{
if (lean_obj_tag(v_it_1055_) == 0)
{
lean_object* v___x_1056_; 
lean_dec_ref(v_inst_1054_);
v___x_1056_ = lean_box(2);
return v___x_1056_;
}
else
{
lean_object* v_val_1057_; lean_object* v_succ_x3f_1058_; lean_object* v___x_1060_; uint8_t v_isShared_1061_; uint8_t v_isSharedCheck_1066_; 
v_val_1057_ = lean_ctor_get(v_it_1055_, 0);
lean_inc(v_val_1057_);
lean_dec_ref_known(v_it_1055_, 1);
v_succ_x3f_1058_ = lean_ctor_get(v_inst_1054_, 0);
v_isSharedCheck_1066_ = !lean_is_exclusive(v_inst_1054_);
if (v_isSharedCheck_1066_ == 0)
{
lean_object* v_unused_1067_; 
v_unused_1067_ = lean_ctor_get(v_inst_1054_, 1);
lean_dec(v_unused_1067_);
v___x_1060_ = v_inst_1054_;
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
else
{
lean_inc(v_succ_x3f_1058_);
lean_dec(v_inst_1054_);
v___x_1060_ = lean_box(0);
v_isShared_1061_ = v_isSharedCheck_1066_;
goto v_resetjp_1059_;
}
v_resetjp_1059_:
{
lean_object* v___x_1062_; lean_object* v___x_1064_; 
lean_inc(v_val_1057_);
v___x_1062_ = lean_apply_1(v_succ_x3f_1058_, v_val_1057_);
if (v_isShared_1061_ == 0)
{
lean_ctor_set(v___x_1060_, 1, v_val_1057_);
lean_ctor_set(v___x_1060_, 0, v___x_1062_);
v___x_1064_ = v___x_1060_;
goto v_reusejp_1063_;
}
else
{
lean_object* v_reuseFailAlloc_1065_; 
v_reuseFailAlloc_1065_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1065_, 0, v___x_1062_);
lean_ctor_set(v_reuseFailAlloc_1065_, 1, v_val_1057_);
v___x_1064_ = v_reuseFailAlloc_1065_;
goto v_reusejp_1063_;
}
v_reusejp_1063_:
{
return v___x_1064_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0(lean_object* v_inst_1068_, lean_object* v_it_1069_){
_start:
{
if (lean_obj_tag(v_it_1069_) == 0)
{
lean_object* v___x_1070_; 
lean_dec_ref(v_inst_1068_);
v___x_1070_ = lean_box(2);
return v___x_1070_;
}
else
{
lean_object* v_val_1071_; lean_object* v_succ_x3f_1072_; lean_object* v___x_1074_; uint8_t v_isShared_1075_; uint8_t v_isSharedCheck_1080_; 
v_val_1071_ = lean_ctor_get(v_it_1069_, 0);
lean_inc(v_val_1071_);
lean_dec_ref_known(v_it_1069_, 1);
v_succ_x3f_1072_ = lean_ctor_get(v_inst_1068_, 0);
v_isSharedCheck_1080_ = !lean_is_exclusive(v_inst_1068_);
if (v_isSharedCheck_1080_ == 0)
{
lean_object* v_unused_1081_; 
v_unused_1081_ = lean_ctor_get(v_inst_1068_, 1);
lean_dec(v_unused_1081_);
v___x_1074_ = v_inst_1068_;
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
else
{
lean_inc(v_succ_x3f_1072_);
lean_dec(v_inst_1068_);
v___x_1074_ = lean_box(0);
v_isShared_1075_ = v_isSharedCheck_1080_;
goto v_resetjp_1073_;
}
v_resetjp_1073_:
{
lean_object* v___x_1076_; lean_object* v___x_1078_; 
lean_inc(v_val_1071_);
v___x_1076_ = lean_apply_1(v_succ_x3f_1072_, v_val_1071_);
if (v_isShared_1075_ == 0)
{
lean_ctor_set(v___x_1074_, 1, v_val_1071_);
lean_ctor_set(v___x_1074_, 0, v___x_1076_);
v___x_1078_ = v___x_1074_;
goto v_reusejp_1077_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v___x_1076_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_val_1071_);
v___x_1078_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1077_;
}
v_reusejp_1077_:
{
return v___x_1078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg(lean_object* v_inst_1082_){
_start:
{
lean_object* v___f_1083_; 
v___f_1083_ = lean_alloc_closure((void*)(l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1083_, 0, v_inst_1082_);
return v___f_1083_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable(lean_object* v_00_u03b1_1084_, lean_object* v_inst_1085_){
_start:
{
lean_object* v___f_1086_; 
v___f_1086_ = lean_alloc_closure((void*)(l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1086_, 0, v_inst_1085_);
return v___f_1086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_1087_, lean_object* v_inst_1088_, lean_object* v_inst_1089_, lean_object* v_inst_1090_){
_start:
{
lean_object* v___x_1091_; 
v___x_1091_ = lean_box(0);
return v___x_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_1092_, lean_object* v_inst_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_){
_start:
{
lean_object* v_res_1096_; 
v_res_1096_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(v_00_u03b1_1092_, v_inst_1093_, v_inst_1094_, v_inst_1095_);
lean_dec_ref(v_inst_1093_);
return v_res_1096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_1097_, lean_object* v_inst_1098_, lean_object* v_inst_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_box(0);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_1101_, lean_object* v_inst_1102_, lean_object* v_inst_1103_){
_start:
{
lean_object* v_res_1104_; 
v_res_1104_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(v_00_u03b1_1101_, v_inst_1102_, v_inst_1103_);
lean_dec_ref(v_inst_1102_);
return v_res_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_1105_, lean_object* v_it_1106_, lean_object* v_n_1107_){
_start:
{
if (lean_obj_tag(v_it_1106_) == 0)
{
lean_object* v___x_1108_; 
lean_dec(v_n_1107_);
lean_dec_ref(v_inst_1105_);
v___x_1108_ = lean_box(2);
return v___x_1108_;
}
else
{
lean_object* v_succ_x3f_1109_; lean_object* v_succMany_x3f_1110_; lean_object* v___x_1112_; uint8_t v_isShared_1113_; uint8_t v_isSharedCheck_1122_; 
v_succ_x3f_1109_ = lean_ctor_get(v_inst_1105_, 0);
v_succMany_x3f_1110_ = lean_ctor_get(v_inst_1105_, 1);
v_isSharedCheck_1122_ = !lean_is_exclusive(v_inst_1105_);
if (v_isSharedCheck_1122_ == 0)
{
v___x_1112_ = v_inst_1105_;
v_isShared_1113_ = v_isSharedCheck_1122_;
goto v_resetjp_1111_;
}
else
{
lean_inc(v_succMany_x3f_1110_);
lean_inc(v_succ_x3f_1109_);
lean_dec(v_inst_1105_);
v___x_1112_ = lean_box(0);
v_isShared_1113_ = v_isSharedCheck_1122_;
goto v_resetjp_1111_;
}
v_resetjp_1111_:
{
lean_object* v_val_1114_; lean_object* v___x_1115_; 
v_val_1114_ = lean_ctor_get(v_it_1106_, 0);
lean_inc(v_val_1114_);
lean_dec_ref_known(v_it_1106_, 1);
v___x_1115_ = lean_apply_2(v_succMany_x3f_1110_, v_n_1107_, v_val_1114_);
if (lean_obj_tag(v___x_1115_) == 0)
{
lean_object* v___x_1116_; 
lean_del_object(v___x_1112_);
lean_dec_ref(v_succ_x3f_1109_);
v___x_1116_ = lean_box(2);
return v___x_1116_;
}
else
{
lean_object* v_val_1117_; lean_object* v___x_1118_; lean_object* v___x_1120_; 
v_val_1117_ = lean_ctor_get(v___x_1115_, 0);
lean_inc_n(v_val_1117_, 2);
lean_dec_ref_known(v___x_1115_, 1);
v___x_1118_ = lean_apply_1(v_succ_x3f_1109_, v_val_1117_);
if (v_isShared_1113_ == 0)
{
lean_ctor_set(v___x_1112_, 1, v_val_1117_);
lean_ctor_set(v___x_1112_, 0, v___x_1118_);
v___x_1120_ = v___x_1112_;
goto v_reusejp_1119_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v___x_1118_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v_val_1117_);
v___x_1120_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1119_;
}
v_reusejp_1119_:
{
return v___x_1120_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg(lean_object* v_inst_1123_){
_start:
{
lean_object* v___f_1124_; 
v___f_1124_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1124_, 0, v_inst_1123_);
return v___f_1124_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess(lean_object* v_00_u03b1_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_){
_start:
{
lean_object* v___f_1128_; 
v___f_1128_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1128_, 0, v_inst_1126_);
return v___f_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object* v_toPure_1129_, lean_object* v_inst_1130_, lean_object* v_f_1131_, lean_object* v_toBind_1132_, lean_object* v_next_1133_, lean_object* v_acc_1134_, lean_object* v_h_1135_, lean_object* v_G_1136_){
_start:
{
lean_object* v___f_1137_; lean_object* v___x_1138_; lean_object* v___x_1139_; 
lean_inc(v_next_1133_);
v___f_1137_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1137_, 0, v_toPure_1129_);
lean_closure_set(v___f_1137_, 1, v_inst_1130_);
lean_closure_set(v___f_1137_, 2, v_next_1133_);
lean_closure_set(v___f_1137_, 3, v_G_1136_);
v___x_1138_ = lean_apply_3(v_f_1131_, v_next_1133_, lean_box(0), v_acc_1134_);
v___x_1139_ = lean_apply_4(v_toBind_1132_, lean_box(0), lean_box(0), v___x_1138_, v___f_1137_);
return v___x_1139_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_1140_, lean_object* v_inst_1141_, lean_object* v_acc_1142_, lean_object* v_next_1143_, lean_object* v_f_1144_){
_start:
{
lean_object* v_toApplicative_1145_; lean_object* v_toBind_1146_; lean_object* v_toPure_1147_; lean_object* v___f_1148_; lean_object* v___x_1149_; 
v_toApplicative_1145_ = lean_ctor_get(v_inst_1141_, 0);
lean_inc_ref(v_toApplicative_1145_);
v_toBind_1146_ = lean_ctor_get(v_inst_1141_, 1);
lean_inc(v_toBind_1146_);
lean_dec_ref(v_inst_1141_);
v_toPure_1147_ = lean_ctor_get(v_toApplicative_1145_, 1);
lean_inc(v_toPure_1147_);
lean_dec_ref(v_toApplicative_1145_);
v___f_1148_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1148_, 0, v_toPure_1147_);
lean_closure_set(v___f_1148_, 1, v_inst_1140_);
lean_closure_set(v___f_1148_, 2, v_f_1144_);
lean_closure_set(v___f_1148_, 3, v_toBind_1146_);
v___x_1149_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1148_, v_next_1143_, v_acc_1142_, lean_box(0));
return v___x_1149_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_1150_, lean_object* v_inst_1151_, lean_object* v_inst_1152_, lean_object* v_n_1153_, lean_object* v_inst_1154_, lean_object* v_00_u03b3_1155_, lean_object* v_Pl_1156_, lean_object* v_LargeEnough_1157_, lean_object* v_hl_1158_, lean_object* v_acc_1159_, lean_object* v_next_1160_, lean_object* v_h_1161_, lean_object* v_f_1162_){
_start:
{
lean_object* v_toApplicative_1163_; lean_object* v_toBind_1164_; lean_object* v_toPure_1165_; lean_object* v___f_1166_; lean_object* v___x_1167_; 
v_toApplicative_1163_ = lean_ctor_get(v_inst_1154_, 0);
lean_inc_ref(v_toApplicative_1163_);
v_toBind_1164_ = lean_ctor_get(v_inst_1154_, 1);
lean_inc(v_toBind_1164_);
lean_dec_ref(v_inst_1154_);
v_toPure_1165_ = lean_ctor_get(v_toApplicative_1163_, 1);
lean_inc(v_toPure_1165_);
lean_dec_ref(v_toApplicative_1163_);
v___f_1166_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1166_, 0, v_toPure_1165_);
lean_closure_set(v___f_1166_, 1, v_inst_1151_);
lean_closure_set(v___f_1166_, 2, v_f_1162_);
lean_closure_set(v___f_1166_, 3, v_toBind_1164_);
v___x_1167_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1166_, v_next_1160_, v_acc_1159_, lean_box(0));
return v___x_1167_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_1168_, lean_object* v_inst_1169_, lean_object* v_toBind_1170_, lean_object* v_x_1171_, lean_object* v_00_u03b3_1172_, lean_object* v_Pl_1173_, lean_object* v_it_1174_, lean_object* v_init_1175_, lean_object* v_f_1176_){
_start:
{
if (lean_obj_tag(v_it_1174_) == 0)
{
lean_object* v___x_1177_; 
lean_dec(v_f_1176_);
lean_dec(v_toBind_1170_);
lean_dec_ref(v_inst_1169_);
v___x_1177_ = lean_apply_2(v_toPure_1168_, lean_box(0), v_init_1175_);
return v___x_1177_;
}
else
{
lean_object* v_val_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; 
v_val_1178_ = lean_ctor_get(v_it_1174_, 0);
lean_inc(v_val_1178_);
lean_dec_ref_known(v_it_1174_, 1);
v___f_1179_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1179_, 0, v_toPure_1168_);
lean_closure_set(v___f_1179_, 1, v_inst_1169_);
lean_closure_set(v___f_1179_, 2, v_f_1176_);
lean_closure_set(v___f_1179_, 3, v_toBind_1170_);
v___x_1180_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1179_, v_val_1178_, v_init_1175_, lean_box(0));
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_1181_, lean_object* v_inst_1182_, lean_object* v_toBind_1183_, lean_object* v_x_1184_, lean_object* v_00_u03b3_1185_, lean_object* v_Pl_1186_, lean_object* v_it_1187_, lean_object* v_init_1188_, lean_object* v_f_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_1181_, v_inst_1182_, v_toBind_1183_, v_x_1184_, v_00_u03b3_1185_, v_Pl_1186_, v_it_1187_, v_init_1188_, v_f_1189_);
lean_dec(v_x_1184_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg(lean_object* v_inst_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v_toApplicative_1193_; lean_object* v_toBind_1194_; lean_object* v_toPure_1195_; lean_object* v___f_1196_; 
v_toApplicative_1193_ = lean_ctor_get(v_inst_1192_, 0);
lean_inc_ref(v_toApplicative_1193_);
v_toBind_1194_ = lean_ctor_get(v_inst_1192_, 1);
lean_inc(v_toBind_1194_);
lean_dec_ref(v_inst_1192_);
v_toPure_1195_ = lean_ctor_get(v_toApplicative_1193_, 1);
lean_inc(v_toPure_1195_);
lean_dec_ref(v_toApplicative_1193_);
v___f_1196_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1196_, 0, v_toPure_1195_);
lean_closure_set(v___f_1196_, 1, v_inst_1191_);
lean_closure_set(v___f_1196_, 2, v_toBind_1194_);
return v___f_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop(lean_object* v_00_u03b1_1197_, lean_object* v_inst_1198_, lean_object* v_inst_1199_, lean_object* v_n_1200_, lean_object* v_inst_1201_){
_start:
{
lean_object* v_toApplicative_1202_; lean_object* v_toBind_1203_; lean_object* v_toPure_1204_; lean_object* v___f_1205_; 
v_toApplicative_1202_ = lean_ctor_get(v_inst_1201_, 0);
lean_inc_ref(v_toApplicative_1202_);
v_toBind_1203_ = lean_ctor_get(v_inst_1201_, 1);
lean_inc(v_toBind_1203_);
lean_dec_ref(v_inst_1201_);
v_toPure_1204_ = lean_ctor_get(v_toApplicative_1202_, 1);
lean_inc(v_toPure_1204_);
lean_dec_ref(v_toApplicative_1202_);
v___f_1205_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1205_, 0, v_toPure_1204_);
lean_closure_set(v___f_1205_, 1, v_inst_1198_);
lean_closure_set(v___f_1205_, 2, v_toBind_1203_);
return v___f_1205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_1206_, lean_object* v_f_1207_, lean_object* v_h__1_1208_, lean_object* v_h__2_1209_){
_start:
{
if (lean_obj_tag(v_it_1206_) == 0)
{
lean_object* v___x_1210_; 
lean_dec(v_h__1_1208_);
v___x_1210_ = lean_apply_1(v_h__2_1209_, v_f_1207_);
return v___x_1210_;
}
else
{
lean_object* v_val_1211_; lean_object* v___x_1212_; 
lean_dec(v_h__2_1209_);
v_val_1211_ = lean_ctor_get(v_it_1206_, 0);
lean_inc(v_val_1211_);
lean_dec_ref_known(v_it_1206_, 1);
v___x_1212_ = lean_apply_2(v_h__1_1208_, v_val_1211_, v_f_1207_);
return v___x_1212_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_1213_, lean_object* v_inst_1214_, lean_object* v_n_1215_, lean_object* v_00_u03b3_1216_, lean_object* v_Pl_1217_, lean_object* v_motive_1218_, lean_object* v_it_1219_, lean_object* v_f_1220_, lean_object* v_h__1_1221_, lean_object* v_h__2_1222_){
_start:
{
if (lean_obj_tag(v_it_1219_) == 0)
{
lean_object* v___x_1223_; 
lean_dec(v_h__1_1221_);
v___x_1223_ = lean_apply_1(v_h__2_1222_, v_f_1220_);
return v___x_1223_;
}
else
{
lean_object* v_val_1224_; lean_object* v___x_1225_; 
lean_dec(v_h__2_1222_);
v_val_1224_ = lean_ctor_get(v_it_1219_, 0);
lean_inc(v_val_1224_);
lean_dec_ref_known(v_it_1219_, 1);
v___x_1225_ = lean_apply_2(v_h__1_1221_, v_val_1224_, v_f_1220_);
return v___x_1225_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_1226_, lean_object* v_inst_1227_, lean_object* v_n_1228_, lean_object* v_00_u03b3_1229_, lean_object* v_Pl_1230_, lean_object* v_motive_1231_, lean_object* v_it_1232_, lean_object* v_f_1233_, lean_object* v_h__1_1234_, lean_object* v_h__2_1235_){
_start:
{
lean_object* v_res_1236_; 
v_res_1236_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_1226_, v_inst_1227_, v_n_1228_, v_00_u03b3_1229_, v_Pl_1230_, v_motive_1231_, v_it_1232_, v_f_1233_, v_h__1_1234_, v_h__2_1235_);
lean_dec_ref(v_inst_1227_);
return v_res_1236_;
}
}
lean_object* runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Range_Polymorphic_PRange(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_ByCases(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Bool(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_PRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Range_Polymorphic_PRange(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Access(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Monadic_Loop(uint8_t builtin);
lean_object* initialize_Init_ByCases(uint8_t builtin);
lean_object* initialize_Init_Data_Bool(uint8_t builtin);
lean_object* initialize_Init_Data_List_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_List_Sublist(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_Iterators_Lemmas_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Range_Polymorphic_PRange(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Access(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Monadic_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_ByCases(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Bool(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_List_Sublist(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_Range_Polymorphic_RangeIterator(builtin);
}
#ifdef __cplusplus
}
#endif
