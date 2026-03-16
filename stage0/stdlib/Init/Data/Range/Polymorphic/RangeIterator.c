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
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___boxed(lean_object**);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_inc(v_val_10_);
lean_dec_ref(v_next_4_);
lean_inc(v_upperBound_6_);
lean_inc(v_val_10_);
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
lean_inc(v_val_40_);
lean_dec_ref(v_next_34_);
lean_inc(v_upperBound_36_);
lean_inc(v_val_40_);
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
lean_inc(v_val_68_);
lean_dec_ref(v_next_62_);
lean_inc(v_upperBound_64_);
lean_inc(v_val_68_);
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
lean_inc(v_val_98_);
lean_dec_ref(v_next_92_);
lean_inc(v_upperBound_94_);
lean_inc(v_val_98_);
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
lean_dec_ref(v_x_117_);
v___x_123_ = lean_apply_1(v_h__2_119_, v_val_122_);
return v___x_123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter(lean_object* v_00_u03b1_124_, lean_object* v_motive_125_, lean_object* v_x_126_, lean_object* v_h__1_127_, lean_object* v_h__2_128_){
_start:
{
lean_object* v___x_129_; 
v___x_129_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_Monadic_step_match__1_splitter___redArg(v_x_126_, v_h__1_127_, v_h__2_128_);
return v___x_129_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0(lean_object* v_inst_130_, lean_object* v_inst_131_, lean_object* v_it_132_){
_start:
{
lean_object* v_next_133_; 
v_next_133_ = lean_ctor_get(v_it_132_, 0);
lean_inc(v_next_133_);
if (lean_obj_tag(v_next_133_) == 0)
{
lean_object* v___x_134_; 
lean_dec_ref(v_it_132_);
lean_dec_ref(v_inst_131_);
lean_dec_ref(v_inst_130_);
v___x_134_ = lean_box(2);
return v___x_134_;
}
else
{
lean_object* v_upperBound_135_; lean_object* v___x_137_; uint8_t v_isShared_138_; uint8_t v_isSharedCheck_156_; 
v_upperBound_135_ = lean_ctor_get(v_it_132_, 1);
v_isSharedCheck_156_ = !lean_is_exclusive(v_it_132_);
if (v_isSharedCheck_156_ == 0)
{
lean_object* v_unused_157_; 
v_unused_157_ = lean_ctor_get(v_it_132_, 0);
lean_dec(v_unused_157_);
v___x_137_ = v_it_132_;
v_isShared_138_ = v_isSharedCheck_156_;
goto v_resetjp_136_;
}
else
{
lean_inc(v_upperBound_135_);
lean_dec(v_it_132_);
v___x_137_ = lean_box(0);
v_isShared_138_ = v_isSharedCheck_156_;
goto v_resetjp_136_;
}
v_resetjp_136_:
{
lean_object* v_val_139_; lean_object* v___x_140_; uint8_t v___x_141_; 
v_val_139_ = lean_ctor_get(v_next_133_, 0);
lean_inc(v_val_139_);
lean_dec_ref(v_next_133_);
lean_inc(v_upperBound_135_);
lean_inc(v_val_139_);
v___x_140_ = lean_apply_2(v_inst_130_, v_val_139_, v_upperBound_135_);
v___x_141_ = lean_unbox(v___x_140_);
if (v___x_141_ == 0)
{
lean_object* v___x_142_; 
lean_dec(v_val_139_);
lean_del_object(v___x_137_);
lean_dec(v_upperBound_135_);
lean_dec_ref(v_inst_131_);
v___x_142_ = lean_box(2);
return v___x_142_;
}
else
{
lean_object* v_succ_x3f_143_; lean_object* v___x_145_; uint8_t v_isShared_146_; uint8_t v_isSharedCheck_154_; 
v_succ_x3f_143_ = lean_ctor_get(v_inst_131_, 0);
v_isSharedCheck_154_ = !lean_is_exclusive(v_inst_131_);
if (v_isSharedCheck_154_ == 0)
{
lean_object* v_unused_155_; 
v_unused_155_ = lean_ctor_get(v_inst_131_, 1);
lean_dec(v_unused_155_);
v___x_145_ = v_inst_131_;
v_isShared_146_ = v_isSharedCheck_154_;
goto v_resetjp_144_;
}
else
{
lean_inc(v_succ_x3f_143_);
lean_dec(v_inst_131_);
v___x_145_ = lean_box(0);
v_isShared_146_ = v_isSharedCheck_154_;
goto v_resetjp_144_;
}
v_resetjp_144_:
{
lean_object* v___x_147_; lean_object* v___x_149_; 
lean_inc(v_val_139_);
v___x_147_ = lean_apply_1(v_succ_x3f_143_, v_val_139_);
if (v_isShared_138_ == 0)
{
lean_ctor_set(v___x_137_, 0, v___x_147_);
v___x_149_ = v___x_137_;
goto v_reusejp_148_;
}
else
{
lean_object* v_reuseFailAlloc_153_; 
v_reuseFailAlloc_153_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_153_, 0, v___x_147_);
lean_ctor_set(v_reuseFailAlloc_153_, 1, v_upperBound_135_);
v___x_149_ = v_reuseFailAlloc_153_;
goto v_reusejp_148_;
}
v_reusejp_148_:
{
lean_object* v___x_151_; 
if (v_isShared_146_ == 0)
{
lean_ctor_set(v___x_145_, 1, v_val_139_);
lean_ctor_set(v___x_145_, 0, v___x_149_);
v___x_151_ = v___x_145_;
goto v_reusejp_150_;
}
else
{
lean_object* v_reuseFailAlloc_152_; 
v_reuseFailAlloc_152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_152_, 0, v___x_149_);
lean_ctor_set(v_reuseFailAlloc_152_, 1, v_val_139_);
v___x_151_ = v_reuseFailAlloc_152_;
goto v_reusejp_150_;
}
v_reusejp_150_:
{
return v___x_151_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg(lean_object* v_inst_158_, lean_object* v_inst_159_){
_start:
{
lean_object* v___f_160_; 
v___f_160_ = lean_alloc_closure((void*)(l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0), 3, 2);
lean_closure_set(v___f_160_, 0, v_inst_159_);
lean_closure_set(v___f_160_, 1, v_inst_158_);
return v___f_160_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE(lean_object* v_00_u03b1_161_, lean_object* v_inst_162_, lean_object* v_inst_163_, lean_object* v_inst_164_){
_start:
{
lean_object* v___f_165_; 
v___f_165_ = lean_alloc_closure((void*)(l_Std_Rxc_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLE___redArg___lam__0), 3, 2);
lean_closure_set(v___f_165_, 0, v_inst_164_);
lean_closure_set(v___f_165_, 1, v_inst_162_);
return v___f_165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterStep_successor_match__1_splitter___redArg(lean_object* v_x_166_, lean_object* v_h__1_167_, lean_object* v_h__2_168_, lean_object* v_h__3_169_){
_start:
{
switch(lean_obj_tag(v_x_166_))
{
case 0:
{
lean_object* v_it_170_; lean_object* v_out_171_; lean_object* v___x_172_; 
lean_dec(v_h__3_169_);
lean_dec(v_h__2_168_);
v_it_170_ = lean_ctor_get(v_x_166_, 0);
lean_inc(v_it_170_);
v_out_171_ = lean_ctor_get(v_x_166_, 1);
lean_inc(v_out_171_);
lean_dec_ref(v_x_166_);
v___x_172_ = lean_apply_2(v_h__1_167_, v_it_170_, v_out_171_);
return v___x_172_;
}
case 1:
{
lean_object* v_it_173_; lean_object* v___x_174_; 
lean_dec(v_h__3_169_);
lean_dec(v_h__1_167_);
v_it_173_ = lean_ctor_get(v_x_166_, 0);
lean_inc(v_it_173_);
lean_dec_ref(v_x_166_);
v___x_174_ = lean_apply_1(v_h__2_168_, v_it_173_);
return v___x_174_;
}
default: 
{
lean_object* v___x_175_; lean_object* v___x_176_; 
lean_dec(v_h__2_168_);
lean_dec(v_h__1_167_);
v___x_175_ = lean_box(0);
v___x_176_ = lean_apply_1(v_h__3_169_, v___x_175_);
return v___x_176_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterStep_successor_match__1_splitter(lean_object* v_00_u03b1_177_, lean_object* v_00_u03b2_178_, lean_object* v_motive_179_, lean_object* v_x_180_, lean_object* v_h__1_181_, lean_object* v_h__2_182_, lean_object* v_h__3_183_){
_start:
{
lean_object* v___x_184_; 
v___x_184_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterStep_successor_match__1_splitter___redArg(v_x_180_, v_h__1_181_, v_h__2_182_, v_h__3_183_);
return v___x_184_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_185_, lean_object* v_inst_186_, lean_object* v_inst_187_, lean_object* v_inst_188_, lean_object* v_inst_189_, lean_object* v_inst_190_){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(0);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_192_, lean_object* v_inst_193_, lean_object* v_inst_194_, lean_object* v_inst_195_, lean_object* v_inst_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(v_00_u03b1_192_, v_inst_193_, v_inst_194_, v_inst_195_, v_inst_196_, v_inst_197_);
lean_dec_ref(v_inst_195_);
lean_dec_ref(v_inst_193_);
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_inst_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(0);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_inst_209_){
_start:
{
lean_object* v_res_210_; 
v_res_210_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(v_00_u03b1_205_, v_inst_206_, v_inst_207_, v_inst_208_, v_inst_209_);
lean_dec_ref(v_inst_208_);
lean_dec_ref(v_inst_206_);
return v_res_210_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter___redArg(lean_object* v_x_211_, lean_object* v_h__1_212_, lean_object* v_h__2_213_){
_start:
{
if (lean_obj_tag(v_x_211_) == 0)
{
lean_object* v___x_214_; lean_object* v___x_215_; 
lean_dec(v_h__2_213_);
v___x_214_ = lean_box(0);
v___x_215_ = lean_apply_1(v_h__1_212_, v___x_214_);
return v___x_215_;
}
else
{
lean_object* v_val_216_; lean_object* v___x_217_; 
lean_dec(v_h__1_212_);
v_val_216_ = lean_ctor_get(v_x_211_, 0);
lean_inc(v_val_216_);
lean_dec_ref(v_x_211_);
v___x_217_ = lean_apply_1(v_h__2_213_, v_val_216_);
return v___x_217_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter(lean_object* v_00_u03b1_218_, lean_object* v_motive_219_, lean_object* v_x_220_, lean_object* v_h__1_221_, lean_object* v_h__2_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter___redArg(v_x_220_, v_h__1_221_, v_h__2_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_it_226_, lean_object* v_n_227_){
_start:
{
lean_object* v_next_228_; 
v_next_228_ = lean_ctor_get(v_it_226_, 0);
lean_inc(v_next_228_);
if (lean_obj_tag(v_next_228_) == 0)
{
lean_object* v___x_229_; 
lean_dec(v_n_227_);
lean_dec_ref(v_it_226_);
lean_dec_ref(v_inst_225_);
lean_dec_ref(v_inst_224_);
v___x_229_ = lean_box(2);
return v___x_229_;
}
else
{
lean_object* v_upperBound_230_; lean_object* v___x_232_; uint8_t v_isShared_233_; uint8_t v_isSharedCheck_254_; 
v_upperBound_230_ = lean_ctor_get(v_it_226_, 1);
v_isSharedCheck_254_ = !lean_is_exclusive(v_it_226_);
if (v_isSharedCheck_254_ == 0)
{
lean_object* v_unused_255_; 
v_unused_255_ = lean_ctor_get(v_it_226_, 0);
lean_dec(v_unused_255_);
v___x_232_ = v_it_226_;
v_isShared_233_ = v_isSharedCheck_254_;
goto v_resetjp_231_;
}
else
{
lean_inc(v_upperBound_230_);
lean_dec(v_it_226_);
v___x_232_ = lean_box(0);
v_isShared_233_ = v_isSharedCheck_254_;
goto v_resetjp_231_;
}
v_resetjp_231_:
{
lean_object* v_succ_x3f_234_; lean_object* v_succMany_x3f_235_; lean_object* v___x_237_; uint8_t v_isShared_238_; uint8_t v_isSharedCheck_253_; 
v_succ_x3f_234_ = lean_ctor_get(v_inst_224_, 0);
v_succMany_x3f_235_ = lean_ctor_get(v_inst_224_, 1);
v_isSharedCheck_253_ = !lean_is_exclusive(v_inst_224_);
if (v_isSharedCheck_253_ == 0)
{
v___x_237_ = v_inst_224_;
v_isShared_238_ = v_isSharedCheck_253_;
goto v_resetjp_236_;
}
else
{
lean_inc(v_succMany_x3f_235_);
lean_inc(v_succ_x3f_234_);
lean_dec(v_inst_224_);
v___x_237_ = lean_box(0);
v_isShared_238_ = v_isSharedCheck_253_;
goto v_resetjp_236_;
}
v_resetjp_236_:
{
lean_object* v_val_239_; lean_object* v___x_240_; 
v_val_239_ = lean_ctor_get(v_next_228_, 0);
lean_inc(v_val_239_);
lean_dec_ref(v_next_228_);
v___x_240_ = lean_apply_2(v_succMany_x3f_235_, v_n_227_, v_val_239_);
if (lean_obj_tag(v___x_240_) == 0)
{
lean_object* v___x_241_; 
lean_del_object(v___x_237_);
lean_dec_ref(v_succ_x3f_234_);
lean_del_object(v___x_232_);
lean_dec(v_upperBound_230_);
lean_dec_ref(v_inst_225_);
v___x_241_ = lean_box(2);
return v___x_241_;
}
else
{
lean_object* v_val_242_; lean_object* v___x_243_; uint8_t v___x_244_; 
v_val_242_ = lean_ctor_get(v___x_240_, 0);
lean_inc(v_val_242_);
lean_dec_ref(v___x_240_);
lean_inc(v_upperBound_230_);
lean_inc(v_val_242_);
v___x_243_ = lean_apply_2(v_inst_225_, v_val_242_, v_upperBound_230_);
v___x_244_ = lean_unbox(v___x_243_);
if (v___x_244_ == 0)
{
lean_object* v___x_245_; 
lean_dec(v_val_242_);
lean_del_object(v___x_237_);
lean_dec_ref(v_succ_x3f_234_);
lean_del_object(v___x_232_);
lean_dec(v_upperBound_230_);
v___x_245_ = lean_box(2);
return v___x_245_;
}
else
{
lean_object* v___x_246_; lean_object* v___x_248_; 
lean_inc(v_val_242_);
v___x_246_ = lean_apply_1(v_succ_x3f_234_, v_val_242_);
if (v_isShared_233_ == 0)
{
lean_ctor_set(v___x_232_, 0, v___x_246_);
v___x_248_ = v___x_232_;
goto v_reusejp_247_;
}
else
{
lean_object* v_reuseFailAlloc_252_; 
v_reuseFailAlloc_252_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_252_, 0, v___x_246_);
lean_ctor_set(v_reuseFailAlloc_252_, 1, v_upperBound_230_);
v___x_248_ = v_reuseFailAlloc_252_;
goto v_reusejp_247_;
}
v_reusejp_247_:
{
lean_object* v___x_250_; 
if (v_isShared_238_ == 0)
{
lean_ctor_set(v___x_237_, 1, v_val_242_);
lean_ctor_set(v___x_237_, 0, v___x_248_);
v___x_250_ = v___x_237_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v___x_248_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_val_242_);
v___x_250_ = v_reuseFailAlloc_251_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
return v___x_250_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess___redArg(lean_object* v_inst_256_, lean_object* v_inst_257_){
_start:
{
lean_object* v___f_258_; 
v___f_258_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_258_, 0, v_inst_256_);
lean_closure_set(v___f_258_, 1, v_inst_257_);
return v___f_258_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess(lean_object* v_00_u03b1_259_, lean_object* v_inst_260_, lean_object* v_inst_261_, lean_object* v_inst_262_, lean_object* v_inst_263_, lean_object* v_inst_264_){
_start:
{
lean_object* v___f_265_; 
v___f_265_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_265_, 0, v_inst_260_);
lean_closure_set(v___f_265_, 1, v_inst_262_);
return v___f_265_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0(lean_object* v_toApplicative_266_, lean_object* v_inst_267_, lean_object* v_next_268_, lean_object* v_G_269_, lean_object* v_____do__lift_270_){
_start:
{
if (lean_obj_tag(v_____do__lift_270_) == 0)
{
lean_object* v_a_271_; lean_object* v_toPure_272_; lean_object* v___x_273_; 
lean_dec(v_G_269_);
lean_dec(v_next_268_);
lean_dec_ref(v_inst_267_);
v_a_271_ = lean_ctor_get(v_____do__lift_270_, 0);
lean_inc(v_a_271_);
lean_dec_ref(v_____do__lift_270_);
v_toPure_272_ = lean_ctor_get(v_toApplicative_266_, 1);
lean_inc(v_toPure_272_);
lean_dec_ref(v_toApplicative_266_);
v___x_273_ = lean_apply_2(v_toPure_272_, lean_box(0), v_a_271_);
return v___x_273_;
}
else
{
lean_object* v_a_274_; lean_object* v_succ_x3f_275_; lean_object* v___x_276_; 
v_a_274_ = lean_ctor_get(v_____do__lift_270_, 0);
lean_inc(v_a_274_);
lean_dec_ref(v_____do__lift_270_);
v_succ_x3f_275_ = lean_ctor_get(v_inst_267_, 0);
lean_inc_ref(v_succ_x3f_275_);
lean_dec_ref(v_inst_267_);
v___x_276_ = lean_apply_1(v_succ_x3f_275_, v_next_268_);
if (lean_obj_tag(v___x_276_) == 0)
{
lean_object* v_toPure_277_; lean_object* v___x_278_; 
lean_dec(v_G_269_);
v_toPure_277_ = lean_ctor_get(v_toApplicative_266_, 1);
lean_inc(v_toPure_277_);
lean_dec_ref(v_toApplicative_266_);
v___x_278_ = lean_apply_2(v_toPure_277_, lean_box(0), v_a_274_);
return v___x_278_;
}
else
{
lean_object* v_val_279_; lean_object* v___x_280_; 
lean_dec_ref(v_toApplicative_266_);
v_val_279_ = lean_ctor_get(v___x_276_, 0);
lean_inc(v_val_279_);
lean_dec_ref(v___x_276_);
v___x_280_ = lean_apply_4(v_G_269_, v_val_279_, v_a_274_, lean_box(0), lean_box(0));
return v___x_280_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object* v_inst_281_, lean_object* v_upperBound_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_f_285_, lean_object* v_next_286_, lean_object* v_acc_287_, lean_object* v_h_288_, lean_object* v_G_289_){
_start:
{
lean_object* v___x_290_; uint8_t v___x_291_; 
lean_inc(v_next_286_);
v___x_290_ = lean_apply_2(v_inst_281_, v_next_286_, v_upperBound_282_);
v___x_291_ = lean_unbox(v___x_290_);
if (v___x_291_ == 0)
{
lean_object* v_toApplicative_292_; lean_object* v_toPure_293_; lean_object* v___x_294_; 
lean_dec(v_G_289_);
lean_dec(v_next_286_);
lean_dec(v_f_285_);
lean_dec_ref(v_inst_284_);
v_toApplicative_292_ = lean_ctor_get(v_inst_283_, 0);
lean_inc_ref(v_toApplicative_292_);
lean_dec_ref(v_inst_283_);
v_toPure_293_ = lean_ctor_get(v_toApplicative_292_, 1);
lean_inc(v_toPure_293_);
lean_dec_ref(v_toApplicative_292_);
v___x_294_ = lean_apply_2(v_toPure_293_, lean_box(0), v_acc_287_);
return v___x_294_;
}
else
{
lean_object* v_toApplicative_295_; lean_object* v_toBind_296_; lean_object* v___f_297_; lean_object* v___x_298_; lean_object* v___x_299_; 
v_toApplicative_295_ = lean_ctor_get(v_inst_283_, 0);
lean_inc_ref(v_toApplicative_295_);
v_toBind_296_ = lean_ctor_get(v_inst_283_, 1);
lean_inc(v_toBind_296_);
lean_dec_ref(v_inst_283_);
lean_inc(v_next_286_);
v___f_297_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_297_, 0, v_toApplicative_295_);
lean_closure_set(v___f_297_, 1, v_inst_284_);
lean_closure_set(v___f_297_, 2, v_next_286_);
lean_closure_set(v___f_297_, 3, v_G_289_);
v___x_298_ = lean_apply_4(v_f_285_, v_next_286_, lean_box(0), lean_box(0), v_acc_287_);
v___x_299_ = lean_apply_4(v_toBind_296_, lean_box(0), lean_box(0), v___x_298_, v___f_297_);
return v___x_299_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_300_, lean_object* v_inst_301_, lean_object* v_inst_302_, lean_object* v_upperBound_303_, lean_object* v_acc_304_, lean_object* v_next_305_, lean_object* v_f_306_){
_start:
{
lean_object* v___f_307_; lean_object* v___x_308_; 
v___f_307_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 9, 5);
lean_closure_set(v___f_307_, 0, v_inst_301_);
lean_closure_set(v___f_307_, 1, v_upperBound_303_);
lean_closure_set(v___f_307_, 2, v_inst_302_);
lean_closure_set(v___f_307_, 3, v_inst_300_);
lean_closure_set(v___f_307_, 4, v_f_306_);
v___x_308_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_307_, v_next_305_, v_acc_304_, lean_box(0));
return v___x_308_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_309_, lean_object* v_inst_310_, lean_object* v_inst_311_, lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_n_315_, lean_object* v_inst_316_, lean_object* v_00_u03b3_317_, lean_object* v_Pl_318_, lean_object* v_LargeEnough_319_, lean_object* v_hl_320_, lean_object* v_upperBound_321_, lean_object* v_acc_322_, lean_object* v_next_323_, lean_object* v_h_324_, lean_object* v_f_325_){
_start:
{
lean_object* v___f_326_; lean_object* v___x_327_; 
v___f_326_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 9, 5);
lean_closure_set(v___f_326_, 0, v_inst_312_);
lean_closure_set(v___f_326_, 1, v_upperBound_321_);
lean_closure_set(v___f_326_, 2, v_inst_316_);
lean_closure_set(v___f_326_, 3, v_inst_310_);
lean_closure_set(v___f_326_, 4, v_f_325_);
v___x_327_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_326_, v_next_323_, v_acc_322_, lean_box(0));
return v___x_327_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_328_ = _args[0];
lean_object* v_inst_329_ = _args[1];
lean_object* v_inst_330_ = _args[2];
lean_object* v_inst_331_ = _args[3];
lean_object* v_inst_332_ = _args[4];
lean_object* v_inst_333_ = _args[5];
lean_object* v_n_334_ = _args[6];
lean_object* v_inst_335_ = _args[7];
lean_object* v_00_u03b3_336_ = _args[8];
lean_object* v_Pl_337_ = _args[9];
lean_object* v_LargeEnough_338_ = _args[10];
lean_object* v_hl_339_ = _args[11];
lean_object* v_upperBound_340_ = _args[12];
lean_object* v_acc_341_ = _args[13];
lean_object* v_next_342_ = _args[14];
lean_object* v_h_343_ = _args[15];
lean_object* v_f_344_ = _args[16];
_start:
{
lean_object* v_res_345_; 
v_res_345_ = l_Std_Rxc_Iterator_instIteratorLoop_loop(v_00_u03b1_328_, v_inst_329_, v_inst_330_, v_inst_331_, v_inst_332_, v_inst_333_, v_n_334_, v_inst_335_, v_00_u03b3_336_, v_Pl_337_, v_LargeEnough_338_, v_hl_339_, v_upperBound_340_, v_acc_341_, v_next_342_, v_h_343_, v_f_344_);
return v_res_345_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_346_, lean_object* v_inst_347_, lean_object* v_next_348_, lean_object* v_G_349_, lean_object* v_____do__lift_350_){
_start:
{
if (lean_obj_tag(v_____do__lift_350_) == 0)
{
lean_object* v_a_351_; lean_object* v___x_352_; 
lean_dec(v_G_349_);
lean_dec(v_next_348_);
lean_dec_ref(v_inst_347_);
v_a_351_ = lean_ctor_get(v_____do__lift_350_, 0);
lean_inc(v_a_351_);
lean_dec_ref(v_____do__lift_350_);
v___x_352_ = lean_apply_2(v_toPure_346_, lean_box(0), v_a_351_);
return v___x_352_;
}
else
{
lean_object* v_a_353_; lean_object* v_succ_x3f_354_; lean_object* v___x_355_; 
v_a_353_ = lean_ctor_get(v_____do__lift_350_, 0);
lean_inc(v_a_353_);
lean_dec_ref(v_____do__lift_350_);
v_succ_x3f_354_ = lean_ctor_get(v_inst_347_, 0);
lean_inc_ref(v_succ_x3f_354_);
lean_dec_ref(v_inst_347_);
v___x_355_ = lean_apply_1(v_succ_x3f_354_, v_next_348_);
if (lean_obj_tag(v___x_355_) == 0)
{
lean_object* v___x_356_; 
lean_dec(v_G_349_);
v___x_356_ = lean_apply_2(v_toPure_346_, lean_box(0), v_a_353_);
return v___x_356_;
}
else
{
lean_object* v_val_357_; lean_object* v___x_358_; 
lean_dec(v_toPure_346_);
v_val_357_ = lean_ctor_get(v___x_355_, 0);
lean_inc(v_val_357_);
lean_dec_ref(v___x_355_);
v___x_358_ = lean_apply_4(v_G_349_, v_val_357_, v_a_353_, lean_box(0), lean_box(0));
return v___x_358_;
}
}
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
v___f_372_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0), 5, 4);
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
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_375_, lean_object* v_inst_376_, lean_object* v_inst_377_, lean_object* v_toBind_378_, lean_object* v_x_379_, lean_object* v_00_u03b3_380_, lean_object* v_Pl_381_, lean_object* v_it_382_, lean_object* v_init_383_, lean_object* v_f_384_){
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
lean_dec_ref(v_next_385_);
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
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_391_, lean_object* v_inst_392_, lean_object* v_inst_393_, lean_object* v_toBind_394_, lean_object* v_x_395_, lean_object* v_00_u03b3_396_, lean_object* v_Pl_397_, lean_object* v_it_398_, lean_object* v_init_399_, lean_object* v_f_400_){
_start:
{
lean_object* v_res_401_; 
v_res_401_ = l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_391_, v_inst_392_, v_inst_393_, v_toBind_394_, v_x_395_, v_00_u03b3_396_, v_Pl_397_, v_it_398_, v_init_399_, v_f_400_);
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
v___f_408_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
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
v___f_420_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
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
lean_dec_ref(v_____do__lift_421_);
v___x_425_ = lean_apply_2(v_h__2_423_, v_a_424_, lean_box(0));
return v___x_425_;
}
else
{
lean_object* v_a_426_; lean_object* v___x_427_; 
lean_dec(v_h__2_423_);
v_a_426_ = lean_ctor_get(v_____do__lift_421_, 0);
lean_inc(v_a_426_);
lean_dec_ref(v_____do__lift_421_);
v___x_427_ = lean_apply_2(v_h__1_422_, v_a_426_, lean_box(0));
return v___x_427_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(lean_object* v_00_u03b1_428_, lean_object* v_00_u03b3_429_, lean_object* v_Pl_430_, lean_object* v_acc_431_, lean_object* v_next_432_, lean_object* v_motive_433_, lean_object* v_____do__lift_434_, lean_object* v_h__1_435_, lean_object* v_h__2_436_){
_start:
{
lean_object* v___x_437_; 
v___x_437_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___redArg(v_____do__lift_434_, v_h__1_435_, v_h__2_436_);
return v___x_437_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___boxed(lean_object* v_00_u03b1_438_, lean_object* v_00_u03b3_439_, lean_object* v_Pl_440_, lean_object* v_acc_441_, lean_object* v_next_442_, lean_object* v_motive_443_, lean_object* v_____do__lift_444_, lean_object* v_h__1_445_, lean_object* v_h__2_446_){
_start:
{
lean_object* v_res_447_; 
v_res_447_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(v_00_u03b1_438_, v_00_u03b3_439_, v_Pl_440_, v_acc_441_, v_next_442_, v_motive_443_, v_____do__lift_444_, v_h__1_445_, v_h__2_446_);
lean_dec(v_next_442_);
lean_dec(v_acc_441_);
return v_res_447_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter___redArg(lean_object* v_x_448_, lean_object* v_h__1_449_, lean_object* v_h__2_450_){
_start:
{
if (lean_obj_tag(v_x_448_) == 0)
{
lean_object* v___x_451_; 
lean_dec(v_h__1_449_);
v___x_451_ = lean_apply_1(v_h__2_450_, lean_box(0));
return v___x_451_;
}
else
{
lean_object* v_val_452_; lean_object* v___x_453_; 
lean_dec(v_h__2_450_);
v_val_452_ = lean_ctor_get(v_x_448_, 0);
lean_inc(v_val_452_);
lean_dec_ref(v_x_448_);
v___x_453_ = lean_apply_2(v_h__1_449_, v_val_452_, lean_box(0));
return v___x_453_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter(lean_object* v_00_u03b1_454_, lean_object* v_motive_455_, lean_object* v_x_456_, lean_object* v_h__1_457_, lean_object* v_h__2_458_){
_start:
{
lean_object* v___x_459_; 
v___x_459_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter___redArg(v_x_456_, v_h__1_457_, v_h__2_458_);
return v___x_459_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___redArg(lean_object* v_____do__lift_460_, lean_object* v_h__1_461_, lean_object* v_h__2_462_){
_start:
{
if (lean_obj_tag(v_____do__lift_460_) == 0)
{
lean_object* v_a_463_; lean_object* v___x_464_; 
lean_dec(v_h__1_461_);
v_a_463_ = lean_ctor_get(v_____do__lift_460_, 0);
lean_inc(v_a_463_);
lean_dec_ref(v_____do__lift_460_);
v___x_464_ = lean_apply_2(v_h__2_462_, v_a_463_, lean_box(0));
return v___x_464_;
}
else
{
lean_object* v_a_465_; lean_object* v___x_466_; 
lean_dec(v_h__2_462_);
v_a_465_ = lean_ctor_get(v_____do__lift_460_, 0);
lean_inc(v_a_465_);
lean_dec_ref(v_____do__lift_460_);
v___x_466_ = lean_apply_2(v_h__1_461_, v_a_465_, lean_box(0));
return v___x_466_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(lean_object* v_00_u03b1_467_, lean_object* v_00_u03b3_468_, lean_object* v_Pl_469_, lean_object* v_next_470_, lean_object* v_acc_471_, lean_object* v_motive_472_, lean_object* v_____do__lift_473_, lean_object* v_h__1_474_, lean_object* v_h__2_475_){
_start:
{
lean_object* v___x_476_; 
v___x_476_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___redArg(v_____do__lift_473_, v_h__1_474_, v_h__2_475_);
return v___x_476_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_477_, lean_object* v_00_u03b3_478_, lean_object* v_Pl_479_, lean_object* v_next_480_, lean_object* v_acc_481_, lean_object* v_motive_482_, lean_object* v_____do__lift_483_, lean_object* v_h__1_484_, lean_object* v_h__2_485_){
_start:
{
lean_object* v_res_486_; 
v_res_486_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(v_00_u03b1_477_, v_00_u03b3_478_, v_Pl_479_, v_next_480_, v_acc_481_, v_motive_482_, v_____do__lift_483_, v_h__1_484_, v_h__2_485_);
lean_dec(v_acc_481_);
lean_dec(v_next_480_);
return v_res_486_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_487_, lean_object* v_h__1_488_, lean_object* v_h__2_489_, lean_object* v_h__3_490_){
_start:
{
switch(lean_obj_tag(v_x_487_))
{
case 0:
{
lean_object* v_it_491_; lean_object* v_out_492_; lean_object* v___x_493_; 
lean_dec(v_h__3_490_);
lean_dec(v_h__2_489_);
v_it_491_ = lean_ctor_get(v_x_487_, 0);
lean_inc(v_it_491_);
v_out_492_ = lean_ctor_get(v_x_487_, 1);
lean_inc(v_out_492_);
lean_dec_ref(v_x_487_);
v___x_493_ = lean_apply_3(v_h__1_488_, v_it_491_, v_out_492_, lean_box(0));
return v___x_493_;
}
case 1:
{
lean_object* v_it_494_; lean_object* v___x_495_; 
lean_dec(v_h__3_490_);
lean_dec(v_h__1_488_);
v_it_494_ = lean_ctor_get(v_x_487_, 0);
lean_inc(v_it_494_);
lean_dec_ref(v_x_487_);
v___x_495_ = lean_apply_2(v_h__2_489_, v_it_494_, lean_box(0));
return v___x_495_;
}
default: 
{
lean_object* v___x_496_; 
lean_dec(v_h__2_489_);
lean_dec(v_h__1_488_);
v___x_496_ = lean_apply_1(v_h__3_490_, lean_box(0));
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_497_, lean_object* v_00_u03b2_498_, lean_object* v_m_499_, lean_object* v_inst_500_, lean_object* v_it_501_, lean_object* v_motive_502_, lean_object* v_x_503_, lean_object* v_h__1_504_, lean_object* v_h__2_505_, lean_object* v_h__3_506_){
_start:
{
lean_object* v___x_507_; 
v___x_507_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(v_x_503_, v_h__1_504_, v_h__2_505_, v_h__3_506_);
return v___x_507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_508_, lean_object* v_00_u03b2_509_, lean_object* v_m_510_, lean_object* v_inst_511_, lean_object* v_it_512_, lean_object* v_motive_513_, lean_object* v_x_514_, lean_object* v_h__1_515_, lean_object* v_h__2_516_, lean_object* v_h__3_517_){
_start:
{
lean_object* v_res_518_; 
v_res_518_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_508_, v_00_u03b2_509_, v_m_510_, v_inst_511_, v_it_512_, v_motive_513_, v_x_514_, v_h__1_515_, v_h__2_516_, v_h__3_517_);
lean_dec(v_it_512_);
lean_dec(v_inst_511_);
return v_res_518_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_){
_start:
{
if (lean_obj_tag(v_____do__lift_519_) == 0)
{
lean_object* v_a_522_; lean_object* v___x_523_; 
lean_dec(v_h__1_520_);
v_a_522_ = lean_ctor_get(v_____do__lift_519_, 0);
lean_inc(v_a_522_);
lean_dec_ref(v_____do__lift_519_);
v___x_523_ = lean_apply_2(v_h__2_521_, v_a_522_, lean_box(0));
return v___x_523_;
}
else
{
lean_object* v_a_524_; lean_object* v___x_525_; 
lean_dec(v_h__2_521_);
v_a_524_ = lean_ctor_get(v_____do__lift_519_, 0);
lean_inc(v_a_524_);
lean_dec_ref(v_____do__lift_519_);
v___x_525_ = lean_apply_2(v_h__1_520_, v_a_524_, lean_box(0));
return v___x_525_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b2_526_, lean_object* v_00_u03b3_527_, lean_object* v_init_528_, lean_object* v_PlausibleForInStep_529_, lean_object* v_out_530_, lean_object* v_motive_531_, lean_object* v_____do__lift_532_, lean_object* v_h__1_533_, lean_object* v_h__2_534_){
_start:
{
lean_object* v___x_535_; 
v___x_535_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(v_____do__lift_532_, v_h__1_533_, v_h__2_534_);
return v___x_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(lean_object* v_00_u03b2_536_, lean_object* v_00_u03b3_537_, lean_object* v_init_538_, lean_object* v_PlausibleForInStep_539_, lean_object* v_out_540_, lean_object* v_motive_541_, lean_object* v_____do__lift_542_, lean_object* v_h__1_543_, lean_object* v_h__2_544_){
_start:
{
lean_object* v_res_545_; 
v_res_545_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_536_, v_00_u03b3_537_, v_init_538_, v_PlausibleForInStep_539_, v_out_540_, v_motive_541_, v_____do__lift_542_, v_h__1_543_, v_h__2_544_);
lean_dec(v_out_540_);
lean_dec(v_init_538_);
return v_res_545_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_546_, lean_object* v_f_547_, lean_object* v_h__1_548_, lean_object* v_h__2_549_){
_start:
{
lean_object* v_next_550_; 
v_next_550_ = lean_ctor_get(v_it_546_, 0);
if (lean_obj_tag(v_next_550_) == 0)
{
lean_object* v_upperBound_551_; lean_object* v___x_552_; 
lean_dec(v_h__1_548_);
v_upperBound_551_ = lean_ctor_get(v_it_546_, 1);
lean_inc(v_upperBound_551_);
lean_dec_ref(v_it_546_);
v___x_552_ = lean_apply_2(v_h__2_549_, v_upperBound_551_, v_f_547_);
return v___x_552_;
}
else
{
lean_object* v_upperBound_553_; lean_object* v_val_554_; lean_object* v___x_555_; 
lean_inc_ref(v_next_550_);
lean_dec(v_h__2_549_);
v_upperBound_553_ = lean_ctor_get(v_it_546_, 1);
lean_inc(v_upperBound_553_);
lean_dec_ref(v_it_546_);
v_val_554_ = lean_ctor_get(v_next_550_, 0);
lean_inc(v_val_554_);
lean_dec_ref(v_next_550_);
v___x_555_ = lean_apply_3(v_h__1_548_, v_val_554_, v_upperBound_553_, v_f_547_);
return v___x_555_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_556_, lean_object* v_inst_557_, lean_object* v_inst_558_, lean_object* v_inst_559_, lean_object* v_n_560_, lean_object* v_00_u03b3_561_, lean_object* v_Pl_562_, lean_object* v_motive_563_, lean_object* v_it_564_, lean_object* v_f_565_, lean_object* v_h__1_566_, lean_object* v_h__2_567_){
_start:
{
lean_object* v___x_568_; 
v___x_568_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___redArg(v_it_564_, v_f_565_, v_h__1_566_, v_h__2_567_);
return v___x_568_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_569_, lean_object* v_inst_570_, lean_object* v_inst_571_, lean_object* v_inst_572_, lean_object* v_n_573_, lean_object* v_00_u03b3_574_, lean_object* v_Pl_575_, lean_object* v_motive_576_, lean_object* v_it_577_, lean_object* v_f_578_, lean_object* v_h__1_579_, lean_object* v_h__2_580_){
_start:
{
lean_object* v_res_581_; 
v_res_581_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_569_, v_inst_570_, v_inst_571_, v_inst_572_, v_n_573_, v_00_u03b3_574_, v_Pl_575_, v_motive_576_, v_it_577_, v_f_578_, v_h__1_579_, v_h__2_580_);
lean_dec_ref(v_inst_572_);
lean_dec_ref(v_inst_570_);
return v_res_581_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object* v_x_582_, lean_object* v_h__1_583_, lean_object* v_h__2_584_, lean_object* v_h__3_585_){
_start:
{
switch(lean_obj_tag(v_x_582_))
{
case 0:
{
lean_object* v_it_586_; lean_object* v_out_587_; lean_object* v___x_588_; 
lean_dec(v_h__3_585_);
lean_dec(v_h__2_584_);
v_it_586_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_it_586_);
v_out_587_ = lean_ctor_get(v_x_582_, 1);
lean_inc(v_out_587_);
lean_dec_ref(v_x_582_);
v___x_588_ = lean_apply_3(v_h__1_583_, v_it_586_, v_out_587_, lean_box(0));
return v___x_588_;
}
case 1:
{
lean_object* v_it_589_; lean_object* v___x_590_; 
lean_dec(v_h__3_585_);
lean_dec(v_h__1_583_);
v_it_589_ = lean_ctor_get(v_x_582_, 0);
lean_inc(v_it_589_);
lean_dec_ref(v_x_582_);
v___x_590_ = lean_apply_2(v_h__2_584_, v_it_589_, lean_box(0));
return v___x_590_;
}
default: 
{
lean_object* v___x_591_; 
lean_dec(v_h__2_584_);
lean_dec(v_h__1_583_);
v___x_591_ = lean_apply_1(v_h__3_585_, lean_box(0));
return v___x_591_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object* v_m_592_, lean_object* v_00_u03b1_593_, lean_object* v_00_u03b2_594_, lean_object* v_inst_595_, lean_object* v_it_596_, lean_object* v_motive_597_, lean_object* v_x_598_, lean_object* v_h__1_599_, lean_object* v_h__2_600_, lean_object* v_h__3_601_){
_start:
{
lean_object* v___x_602_; 
v___x_602_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(v_x_598_, v_h__1_599_, v_h__2_600_, v_h__3_601_);
return v___x_602_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object* v_m_603_, lean_object* v_00_u03b1_604_, lean_object* v_00_u03b2_605_, lean_object* v_inst_606_, lean_object* v_it_607_, lean_object* v_motive_608_, lean_object* v_x_609_, lean_object* v_h__1_610_, lean_object* v_h__2_611_, lean_object* v_h__3_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_603_, v_00_u03b1_604_, v_00_u03b2_605_, v_inst_606_, v_it_607_, v_motive_608_, v_x_609_, v_h__1_610_, v_h__2_611_, v_h__3_612_);
lean_dec(v_it_607_);
lean_dec(v_inst_606_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object* v_____do__lift_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_){
_start:
{
if (lean_obj_tag(v_____do__lift_614_) == 0)
{
lean_object* v_a_617_; lean_object* v___x_618_; 
lean_dec(v_h__1_615_);
v_a_617_ = lean_ctor_get(v_____do__lift_614_, 0);
lean_inc(v_a_617_);
lean_dec_ref(v_____do__lift_614_);
v___x_618_ = lean_apply_2(v_h__2_616_, v_a_617_, lean_box(0));
return v___x_618_;
}
else
{
lean_object* v_a_619_; lean_object* v___x_620_; 
lean_dec(v_h__2_616_);
v_a_619_ = lean_ctor_get(v_____do__lift_614_, 0);
lean_inc(v_a_619_);
lean_dec_ref(v_____do__lift_614_);
v___x_620_ = lean_apply_2(v_h__1_615_, v_a_619_, lean_box(0));
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object* v_00_u03b2_621_, lean_object* v_00_u03b3_622_, lean_object* v_PlausibleForInStep_623_, lean_object* v_acc_624_, lean_object* v_out_625_, lean_object* v_motive_626_, lean_object* v_____do__lift_627_, lean_object* v_h__1_628_, lean_object* v_h__2_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(v_____do__lift_627_, v_h__1_628_, v_h__2_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object* v_00_u03b2_631_, lean_object* v_00_u03b3_632_, lean_object* v_PlausibleForInStep_633_, lean_object* v_acc_634_, lean_object* v_out_635_, lean_object* v_motive_636_, lean_object* v_____do__lift_637_, lean_object* v_h__1_638_, lean_object* v_h__2_639_){
_start:
{
lean_object* v_res_640_; 
v_res_640_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_631_, v_00_u03b3_632_, v_PlausibleForInStep_633_, v_acc_634_, v_out_635_, v_motive_636_, v_____do__lift_637_, v_h__1_638_, v_h__2_639_);
lean_dec(v_out_635_);
lean_dec(v_acc_634_);
return v_res_640_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step___redArg(lean_object* v_inst_641_, lean_object* v_inst_642_, lean_object* v_it_643_){
_start:
{
lean_object* v_next_644_; 
v_next_644_ = lean_ctor_get(v_it_643_, 0);
lean_inc(v_next_644_);
if (lean_obj_tag(v_next_644_) == 0)
{
lean_object* v___x_645_; 
lean_dec_ref(v_it_643_);
lean_dec_ref(v_inst_642_);
lean_dec_ref(v_inst_641_);
v___x_645_ = lean_box(2);
return v___x_645_;
}
else
{
lean_object* v_upperBound_646_; lean_object* v___x_648_; uint8_t v_isShared_649_; uint8_t v_isSharedCheck_667_; 
v_upperBound_646_ = lean_ctor_get(v_it_643_, 1);
v_isSharedCheck_667_ = !lean_is_exclusive(v_it_643_);
if (v_isSharedCheck_667_ == 0)
{
lean_object* v_unused_668_; 
v_unused_668_ = lean_ctor_get(v_it_643_, 0);
lean_dec(v_unused_668_);
v___x_648_ = v_it_643_;
v_isShared_649_ = v_isSharedCheck_667_;
goto v_resetjp_647_;
}
else
{
lean_inc(v_upperBound_646_);
lean_dec(v_it_643_);
v___x_648_ = lean_box(0);
v_isShared_649_ = v_isSharedCheck_667_;
goto v_resetjp_647_;
}
v_resetjp_647_:
{
lean_object* v_val_650_; lean_object* v___x_651_; uint8_t v___x_652_; 
v_val_650_ = lean_ctor_get(v_next_644_, 0);
lean_inc(v_val_650_);
lean_dec_ref(v_next_644_);
lean_inc(v_upperBound_646_);
lean_inc(v_val_650_);
v___x_651_ = lean_apply_2(v_inst_642_, v_val_650_, v_upperBound_646_);
v___x_652_ = lean_unbox(v___x_651_);
if (v___x_652_ == 0)
{
lean_object* v___x_653_; 
lean_dec(v_val_650_);
lean_del_object(v___x_648_);
lean_dec(v_upperBound_646_);
lean_dec_ref(v_inst_641_);
v___x_653_ = lean_box(2);
return v___x_653_;
}
else
{
lean_object* v_succ_x3f_654_; lean_object* v___x_656_; uint8_t v_isShared_657_; uint8_t v_isSharedCheck_665_; 
v_succ_x3f_654_ = lean_ctor_get(v_inst_641_, 0);
v_isSharedCheck_665_ = !lean_is_exclusive(v_inst_641_);
if (v_isSharedCheck_665_ == 0)
{
lean_object* v_unused_666_; 
v_unused_666_ = lean_ctor_get(v_inst_641_, 1);
lean_dec(v_unused_666_);
v___x_656_ = v_inst_641_;
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
else
{
lean_inc(v_succ_x3f_654_);
lean_dec(v_inst_641_);
v___x_656_ = lean_box(0);
v_isShared_657_ = v_isSharedCheck_665_;
goto v_resetjp_655_;
}
v_resetjp_655_:
{
lean_object* v___x_658_; lean_object* v___x_660_; 
lean_inc(v_val_650_);
v___x_658_ = lean_apply_1(v_succ_x3f_654_, v_val_650_);
if (v_isShared_649_ == 0)
{
lean_ctor_set(v___x_648_, 0, v___x_658_);
v___x_660_ = v___x_648_;
goto v_reusejp_659_;
}
else
{
lean_object* v_reuseFailAlloc_664_; 
v_reuseFailAlloc_664_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_664_, 0, v___x_658_);
lean_ctor_set(v_reuseFailAlloc_664_, 1, v_upperBound_646_);
v___x_660_ = v_reuseFailAlloc_664_;
goto v_reusejp_659_;
}
v_reusejp_659_:
{
lean_object* v___x_662_; 
if (v_isShared_657_ == 0)
{
lean_ctor_set(v___x_656_, 1, v_val_650_);
lean_ctor_set(v___x_656_, 0, v___x_660_);
v___x_662_ = v___x_656_;
goto v_reusejp_661_;
}
else
{
lean_object* v_reuseFailAlloc_663_; 
v_reuseFailAlloc_663_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_663_, 0, v___x_660_);
lean_ctor_set(v_reuseFailAlloc_663_, 1, v_val_650_);
v___x_662_ = v_reuseFailAlloc_663_;
goto v_reusejp_661_;
}
v_reusejp_661_:
{
return v___x_662_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step(lean_object* v_00_u03b1_669_, lean_object* v_inst_670_, lean_object* v_inst_671_, lean_object* v_inst_672_, lean_object* v_it_673_){
_start:
{
lean_object* v_next_674_; 
v_next_674_ = lean_ctor_get(v_it_673_, 0);
lean_inc(v_next_674_);
if (lean_obj_tag(v_next_674_) == 0)
{
lean_object* v___x_675_; 
lean_dec_ref(v_it_673_);
lean_dec_ref(v_inst_672_);
lean_dec_ref(v_inst_670_);
v___x_675_ = lean_box(2);
return v___x_675_;
}
else
{
lean_object* v_upperBound_676_; lean_object* v___x_678_; uint8_t v_isShared_679_; uint8_t v_isSharedCheck_697_; 
v_upperBound_676_ = lean_ctor_get(v_it_673_, 1);
v_isSharedCheck_697_ = !lean_is_exclusive(v_it_673_);
if (v_isSharedCheck_697_ == 0)
{
lean_object* v_unused_698_; 
v_unused_698_ = lean_ctor_get(v_it_673_, 0);
lean_dec(v_unused_698_);
v___x_678_ = v_it_673_;
v_isShared_679_ = v_isSharedCheck_697_;
goto v_resetjp_677_;
}
else
{
lean_inc(v_upperBound_676_);
lean_dec(v_it_673_);
v___x_678_ = lean_box(0);
v_isShared_679_ = v_isSharedCheck_697_;
goto v_resetjp_677_;
}
v_resetjp_677_:
{
lean_object* v_val_680_; lean_object* v___x_681_; uint8_t v___x_682_; 
v_val_680_ = lean_ctor_get(v_next_674_, 0);
lean_inc(v_val_680_);
lean_dec_ref(v_next_674_);
lean_inc(v_upperBound_676_);
lean_inc(v_val_680_);
v___x_681_ = lean_apply_2(v_inst_672_, v_val_680_, v_upperBound_676_);
v___x_682_ = lean_unbox(v___x_681_);
if (v___x_682_ == 0)
{
lean_object* v___x_683_; 
lean_dec(v_val_680_);
lean_del_object(v___x_678_);
lean_dec(v_upperBound_676_);
lean_dec_ref(v_inst_670_);
v___x_683_ = lean_box(2);
return v___x_683_;
}
else
{
lean_object* v_succ_x3f_684_; lean_object* v___x_686_; uint8_t v_isShared_687_; uint8_t v_isSharedCheck_695_; 
v_succ_x3f_684_ = lean_ctor_get(v_inst_670_, 0);
v_isSharedCheck_695_ = !lean_is_exclusive(v_inst_670_);
if (v_isSharedCheck_695_ == 0)
{
lean_object* v_unused_696_; 
v_unused_696_ = lean_ctor_get(v_inst_670_, 1);
lean_dec(v_unused_696_);
v___x_686_ = v_inst_670_;
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
else
{
lean_inc(v_succ_x3f_684_);
lean_dec(v_inst_670_);
v___x_686_ = lean_box(0);
v_isShared_687_ = v_isSharedCheck_695_;
goto v_resetjp_685_;
}
v_resetjp_685_:
{
lean_object* v___x_688_; lean_object* v___x_690_; 
lean_inc(v_val_680_);
v___x_688_ = lean_apply_1(v_succ_x3f_684_, v_val_680_);
if (v_isShared_679_ == 0)
{
lean_ctor_set(v___x_678_, 0, v___x_688_);
v___x_690_ = v___x_678_;
goto v_reusejp_689_;
}
else
{
lean_object* v_reuseFailAlloc_694_; 
v_reuseFailAlloc_694_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_694_, 0, v___x_688_);
lean_ctor_set(v_reuseFailAlloc_694_, 1, v_upperBound_676_);
v___x_690_ = v_reuseFailAlloc_694_;
goto v_reusejp_689_;
}
v_reusejp_689_:
{
lean_object* v___x_692_; 
if (v_isShared_687_ == 0)
{
lean_ctor_set(v___x_686_, 1, v_val_680_);
lean_ctor_set(v___x_686_, 0, v___x_690_);
v___x_692_ = v___x_686_;
goto v_reusejp_691_;
}
else
{
lean_object* v_reuseFailAlloc_693_; 
v_reuseFailAlloc_693_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_693_, 0, v___x_690_);
lean_ctor_set(v_reuseFailAlloc_693_, 1, v_val_680_);
v___x_692_ = v_reuseFailAlloc_693_;
goto v_reusejp_691_;
}
v_reusejp_691_:
{
return v___x_692_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step___redArg(lean_object* v_inst_699_, lean_object* v_inst_700_, lean_object* v_it_701_){
_start:
{
lean_object* v_next_702_; 
v_next_702_ = lean_ctor_get(v_it_701_, 0);
lean_inc(v_next_702_);
if (lean_obj_tag(v_next_702_) == 0)
{
lean_object* v___x_703_; 
lean_dec_ref(v_it_701_);
lean_dec_ref(v_inst_700_);
lean_dec_ref(v_inst_699_);
v___x_703_ = lean_box(2);
return v___x_703_;
}
else
{
lean_object* v_upperBound_704_; lean_object* v___x_706_; uint8_t v_isShared_707_; uint8_t v_isSharedCheck_725_; 
v_upperBound_704_ = lean_ctor_get(v_it_701_, 1);
v_isSharedCheck_725_ = !lean_is_exclusive(v_it_701_);
if (v_isSharedCheck_725_ == 0)
{
lean_object* v_unused_726_; 
v_unused_726_ = lean_ctor_get(v_it_701_, 0);
lean_dec(v_unused_726_);
v___x_706_ = v_it_701_;
v_isShared_707_ = v_isSharedCheck_725_;
goto v_resetjp_705_;
}
else
{
lean_inc(v_upperBound_704_);
lean_dec(v_it_701_);
v___x_706_ = lean_box(0);
v_isShared_707_ = v_isSharedCheck_725_;
goto v_resetjp_705_;
}
v_resetjp_705_:
{
lean_object* v_val_708_; lean_object* v___x_709_; uint8_t v___x_710_; 
v_val_708_ = lean_ctor_get(v_next_702_, 0);
lean_inc(v_val_708_);
lean_dec_ref(v_next_702_);
lean_inc(v_upperBound_704_);
lean_inc(v_val_708_);
v___x_709_ = lean_apply_2(v_inst_700_, v_val_708_, v_upperBound_704_);
v___x_710_ = lean_unbox(v___x_709_);
if (v___x_710_ == 0)
{
lean_object* v___x_711_; 
lean_dec(v_val_708_);
lean_del_object(v___x_706_);
lean_dec(v_upperBound_704_);
lean_dec_ref(v_inst_699_);
v___x_711_ = lean_box(2);
return v___x_711_;
}
else
{
lean_object* v_succ_x3f_712_; lean_object* v___x_714_; uint8_t v_isShared_715_; uint8_t v_isSharedCheck_723_; 
v_succ_x3f_712_ = lean_ctor_get(v_inst_699_, 0);
v_isSharedCheck_723_ = !lean_is_exclusive(v_inst_699_);
if (v_isSharedCheck_723_ == 0)
{
lean_object* v_unused_724_; 
v_unused_724_ = lean_ctor_get(v_inst_699_, 1);
lean_dec(v_unused_724_);
v___x_714_ = v_inst_699_;
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
else
{
lean_inc(v_succ_x3f_712_);
lean_dec(v_inst_699_);
v___x_714_ = lean_box(0);
v_isShared_715_ = v_isSharedCheck_723_;
goto v_resetjp_713_;
}
v_resetjp_713_:
{
lean_object* v___x_716_; lean_object* v___x_718_; 
lean_inc(v_val_708_);
v___x_716_ = lean_apply_1(v_succ_x3f_712_, v_val_708_);
if (v_isShared_707_ == 0)
{
lean_ctor_set(v___x_706_, 0, v___x_716_);
v___x_718_ = v___x_706_;
goto v_reusejp_717_;
}
else
{
lean_object* v_reuseFailAlloc_722_; 
v_reuseFailAlloc_722_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_722_, 0, v___x_716_);
lean_ctor_set(v_reuseFailAlloc_722_, 1, v_upperBound_704_);
v___x_718_ = v_reuseFailAlloc_722_;
goto v_reusejp_717_;
}
v_reusejp_717_:
{
lean_object* v___x_720_; 
if (v_isShared_715_ == 0)
{
lean_ctor_set(v___x_714_, 1, v_val_708_);
lean_ctor_set(v___x_714_, 0, v___x_718_);
v___x_720_ = v___x_714_;
goto v_reusejp_719_;
}
else
{
lean_object* v_reuseFailAlloc_721_; 
v_reuseFailAlloc_721_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_721_, 0, v___x_718_);
lean_ctor_set(v_reuseFailAlloc_721_, 1, v_val_708_);
v___x_720_ = v_reuseFailAlloc_721_;
goto v_reusejp_719_;
}
v_reusejp_719_:
{
return v___x_720_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step(lean_object* v_00_u03b1_727_, lean_object* v_inst_728_, lean_object* v_inst_729_, lean_object* v_inst_730_, lean_object* v_it_731_){
_start:
{
lean_object* v_next_732_; 
v_next_732_ = lean_ctor_get(v_it_731_, 0);
lean_inc(v_next_732_);
if (lean_obj_tag(v_next_732_) == 0)
{
lean_object* v___x_733_; 
lean_dec_ref(v_it_731_);
lean_dec_ref(v_inst_730_);
lean_dec_ref(v_inst_728_);
v___x_733_ = lean_box(2);
return v___x_733_;
}
else
{
lean_object* v_upperBound_734_; lean_object* v___x_736_; uint8_t v_isShared_737_; uint8_t v_isSharedCheck_755_; 
v_upperBound_734_ = lean_ctor_get(v_it_731_, 1);
v_isSharedCheck_755_ = !lean_is_exclusive(v_it_731_);
if (v_isSharedCheck_755_ == 0)
{
lean_object* v_unused_756_; 
v_unused_756_ = lean_ctor_get(v_it_731_, 0);
lean_dec(v_unused_756_);
v___x_736_ = v_it_731_;
v_isShared_737_ = v_isSharedCheck_755_;
goto v_resetjp_735_;
}
else
{
lean_inc(v_upperBound_734_);
lean_dec(v_it_731_);
v___x_736_ = lean_box(0);
v_isShared_737_ = v_isSharedCheck_755_;
goto v_resetjp_735_;
}
v_resetjp_735_:
{
lean_object* v_val_738_; lean_object* v___x_739_; uint8_t v___x_740_; 
v_val_738_ = lean_ctor_get(v_next_732_, 0);
lean_inc(v_val_738_);
lean_dec_ref(v_next_732_);
lean_inc(v_upperBound_734_);
lean_inc(v_val_738_);
v___x_739_ = lean_apply_2(v_inst_730_, v_val_738_, v_upperBound_734_);
v___x_740_ = lean_unbox(v___x_739_);
if (v___x_740_ == 0)
{
lean_object* v___x_741_; 
lean_dec(v_val_738_);
lean_del_object(v___x_736_);
lean_dec(v_upperBound_734_);
lean_dec_ref(v_inst_728_);
v___x_741_ = lean_box(2);
return v___x_741_;
}
else
{
lean_object* v_succ_x3f_742_; lean_object* v___x_744_; uint8_t v_isShared_745_; uint8_t v_isSharedCheck_753_; 
v_succ_x3f_742_ = lean_ctor_get(v_inst_728_, 0);
v_isSharedCheck_753_ = !lean_is_exclusive(v_inst_728_);
if (v_isSharedCheck_753_ == 0)
{
lean_object* v_unused_754_; 
v_unused_754_ = lean_ctor_get(v_inst_728_, 1);
lean_dec(v_unused_754_);
v___x_744_ = v_inst_728_;
v_isShared_745_ = v_isSharedCheck_753_;
goto v_resetjp_743_;
}
else
{
lean_inc(v_succ_x3f_742_);
lean_dec(v_inst_728_);
v___x_744_ = lean_box(0);
v_isShared_745_ = v_isSharedCheck_753_;
goto v_resetjp_743_;
}
v_resetjp_743_:
{
lean_object* v___x_746_; lean_object* v___x_748_; 
lean_inc(v_val_738_);
v___x_746_ = lean_apply_1(v_succ_x3f_742_, v_val_738_);
if (v_isShared_737_ == 0)
{
lean_ctor_set(v___x_736_, 0, v___x_746_);
v___x_748_ = v___x_736_;
goto v_reusejp_747_;
}
else
{
lean_object* v_reuseFailAlloc_752_; 
v_reuseFailAlloc_752_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_752_, 0, v___x_746_);
lean_ctor_set(v_reuseFailAlloc_752_, 1, v_upperBound_734_);
v___x_748_ = v_reuseFailAlloc_752_;
goto v_reusejp_747_;
}
v_reusejp_747_:
{
lean_object* v___x_750_; 
if (v_isShared_745_ == 0)
{
lean_ctor_set(v___x_744_, 1, v_val_738_);
lean_ctor_set(v___x_744_, 0, v___x_748_);
v___x_750_ = v___x_744_;
goto v_reusejp_749_;
}
else
{
lean_object* v_reuseFailAlloc_751_; 
v_reuseFailAlloc_751_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_751_, 0, v___x_748_);
lean_ctor_set(v_reuseFailAlloc_751_, 1, v_val_738_);
v___x_750_ = v_reuseFailAlloc_751_;
goto v_reusejp_749_;
}
v_reusejp_749_:
{
return v___x_750_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0(lean_object* v_inst_757_, lean_object* v_inst_758_, lean_object* v_it_759_){
_start:
{
lean_object* v_next_760_; 
v_next_760_ = lean_ctor_get(v_it_759_, 0);
lean_inc(v_next_760_);
if (lean_obj_tag(v_next_760_) == 0)
{
lean_object* v___x_761_; 
lean_dec_ref(v_it_759_);
lean_dec_ref(v_inst_758_);
lean_dec_ref(v_inst_757_);
v___x_761_ = lean_box(2);
return v___x_761_;
}
else
{
lean_object* v_upperBound_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_783_; 
v_upperBound_762_ = lean_ctor_get(v_it_759_, 1);
v_isSharedCheck_783_ = !lean_is_exclusive(v_it_759_);
if (v_isSharedCheck_783_ == 0)
{
lean_object* v_unused_784_; 
v_unused_784_ = lean_ctor_get(v_it_759_, 0);
lean_dec(v_unused_784_);
v___x_764_ = v_it_759_;
v_isShared_765_ = v_isSharedCheck_783_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_upperBound_762_);
lean_dec(v_it_759_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_783_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v_val_766_; lean_object* v___x_767_; uint8_t v___x_768_; 
v_val_766_ = lean_ctor_get(v_next_760_, 0);
lean_inc(v_val_766_);
lean_dec_ref(v_next_760_);
lean_inc(v_upperBound_762_);
lean_inc(v_val_766_);
v___x_767_ = lean_apply_2(v_inst_757_, v_val_766_, v_upperBound_762_);
v___x_768_ = lean_unbox(v___x_767_);
if (v___x_768_ == 0)
{
lean_object* v___x_769_; 
lean_dec(v_val_766_);
lean_del_object(v___x_764_);
lean_dec(v_upperBound_762_);
lean_dec_ref(v_inst_758_);
v___x_769_ = lean_box(2);
return v___x_769_;
}
else
{
lean_object* v_succ_x3f_770_; lean_object* v___x_772_; uint8_t v_isShared_773_; uint8_t v_isSharedCheck_781_; 
v_succ_x3f_770_ = lean_ctor_get(v_inst_758_, 0);
v_isSharedCheck_781_ = !lean_is_exclusive(v_inst_758_);
if (v_isSharedCheck_781_ == 0)
{
lean_object* v_unused_782_; 
v_unused_782_ = lean_ctor_get(v_inst_758_, 1);
lean_dec(v_unused_782_);
v___x_772_ = v_inst_758_;
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
else
{
lean_inc(v_succ_x3f_770_);
lean_dec(v_inst_758_);
v___x_772_ = lean_box(0);
v_isShared_773_ = v_isSharedCheck_781_;
goto v_resetjp_771_;
}
v_resetjp_771_:
{
lean_object* v___x_774_; lean_object* v___x_776_; 
lean_inc(v_val_766_);
v___x_774_ = lean_apply_1(v_succ_x3f_770_, v_val_766_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 0, v___x_774_);
v___x_776_ = v___x_764_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_780_; 
v_reuseFailAlloc_780_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_780_, 0, v___x_774_);
lean_ctor_set(v_reuseFailAlloc_780_, 1, v_upperBound_762_);
v___x_776_ = v_reuseFailAlloc_780_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
lean_object* v___x_778_; 
if (v_isShared_773_ == 0)
{
lean_ctor_set(v___x_772_, 1, v_val_766_);
lean_ctor_set(v___x_772_, 0, v___x_776_);
v___x_778_ = v___x_772_;
goto v_reusejp_777_;
}
else
{
lean_object* v_reuseFailAlloc_779_; 
v_reuseFailAlloc_779_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_779_, 0, v___x_776_);
lean_ctor_set(v_reuseFailAlloc_779_, 1, v_val_766_);
v___x_778_ = v_reuseFailAlloc_779_;
goto v_reusejp_777_;
}
v_reusejp_777_:
{
return v___x_778_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg(lean_object* v_inst_785_, lean_object* v_inst_786_){
_start:
{
lean_object* v___f_787_; 
v___f_787_ = lean_alloc_closure((void*)(l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_787_, 0, v_inst_786_);
lean_closure_set(v___f_787_, 1, v_inst_785_);
return v___f_787_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT(lean_object* v_00_u03b1_788_, lean_object* v_inst_789_, lean_object* v_inst_790_, lean_object* v_inst_791_){
_start:
{
lean_object* v___f_792_; 
v___f_792_ = lean_alloc_closure((void*)(l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_792_, 0, v_inst_791_);
lean_closure_set(v___f_792_, 1, v_inst_789_);
return v___f_792_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_793_, lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_inst_796_, lean_object* v_inst_797_, lean_object* v_inst_798_){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = lean_box(0);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_800_, lean_object* v_inst_801_, lean_object* v_inst_802_, lean_object* v_inst_803_, lean_object* v_inst_804_, lean_object* v_inst_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(v_00_u03b1_800_, v_inst_801_, v_inst_802_, v_inst_803_, v_inst_804_, v_inst_805_);
lean_dec_ref(v_inst_803_);
lean_dec_ref(v_inst_801_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_807_, lean_object* v_inst_808_, lean_object* v_inst_809_, lean_object* v_inst_810_, lean_object* v_inst_811_){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_box(0);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_813_, lean_object* v_inst_814_, lean_object* v_inst_815_, lean_object* v_inst_816_, lean_object* v_inst_817_){
_start:
{
lean_object* v_res_818_; 
v_res_818_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(v_00_u03b1_813_, v_inst_814_, v_inst_815_, v_inst_816_, v_inst_817_);
lean_dec_ref(v_inst_816_);
lean_dec_ref(v_inst_814_);
return v_res_818_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_819_, lean_object* v_inst_820_, lean_object* v_it_821_, lean_object* v_n_822_){
_start:
{
lean_object* v_next_823_; 
v_next_823_ = lean_ctor_get(v_it_821_, 0);
lean_inc(v_next_823_);
if (lean_obj_tag(v_next_823_) == 0)
{
lean_object* v___x_824_; 
lean_dec(v_n_822_);
lean_dec_ref(v_it_821_);
lean_dec_ref(v_inst_820_);
lean_dec_ref(v_inst_819_);
v___x_824_ = lean_box(2);
return v___x_824_;
}
else
{
lean_object* v_upperBound_825_; lean_object* v___x_827_; uint8_t v_isShared_828_; uint8_t v_isSharedCheck_849_; 
v_upperBound_825_ = lean_ctor_get(v_it_821_, 1);
v_isSharedCheck_849_ = !lean_is_exclusive(v_it_821_);
if (v_isSharedCheck_849_ == 0)
{
lean_object* v_unused_850_; 
v_unused_850_ = lean_ctor_get(v_it_821_, 0);
lean_dec(v_unused_850_);
v___x_827_ = v_it_821_;
v_isShared_828_ = v_isSharedCheck_849_;
goto v_resetjp_826_;
}
else
{
lean_inc(v_upperBound_825_);
lean_dec(v_it_821_);
v___x_827_ = lean_box(0);
v_isShared_828_ = v_isSharedCheck_849_;
goto v_resetjp_826_;
}
v_resetjp_826_:
{
lean_object* v_succ_x3f_829_; lean_object* v_succMany_x3f_830_; lean_object* v___x_832_; uint8_t v_isShared_833_; uint8_t v_isSharedCheck_848_; 
v_succ_x3f_829_ = lean_ctor_get(v_inst_819_, 0);
v_succMany_x3f_830_ = lean_ctor_get(v_inst_819_, 1);
v_isSharedCheck_848_ = !lean_is_exclusive(v_inst_819_);
if (v_isSharedCheck_848_ == 0)
{
v___x_832_ = v_inst_819_;
v_isShared_833_ = v_isSharedCheck_848_;
goto v_resetjp_831_;
}
else
{
lean_inc(v_succMany_x3f_830_);
lean_inc(v_succ_x3f_829_);
lean_dec(v_inst_819_);
v___x_832_ = lean_box(0);
v_isShared_833_ = v_isSharedCheck_848_;
goto v_resetjp_831_;
}
v_resetjp_831_:
{
lean_object* v_val_834_; lean_object* v___x_835_; 
v_val_834_ = lean_ctor_get(v_next_823_, 0);
lean_inc(v_val_834_);
lean_dec_ref(v_next_823_);
v___x_835_ = lean_apply_2(v_succMany_x3f_830_, v_n_822_, v_val_834_);
if (lean_obj_tag(v___x_835_) == 0)
{
lean_object* v___x_836_; 
lean_del_object(v___x_832_);
lean_dec_ref(v_succ_x3f_829_);
lean_del_object(v___x_827_);
lean_dec(v_upperBound_825_);
lean_dec_ref(v_inst_820_);
v___x_836_ = lean_box(2);
return v___x_836_;
}
else
{
lean_object* v_val_837_; lean_object* v___x_838_; uint8_t v___x_839_; 
v_val_837_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_val_837_);
lean_dec_ref(v___x_835_);
lean_inc(v_upperBound_825_);
lean_inc(v_val_837_);
v___x_838_ = lean_apply_2(v_inst_820_, v_val_837_, v_upperBound_825_);
v___x_839_ = lean_unbox(v___x_838_);
if (v___x_839_ == 0)
{
lean_object* v___x_840_; 
lean_dec(v_val_837_);
lean_del_object(v___x_832_);
lean_dec_ref(v_succ_x3f_829_);
lean_del_object(v___x_827_);
lean_dec(v_upperBound_825_);
v___x_840_ = lean_box(2);
return v___x_840_;
}
else
{
lean_object* v___x_841_; lean_object* v___x_843_; 
lean_inc(v_val_837_);
v___x_841_ = lean_apply_1(v_succ_x3f_829_, v_val_837_);
if (v_isShared_828_ == 0)
{
lean_ctor_set(v___x_827_, 0, v___x_841_);
v___x_843_ = v___x_827_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_847_; 
v_reuseFailAlloc_847_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_847_, 0, v___x_841_);
lean_ctor_set(v_reuseFailAlloc_847_, 1, v_upperBound_825_);
v___x_843_ = v_reuseFailAlloc_847_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
lean_object* v___x_845_; 
if (v_isShared_833_ == 0)
{
lean_ctor_set(v___x_832_, 1, v_val_837_);
lean_ctor_set(v___x_832_, 0, v___x_843_);
v___x_845_ = v___x_832_;
goto v_reusejp_844_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v___x_843_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_val_837_);
v___x_845_ = v_reuseFailAlloc_846_;
goto v_reusejp_844_;
}
v_reusejp_844_:
{
return v___x_845_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg(lean_object* v_inst_851_, lean_object* v_inst_852_){
_start:
{
lean_object* v___f_853_; 
v___f_853_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_853_, 0, v_inst_851_);
lean_closure_set(v___f_853_, 1, v_inst_852_);
return v___f_853_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess(lean_object* v_00_u03b1_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_, lean_object* v_inst_859_){
_start:
{
lean_object* v___f_860_; 
v___f_860_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_860_, 0, v_inst_855_);
lean_closure_set(v___f_860_, 1, v_inst_857_);
return v___f_860_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_861_, lean_object* v_inst_862_, lean_object* v_inst_863_, lean_object* v_upperBound_864_, lean_object* v_acc_865_, lean_object* v_next_866_, lean_object* v_f_867_){
_start:
{
lean_object* v___f_868_; lean_object* v___x_869_; 
v___f_868_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 9, 5);
lean_closure_set(v___f_868_, 0, v_inst_862_);
lean_closure_set(v___f_868_, 1, v_upperBound_864_);
lean_closure_set(v___f_868_, 2, v_inst_863_);
lean_closure_set(v___f_868_, 3, v_inst_861_);
lean_closure_set(v___f_868_, 4, v_f_867_);
v___x_869_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_868_, v_next_866_, v_acc_865_, lean_box(0));
return v___x_869_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_870_, lean_object* v_inst_871_, lean_object* v_inst_872_, lean_object* v_inst_873_, lean_object* v_inst_874_, lean_object* v_n_875_, lean_object* v_inst_876_, lean_object* v_00_u03b3_877_, lean_object* v_Pl_878_, lean_object* v_LargeEnough_879_, lean_object* v_hl_880_, lean_object* v_upperBound_881_, lean_object* v_acc_882_, lean_object* v_next_883_, lean_object* v_h_884_, lean_object* v_f_885_){
_start:
{
lean_object* v___f_886_; lean_object* v___x_887_; 
v___f_886_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 9, 5);
lean_closure_set(v___f_886_, 0, v_inst_873_);
lean_closure_set(v___f_886_, 1, v_upperBound_881_);
lean_closure_set(v___f_886_, 2, v_inst_876_);
lean_closure_set(v___f_886_, 3, v_inst_871_);
lean_closure_set(v___f_886_, 4, v_f_885_);
v___x_887_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_886_, v_next_883_, v_acc_882_, lean_box(0));
return v___x_887_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_888_, lean_object* v_inst_889_, lean_object* v_inst_890_, lean_object* v_toBind_891_, lean_object* v_x_892_, lean_object* v_00_u03b3_893_, lean_object* v_Pl_894_, lean_object* v_it_895_, lean_object* v_init_896_, lean_object* v_f_897_){
_start:
{
lean_object* v_next_898_; 
v_next_898_ = lean_ctor_get(v_it_895_, 0);
lean_inc(v_next_898_);
if (lean_obj_tag(v_next_898_) == 0)
{
lean_object* v___x_899_; 
lean_dec(v_f_897_);
lean_dec_ref(v_it_895_);
lean_dec(v_toBind_891_);
lean_dec_ref(v_inst_890_);
lean_dec_ref(v_inst_889_);
v___x_899_ = lean_apply_2(v_toPure_888_, lean_box(0), v_init_896_);
return v___x_899_;
}
else
{
lean_object* v_upperBound_900_; lean_object* v_val_901_; lean_object* v___f_902_; lean_object* v___x_903_; 
v_upperBound_900_ = lean_ctor_get(v_it_895_, 1);
lean_inc(v_upperBound_900_);
lean_dec_ref(v_it_895_);
v_val_901_ = lean_ctor_get(v_next_898_, 0);
lean_inc(v_val_901_);
lean_dec_ref(v_next_898_);
v___f_902_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_902_, 0, v_inst_889_);
lean_closure_set(v___f_902_, 1, v_upperBound_900_);
lean_closure_set(v___f_902_, 2, v_toPure_888_);
lean_closure_set(v___f_902_, 3, v_inst_890_);
lean_closure_set(v___f_902_, 4, v_f_897_);
lean_closure_set(v___f_902_, 5, v_toBind_891_);
v___x_903_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_902_, v_val_901_, v_init_896_, lean_box(0));
return v___x_903_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_toBind_907_, lean_object* v_x_908_, lean_object* v_00_u03b3_909_, lean_object* v_Pl_910_, lean_object* v_it_911_, lean_object* v_init_912_, lean_object* v_f_913_){
_start:
{
lean_object* v_res_914_; 
v_res_914_ = l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_904_, v_inst_905_, v_inst_906_, v_toBind_907_, v_x_908_, v_00_u03b3_909_, v_Pl_910_, v_it_911_, v_init_912_, v_f_913_);
lean_dec(v_x_908_);
return v_res_914_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg(lean_object* v_inst_915_, lean_object* v_inst_916_, lean_object* v_inst_917_){
_start:
{
lean_object* v_toApplicative_918_; lean_object* v_toBind_919_; lean_object* v_toPure_920_; lean_object* v___f_921_; 
v_toApplicative_918_ = lean_ctor_get(v_inst_917_, 0);
lean_inc_ref(v_toApplicative_918_);
v_toBind_919_ = lean_ctor_get(v_inst_917_, 1);
lean_inc(v_toBind_919_);
lean_dec_ref(v_inst_917_);
v_toPure_920_ = lean_ctor_get(v_toApplicative_918_, 1);
lean_inc(v_toPure_920_);
lean_dec_ref(v_toApplicative_918_);
v___f_921_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_921_, 0, v_toPure_920_);
lean_closure_set(v___f_921_, 1, v_inst_916_);
lean_closure_set(v___f_921_, 2, v_inst_915_);
lean_closure_set(v___f_921_, 3, v_toBind_919_);
return v___f_921_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop(lean_object* v_00_u03b1_922_, lean_object* v_inst_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_n_928_, lean_object* v_inst_929_){
_start:
{
lean_object* v_toApplicative_930_; lean_object* v_toBind_931_; lean_object* v_toPure_932_; lean_object* v___f_933_; 
v_toApplicative_930_ = lean_ctor_get(v_inst_929_, 0);
lean_inc_ref(v_toApplicative_930_);
v_toBind_931_ = lean_ctor_get(v_inst_929_, 1);
lean_inc(v_toBind_931_);
lean_dec_ref(v_inst_929_);
v_toPure_932_ = lean_ctor_get(v_toApplicative_930_, 1);
lean_inc(v_toPure_932_);
lean_dec_ref(v_toApplicative_930_);
v___f_933_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_933_, 0, v_toPure_932_);
lean_closure_set(v___f_933_, 1, v_inst_925_);
lean_closure_set(v___f_933_, 2, v_inst_923_);
lean_closure_set(v___f_933_, 3, v_toBind_931_);
return v___f_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_934_, lean_object* v_f_935_, lean_object* v_h__1_936_, lean_object* v_h__2_937_){
_start:
{
lean_object* v_next_938_; 
v_next_938_ = lean_ctor_get(v_it_934_, 0);
if (lean_obj_tag(v_next_938_) == 0)
{
lean_object* v_upperBound_939_; lean_object* v___x_940_; 
lean_dec(v_h__1_936_);
v_upperBound_939_ = lean_ctor_get(v_it_934_, 1);
lean_inc(v_upperBound_939_);
lean_dec_ref(v_it_934_);
v___x_940_ = lean_apply_2(v_h__2_937_, v_upperBound_939_, v_f_935_);
return v___x_940_;
}
else
{
lean_object* v_upperBound_941_; lean_object* v_val_942_; lean_object* v___x_943_; 
lean_inc_ref(v_next_938_);
lean_dec(v_h__2_937_);
v_upperBound_941_ = lean_ctor_get(v_it_934_, 1);
lean_inc(v_upperBound_941_);
lean_dec_ref(v_it_934_);
v_val_942_ = lean_ctor_get(v_next_938_, 0);
lean_inc(v_val_942_);
lean_dec_ref(v_next_938_);
v___x_943_ = lean_apply_3(v_h__1_936_, v_val_942_, v_upperBound_941_, v_f_935_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_944_, lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_n_948_, lean_object* v_00_u03b3_949_, lean_object* v_Pl_950_, lean_object* v_motive_951_, lean_object* v_it_952_, lean_object* v_f_953_, lean_object* v_h__1_954_, lean_object* v_h__2_955_){
_start:
{
lean_object* v___x_956_; 
v___x_956_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___redArg(v_it_952_, v_f_953_, v_h__1_954_, v_h__2_955_);
return v___x_956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_957_, lean_object* v_inst_958_, lean_object* v_inst_959_, lean_object* v_inst_960_, lean_object* v_n_961_, lean_object* v_00_u03b3_962_, lean_object* v_Pl_963_, lean_object* v_motive_964_, lean_object* v_it_965_, lean_object* v_f_966_, lean_object* v_h__1_967_, lean_object* v_h__2_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_957_, v_inst_958_, v_inst_959_, v_inst_960_, v_n_961_, v_00_u03b3_962_, v_Pl_963_, v_motive_964_, v_it_965_, v_f_966_, v_h__1_967_, v_h__2_968_);
lean_dec_ref(v_inst_960_);
lean_dec_ref(v_inst_958_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step___redArg(lean_object* v_inst_970_, lean_object* v_it_971_){
_start:
{
if (lean_obj_tag(v_it_971_) == 0)
{
lean_object* v___x_972_; 
lean_dec_ref(v_inst_970_);
v___x_972_ = lean_box(2);
return v___x_972_;
}
else
{
lean_object* v_val_973_; lean_object* v_succ_x3f_974_; lean_object* v___x_976_; uint8_t v_isShared_977_; uint8_t v_isSharedCheck_982_; 
v_val_973_ = lean_ctor_get(v_it_971_, 0);
lean_inc(v_val_973_);
lean_dec_ref(v_it_971_);
v_succ_x3f_974_ = lean_ctor_get(v_inst_970_, 0);
v_isSharedCheck_982_ = !lean_is_exclusive(v_inst_970_);
if (v_isSharedCheck_982_ == 0)
{
lean_object* v_unused_983_; 
v_unused_983_ = lean_ctor_get(v_inst_970_, 1);
lean_dec(v_unused_983_);
v___x_976_ = v_inst_970_;
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
else
{
lean_inc(v_succ_x3f_974_);
lean_dec(v_inst_970_);
v___x_976_ = lean_box(0);
v_isShared_977_ = v_isSharedCheck_982_;
goto v_resetjp_975_;
}
v_resetjp_975_:
{
lean_object* v___x_978_; lean_object* v___x_980_; 
lean_inc(v_val_973_);
v___x_978_ = lean_apply_1(v_succ_x3f_974_, v_val_973_);
if (v_isShared_977_ == 0)
{
lean_ctor_set(v___x_976_, 1, v_val_973_);
lean_ctor_set(v___x_976_, 0, v___x_978_);
v___x_980_ = v___x_976_;
goto v_reusejp_979_;
}
else
{
lean_object* v_reuseFailAlloc_981_; 
v_reuseFailAlloc_981_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_981_, 0, v___x_978_);
lean_ctor_set(v_reuseFailAlloc_981_, 1, v_val_973_);
v___x_980_ = v_reuseFailAlloc_981_;
goto v_reusejp_979_;
}
v_reusejp_979_:
{
return v___x_980_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step(lean_object* v_00_u03b1_984_, lean_object* v_inst_985_, lean_object* v_it_986_){
_start:
{
if (lean_obj_tag(v_it_986_) == 0)
{
lean_object* v___x_987_; 
lean_dec_ref(v_inst_985_);
v___x_987_ = lean_box(2);
return v___x_987_;
}
else
{
lean_object* v_val_988_; lean_object* v_succ_x3f_989_; lean_object* v___x_991_; uint8_t v_isShared_992_; uint8_t v_isSharedCheck_997_; 
v_val_988_ = lean_ctor_get(v_it_986_, 0);
lean_inc(v_val_988_);
lean_dec_ref(v_it_986_);
v_succ_x3f_989_ = lean_ctor_get(v_inst_985_, 0);
v_isSharedCheck_997_ = !lean_is_exclusive(v_inst_985_);
if (v_isSharedCheck_997_ == 0)
{
lean_object* v_unused_998_; 
v_unused_998_ = lean_ctor_get(v_inst_985_, 1);
lean_dec(v_unused_998_);
v___x_991_ = v_inst_985_;
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
else
{
lean_inc(v_succ_x3f_989_);
lean_dec(v_inst_985_);
v___x_991_ = lean_box(0);
v_isShared_992_ = v_isSharedCheck_997_;
goto v_resetjp_990_;
}
v_resetjp_990_:
{
lean_object* v___x_993_; lean_object* v___x_995_; 
lean_inc(v_val_988_);
v___x_993_ = lean_apply_1(v_succ_x3f_989_, v_val_988_);
if (v_isShared_992_ == 0)
{
lean_ctor_set(v___x_991_, 1, v_val_988_);
lean_ctor_set(v___x_991_, 0, v___x_993_);
v___x_995_ = v___x_991_;
goto v_reusejp_994_;
}
else
{
lean_object* v_reuseFailAlloc_996_; 
v_reuseFailAlloc_996_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_996_, 0, v___x_993_);
lean_ctor_set(v_reuseFailAlloc_996_, 1, v_val_988_);
v___x_995_ = v_reuseFailAlloc_996_;
goto v_reusejp_994_;
}
v_reusejp_994_:
{
return v___x_995_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step___redArg(lean_object* v_inst_999_, lean_object* v_it_1000_){
_start:
{
if (lean_obj_tag(v_it_1000_) == 0)
{
lean_object* v___x_1001_; 
lean_dec_ref(v_inst_999_);
v___x_1001_ = lean_box(2);
return v___x_1001_;
}
else
{
lean_object* v_val_1002_; lean_object* v_succ_x3f_1003_; lean_object* v___x_1005_; uint8_t v_isShared_1006_; uint8_t v_isSharedCheck_1011_; 
v_val_1002_ = lean_ctor_get(v_it_1000_, 0);
lean_inc(v_val_1002_);
lean_dec_ref(v_it_1000_);
v_succ_x3f_1003_ = lean_ctor_get(v_inst_999_, 0);
v_isSharedCheck_1011_ = !lean_is_exclusive(v_inst_999_);
if (v_isSharedCheck_1011_ == 0)
{
lean_object* v_unused_1012_; 
v_unused_1012_ = lean_ctor_get(v_inst_999_, 1);
lean_dec(v_unused_1012_);
v___x_1005_ = v_inst_999_;
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
else
{
lean_inc(v_succ_x3f_1003_);
lean_dec(v_inst_999_);
v___x_1005_ = lean_box(0);
v_isShared_1006_ = v_isSharedCheck_1011_;
goto v_resetjp_1004_;
}
v_resetjp_1004_:
{
lean_object* v___x_1007_; lean_object* v___x_1009_; 
lean_inc(v_val_1002_);
v___x_1007_ = lean_apply_1(v_succ_x3f_1003_, v_val_1002_);
if (v_isShared_1006_ == 0)
{
lean_ctor_set(v___x_1005_, 1, v_val_1002_);
lean_ctor_set(v___x_1005_, 0, v___x_1007_);
v___x_1009_ = v___x_1005_;
goto v_reusejp_1008_;
}
else
{
lean_object* v_reuseFailAlloc_1010_; 
v_reuseFailAlloc_1010_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1010_, 0, v___x_1007_);
lean_ctor_set(v_reuseFailAlloc_1010_, 1, v_val_1002_);
v___x_1009_ = v_reuseFailAlloc_1010_;
goto v_reusejp_1008_;
}
v_reusejp_1008_:
{
return v___x_1009_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step(lean_object* v_00_u03b1_1013_, lean_object* v_inst_1014_, lean_object* v_it_1015_){
_start:
{
if (lean_obj_tag(v_it_1015_) == 0)
{
lean_object* v___x_1016_; 
lean_dec_ref(v_inst_1014_);
v___x_1016_ = lean_box(2);
return v___x_1016_;
}
else
{
lean_object* v_val_1017_; lean_object* v_succ_x3f_1018_; lean_object* v___x_1020_; uint8_t v_isShared_1021_; uint8_t v_isSharedCheck_1026_; 
v_val_1017_ = lean_ctor_get(v_it_1015_, 0);
lean_inc(v_val_1017_);
lean_dec_ref(v_it_1015_);
v_succ_x3f_1018_ = lean_ctor_get(v_inst_1014_, 0);
v_isSharedCheck_1026_ = !lean_is_exclusive(v_inst_1014_);
if (v_isSharedCheck_1026_ == 0)
{
lean_object* v_unused_1027_; 
v_unused_1027_ = lean_ctor_get(v_inst_1014_, 1);
lean_dec(v_unused_1027_);
v___x_1020_ = v_inst_1014_;
v_isShared_1021_ = v_isSharedCheck_1026_;
goto v_resetjp_1019_;
}
else
{
lean_inc(v_succ_x3f_1018_);
lean_dec(v_inst_1014_);
v___x_1020_ = lean_box(0);
v_isShared_1021_ = v_isSharedCheck_1026_;
goto v_resetjp_1019_;
}
v_resetjp_1019_:
{
lean_object* v___x_1022_; lean_object* v___x_1024_; 
lean_inc(v_val_1017_);
v___x_1022_ = lean_apply_1(v_succ_x3f_1018_, v_val_1017_);
if (v_isShared_1021_ == 0)
{
lean_ctor_set(v___x_1020_, 1, v_val_1017_);
lean_ctor_set(v___x_1020_, 0, v___x_1022_);
v___x_1024_ = v___x_1020_;
goto v_reusejp_1023_;
}
else
{
lean_object* v_reuseFailAlloc_1025_; 
v_reuseFailAlloc_1025_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1025_, 0, v___x_1022_);
lean_ctor_set(v_reuseFailAlloc_1025_, 1, v_val_1017_);
v___x_1024_ = v_reuseFailAlloc_1025_;
goto v_reusejp_1023_;
}
v_reusejp_1023_:
{
return v___x_1024_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0(lean_object* v_inst_1028_, lean_object* v_it_1029_){
_start:
{
if (lean_obj_tag(v_it_1029_) == 0)
{
lean_object* v___x_1030_; 
lean_dec_ref(v_inst_1028_);
v___x_1030_ = lean_box(2);
return v___x_1030_;
}
else
{
lean_object* v_val_1031_; lean_object* v_succ_x3f_1032_; lean_object* v___x_1034_; uint8_t v_isShared_1035_; uint8_t v_isSharedCheck_1040_; 
v_val_1031_ = lean_ctor_get(v_it_1029_, 0);
lean_inc(v_val_1031_);
lean_dec_ref(v_it_1029_);
v_succ_x3f_1032_ = lean_ctor_get(v_inst_1028_, 0);
v_isSharedCheck_1040_ = !lean_is_exclusive(v_inst_1028_);
if (v_isSharedCheck_1040_ == 0)
{
lean_object* v_unused_1041_; 
v_unused_1041_ = lean_ctor_get(v_inst_1028_, 1);
lean_dec(v_unused_1041_);
v___x_1034_ = v_inst_1028_;
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
else
{
lean_inc(v_succ_x3f_1032_);
lean_dec(v_inst_1028_);
v___x_1034_ = lean_box(0);
v_isShared_1035_ = v_isSharedCheck_1040_;
goto v_resetjp_1033_;
}
v_resetjp_1033_:
{
lean_object* v___x_1036_; lean_object* v___x_1038_; 
lean_inc(v_val_1031_);
v___x_1036_ = lean_apply_1(v_succ_x3f_1032_, v_val_1031_);
if (v_isShared_1035_ == 0)
{
lean_ctor_set(v___x_1034_, 1, v_val_1031_);
lean_ctor_set(v___x_1034_, 0, v___x_1036_);
v___x_1038_ = v___x_1034_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1039_; 
v_reuseFailAlloc_1039_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1039_, 0, v___x_1036_);
lean_ctor_set(v_reuseFailAlloc_1039_, 1, v_val_1031_);
v___x_1038_ = v_reuseFailAlloc_1039_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
return v___x_1038_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg(lean_object* v_inst_1042_){
_start:
{
lean_object* v___f_1043_; 
v___f_1043_ = lean_alloc_closure((void*)(l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1043_, 0, v_inst_1042_);
return v___f_1043_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable(lean_object* v_00_u03b1_1044_, lean_object* v_inst_1045_){
_start:
{
lean_object* v___f_1046_; 
v___f_1046_ = lean_alloc_closure((void*)(l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1046_, 0, v_inst_1045_);
return v___f_1046_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_1047_, lean_object* v_inst_1048_, lean_object* v_inst_1049_, lean_object* v_inst_1050_){
_start:
{
lean_object* v___x_1051_; 
v___x_1051_ = lean_box(0);
return v___x_1051_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_1052_, lean_object* v_inst_1053_, lean_object* v_inst_1054_, lean_object* v_inst_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(v_00_u03b1_1052_, v_inst_1053_, v_inst_1054_, v_inst_1055_);
lean_dec_ref(v_inst_1053_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_1057_, lean_object* v_inst_1058_, lean_object* v_inst_1059_){
_start:
{
lean_object* v___x_1060_; 
v___x_1060_ = lean_box(0);
return v___x_1060_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_1061_, lean_object* v_inst_1062_, lean_object* v_inst_1063_){
_start:
{
lean_object* v_res_1064_; 
v_res_1064_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(v_00_u03b1_1061_, v_inst_1062_, v_inst_1063_);
lean_dec_ref(v_inst_1062_);
return v_res_1064_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_1065_, lean_object* v_it_1066_, lean_object* v_n_1067_){
_start:
{
if (lean_obj_tag(v_it_1066_) == 0)
{
lean_object* v___x_1068_; 
lean_dec(v_n_1067_);
lean_dec_ref(v_inst_1065_);
v___x_1068_ = lean_box(2);
return v___x_1068_;
}
else
{
lean_object* v_succ_x3f_1069_; lean_object* v_succMany_x3f_1070_; lean_object* v___x_1072_; uint8_t v_isShared_1073_; uint8_t v_isSharedCheck_1082_; 
v_succ_x3f_1069_ = lean_ctor_get(v_inst_1065_, 0);
v_succMany_x3f_1070_ = lean_ctor_get(v_inst_1065_, 1);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_inst_1065_);
if (v_isSharedCheck_1082_ == 0)
{
v___x_1072_ = v_inst_1065_;
v_isShared_1073_ = v_isSharedCheck_1082_;
goto v_resetjp_1071_;
}
else
{
lean_inc(v_succMany_x3f_1070_);
lean_inc(v_succ_x3f_1069_);
lean_dec(v_inst_1065_);
v___x_1072_ = lean_box(0);
v_isShared_1073_ = v_isSharedCheck_1082_;
goto v_resetjp_1071_;
}
v_resetjp_1071_:
{
lean_object* v_val_1074_; lean_object* v___x_1075_; 
v_val_1074_ = lean_ctor_get(v_it_1066_, 0);
lean_inc(v_val_1074_);
lean_dec_ref(v_it_1066_);
v___x_1075_ = lean_apply_2(v_succMany_x3f_1070_, v_n_1067_, v_val_1074_);
if (lean_obj_tag(v___x_1075_) == 0)
{
lean_object* v___x_1076_; 
lean_del_object(v___x_1072_);
lean_dec_ref(v_succ_x3f_1069_);
v___x_1076_ = lean_box(2);
return v___x_1076_;
}
else
{
lean_object* v_val_1077_; lean_object* v___x_1078_; lean_object* v___x_1080_; 
v_val_1077_ = lean_ctor_get(v___x_1075_, 0);
lean_inc(v_val_1077_);
lean_dec_ref(v___x_1075_);
lean_inc(v_val_1077_);
v___x_1078_ = lean_apply_1(v_succ_x3f_1069_, v_val_1077_);
if (v_isShared_1073_ == 0)
{
lean_ctor_set(v___x_1072_, 1, v_val_1077_);
lean_ctor_set(v___x_1072_, 0, v___x_1078_);
v___x_1080_ = v___x_1072_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_val_1077_);
v___x_1080_ = v_reuseFailAlloc_1081_;
goto v_reusejp_1079_;
}
v_reusejp_1079_:
{
return v___x_1080_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg(lean_object* v_inst_1083_){
_start:
{
lean_object* v___f_1084_; 
v___f_1084_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1084_, 0, v_inst_1083_);
return v___f_1084_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess(lean_object* v_00_u03b1_1085_, lean_object* v_inst_1086_, lean_object* v_inst_1087_){
_start:
{
lean_object* v___f_1088_; 
v___f_1088_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1088_, 0, v_inst_1086_);
return v___f_1088_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object* v_toPure_1089_, lean_object* v_inst_1090_, lean_object* v_f_1091_, lean_object* v_toBind_1092_, lean_object* v_next_1093_, lean_object* v_acc_1094_, lean_object* v_h_1095_, lean_object* v_G_1096_){
_start:
{
lean_object* v___f_1097_; lean_object* v___x_1098_; lean_object* v___x_1099_; 
lean_inc(v_next_1093_);
v___f_1097_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1097_, 0, v_toPure_1089_);
lean_closure_set(v___f_1097_, 1, v_inst_1090_);
lean_closure_set(v___f_1097_, 2, v_next_1093_);
lean_closure_set(v___f_1097_, 3, v_G_1096_);
v___x_1098_ = lean_apply_3(v_f_1091_, v_next_1093_, lean_box(0), v_acc_1094_);
v___x_1099_ = lean_apply_4(v_toBind_1092_, lean_box(0), lean_box(0), v___x_1098_, v___f_1097_);
return v___x_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_1100_, lean_object* v_inst_1101_, lean_object* v_acc_1102_, lean_object* v_next_1103_, lean_object* v_f_1104_){
_start:
{
lean_object* v_toApplicative_1105_; lean_object* v_toBind_1106_; lean_object* v_toPure_1107_; lean_object* v___f_1108_; lean_object* v___x_1109_; 
v_toApplicative_1105_ = lean_ctor_get(v_inst_1101_, 0);
lean_inc_ref(v_toApplicative_1105_);
v_toBind_1106_ = lean_ctor_get(v_inst_1101_, 1);
lean_inc(v_toBind_1106_);
lean_dec_ref(v_inst_1101_);
v_toPure_1107_ = lean_ctor_get(v_toApplicative_1105_, 1);
lean_inc(v_toPure_1107_);
lean_dec_ref(v_toApplicative_1105_);
v___f_1108_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1108_, 0, v_toPure_1107_);
lean_closure_set(v___f_1108_, 1, v_inst_1100_);
lean_closure_set(v___f_1108_, 2, v_f_1104_);
lean_closure_set(v___f_1108_, 3, v_toBind_1106_);
v___x_1109_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1108_, v_next_1103_, v_acc_1102_, lean_box(0));
return v___x_1109_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_1110_, lean_object* v_inst_1111_, lean_object* v_inst_1112_, lean_object* v_n_1113_, lean_object* v_inst_1114_, lean_object* v_00_u03b3_1115_, lean_object* v_Pl_1116_, lean_object* v_LargeEnough_1117_, lean_object* v_hl_1118_, lean_object* v_acc_1119_, lean_object* v_next_1120_, lean_object* v_h_1121_, lean_object* v_f_1122_){
_start:
{
lean_object* v_toApplicative_1123_; lean_object* v_toBind_1124_; lean_object* v_toPure_1125_; lean_object* v___f_1126_; lean_object* v___x_1127_; 
v_toApplicative_1123_ = lean_ctor_get(v_inst_1114_, 0);
lean_inc_ref(v_toApplicative_1123_);
v_toBind_1124_ = lean_ctor_get(v_inst_1114_, 1);
lean_inc(v_toBind_1124_);
lean_dec_ref(v_inst_1114_);
v_toPure_1125_ = lean_ctor_get(v_toApplicative_1123_, 1);
lean_inc(v_toPure_1125_);
lean_dec_ref(v_toApplicative_1123_);
v___f_1126_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1126_, 0, v_toPure_1125_);
lean_closure_set(v___f_1126_, 1, v_inst_1111_);
lean_closure_set(v___f_1126_, 2, v_f_1122_);
lean_closure_set(v___f_1126_, 3, v_toBind_1124_);
v___x_1127_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1126_, v_next_1120_, v_acc_1119_, lean_box(0));
return v___x_1127_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_1128_, lean_object* v_inst_1129_, lean_object* v_toBind_1130_, lean_object* v_x_1131_, lean_object* v_00_u03b3_1132_, lean_object* v_Pl_1133_, lean_object* v_it_1134_, lean_object* v_init_1135_, lean_object* v_f_1136_){
_start:
{
if (lean_obj_tag(v_it_1134_) == 0)
{
lean_object* v___x_1137_; 
lean_dec(v_f_1136_);
lean_dec(v_toBind_1130_);
lean_dec_ref(v_inst_1129_);
v___x_1137_ = lean_apply_2(v_toPure_1128_, lean_box(0), v_init_1135_);
return v___x_1137_;
}
else
{
lean_object* v_val_1138_; lean_object* v___f_1139_; lean_object* v___x_1140_; 
v_val_1138_ = lean_ctor_get(v_it_1134_, 0);
lean_inc(v_val_1138_);
lean_dec_ref(v_it_1134_);
v___f_1139_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1139_, 0, v_toPure_1128_);
lean_closure_set(v___f_1139_, 1, v_inst_1129_);
lean_closure_set(v___f_1139_, 2, v_f_1136_);
lean_closure_set(v___f_1139_, 3, v_toBind_1130_);
v___x_1140_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1139_, v_val_1138_, v_init_1135_, lean_box(0));
return v___x_1140_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_1141_, lean_object* v_inst_1142_, lean_object* v_toBind_1143_, lean_object* v_x_1144_, lean_object* v_00_u03b3_1145_, lean_object* v_Pl_1146_, lean_object* v_it_1147_, lean_object* v_init_1148_, lean_object* v_f_1149_){
_start:
{
lean_object* v_res_1150_; 
v_res_1150_ = l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_1141_, v_inst_1142_, v_toBind_1143_, v_x_1144_, v_00_u03b3_1145_, v_Pl_1146_, v_it_1147_, v_init_1148_, v_f_1149_);
lean_dec(v_x_1144_);
return v_res_1150_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg(lean_object* v_inst_1151_, lean_object* v_inst_1152_){
_start:
{
lean_object* v_toApplicative_1153_; lean_object* v_toBind_1154_; lean_object* v_toPure_1155_; lean_object* v___f_1156_; 
v_toApplicative_1153_ = lean_ctor_get(v_inst_1152_, 0);
lean_inc_ref(v_toApplicative_1153_);
v_toBind_1154_ = lean_ctor_get(v_inst_1152_, 1);
lean_inc(v_toBind_1154_);
lean_dec_ref(v_inst_1152_);
v_toPure_1155_ = lean_ctor_get(v_toApplicative_1153_, 1);
lean_inc(v_toPure_1155_);
lean_dec_ref(v_toApplicative_1153_);
v___f_1156_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1156_, 0, v_toPure_1155_);
lean_closure_set(v___f_1156_, 1, v_inst_1151_);
lean_closure_set(v___f_1156_, 2, v_toBind_1154_);
return v___f_1156_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop(lean_object* v_00_u03b1_1157_, lean_object* v_inst_1158_, lean_object* v_inst_1159_, lean_object* v_n_1160_, lean_object* v_inst_1161_){
_start:
{
lean_object* v_toApplicative_1162_; lean_object* v_toBind_1163_; lean_object* v_toPure_1164_; lean_object* v___f_1165_; 
v_toApplicative_1162_ = lean_ctor_get(v_inst_1161_, 0);
lean_inc_ref(v_toApplicative_1162_);
v_toBind_1163_ = lean_ctor_get(v_inst_1161_, 1);
lean_inc(v_toBind_1163_);
lean_dec_ref(v_inst_1161_);
v_toPure_1164_ = lean_ctor_get(v_toApplicative_1162_, 1);
lean_inc(v_toPure_1164_);
lean_dec_ref(v_toApplicative_1162_);
v___f_1165_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1165_, 0, v_toPure_1164_);
lean_closure_set(v___f_1165_, 1, v_inst_1158_);
lean_closure_set(v___f_1165_, 2, v_toBind_1163_);
return v___f_1165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_1166_, lean_object* v_f_1167_, lean_object* v_h__1_1168_, lean_object* v_h__2_1169_){
_start:
{
if (lean_obj_tag(v_it_1166_) == 0)
{
lean_object* v___x_1170_; 
lean_dec(v_h__1_1168_);
v___x_1170_ = lean_apply_1(v_h__2_1169_, v_f_1167_);
return v___x_1170_;
}
else
{
lean_object* v_val_1171_; lean_object* v___x_1172_; 
lean_dec(v_h__2_1169_);
v_val_1171_ = lean_ctor_get(v_it_1166_, 0);
lean_inc(v_val_1171_);
lean_dec_ref(v_it_1166_);
v___x_1172_ = lean_apply_2(v_h__1_1168_, v_val_1171_, v_f_1167_);
return v___x_1172_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_1173_, lean_object* v_inst_1174_, lean_object* v_n_1175_, lean_object* v_00_u03b3_1176_, lean_object* v_Pl_1177_, lean_object* v_motive_1178_, lean_object* v_it_1179_, lean_object* v_f_1180_, lean_object* v_h__1_1181_, lean_object* v_h__2_1182_){
_start:
{
lean_object* v___x_1183_; 
v___x_1183_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___redArg(v_it_1179_, v_f_1180_, v_h__1_1181_, v_h__2_1182_);
return v___x_1183_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_1184_, lean_object* v_inst_1185_, lean_object* v_n_1186_, lean_object* v_00_u03b3_1187_, lean_object* v_Pl_1188_, lean_object* v_motive_1189_, lean_object* v_it_1190_, lean_object* v_f_1191_, lean_object* v_h__1_1192_, lean_object* v_h__2_1193_){
_start:
{
lean_object* v_res_1194_; 
v_res_1194_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_1184_, v_inst_1185_, v_n_1186_, v_00_u03b3_1187_, v_Pl_1188_, v_motive_1189_, v_it_1190_, v_f_1191_, v_h__1_1192_, v_h__2_1193_);
lean_dec_ref(v_inst_1185_);
return v_res_1194_;
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
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_Range_Polymorphic_RangeIterator(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
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
