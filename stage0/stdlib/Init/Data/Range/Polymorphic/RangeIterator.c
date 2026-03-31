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
lean_inc_n(v_val_10_, 2);
lean_dec_ref(v_next_4_);
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
lean_dec_ref(v_next_34_);
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
lean_dec_ref(v_next_62_);
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
lean_dec_ref(v_next_92_);
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
lean_dec_ref(v_x_117_);
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
lean_dec_ref(v_x_126_);
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
lean_dec_ref(v_next_136_);
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
lean_dec_ref(v_x_169_);
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
lean_dec_ref(v_x_169_);
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
lean_dec_ref(v_x_183_);
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
lean_dec_ref(v_x_183_);
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
lean_dec_ref(v_x_220_);
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
lean_dec_ref(v_x_229_);
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
lean_dec_ref(v_next_240_);
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
lean_dec_ref(v___x_252_);
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
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0(lean_object* v_toApplicative_278_, lean_object* v_inst_279_, lean_object* v_next_280_, lean_object* v_G_281_, lean_object* v_____do__lift_282_){
_start:
{
if (lean_obj_tag(v_____do__lift_282_) == 0)
{
lean_object* v_a_283_; lean_object* v_toPure_284_; lean_object* v___x_285_; 
lean_dec(v_G_281_);
lean_dec(v_next_280_);
lean_dec_ref(v_inst_279_);
v_a_283_ = lean_ctor_get(v_____do__lift_282_, 0);
lean_inc(v_a_283_);
lean_dec_ref(v_____do__lift_282_);
v_toPure_284_ = lean_ctor_get(v_toApplicative_278_, 1);
lean_inc(v_toPure_284_);
lean_dec_ref(v_toApplicative_278_);
v___x_285_ = lean_apply_2(v_toPure_284_, lean_box(0), v_a_283_);
return v___x_285_;
}
else
{
lean_object* v_a_286_; lean_object* v_succ_x3f_287_; lean_object* v___x_288_; 
v_a_286_ = lean_ctor_get(v_____do__lift_282_, 0);
lean_inc(v_a_286_);
lean_dec_ref(v_____do__lift_282_);
v_succ_x3f_287_ = lean_ctor_get(v_inst_279_, 0);
lean_inc_ref(v_succ_x3f_287_);
lean_dec_ref(v_inst_279_);
v___x_288_ = lean_apply_1(v_succ_x3f_287_, v_next_280_);
if (lean_obj_tag(v___x_288_) == 0)
{
lean_object* v_toPure_289_; lean_object* v___x_290_; 
lean_dec(v_G_281_);
v_toPure_289_ = lean_ctor_get(v_toApplicative_278_, 1);
lean_inc(v_toPure_289_);
lean_dec_ref(v_toApplicative_278_);
v___x_290_ = lean_apply_2(v_toPure_289_, lean_box(0), v_a_286_);
return v___x_290_;
}
else
{
lean_object* v_val_291_; lean_object* v___x_292_; 
lean_dec_ref(v_toApplicative_278_);
v_val_291_ = lean_ctor_get(v___x_288_, 0);
lean_inc(v_val_291_);
lean_dec_ref(v___x_288_);
v___x_292_ = lean_apply_4(v_G_281_, v_val_291_, v_a_286_, lean_box(0), lean_box(0));
return v___x_292_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object* v_inst_293_, lean_object* v_upperBound_294_, lean_object* v_inst_295_, lean_object* v_inst_296_, lean_object* v_f_297_, lean_object* v_next_298_, lean_object* v_acc_299_, lean_object* v_h_300_, lean_object* v_G_301_){
_start:
{
lean_object* v___x_302_; uint8_t v___x_303_; 
lean_inc(v_next_298_);
v___x_302_ = lean_apply_2(v_inst_293_, v_next_298_, v_upperBound_294_);
v___x_303_ = lean_unbox(v___x_302_);
if (v___x_303_ == 0)
{
lean_object* v_toApplicative_304_; lean_object* v_toPure_305_; lean_object* v___x_306_; 
lean_dec(v_G_301_);
lean_dec(v_next_298_);
lean_dec(v_f_297_);
lean_dec_ref(v_inst_296_);
v_toApplicative_304_ = lean_ctor_get(v_inst_295_, 0);
lean_inc_ref(v_toApplicative_304_);
lean_dec_ref(v_inst_295_);
v_toPure_305_ = lean_ctor_get(v_toApplicative_304_, 1);
lean_inc(v_toPure_305_);
lean_dec_ref(v_toApplicative_304_);
v___x_306_ = lean_apply_2(v_toPure_305_, lean_box(0), v_acc_299_);
return v___x_306_;
}
else
{
lean_object* v_toApplicative_307_; lean_object* v_toBind_308_; lean_object* v___f_309_; lean_object* v___x_310_; lean_object* v___x_311_; 
v_toApplicative_307_ = lean_ctor_get(v_inst_295_, 0);
lean_inc_ref(v_toApplicative_307_);
v_toBind_308_ = lean_ctor_get(v_inst_295_, 1);
lean_inc(v_toBind_308_);
lean_dec_ref(v_inst_295_);
lean_inc(v_next_298_);
v___f_309_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_309_, 0, v_toApplicative_307_);
lean_closure_set(v___f_309_, 1, v_inst_296_);
lean_closure_set(v___f_309_, 2, v_next_298_);
lean_closure_set(v___f_309_, 3, v_G_301_);
v___x_310_ = lean_apply_4(v_f_297_, v_next_298_, lean_box(0), lean_box(0), v_acc_299_);
v___x_311_ = lean_apply_4(v_toBind_308_, lean_box(0), lean_box(0), v___x_310_, v___f_309_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_312_, lean_object* v_inst_313_, lean_object* v_inst_314_, lean_object* v_upperBound_315_, lean_object* v_acc_316_, lean_object* v_next_317_, lean_object* v_f_318_){
_start:
{
lean_object* v___f_319_; lean_object* v___x_320_; 
v___f_319_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 9, 5);
lean_closure_set(v___f_319_, 0, v_inst_313_);
lean_closure_set(v___f_319_, 1, v_upperBound_315_);
lean_closure_set(v___f_319_, 2, v_inst_314_);
lean_closure_set(v___f_319_, 3, v_inst_312_);
lean_closure_set(v___f_319_, 4, v_f_318_);
v___x_320_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_319_, v_next_317_, v_acc_316_, lean_box(0));
return v___x_320_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_321_, lean_object* v_inst_322_, lean_object* v_inst_323_, lean_object* v_inst_324_, lean_object* v_inst_325_, lean_object* v_inst_326_, lean_object* v_n_327_, lean_object* v_inst_328_, lean_object* v_00_u03b3_329_, lean_object* v_Pl_330_, lean_object* v_LargeEnough_331_, lean_object* v_hl_332_, lean_object* v_upperBound_333_, lean_object* v_acc_334_, lean_object* v_next_335_, lean_object* v_h_336_, lean_object* v_f_337_){
_start:
{
lean_object* v___f_338_; lean_object* v___x_339_; 
v___f_338_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 9, 5);
lean_closure_set(v___f_338_, 0, v_inst_324_);
lean_closure_set(v___f_338_, 1, v_upperBound_333_);
lean_closure_set(v___f_338_, 2, v_inst_328_);
lean_closure_set(v___f_338_, 3, v_inst_322_);
lean_closure_set(v___f_338_, 4, v_f_337_);
v___x_339_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_338_, v_next_335_, v_acc_334_, lean_box(0));
return v___x_339_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_340_ = _args[0];
lean_object* v_inst_341_ = _args[1];
lean_object* v_inst_342_ = _args[2];
lean_object* v_inst_343_ = _args[3];
lean_object* v_inst_344_ = _args[4];
lean_object* v_inst_345_ = _args[5];
lean_object* v_n_346_ = _args[6];
lean_object* v_inst_347_ = _args[7];
lean_object* v_00_u03b3_348_ = _args[8];
lean_object* v_Pl_349_ = _args[9];
lean_object* v_LargeEnough_350_ = _args[10];
lean_object* v_hl_351_ = _args[11];
lean_object* v_upperBound_352_ = _args[12];
lean_object* v_acc_353_ = _args[13];
lean_object* v_next_354_ = _args[14];
lean_object* v_h_355_ = _args[15];
lean_object* v_f_356_ = _args[16];
_start:
{
lean_object* v_res_357_; 
v_res_357_ = l_Std_Rxc_Iterator_instIteratorLoop_loop(v_00_u03b1_340_, v_inst_341_, v_inst_342_, v_inst_343_, v_inst_344_, v_inst_345_, v_n_346_, v_inst_347_, v_00_u03b3_348_, v_Pl_349_, v_LargeEnough_350_, v_hl_351_, v_upperBound_352_, v_acc_353_, v_next_354_, v_h_355_, v_f_356_);
return v_res_357_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_358_, lean_object* v_inst_359_, lean_object* v_next_360_, lean_object* v_G_361_, lean_object* v_____do__lift_362_){
_start:
{
if (lean_obj_tag(v_____do__lift_362_) == 0)
{
lean_object* v_a_363_; lean_object* v___x_364_; 
lean_dec(v_G_361_);
lean_dec(v_next_360_);
lean_dec_ref(v_inst_359_);
v_a_363_ = lean_ctor_get(v_____do__lift_362_, 0);
lean_inc(v_a_363_);
lean_dec_ref(v_____do__lift_362_);
v___x_364_ = lean_apply_2(v_toPure_358_, lean_box(0), v_a_363_);
return v___x_364_;
}
else
{
lean_object* v_a_365_; lean_object* v_succ_x3f_366_; lean_object* v___x_367_; 
v_a_365_ = lean_ctor_get(v_____do__lift_362_, 0);
lean_inc(v_a_365_);
lean_dec_ref(v_____do__lift_362_);
v_succ_x3f_366_ = lean_ctor_get(v_inst_359_, 0);
lean_inc_ref(v_succ_x3f_366_);
lean_dec_ref(v_inst_359_);
v___x_367_ = lean_apply_1(v_succ_x3f_366_, v_next_360_);
if (lean_obj_tag(v___x_367_) == 0)
{
lean_object* v___x_368_; 
lean_dec(v_G_361_);
v___x_368_ = lean_apply_2(v_toPure_358_, lean_box(0), v_a_365_);
return v___x_368_;
}
else
{
lean_object* v_val_369_; lean_object* v___x_370_; 
lean_dec(v_toPure_358_);
v_val_369_ = lean_ctor_get(v___x_367_, 0);
lean_inc(v_val_369_);
lean_dec_ref(v___x_367_);
v___x_370_ = lean_apply_4(v_G_361_, v_val_369_, v_a_365_, lean_box(0), lean_box(0));
return v___x_370_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1(lean_object* v_inst_371_, lean_object* v_upperBound_372_, lean_object* v_toPure_373_, lean_object* v_inst_374_, lean_object* v_f_375_, lean_object* v_toBind_376_, lean_object* v_next_377_, lean_object* v_acc_378_, lean_object* v_h_379_, lean_object* v_G_380_){
_start:
{
lean_object* v___x_381_; uint8_t v___x_382_; 
lean_inc(v_next_377_);
v___x_381_ = lean_apply_2(v_inst_371_, v_next_377_, v_upperBound_372_);
v___x_382_ = lean_unbox(v___x_381_);
if (v___x_382_ == 0)
{
lean_object* v___x_383_; 
lean_dec(v_G_380_);
lean_dec(v_next_377_);
lean_dec(v_toBind_376_);
lean_dec(v_f_375_);
lean_dec_ref(v_inst_374_);
v___x_383_ = lean_apply_2(v_toPure_373_, lean_box(0), v_acc_378_);
return v___x_383_;
}
else
{
lean_object* v___f_384_; lean_object* v___x_385_; lean_object* v___x_386_; 
lean_inc(v_next_377_);
v___f_384_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_384_, 0, v_toPure_373_);
lean_closure_set(v___f_384_, 1, v_inst_374_);
lean_closure_set(v___f_384_, 2, v_next_377_);
lean_closure_set(v___f_384_, 3, v_G_380_);
v___x_385_ = lean_apply_3(v_f_375_, v_next_377_, lean_box(0), v_acc_378_);
v___x_386_ = lean_apply_4(v_toBind_376_, lean_box(0), lean_box(0), v___x_385_, v___f_384_);
return v___x_386_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_387_, lean_object* v_inst_388_, lean_object* v_inst_389_, lean_object* v_toBind_390_, lean_object* v_x_391_, lean_object* v_00_u03b3_392_, lean_object* v_Pl_393_, lean_object* v_it_394_, lean_object* v_init_395_, lean_object* v_f_396_){
_start:
{
lean_object* v_next_397_; 
v_next_397_ = lean_ctor_get(v_it_394_, 0);
lean_inc(v_next_397_);
if (lean_obj_tag(v_next_397_) == 0)
{
lean_object* v___x_398_; 
lean_dec(v_f_396_);
lean_dec_ref(v_it_394_);
lean_dec(v_toBind_390_);
lean_dec_ref(v_inst_389_);
lean_dec_ref(v_inst_388_);
v___x_398_ = lean_apply_2(v_toPure_387_, lean_box(0), v_init_395_);
return v___x_398_;
}
else
{
lean_object* v_upperBound_399_; lean_object* v_val_400_; lean_object* v___f_401_; lean_object* v___x_402_; 
v_upperBound_399_ = lean_ctor_get(v_it_394_, 1);
lean_inc(v_upperBound_399_);
lean_dec_ref(v_it_394_);
v_val_400_ = lean_ctor_get(v_next_397_, 0);
lean_inc(v_val_400_);
lean_dec_ref(v_next_397_);
v___f_401_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_401_, 0, v_inst_388_);
lean_closure_set(v___f_401_, 1, v_upperBound_399_);
lean_closure_set(v___f_401_, 2, v_toPure_387_);
lean_closure_set(v___f_401_, 3, v_inst_389_);
lean_closure_set(v___f_401_, 4, v_f_396_);
lean_closure_set(v___f_401_, 5, v_toBind_390_);
v___x_402_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_401_, v_val_400_, v_init_395_, lean_box(0));
return v___x_402_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_403_, lean_object* v_inst_404_, lean_object* v_inst_405_, lean_object* v_toBind_406_, lean_object* v_x_407_, lean_object* v_00_u03b3_408_, lean_object* v_Pl_409_, lean_object* v_it_410_, lean_object* v_init_411_, lean_object* v_f_412_){
_start:
{
lean_object* v_res_413_; 
v_res_413_ = l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_403_, v_inst_404_, v_inst_405_, v_toBind_406_, v_x_407_, v_00_u03b3_408_, v_Pl_409_, v_it_410_, v_init_411_, v_f_412_);
lean_dec(v_x_407_);
return v_res_413_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg(lean_object* v_inst_414_, lean_object* v_inst_415_, lean_object* v_inst_416_){
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
lean_closure_set(v___f_420_, 1, v_inst_415_);
lean_closure_set(v___f_420_, 2, v_inst_414_);
lean_closure_set(v___f_420_, 3, v_toBind_418_);
return v___f_420_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop(lean_object* v_00_u03b1_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_inst_426_, lean_object* v_n_427_, lean_object* v_inst_428_){
_start:
{
lean_object* v_toApplicative_429_; lean_object* v_toBind_430_; lean_object* v_toPure_431_; lean_object* v___f_432_; 
v_toApplicative_429_ = lean_ctor_get(v_inst_428_, 0);
lean_inc_ref(v_toApplicative_429_);
v_toBind_430_ = lean_ctor_get(v_inst_428_, 1);
lean_inc(v_toBind_430_);
lean_dec_ref(v_inst_428_);
v_toPure_431_ = lean_ctor_get(v_toApplicative_429_, 1);
lean_inc(v_toPure_431_);
lean_dec_ref(v_toApplicative_429_);
v___f_432_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_432_, 0, v_toPure_431_);
lean_closure_set(v___f_432_, 1, v_inst_424_);
lean_closure_set(v___f_432_, 2, v_inst_422_);
lean_closure_set(v___f_432_, 3, v_toBind_430_);
return v___f_432_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___redArg(lean_object* v_____do__lift_433_, lean_object* v_h__1_434_, lean_object* v_h__2_435_){
_start:
{
if (lean_obj_tag(v_____do__lift_433_) == 0)
{
lean_object* v_a_436_; lean_object* v___x_437_; 
lean_dec(v_h__1_434_);
v_a_436_ = lean_ctor_get(v_____do__lift_433_, 0);
lean_inc(v_a_436_);
lean_dec_ref(v_____do__lift_433_);
v___x_437_ = lean_apply_2(v_h__2_435_, v_a_436_, lean_box(0));
return v___x_437_;
}
else
{
lean_object* v_a_438_; lean_object* v___x_439_; 
lean_dec(v_h__2_435_);
v_a_438_ = lean_ctor_get(v_____do__lift_433_, 0);
lean_inc(v_a_438_);
lean_dec_ref(v_____do__lift_433_);
v___x_439_ = lean_apply_2(v_h__1_434_, v_a_438_, lean_box(0));
return v___x_439_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(lean_object* v_00_u03b1_440_, lean_object* v_00_u03b3_441_, lean_object* v_Pl_442_, lean_object* v_acc_443_, lean_object* v_next_444_, lean_object* v_motive_445_, lean_object* v_____do__lift_446_, lean_object* v_h__1_447_, lean_object* v_h__2_448_){
_start:
{
if (lean_obj_tag(v_____do__lift_446_) == 0)
{
lean_object* v_a_449_; lean_object* v___x_450_; 
lean_dec(v_h__1_447_);
v_a_449_ = lean_ctor_get(v_____do__lift_446_, 0);
lean_inc(v_a_449_);
lean_dec_ref(v_____do__lift_446_);
v___x_450_ = lean_apply_2(v_h__2_448_, v_a_449_, lean_box(0));
return v___x_450_;
}
else
{
lean_object* v_a_451_; lean_object* v___x_452_; 
lean_dec(v_h__2_448_);
v_a_451_ = lean_ctor_get(v_____do__lift_446_, 0);
lean_inc(v_a_451_);
lean_dec_ref(v_____do__lift_446_);
v___x_452_ = lean_apply_2(v_h__1_447_, v_a_451_, lean_box(0));
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___boxed(lean_object* v_00_u03b1_453_, lean_object* v_00_u03b3_454_, lean_object* v_Pl_455_, lean_object* v_acc_456_, lean_object* v_next_457_, lean_object* v_motive_458_, lean_object* v_____do__lift_459_, lean_object* v_h__1_460_, lean_object* v_h__2_461_){
_start:
{
lean_object* v_res_462_; 
v_res_462_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(v_00_u03b1_453_, v_00_u03b3_454_, v_Pl_455_, v_acc_456_, v_next_457_, v_motive_458_, v_____do__lift_459_, v_h__1_460_, v_h__2_461_);
lean_dec(v_next_457_);
lean_dec(v_acc_456_);
return v_res_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter___redArg(lean_object* v_x_463_, lean_object* v_h__1_464_, lean_object* v_h__2_465_){
_start:
{
if (lean_obj_tag(v_x_463_) == 0)
{
lean_object* v___x_466_; 
lean_dec(v_h__1_464_);
v___x_466_ = lean_apply_1(v_h__2_465_, lean_box(0));
return v___x_466_;
}
else
{
lean_object* v_val_467_; lean_object* v___x_468_; 
lean_dec(v_h__2_465_);
v_val_467_ = lean_ctor_get(v_x_463_, 0);
lean_inc(v_val_467_);
lean_dec_ref(v_x_463_);
v___x_468_ = lean_apply_2(v_h__1_464_, v_val_467_, lean_box(0));
return v___x_468_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter(lean_object* v_00_u03b1_469_, lean_object* v_motive_470_, lean_object* v_x_471_, lean_object* v_h__1_472_, lean_object* v_h__2_473_){
_start:
{
if (lean_obj_tag(v_x_471_) == 0)
{
lean_object* v___x_474_; 
lean_dec(v_h__1_472_);
v___x_474_ = lean_apply_1(v_h__2_473_, lean_box(0));
return v___x_474_;
}
else
{
lean_object* v_val_475_; lean_object* v___x_476_; 
lean_dec(v_h__2_473_);
v_val_475_ = lean_ctor_get(v_x_471_, 0);
lean_inc(v_val_475_);
lean_dec_ref(v_x_471_);
v___x_476_ = lean_apply_2(v_h__1_472_, v_val_475_, lean_box(0));
return v___x_476_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___redArg(lean_object* v_____do__lift_477_, lean_object* v_h__1_478_, lean_object* v_h__2_479_){
_start:
{
if (lean_obj_tag(v_____do__lift_477_) == 0)
{
lean_object* v_a_480_; lean_object* v___x_481_; 
lean_dec(v_h__1_478_);
v_a_480_ = lean_ctor_get(v_____do__lift_477_, 0);
lean_inc(v_a_480_);
lean_dec_ref(v_____do__lift_477_);
v___x_481_ = lean_apply_2(v_h__2_479_, v_a_480_, lean_box(0));
return v___x_481_;
}
else
{
lean_object* v_a_482_; lean_object* v___x_483_; 
lean_dec(v_h__2_479_);
v_a_482_ = lean_ctor_get(v_____do__lift_477_, 0);
lean_inc(v_a_482_);
lean_dec_ref(v_____do__lift_477_);
v___x_483_ = lean_apply_2(v_h__1_478_, v_a_482_, lean_box(0));
return v___x_483_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(lean_object* v_00_u03b1_484_, lean_object* v_00_u03b3_485_, lean_object* v_Pl_486_, lean_object* v_next_487_, lean_object* v_acc_488_, lean_object* v_motive_489_, lean_object* v_____do__lift_490_, lean_object* v_h__1_491_, lean_object* v_h__2_492_){
_start:
{
if (lean_obj_tag(v_____do__lift_490_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_494_; 
lean_dec(v_h__1_491_);
v_a_493_ = lean_ctor_get(v_____do__lift_490_, 0);
lean_inc(v_a_493_);
lean_dec_ref(v_____do__lift_490_);
v___x_494_ = lean_apply_2(v_h__2_492_, v_a_493_, lean_box(0));
return v___x_494_;
}
else
{
lean_object* v_a_495_; lean_object* v___x_496_; 
lean_dec(v_h__2_492_);
v_a_495_ = lean_ctor_get(v_____do__lift_490_, 0);
lean_inc(v_a_495_);
lean_dec_ref(v_____do__lift_490_);
v___x_496_ = lean_apply_2(v_h__1_491_, v_a_495_, lean_box(0));
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_497_, lean_object* v_00_u03b3_498_, lean_object* v_Pl_499_, lean_object* v_next_500_, lean_object* v_acc_501_, lean_object* v_motive_502_, lean_object* v_____do__lift_503_, lean_object* v_h__1_504_, lean_object* v_h__2_505_){
_start:
{
lean_object* v_res_506_; 
v_res_506_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(v_00_u03b1_497_, v_00_u03b3_498_, v_Pl_499_, v_next_500_, v_acc_501_, v_motive_502_, v_____do__lift_503_, v_h__1_504_, v_h__2_505_);
lean_dec(v_acc_501_);
lean_dec(v_next_500_);
return v_res_506_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_507_, lean_object* v_h__1_508_, lean_object* v_h__2_509_, lean_object* v_h__3_510_){
_start:
{
switch(lean_obj_tag(v_x_507_))
{
case 0:
{
lean_object* v_it_511_; lean_object* v_out_512_; lean_object* v___x_513_; 
lean_dec(v_h__3_510_);
lean_dec(v_h__2_509_);
v_it_511_ = lean_ctor_get(v_x_507_, 0);
lean_inc(v_it_511_);
v_out_512_ = lean_ctor_get(v_x_507_, 1);
lean_inc(v_out_512_);
lean_dec_ref(v_x_507_);
v___x_513_ = lean_apply_3(v_h__1_508_, v_it_511_, v_out_512_, lean_box(0));
return v___x_513_;
}
case 1:
{
lean_object* v_it_514_; lean_object* v___x_515_; 
lean_dec(v_h__3_510_);
lean_dec(v_h__1_508_);
v_it_514_ = lean_ctor_get(v_x_507_, 0);
lean_inc(v_it_514_);
lean_dec_ref(v_x_507_);
v___x_515_ = lean_apply_2(v_h__2_509_, v_it_514_, lean_box(0));
return v___x_515_;
}
default: 
{
lean_object* v___x_516_; 
lean_dec(v_h__2_509_);
lean_dec(v_h__1_508_);
v___x_516_ = lean_apply_1(v_h__3_510_, lean_box(0));
return v___x_516_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_517_, lean_object* v_00_u03b2_518_, lean_object* v_m_519_, lean_object* v_inst_520_, lean_object* v_it_521_, lean_object* v_motive_522_, lean_object* v_x_523_, lean_object* v_h__1_524_, lean_object* v_h__2_525_, lean_object* v_h__3_526_){
_start:
{
switch(lean_obj_tag(v_x_523_))
{
case 0:
{
lean_object* v_it_527_; lean_object* v_out_528_; lean_object* v___x_529_; 
lean_dec(v_h__3_526_);
lean_dec(v_h__2_525_);
v_it_527_ = lean_ctor_get(v_x_523_, 0);
lean_inc(v_it_527_);
v_out_528_ = lean_ctor_get(v_x_523_, 1);
lean_inc(v_out_528_);
lean_dec_ref(v_x_523_);
v___x_529_ = lean_apply_3(v_h__1_524_, v_it_527_, v_out_528_, lean_box(0));
return v___x_529_;
}
case 1:
{
lean_object* v_it_530_; lean_object* v___x_531_; 
lean_dec(v_h__3_526_);
lean_dec(v_h__1_524_);
v_it_530_ = lean_ctor_get(v_x_523_, 0);
lean_inc(v_it_530_);
lean_dec_ref(v_x_523_);
v___x_531_ = lean_apply_2(v_h__2_525_, v_it_530_, lean_box(0));
return v___x_531_;
}
default: 
{
lean_object* v___x_532_; 
lean_dec(v_h__2_525_);
lean_dec(v_h__1_524_);
v___x_532_ = lean_apply_1(v_h__3_526_, lean_box(0));
return v___x_532_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_533_, lean_object* v_00_u03b2_534_, lean_object* v_m_535_, lean_object* v_inst_536_, lean_object* v_it_537_, lean_object* v_motive_538_, lean_object* v_x_539_, lean_object* v_h__1_540_, lean_object* v_h__2_541_, lean_object* v_h__3_542_){
_start:
{
lean_object* v_res_543_; 
v_res_543_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_533_, v_00_u03b2_534_, v_m_535_, v_inst_536_, v_it_537_, v_motive_538_, v_x_539_, v_h__1_540_, v_h__2_541_, v_h__3_542_);
lean_dec(v_it_537_);
lean_dec(v_inst_536_);
return v_res_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_544_, lean_object* v_h__1_545_, lean_object* v_h__2_546_){
_start:
{
if (lean_obj_tag(v_____do__lift_544_) == 0)
{
lean_object* v_a_547_; lean_object* v___x_548_; 
lean_dec(v_h__1_545_);
v_a_547_ = lean_ctor_get(v_____do__lift_544_, 0);
lean_inc(v_a_547_);
lean_dec_ref(v_____do__lift_544_);
v___x_548_ = lean_apply_2(v_h__2_546_, v_a_547_, lean_box(0));
return v___x_548_;
}
else
{
lean_object* v_a_549_; lean_object* v___x_550_; 
lean_dec(v_h__2_546_);
v_a_549_ = lean_ctor_get(v_____do__lift_544_, 0);
lean_inc(v_a_549_);
lean_dec_ref(v_____do__lift_544_);
v___x_550_ = lean_apply_2(v_h__1_545_, v_a_549_, lean_box(0));
return v___x_550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b2_551_, lean_object* v_00_u03b3_552_, lean_object* v_init_553_, lean_object* v_PlausibleForInStep_554_, lean_object* v_out_555_, lean_object* v_motive_556_, lean_object* v_____do__lift_557_, lean_object* v_h__1_558_, lean_object* v_h__2_559_){
_start:
{
if (lean_obj_tag(v_____do__lift_557_) == 0)
{
lean_object* v_a_560_; lean_object* v___x_561_; 
lean_dec(v_h__1_558_);
v_a_560_ = lean_ctor_get(v_____do__lift_557_, 0);
lean_inc(v_a_560_);
lean_dec_ref(v_____do__lift_557_);
v___x_561_ = lean_apply_2(v_h__2_559_, v_a_560_, lean_box(0));
return v___x_561_;
}
else
{
lean_object* v_a_562_; lean_object* v___x_563_; 
lean_dec(v_h__2_559_);
v_a_562_ = lean_ctor_get(v_____do__lift_557_, 0);
lean_inc(v_a_562_);
lean_dec_ref(v_____do__lift_557_);
v___x_563_ = lean_apply_2(v_h__1_558_, v_a_562_, lean_box(0));
return v___x_563_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(lean_object* v_00_u03b2_564_, lean_object* v_00_u03b3_565_, lean_object* v_init_566_, lean_object* v_PlausibleForInStep_567_, lean_object* v_out_568_, lean_object* v_motive_569_, lean_object* v_____do__lift_570_, lean_object* v_h__1_571_, lean_object* v_h__2_572_){
_start:
{
lean_object* v_res_573_; 
v_res_573_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_564_, v_00_u03b3_565_, v_init_566_, v_PlausibleForInStep_567_, v_out_568_, v_motive_569_, v_____do__lift_570_, v_h__1_571_, v_h__2_572_);
lean_dec(v_out_568_);
lean_dec(v_init_566_);
return v_res_573_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_574_, lean_object* v_f_575_, lean_object* v_h__1_576_, lean_object* v_h__2_577_){
_start:
{
lean_object* v_next_578_; 
v_next_578_ = lean_ctor_get(v_it_574_, 0);
if (lean_obj_tag(v_next_578_) == 0)
{
lean_object* v_upperBound_579_; lean_object* v___x_580_; 
lean_dec(v_h__1_576_);
v_upperBound_579_ = lean_ctor_get(v_it_574_, 1);
lean_inc(v_upperBound_579_);
lean_dec_ref(v_it_574_);
v___x_580_ = lean_apply_2(v_h__2_577_, v_upperBound_579_, v_f_575_);
return v___x_580_;
}
else
{
lean_object* v_upperBound_581_; lean_object* v_val_582_; lean_object* v___x_583_; 
lean_inc_ref(v_next_578_);
lean_dec(v_h__2_577_);
v_upperBound_581_ = lean_ctor_get(v_it_574_, 1);
lean_inc(v_upperBound_581_);
lean_dec_ref(v_it_574_);
v_val_582_ = lean_ctor_get(v_next_578_, 0);
lean_inc(v_val_582_);
lean_dec_ref(v_next_578_);
v___x_583_ = lean_apply_3(v_h__1_576_, v_val_582_, v_upperBound_581_, v_f_575_);
return v___x_583_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_inst_587_, lean_object* v_n_588_, lean_object* v_00_u03b3_589_, lean_object* v_Pl_590_, lean_object* v_motive_591_, lean_object* v_it_592_, lean_object* v_f_593_, lean_object* v_h__1_594_, lean_object* v_h__2_595_){
_start:
{
lean_object* v_next_596_; 
v_next_596_ = lean_ctor_get(v_it_592_, 0);
if (lean_obj_tag(v_next_596_) == 0)
{
lean_object* v_upperBound_597_; lean_object* v___x_598_; 
lean_dec(v_h__1_594_);
v_upperBound_597_ = lean_ctor_get(v_it_592_, 1);
lean_inc(v_upperBound_597_);
lean_dec_ref(v_it_592_);
v___x_598_ = lean_apply_2(v_h__2_595_, v_upperBound_597_, v_f_593_);
return v___x_598_;
}
else
{
lean_object* v_upperBound_599_; lean_object* v_val_600_; lean_object* v___x_601_; 
lean_inc_ref(v_next_596_);
lean_dec(v_h__2_595_);
v_upperBound_599_ = lean_ctor_get(v_it_592_, 1);
lean_inc(v_upperBound_599_);
lean_dec_ref(v_it_592_);
v_val_600_ = lean_ctor_get(v_next_596_, 0);
lean_inc(v_val_600_);
lean_dec_ref(v_next_596_);
v___x_601_ = lean_apply_3(v_h__1_594_, v_val_600_, v_upperBound_599_, v_f_593_);
return v___x_601_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_inst_605_, lean_object* v_n_606_, lean_object* v_00_u03b3_607_, lean_object* v_Pl_608_, lean_object* v_motive_609_, lean_object* v_it_610_, lean_object* v_f_611_, lean_object* v_h__1_612_, lean_object* v_h__2_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_602_, v_inst_603_, v_inst_604_, v_inst_605_, v_n_606_, v_00_u03b3_607_, v_Pl_608_, v_motive_609_, v_it_610_, v_f_611_, v_h__1_612_, v_h__2_613_);
lean_dec_ref(v_inst_605_);
lean_dec_ref(v_inst_603_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object* v_x_615_, lean_object* v_h__1_616_, lean_object* v_h__2_617_, lean_object* v_h__3_618_){
_start:
{
switch(lean_obj_tag(v_x_615_))
{
case 0:
{
lean_object* v_it_619_; lean_object* v_out_620_; lean_object* v___x_621_; 
lean_dec(v_h__3_618_);
lean_dec(v_h__2_617_);
v_it_619_ = lean_ctor_get(v_x_615_, 0);
lean_inc(v_it_619_);
v_out_620_ = lean_ctor_get(v_x_615_, 1);
lean_inc(v_out_620_);
lean_dec_ref(v_x_615_);
v___x_621_ = lean_apply_3(v_h__1_616_, v_it_619_, v_out_620_, lean_box(0));
return v___x_621_;
}
case 1:
{
lean_object* v_it_622_; lean_object* v___x_623_; 
lean_dec(v_h__3_618_);
lean_dec(v_h__1_616_);
v_it_622_ = lean_ctor_get(v_x_615_, 0);
lean_inc(v_it_622_);
lean_dec_ref(v_x_615_);
v___x_623_ = lean_apply_2(v_h__2_617_, v_it_622_, lean_box(0));
return v___x_623_;
}
default: 
{
lean_object* v___x_624_; 
lean_dec(v_h__2_617_);
lean_dec(v_h__1_616_);
v___x_624_ = lean_apply_1(v_h__3_618_, lean_box(0));
return v___x_624_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object* v_m_625_, lean_object* v_00_u03b1_626_, lean_object* v_00_u03b2_627_, lean_object* v_inst_628_, lean_object* v_it_629_, lean_object* v_motive_630_, lean_object* v_x_631_, lean_object* v_h__1_632_, lean_object* v_h__2_633_, lean_object* v_h__3_634_){
_start:
{
switch(lean_obj_tag(v_x_631_))
{
case 0:
{
lean_object* v_it_635_; lean_object* v_out_636_; lean_object* v___x_637_; 
lean_dec(v_h__3_634_);
lean_dec(v_h__2_633_);
v_it_635_ = lean_ctor_get(v_x_631_, 0);
lean_inc(v_it_635_);
v_out_636_ = lean_ctor_get(v_x_631_, 1);
lean_inc(v_out_636_);
lean_dec_ref(v_x_631_);
v___x_637_ = lean_apply_3(v_h__1_632_, v_it_635_, v_out_636_, lean_box(0));
return v___x_637_;
}
case 1:
{
lean_object* v_it_638_; lean_object* v___x_639_; 
lean_dec(v_h__3_634_);
lean_dec(v_h__1_632_);
v_it_638_ = lean_ctor_get(v_x_631_, 0);
lean_inc(v_it_638_);
lean_dec_ref(v_x_631_);
v___x_639_ = lean_apply_2(v_h__2_633_, v_it_638_, lean_box(0));
return v___x_639_;
}
default: 
{
lean_object* v___x_640_; 
lean_dec(v_h__2_633_);
lean_dec(v_h__1_632_);
v___x_640_ = lean_apply_1(v_h__3_634_, lean_box(0));
return v___x_640_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object* v_m_641_, lean_object* v_00_u03b1_642_, lean_object* v_00_u03b2_643_, lean_object* v_inst_644_, lean_object* v_it_645_, lean_object* v_motive_646_, lean_object* v_x_647_, lean_object* v_h__1_648_, lean_object* v_h__2_649_, lean_object* v_h__3_650_){
_start:
{
lean_object* v_res_651_; 
v_res_651_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_641_, v_00_u03b1_642_, v_00_u03b2_643_, v_inst_644_, v_it_645_, v_motive_646_, v_x_647_, v_h__1_648_, v_h__2_649_, v_h__3_650_);
lean_dec(v_it_645_);
lean_dec(v_inst_644_);
return v_res_651_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object* v_____do__lift_652_, lean_object* v_h__1_653_, lean_object* v_h__2_654_){
_start:
{
if (lean_obj_tag(v_____do__lift_652_) == 0)
{
lean_object* v_a_655_; lean_object* v___x_656_; 
lean_dec(v_h__1_653_);
v_a_655_ = lean_ctor_get(v_____do__lift_652_, 0);
lean_inc(v_a_655_);
lean_dec_ref(v_____do__lift_652_);
v___x_656_ = lean_apply_2(v_h__2_654_, v_a_655_, lean_box(0));
return v___x_656_;
}
else
{
lean_object* v_a_657_; lean_object* v___x_658_; 
lean_dec(v_h__2_654_);
v_a_657_ = lean_ctor_get(v_____do__lift_652_, 0);
lean_inc(v_a_657_);
lean_dec_ref(v_____do__lift_652_);
v___x_658_ = lean_apply_2(v_h__1_653_, v_a_657_, lean_box(0));
return v___x_658_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object* v_00_u03b2_659_, lean_object* v_00_u03b3_660_, lean_object* v_PlausibleForInStep_661_, lean_object* v_acc_662_, lean_object* v_out_663_, lean_object* v_motive_664_, lean_object* v_____do__lift_665_, lean_object* v_h__1_666_, lean_object* v_h__2_667_){
_start:
{
if (lean_obj_tag(v_____do__lift_665_) == 0)
{
lean_object* v_a_668_; lean_object* v___x_669_; 
lean_dec(v_h__1_666_);
v_a_668_ = lean_ctor_get(v_____do__lift_665_, 0);
lean_inc(v_a_668_);
lean_dec_ref(v_____do__lift_665_);
v___x_669_ = lean_apply_2(v_h__2_667_, v_a_668_, lean_box(0));
return v___x_669_;
}
else
{
lean_object* v_a_670_; lean_object* v___x_671_; 
lean_dec(v_h__2_667_);
v_a_670_ = lean_ctor_get(v_____do__lift_665_, 0);
lean_inc(v_a_670_);
lean_dec_ref(v_____do__lift_665_);
v___x_671_ = lean_apply_2(v_h__1_666_, v_a_670_, lean_box(0));
return v___x_671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object* v_00_u03b2_672_, lean_object* v_00_u03b3_673_, lean_object* v_PlausibleForInStep_674_, lean_object* v_acc_675_, lean_object* v_out_676_, lean_object* v_motive_677_, lean_object* v_____do__lift_678_, lean_object* v_h__1_679_, lean_object* v_h__2_680_){
_start:
{
lean_object* v_res_681_; 
v_res_681_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_672_, v_00_u03b3_673_, v_PlausibleForInStep_674_, v_acc_675_, v_out_676_, v_motive_677_, v_____do__lift_678_, v_h__1_679_, v_h__2_680_);
lean_dec(v_out_676_);
lean_dec(v_acc_675_);
return v_res_681_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step___redArg(lean_object* v_inst_682_, lean_object* v_inst_683_, lean_object* v_it_684_){
_start:
{
lean_object* v_next_685_; 
v_next_685_ = lean_ctor_get(v_it_684_, 0);
lean_inc(v_next_685_);
if (lean_obj_tag(v_next_685_) == 0)
{
lean_object* v___x_686_; 
lean_dec_ref(v_it_684_);
lean_dec_ref(v_inst_683_);
lean_dec_ref(v_inst_682_);
v___x_686_ = lean_box(2);
return v___x_686_;
}
else
{
lean_object* v_upperBound_687_; lean_object* v___x_689_; uint8_t v_isShared_690_; uint8_t v_isSharedCheck_708_; 
v_upperBound_687_ = lean_ctor_get(v_it_684_, 1);
v_isSharedCheck_708_ = !lean_is_exclusive(v_it_684_);
if (v_isSharedCheck_708_ == 0)
{
lean_object* v_unused_709_; 
v_unused_709_ = lean_ctor_get(v_it_684_, 0);
lean_dec(v_unused_709_);
v___x_689_ = v_it_684_;
v_isShared_690_ = v_isSharedCheck_708_;
goto v_resetjp_688_;
}
else
{
lean_inc(v_upperBound_687_);
lean_dec(v_it_684_);
v___x_689_ = lean_box(0);
v_isShared_690_ = v_isSharedCheck_708_;
goto v_resetjp_688_;
}
v_resetjp_688_:
{
lean_object* v_val_691_; lean_object* v___x_692_; uint8_t v___x_693_; 
v_val_691_ = lean_ctor_get(v_next_685_, 0);
lean_inc_n(v_val_691_, 2);
lean_dec_ref(v_next_685_);
lean_inc(v_upperBound_687_);
v___x_692_ = lean_apply_2(v_inst_683_, v_val_691_, v_upperBound_687_);
v___x_693_ = lean_unbox(v___x_692_);
if (v___x_693_ == 0)
{
lean_object* v___x_694_; 
lean_dec(v_val_691_);
lean_del_object(v___x_689_);
lean_dec(v_upperBound_687_);
lean_dec_ref(v_inst_682_);
v___x_694_ = lean_box(2);
return v___x_694_;
}
else
{
lean_object* v_succ_x3f_695_; lean_object* v___x_697_; uint8_t v_isShared_698_; uint8_t v_isSharedCheck_706_; 
v_succ_x3f_695_ = lean_ctor_get(v_inst_682_, 0);
v_isSharedCheck_706_ = !lean_is_exclusive(v_inst_682_);
if (v_isSharedCheck_706_ == 0)
{
lean_object* v_unused_707_; 
v_unused_707_ = lean_ctor_get(v_inst_682_, 1);
lean_dec(v_unused_707_);
v___x_697_ = v_inst_682_;
v_isShared_698_ = v_isSharedCheck_706_;
goto v_resetjp_696_;
}
else
{
lean_inc(v_succ_x3f_695_);
lean_dec(v_inst_682_);
v___x_697_ = lean_box(0);
v_isShared_698_ = v_isSharedCheck_706_;
goto v_resetjp_696_;
}
v_resetjp_696_:
{
lean_object* v___x_699_; lean_object* v___x_701_; 
lean_inc(v_val_691_);
v___x_699_ = lean_apply_1(v_succ_x3f_695_, v_val_691_);
if (v_isShared_690_ == 0)
{
lean_ctor_set(v___x_689_, 0, v___x_699_);
v___x_701_ = v___x_689_;
goto v_reusejp_700_;
}
else
{
lean_object* v_reuseFailAlloc_705_; 
v_reuseFailAlloc_705_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_705_, 0, v___x_699_);
lean_ctor_set(v_reuseFailAlloc_705_, 1, v_upperBound_687_);
v___x_701_ = v_reuseFailAlloc_705_;
goto v_reusejp_700_;
}
v_reusejp_700_:
{
lean_object* v___x_703_; 
if (v_isShared_698_ == 0)
{
lean_ctor_set(v___x_697_, 1, v_val_691_);
lean_ctor_set(v___x_697_, 0, v___x_701_);
v___x_703_ = v___x_697_;
goto v_reusejp_702_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_701_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_val_691_);
v___x_703_ = v_reuseFailAlloc_704_;
goto v_reusejp_702_;
}
v_reusejp_702_:
{
return v___x_703_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step(lean_object* v_00_u03b1_710_, lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_inst_713_, lean_object* v_it_714_){
_start:
{
lean_object* v_next_715_; 
v_next_715_ = lean_ctor_get(v_it_714_, 0);
lean_inc(v_next_715_);
if (lean_obj_tag(v_next_715_) == 0)
{
lean_object* v___x_716_; 
lean_dec_ref(v_it_714_);
lean_dec_ref(v_inst_713_);
lean_dec_ref(v_inst_711_);
v___x_716_ = lean_box(2);
return v___x_716_;
}
else
{
lean_object* v_upperBound_717_; lean_object* v___x_719_; uint8_t v_isShared_720_; uint8_t v_isSharedCheck_738_; 
v_upperBound_717_ = lean_ctor_get(v_it_714_, 1);
v_isSharedCheck_738_ = !lean_is_exclusive(v_it_714_);
if (v_isSharedCheck_738_ == 0)
{
lean_object* v_unused_739_; 
v_unused_739_ = lean_ctor_get(v_it_714_, 0);
lean_dec(v_unused_739_);
v___x_719_ = v_it_714_;
v_isShared_720_ = v_isSharedCheck_738_;
goto v_resetjp_718_;
}
else
{
lean_inc(v_upperBound_717_);
lean_dec(v_it_714_);
v___x_719_ = lean_box(0);
v_isShared_720_ = v_isSharedCheck_738_;
goto v_resetjp_718_;
}
v_resetjp_718_:
{
lean_object* v_val_721_; lean_object* v___x_722_; uint8_t v___x_723_; 
v_val_721_ = lean_ctor_get(v_next_715_, 0);
lean_inc_n(v_val_721_, 2);
lean_dec_ref(v_next_715_);
lean_inc(v_upperBound_717_);
v___x_722_ = lean_apply_2(v_inst_713_, v_val_721_, v_upperBound_717_);
v___x_723_ = lean_unbox(v___x_722_);
if (v___x_723_ == 0)
{
lean_object* v___x_724_; 
lean_dec(v_val_721_);
lean_del_object(v___x_719_);
lean_dec(v_upperBound_717_);
lean_dec_ref(v_inst_711_);
v___x_724_ = lean_box(2);
return v___x_724_;
}
else
{
lean_object* v_succ_x3f_725_; lean_object* v___x_727_; uint8_t v_isShared_728_; uint8_t v_isSharedCheck_736_; 
v_succ_x3f_725_ = lean_ctor_get(v_inst_711_, 0);
v_isSharedCheck_736_ = !lean_is_exclusive(v_inst_711_);
if (v_isSharedCheck_736_ == 0)
{
lean_object* v_unused_737_; 
v_unused_737_ = lean_ctor_get(v_inst_711_, 1);
lean_dec(v_unused_737_);
v___x_727_ = v_inst_711_;
v_isShared_728_ = v_isSharedCheck_736_;
goto v_resetjp_726_;
}
else
{
lean_inc(v_succ_x3f_725_);
lean_dec(v_inst_711_);
v___x_727_ = lean_box(0);
v_isShared_728_ = v_isSharedCheck_736_;
goto v_resetjp_726_;
}
v_resetjp_726_:
{
lean_object* v___x_729_; lean_object* v___x_731_; 
lean_inc(v_val_721_);
v___x_729_ = lean_apply_1(v_succ_x3f_725_, v_val_721_);
if (v_isShared_720_ == 0)
{
lean_ctor_set(v___x_719_, 0, v___x_729_);
v___x_731_ = v___x_719_;
goto v_reusejp_730_;
}
else
{
lean_object* v_reuseFailAlloc_735_; 
v_reuseFailAlloc_735_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_735_, 0, v___x_729_);
lean_ctor_set(v_reuseFailAlloc_735_, 1, v_upperBound_717_);
v___x_731_ = v_reuseFailAlloc_735_;
goto v_reusejp_730_;
}
v_reusejp_730_:
{
lean_object* v___x_733_; 
if (v_isShared_728_ == 0)
{
lean_ctor_set(v___x_727_, 1, v_val_721_);
lean_ctor_set(v___x_727_, 0, v___x_731_);
v___x_733_ = v___x_727_;
goto v_reusejp_732_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_731_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_val_721_);
v___x_733_ = v_reuseFailAlloc_734_;
goto v_reusejp_732_;
}
v_reusejp_732_:
{
return v___x_733_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step___redArg(lean_object* v_inst_740_, lean_object* v_inst_741_, lean_object* v_it_742_){
_start:
{
lean_object* v_next_743_; 
v_next_743_ = lean_ctor_get(v_it_742_, 0);
lean_inc(v_next_743_);
if (lean_obj_tag(v_next_743_) == 0)
{
lean_object* v___x_744_; 
lean_dec_ref(v_it_742_);
lean_dec_ref(v_inst_741_);
lean_dec_ref(v_inst_740_);
v___x_744_ = lean_box(2);
return v___x_744_;
}
else
{
lean_object* v_upperBound_745_; lean_object* v___x_747_; uint8_t v_isShared_748_; uint8_t v_isSharedCheck_766_; 
v_upperBound_745_ = lean_ctor_get(v_it_742_, 1);
v_isSharedCheck_766_ = !lean_is_exclusive(v_it_742_);
if (v_isSharedCheck_766_ == 0)
{
lean_object* v_unused_767_; 
v_unused_767_ = lean_ctor_get(v_it_742_, 0);
lean_dec(v_unused_767_);
v___x_747_ = v_it_742_;
v_isShared_748_ = v_isSharedCheck_766_;
goto v_resetjp_746_;
}
else
{
lean_inc(v_upperBound_745_);
lean_dec(v_it_742_);
v___x_747_ = lean_box(0);
v_isShared_748_ = v_isSharedCheck_766_;
goto v_resetjp_746_;
}
v_resetjp_746_:
{
lean_object* v_val_749_; lean_object* v___x_750_; uint8_t v___x_751_; 
v_val_749_ = lean_ctor_get(v_next_743_, 0);
lean_inc_n(v_val_749_, 2);
lean_dec_ref(v_next_743_);
lean_inc(v_upperBound_745_);
v___x_750_ = lean_apply_2(v_inst_741_, v_val_749_, v_upperBound_745_);
v___x_751_ = lean_unbox(v___x_750_);
if (v___x_751_ == 0)
{
lean_object* v___x_752_; 
lean_dec(v_val_749_);
lean_del_object(v___x_747_);
lean_dec(v_upperBound_745_);
lean_dec_ref(v_inst_740_);
v___x_752_ = lean_box(2);
return v___x_752_;
}
else
{
lean_object* v_succ_x3f_753_; lean_object* v___x_755_; uint8_t v_isShared_756_; uint8_t v_isSharedCheck_764_; 
v_succ_x3f_753_ = lean_ctor_get(v_inst_740_, 0);
v_isSharedCheck_764_ = !lean_is_exclusive(v_inst_740_);
if (v_isSharedCheck_764_ == 0)
{
lean_object* v_unused_765_; 
v_unused_765_ = lean_ctor_get(v_inst_740_, 1);
lean_dec(v_unused_765_);
v___x_755_ = v_inst_740_;
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
else
{
lean_inc(v_succ_x3f_753_);
lean_dec(v_inst_740_);
v___x_755_ = lean_box(0);
v_isShared_756_ = v_isSharedCheck_764_;
goto v_resetjp_754_;
}
v_resetjp_754_:
{
lean_object* v___x_757_; lean_object* v___x_759_; 
lean_inc(v_val_749_);
v___x_757_ = lean_apply_1(v_succ_x3f_753_, v_val_749_);
if (v_isShared_748_ == 0)
{
lean_ctor_set(v___x_747_, 0, v___x_757_);
v___x_759_ = v___x_747_;
goto v_reusejp_758_;
}
else
{
lean_object* v_reuseFailAlloc_763_; 
v_reuseFailAlloc_763_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_763_, 0, v___x_757_);
lean_ctor_set(v_reuseFailAlloc_763_, 1, v_upperBound_745_);
v___x_759_ = v_reuseFailAlloc_763_;
goto v_reusejp_758_;
}
v_reusejp_758_:
{
lean_object* v___x_761_; 
if (v_isShared_756_ == 0)
{
lean_ctor_set(v___x_755_, 1, v_val_749_);
lean_ctor_set(v___x_755_, 0, v___x_759_);
v___x_761_ = v___x_755_;
goto v_reusejp_760_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_759_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_val_749_);
v___x_761_ = v_reuseFailAlloc_762_;
goto v_reusejp_760_;
}
v_reusejp_760_:
{
return v___x_761_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step(lean_object* v_00_u03b1_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_inst_771_, lean_object* v_it_772_){
_start:
{
lean_object* v_next_773_; 
v_next_773_ = lean_ctor_get(v_it_772_, 0);
lean_inc(v_next_773_);
if (lean_obj_tag(v_next_773_) == 0)
{
lean_object* v___x_774_; 
lean_dec_ref(v_it_772_);
lean_dec_ref(v_inst_771_);
lean_dec_ref(v_inst_769_);
v___x_774_ = lean_box(2);
return v___x_774_;
}
else
{
lean_object* v_upperBound_775_; lean_object* v___x_777_; uint8_t v_isShared_778_; uint8_t v_isSharedCheck_796_; 
v_upperBound_775_ = lean_ctor_get(v_it_772_, 1);
v_isSharedCheck_796_ = !lean_is_exclusive(v_it_772_);
if (v_isSharedCheck_796_ == 0)
{
lean_object* v_unused_797_; 
v_unused_797_ = lean_ctor_get(v_it_772_, 0);
lean_dec(v_unused_797_);
v___x_777_ = v_it_772_;
v_isShared_778_ = v_isSharedCheck_796_;
goto v_resetjp_776_;
}
else
{
lean_inc(v_upperBound_775_);
lean_dec(v_it_772_);
v___x_777_ = lean_box(0);
v_isShared_778_ = v_isSharedCheck_796_;
goto v_resetjp_776_;
}
v_resetjp_776_:
{
lean_object* v_val_779_; lean_object* v___x_780_; uint8_t v___x_781_; 
v_val_779_ = lean_ctor_get(v_next_773_, 0);
lean_inc_n(v_val_779_, 2);
lean_dec_ref(v_next_773_);
lean_inc(v_upperBound_775_);
v___x_780_ = lean_apply_2(v_inst_771_, v_val_779_, v_upperBound_775_);
v___x_781_ = lean_unbox(v___x_780_);
if (v___x_781_ == 0)
{
lean_object* v___x_782_; 
lean_dec(v_val_779_);
lean_del_object(v___x_777_);
lean_dec(v_upperBound_775_);
lean_dec_ref(v_inst_769_);
v___x_782_ = lean_box(2);
return v___x_782_;
}
else
{
lean_object* v_succ_x3f_783_; lean_object* v___x_785_; uint8_t v_isShared_786_; uint8_t v_isSharedCheck_794_; 
v_succ_x3f_783_ = lean_ctor_get(v_inst_769_, 0);
v_isSharedCheck_794_ = !lean_is_exclusive(v_inst_769_);
if (v_isSharedCheck_794_ == 0)
{
lean_object* v_unused_795_; 
v_unused_795_ = lean_ctor_get(v_inst_769_, 1);
lean_dec(v_unused_795_);
v___x_785_ = v_inst_769_;
v_isShared_786_ = v_isSharedCheck_794_;
goto v_resetjp_784_;
}
else
{
lean_inc(v_succ_x3f_783_);
lean_dec(v_inst_769_);
v___x_785_ = lean_box(0);
v_isShared_786_ = v_isSharedCheck_794_;
goto v_resetjp_784_;
}
v_resetjp_784_:
{
lean_object* v___x_787_; lean_object* v___x_789_; 
lean_inc(v_val_779_);
v___x_787_ = lean_apply_1(v_succ_x3f_783_, v_val_779_);
if (v_isShared_778_ == 0)
{
lean_ctor_set(v___x_777_, 0, v___x_787_);
v___x_789_ = v___x_777_;
goto v_reusejp_788_;
}
else
{
lean_object* v_reuseFailAlloc_793_; 
v_reuseFailAlloc_793_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_793_, 0, v___x_787_);
lean_ctor_set(v_reuseFailAlloc_793_, 1, v_upperBound_775_);
v___x_789_ = v_reuseFailAlloc_793_;
goto v_reusejp_788_;
}
v_reusejp_788_:
{
lean_object* v___x_791_; 
if (v_isShared_786_ == 0)
{
lean_ctor_set(v___x_785_, 1, v_val_779_);
lean_ctor_set(v___x_785_, 0, v___x_789_);
v___x_791_ = v___x_785_;
goto v_reusejp_790_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_789_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_val_779_);
v___x_791_ = v_reuseFailAlloc_792_;
goto v_reusejp_790_;
}
v_reusejp_790_:
{
return v___x_791_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0(lean_object* v_inst_798_, lean_object* v_inst_799_, lean_object* v_it_800_){
_start:
{
lean_object* v_next_801_; 
v_next_801_ = lean_ctor_get(v_it_800_, 0);
lean_inc(v_next_801_);
if (lean_obj_tag(v_next_801_) == 0)
{
lean_object* v___x_802_; 
lean_dec_ref(v_it_800_);
lean_dec_ref(v_inst_799_);
lean_dec_ref(v_inst_798_);
v___x_802_ = lean_box(2);
return v___x_802_;
}
else
{
lean_object* v_upperBound_803_; lean_object* v___x_805_; uint8_t v_isShared_806_; uint8_t v_isSharedCheck_824_; 
v_upperBound_803_ = lean_ctor_get(v_it_800_, 1);
v_isSharedCheck_824_ = !lean_is_exclusive(v_it_800_);
if (v_isSharedCheck_824_ == 0)
{
lean_object* v_unused_825_; 
v_unused_825_ = lean_ctor_get(v_it_800_, 0);
lean_dec(v_unused_825_);
v___x_805_ = v_it_800_;
v_isShared_806_ = v_isSharedCheck_824_;
goto v_resetjp_804_;
}
else
{
lean_inc(v_upperBound_803_);
lean_dec(v_it_800_);
v___x_805_ = lean_box(0);
v_isShared_806_ = v_isSharedCheck_824_;
goto v_resetjp_804_;
}
v_resetjp_804_:
{
lean_object* v_val_807_; lean_object* v___x_808_; uint8_t v___x_809_; 
v_val_807_ = lean_ctor_get(v_next_801_, 0);
lean_inc_n(v_val_807_, 2);
lean_dec_ref(v_next_801_);
lean_inc(v_upperBound_803_);
v___x_808_ = lean_apply_2(v_inst_798_, v_val_807_, v_upperBound_803_);
v___x_809_ = lean_unbox(v___x_808_);
if (v___x_809_ == 0)
{
lean_object* v___x_810_; 
lean_dec(v_val_807_);
lean_del_object(v___x_805_);
lean_dec(v_upperBound_803_);
lean_dec_ref(v_inst_799_);
v___x_810_ = lean_box(2);
return v___x_810_;
}
else
{
lean_object* v_succ_x3f_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_822_; 
v_succ_x3f_811_ = lean_ctor_get(v_inst_799_, 0);
v_isSharedCheck_822_ = !lean_is_exclusive(v_inst_799_);
if (v_isSharedCheck_822_ == 0)
{
lean_object* v_unused_823_; 
v_unused_823_ = lean_ctor_get(v_inst_799_, 1);
lean_dec(v_unused_823_);
v___x_813_ = v_inst_799_;
v_isShared_814_ = v_isSharedCheck_822_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_succ_x3f_811_);
lean_dec(v_inst_799_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_822_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; lean_object* v___x_817_; 
lean_inc(v_val_807_);
v___x_815_ = lean_apply_1(v_succ_x3f_811_, v_val_807_);
if (v_isShared_806_ == 0)
{
lean_ctor_set(v___x_805_, 0, v___x_815_);
v___x_817_ = v___x_805_;
goto v_reusejp_816_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v___x_815_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_upperBound_803_);
v___x_817_ = v_reuseFailAlloc_821_;
goto v_reusejp_816_;
}
v_reusejp_816_:
{
lean_object* v___x_819_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v_val_807_);
lean_ctor_set(v___x_813_, 0, v___x_817_);
v___x_819_ = v___x_813_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_817_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_val_807_);
v___x_819_ = v_reuseFailAlloc_820_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
return v___x_819_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg(lean_object* v_inst_826_, lean_object* v_inst_827_){
_start:
{
lean_object* v___f_828_; 
v___f_828_ = lean_alloc_closure((void*)(l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_828_, 0, v_inst_827_);
lean_closure_set(v___f_828_, 1, v_inst_826_);
return v___f_828_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT(lean_object* v_00_u03b1_829_, lean_object* v_inst_830_, lean_object* v_inst_831_, lean_object* v_inst_832_){
_start:
{
lean_object* v___f_833_; 
v___f_833_ = lean_alloc_closure((void*)(l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_833_, 0, v_inst_832_);
lean_closure_set(v___f_833_, 1, v_inst_830_);
return v___f_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_834_, lean_object* v_inst_835_, lean_object* v_inst_836_, lean_object* v_inst_837_, lean_object* v_inst_838_, lean_object* v_inst_839_){
_start:
{
lean_object* v___x_840_; 
v___x_840_ = lean_box(0);
return v___x_840_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_841_, lean_object* v_inst_842_, lean_object* v_inst_843_, lean_object* v_inst_844_, lean_object* v_inst_845_, lean_object* v_inst_846_){
_start:
{
lean_object* v_res_847_; 
v_res_847_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(v_00_u03b1_841_, v_inst_842_, v_inst_843_, v_inst_844_, v_inst_845_, v_inst_846_);
lean_dec_ref(v_inst_844_);
lean_dec_ref(v_inst_842_);
return v_res_847_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_848_, lean_object* v_inst_849_, lean_object* v_inst_850_, lean_object* v_inst_851_, lean_object* v_inst_852_){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_box(0);
return v___x_853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_854_, lean_object* v_inst_855_, lean_object* v_inst_856_, lean_object* v_inst_857_, lean_object* v_inst_858_){
_start:
{
lean_object* v_res_859_; 
v_res_859_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(v_00_u03b1_854_, v_inst_855_, v_inst_856_, v_inst_857_, v_inst_858_);
lean_dec_ref(v_inst_857_);
lean_dec_ref(v_inst_855_);
return v_res_859_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_it_862_, lean_object* v_n_863_){
_start:
{
lean_object* v_next_864_; 
v_next_864_ = lean_ctor_get(v_it_862_, 0);
lean_inc(v_next_864_);
if (lean_obj_tag(v_next_864_) == 0)
{
lean_object* v___x_865_; 
lean_dec(v_n_863_);
lean_dec_ref(v_it_862_);
lean_dec_ref(v_inst_861_);
lean_dec_ref(v_inst_860_);
v___x_865_ = lean_box(2);
return v___x_865_;
}
else
{
lean_object* v_upperBound_866_; lean_object* v___x_868_; uint8_t v_isShared_869_; uint8_t v_isSharedCheck_890_; 
v_upperBound_866_ = lean_ctor_get(v_it_862_, 1);
v_isSharedCheck_890_ = !lean_is_exclusive(v_it_862_);
if (v_isSharedCheck_890_ == 0)
{
lean_object* v_unused_891_; 
v_unused_891_ = lean_ctor_get(v_it_862_, 0);
lean_dec(v_unused_891_);
v___x_868_ = v_it_862_;
v_isShared_869_ = v_isSharedCheck_890_;
goto v_resetjp_867_;
}
else
{
lean_inc(v_upperBound_866_);
lean_dec(v_it_862_);
v___x_868_ = lean_box(0);
v_isShared_869_ = v_isSharedCheck_890_;
goto v_resetjp_867_;
}
v_resetjp_867_:
{
lean_object* v_succ_x3f_870_; lean_object* v_succMany_x3f_871_; lean_object* v___x_873_; uint8_t v_isShared_874_; uint8_t v_isSharedCheck_889_; 
v_succ_x3f_870_ = lean_ctor_get(v_inst_860_, 0);
v_succMany_x3f_871_ = lean_ctor_get(v_inst_860_, 1);
v_isSharedCheck_889_ = !lean_is_exclusive(v_inst_860_);
if (v_isSharedCheck_889_ == 0)
{
v___x_873_ = v_inst_860_;
v_isShared_874_ = v_isSharedCheck_889_;
goto v_resetjp_872_;
}
else
{
lean_inc(v_succMany_x3f_871_);
lean_inc(v_succ_x3f_870_);
lean_dec(v_inst_860_);
v___x_873_ = lean_box(0);
v_isShared_874_ = v_isSharedCheck_889_;
goto v_resetjp_872_;
}
v_resetjp_872_:
{
lean_object* v_val_875_; lean_object* v___x_876_; 
v_val_875_ = lean_ctor_get(v_next_864_, 0);
lean_inc(v_val_875_);
lean_dec_ref(v_next_864_);
v___x_876_ = lean_apply_2(v_succMany_x3f_871_, v_n_863_, v_val_875_);
if (lean_obj_tag(v___x_876_) == 0)
{
lean_object* v___x_877_; 
lean_del_object(v___x_873_);
lean_dec_ref(v_succ_x3f_870_);
lean_del_object(v___x_868_);
lean_dec(v_upperBound_866_);
lean_dec_ref(v_inst_861_);
v___x_877_ = lean_box(2);
return v___x_877_;
}
else
{
lean_object* v_val_878_; lean_object* v___x_879_; uint8_t v___x_880_; 
v_val_878_ = lean_ctor_get(v___x_876_, 0);
lean_inc_n(v_val_878_, 2);
lean_dec_ref(v___x_876_);
lean_inc(v_upperBound_866_);
v___x_879_ = lean_apply_2(v_inst_861_, v_val_878_, v_upperBound_866_);
v___x_880_ = lean_unbox(v___x_879_);
if (v___x_880_ == 0)
{
lean_object* v___x_881_; 
lean_dec(v_val_878_);
lean_del_object(v___x_873_);
lean_dec_ref(v_succ_x3f_870_);
lean_del_object(v___x_868_);
lean_dec(v_upperBound_866_);
v___x_881_ = lean_box(2);
return v___x_881_;
}
else
{
lean_object* v___x_882_; lean_object* v___x_884_; 
lean_inc(v_val_878_);
v___x_882_ = lean_apply_1(v_succ_x3f_870_, v_val_878_);
if (v_isShared_869_ == 0)
{
lean_ctor_set(v___x_868_, 0, v___x_882_);
v___x_884_ = v___x_868_;
goto v_reusejp_883_;
}
else
{
lean_object* v_reuseFailAlloc_888_; 
v_reuseFailAlloc_888_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_888_, 0, v___x_882_);
lean_ctor_set(v_reuseFailAlloc_888_, 1, v_upperBound_866_);
v___x_884_ = v_reuseFailAlloc_888_;
goto v_reusejp_883_;
}
v_reusejp_883_:
{
lean_object* v___x_886_; 
if (v_isShared_874_ == 0)
{
lean_ctor_set(v___x_873_, 1, v_val_878_);
lean_ctor_set(v___x_873_, 0, v___x_884_);
v___x_886_ = v___x_873_;
goto v_reusejp_885_;
}
else
{
lean_object* v_reuseFailAlloc_887_; 
v_reuseFailAlloc_887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_887_, 0, v___x_884_);
lean_ctor_set(v_reuseFailAlloc_887_, 1, v_val_878_);
v___x_886_ = v_reuseFailAlloc_887_;
goto v_reusejp_885_;
}
v_reusejp_885_:
{
return v___x_886_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg(lean_object* v_inst_892_, lean_object* v_inst_893_){
_start:
{
lean_object* v___f_894_; 
v___f_894_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_894_, 0, v_inst_892_);
lean_closure_set(v___f_894_, 1, v_inst_893_);
return v___f_894_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess(lean_object* v_00_u03b1_895_, lean_object* v_inst_896_, lean_object* v_inst_897_, lean_object* v_inst_898_, lean_object* v_inst_899_, lean_object* v_inst_900_){
_start:
{
lean_object* v___f_901_; 
v___f_901_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_901_, 0, v_inst_896_);
lean_closure_set(v___f_901_, 1, v_inst_898_);
return v___f_901_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_inst_904_, lean_object* v_upperBound_905_, lean_object* v_acc_906_, lean_object* v_next_907_, lean_object* v_f_908_){
_start:
{
lean_object* v___f_909_; lean_object* v___x_910_; 
v___f_909_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 9, 5);
lean_closure_set(v___f_909_, 0, v_inst_903_);
lean_closure_set(v___f_909_, 1, v_upperBound_905_);
lean_closure_set(v___f_909_, 2, v_inst_904_);
lean_closure_set(v___f_909_, 3, v_inst_902_);
lean_closure_set(v___f_909_, 4, v_f_908_);
v___x_910_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_909_, v_next_907_, v_acc_906_, lean_box(0));
return v___x_910_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_911_, lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_inst_914_, lean_object* v_inst_915_, lean_object* v_n_916_, lean_object* v_inst_917_, lean_object* v_00_u03b3_918_, lean_object* v_Pl_919_, lean_object* v_LargeEnough_920_, lean_object* v_hl_921_, lean_object* v_upperBound_922_, lean_object* v_acc_923_, lean_object* v_next_924_, lean_object* v_h_925_, lean_object* v_f_926_){
_start:
{
lean_object* v___f_927_; lean_object* v___x_928_; 
v___f_927_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 9, 5);
lean_closure_set(v___f_927_, 0, v_inst_914_);
lean_closure_set(v___f_927_, 1, v_upperBound_922_);
lean_closure_set(v___f_927_, 2, v_inst_917_);
lean_closure_set(v___f_927_, 3, v_inst_912_);
lean_closure_set(v___f_927_, 4, v_f_926_);
v___x_928_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_927_, v_next_924_, v_acc_923_, lean_box(0));
return v___x_928_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_929_, lean_object* v_inst_930_, lean_object* v_inst_931_, lean_object* v_toBind_932_, lean_object* v_x_933_, lean_object* v_00_u03b3_934_, lean_object* v_Pl_935_, lean_object* v_it_936_, lean_object* v_init_937_, lean_object* v_f_938_){
_start:
{
lean_object* v_next_939_; 
v_next_939_ = lean_ctor_get(v_it_936_, 0);
lean_inc(v_next_939_);
if (lean_obj_tag(v_next_939_) == 0)
{
lean_object* v___x_940_; 
lean_dec(v_f_938_);
lean_dec_ref(v_it_936_);
lean_dec(v_toBind_932_);
lean_dec_ref(v_inst_931_);
lean_dec_ref(v_inst_930_);
v___x_940_ = lean_apply_2(v_toPure_929_, lean_box(0), v_init_937_);
return v___x_940_;
}
else
{
lean_object* v_upperBound_941_; lean_object* v_val_942_; lean_object* v___f_943_; lean_object* v___x_944_; 
v_upperBound_941_ = lean_ctor_get(v_it_936_, 1);
lean_inc(v_upperBound_941_);
lean_dec_ref(v_it_936_);
v_val_942_ = lean_ctor_get(v_next_939_, 0);
lean_inc(v_val_942_);
lean_dec_ref(v_next_939_);
v___f_943_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_943_, 0, v_inst_930_);
lean_closure_set(v___f_943_, 1, v_upperBound_941_);
lean_closure_set(v___f_943_, 2, v_toPure_929_);
lean_closure_set(v___f_943_, 3, v_inst_931_);
lean_closure_set(v___f_943_, 4, v_f_938_);
lean_closure_set(v___f_943_, 5, v_toBind_932_);
v___x_944_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_943_, v_val_942_, v_init_937_, lean_box(0));
return v___x_944_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_945_, lean_object* v_inst_946_, lean_object* v_inst_947_, lean_object* v_toBind_948_, lean_object* v_x_949_, lean_object* v_00_u03b3_950_, lean_object* v_Pl_951_, lean_object* v_it_952_, lean_object* v_init_953_, lean_object* v_f_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_945_, v_inst_946_, v_inst_947_, v_toBind_948_, v_x_949_, v_00_u03b3_950_, v_Pl_951_, v_it_952_, v_init_953_, v_f_954_);
lean_dec(v_x_949_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg(lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_inst_958_){
_start:
{
lean_object* v_toApplicative_959_; lean_object* v_toBind_960_; lean_object* v_toPure_961_; lean_object* v___f_962_; 
v_toApplicative_959_ = lean_ctor_get(v_inst_958_, 0);
lean_inc_ref(v_toApplicative_959_);
v_toBind_960_ = lean_ctor_get(v_inst_958_, 1);
lean_inc(v_toBind_960_);
lean_dec_ref(v_inst_958_);
v_toPure_961_ = lean_ctor_get(v_toApplicative_959_, 1);
lean_inc(v_toPure_961_);
lean_dec_ref(v_toApplicative_959_);
v___f_962_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_962_, 0, v_toPure_961_);
lean_closure_set(v___f_962_, 1, v_inst_957_);
lean_closure_set(v___f_962_, 2, v_inst_956_);
lean_closure_set(v___f_962_, 3, v_toBind_960_);
return v___f_962_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop(lean_object* v_00_u03b1_963_, lean_object* v_inst_964_, lean_object* v_inst_965_, lean_object* v_inst_966_, lean_object* v_inst_967_, lean_object* v_inst_968_, lean_object* v_n_969_, lean_object* v_inst_970_){
_start:
{
lean_object* v_toApplicative_971_; lean_object* v_toBind_972_; lean_object* v_toPure_973_; lean_object* v___f_974_; 
v_toApplicative_971_ = lean_ctor_get(v_inst_970_, 0);
lean_inc_ref(v_toApplicative_971_);
v_toBind_972_ = lean_ctor_get(v_inst_970_, 1);
lean_inc(v_toBind_972_);
lean_dec_ref(v_inst_970_);
v_toPure_973_ = lean_ctor_get(v_toApplicative_971_, 1);
lean_inc(v_toPure_973_);
lean_dec_ref(v_toApplicative_971_);
v___f_974_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_974_, 0, v_toPure_973_);
lean_closure_set(v___f_974_, 1, v_inst_966_);
lean_closure_set(v___f_974_, 2, v_inst_964_);
lean_closure_set(v___f_974_, 3, v_toBind_972_);
return v___f_974_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_975_, lean_object* v_f_976_, lean_object* v_h__1_977_, lean_object* v_h__2_978_){
_start:
{
lean_object* v_next_979_; 
v_next_979_ = lean_ctor_get(v_it_975_, 0);
if (lean_obj_tag(v_next_979_) == 0)
{
lean_object* v_upperBound_980_; lean_object* v___x_981_; 
lean_dec(v_h__1_977_);
v_upperBound_980_ = lean_ctor_get(v_it_975_, 1);
lean_inc(v_upperBound_980_);
lean_dec_ref(v_it_975_);
v___x_981_ = lean_apply_2(v_h__2_978_, v_upperBound_980_, v_f_976_);
return v___x_981_;
}
else
{
lean_object* v_upperBound_982_; lean_object* v_val_983_; lean_object* v___x_984_; 
lean_inc_ref(v_next_979_);
lean_dec(v_h__2_978_);
v_upperBound_982_ = lean_ctor_get(v_it_975_, 1);
lean_inc(v_upperBound_982_);
lean_dec_ref(v_it_975_);
v_val_983_ = lean_ctor_get(v_next_979_, 0);
lean_inc(v_val_983_);
lean_dec_ref(v_next_979_);
v___x_984_ = lean_apply_3(v_h__1_977_, v_val_983_, v_upperBound_982_, v_f_976_);
return v___x_984_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_985_, lean_object* v_inst_986_, lean_object* v_inst_987_, lean_object* v_inst_988_, lean_object* v_n_989_, lean_object* v_00_u03b3_990_, lean_object* v_Pl_991_, lean_object* v_motive_992_, lean_object* v_it_993_, lean_object* v_f_994_, lean_object* v_h__1_995_, lean_object* v_h__2_996_){
_start:
{
lean_object* v_next_997_; 
v_next_997_ = lean_ctor_get(v_it_993_, 0);
if (lean_obj_tag(v_next_997_) == 0)
{
lean_object* v_upperBound_998_; lean_object* v___x_999_; 
lean_dec(v_h__1_995_);
v_upperBound_998_ = lean_ctor_get(v_it_993_, 1);
lean_inc(v_upperBound_998_);
lean_dec_ref(v_it_993_);
v___x_999_ = lean_apply_2(v_h__2_996_, v_upperBound_998_, v_f_994_);
return v___x_999_;
}
else
{
lean_object* v_upperBound_1000_; lean_object* v_val_1001_; lean_object* v___x_1002_; 
lean_inc_ref(v_next_997_);
lean_dec(v_h__2_996_);
v_upperBound_1000_ = lean_ctor_get(v_it_993_, 1);
lean_inc(v_upperBound_1000_);
lean_dec_ref(v_it_993_);
v_val_1001_ = lean_ctor_get(v_next_997_, 0);
lean_inc(v_val_1001_);
lean_dec_ref(v_next_997_);
v___x_1002_ = lean_apply_3(v_h__1_995_, v_val_1001_, v_upperBound_1000_, v_f_994_);
return v___x_1002_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_1003_, lean_object* v_inst_1004_, lean_object* v_inst_1005_, lean_object* v_inst_1006_, lean_object* v_n_1007_, lean_object* v_00_u03b3_1008_, lean_object* v_Pl_1009_, lean_object* v_motive_1010_, lean_object* v_it_1011_, lean_object* v_f_1012_, lean_object* v_h__1_1013_, lean_object* v_h__2_1014_){
_start:
{
lean_object* v_res_1015_; 
v_res_1015_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_1003_, v_inst_1004_, v_inst_1005_, v_inst_1006_, v_n_1007_, v_00_u03b3_1008_, v_Pl_1009_, v_motive_1010_, v_it_1011_, v_f_1012_, v_h__1_1013_, v_h__2_1014_);
lean_dec_ref(v_inst_1006_);
lean_dec_ref(v_inst_1004_);
return v_res_1015_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step___redArg(lean_object* v_inst_1016_, lean_object* v_it_1017_){
_start:
{
if (lean_obj_tag(v_it_1017_) == 0)
{
lean_object* v___x_1018_; 
lean_dec_ref(v_inst_1016_);
v___x_1018_ = lean_box(2);
return v___x_1018_;
}
else
{
lean_object* v_val_1019_; lean_object* v_succ_x3f_1020_; lean_object* v___x_1022_; uint8_t v_isShared_1023_; uint8_t v_isSharedCheck_1028_; 
v_val_1019_ = lean_ctor_get(v_it_1017_, 0);
lean_inc(v_val_1019_);
lean_dec_ref(v_it_1017_);
v_succ_x3f_1020_ = lean_ctor_get(v_inst_1016_, 0);
v_isSharedCheck_1028_ = !lean_is_exclusive(v_inst_1016_);
if (v_isSharedCheck_1028_ == 0)
{
lean_object* v_unused_1029_; 
v_unused_1029_ = lean_ctor_get(v_inst_1016_, 1);
lean_dec(v_unused_1029_);
v___x_1022_ = v_inst_1016_;
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
else
{
lean_inc(v_succ_x3f_1020_);
lean_dec(v_inst_1016_);
v___x_1022_ = lean_box(0);
v_isShared_1023_ = v_isSharedCheck_1028_;
goto v_resetjp_1021_;
}
v_resetjp_1021_:
{
lean_object* v___x_1024_; lean_object* v___x_1026_; 
lean_inc(v_val_1019_);
v___x_1024_ = lean_apply_1(v_succ_x3f_1020_, v_val_1019_);
if (v_isShared_1023_ == 0)
{
lean_ctor_set(v___x_1022_, 1, v_val_1019_);
lean_ctor_set(v___x_1022_, 0, v___x_1024_);
v___x_1026_ = v___x_1022_;
goto v_reusejp_1025_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v___x_1024_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_val_1019_);
v___x_1026_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1025_;
}
v_reusejp_1025_:
{
return v___x_1026_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step(lean_object* v_00_u03b1_1030_, lean_object* v_inst_1031_, lean_object* v_it_1032_){
_start:
{
if (lean_obj_tag(v_it_1032_) == 0)
{
lean_object* v___x_1033_; 
lean_dec_ref(v_inst_1031_);
v___x_1033_ = lean_box(2);
return v___x_1033_;
}
else
{
lean_object* v_val_1034_; lean_object* v_succ_x3f_1035_; lean_object* v___x_1037_; uint8_t v_isShared_1038_; uint8_t v_isSharedCheck_1043_; 
v_val_1034_ = lean_ctor_get(v_it_1032_, 0);
lean_inc(v_val_1034_);
lean_dec_ref(v_it_1032_);
v_succ_x3f_1035_ = lean_ctor_get(v_inst_1031_, 0);
v_isSharedCheck_1043_ = !lean_is_exclusive(v_inst_1031_);
if (v_isSharedCheck_1043_ == 0)
{
lean_object* v_unused_1044_; 
v_unused_1044_ = lean_ctor_get(v_inst_1031_, 1);
lean_dec(v_unused_1044_);
v___x_1037_ = v_inst_1031_;
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
else
{
lean_inc(v_succ_x3f_1035_);
lean_dec(v_inst_1031_);
v___x_1037_ = lean_box(0);
v_isShared_1038_ = v_isSharedCheck_1043_;
goto v_resetjp_1036_;
}
v_resetjp_1036_:
{
lean_object* v___x_1039_; lean_object* v___x_1041_; 
lean_inc(v_val_1034_);
v___x_1039_ = lean_apply_1(v_succ_x3f_1035_, v_val_1034_);
if (v_isShared_1038_ == 0)
{
lean_ctor_set(v___x_1037_, 1, v_val_1034_);
lean_ctor_set(v___x_1037_, 0, v___x_1039_);
v___x_1041_ = v___x_1037_;
goto v_reusejp_1040_;
}
else
{
lean_object* v_reuseFailAlloc_1042_; 
v_reuseFailAlloc_1042_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1042_, 0, v___x_1039_);
lean_ctor_set(v_reuseFailAlloc_1042_, 1, v_val_1034_);
v___x_1041_ = v_reuseFailAlloc_1042_;
goto v_reusejp_1040_;
}
v_reusejp_1040_:
{
return v___x_1041_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step___redArg(lean_object* v_inst_1045_, lean_object* v_it_1046_){
_start:
{
if (lean_obj_tag(v_it_1046_) == 0)
{
lean_object* v___x_1047_; 
lean_dec_ref(v_inst_1045_);
v___x_1047_ = lean_box(2);
return v___x_1047_;
}
else
{
lean_object* v_val_1048_; lean_object* v_succ_x3f_1049_; lean_object* v___x_1051_; uint8_t v_isShared_1052_; uint8_t v_isSharedCheck_1057_; 
v_val_1048_ = lean_ctor_get(v_it_1046_, 0);
lean_inc(v_val_1048_);
lean_dec_ref(v_it_1046_);
v_succ_x3f_1049_ = lean_ctor_get(v_inst_1045_, 0);
v_isSharedCheck_1057_ = !lean_is_exclusive(v_inst_1045_);
if (v_isSharedCheck_1057_ == 0)
{
lean_object* v_unused_1058_; 
v_unused_1058_ = lean_ctor_get(v_inst_1045_, 1);
lean_dec(v_unused_1058_);
v___x_1051_ = v_inst_1045_;
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
else
{
lean_inc(v_succ_x3f_1049_);
lean_dec(v_inst_1045_);
v___x_1051_ = lean_box(0);
v_isShared_1052_ = v_isSharedCheck_1057_;
goto v_resetjp_1050_;
}
v_resetjp_1050_:
{
lean_object* v___x_1053_; lean_object* v___x_1055_; 
lean_inc(v_val_1048_);
v___x_1053_ = lean_apply_1(v_succ_x3f_1049_, v_val_1048_);
if (v_isShared_1052_ == 0)
{
lean_ctor_set(v___x_1051_, 1, v_val_1048_);
lean_ctor_set(v___x_1051_, 0, v___x_1053_);
v___x_1055_ = v___x_1051_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1056_; 
v_reuseFailAlloc_1056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1056_, 0, v___x_1053_);
lean_ctor_set(v_reuseFailAlloc_1056_, 1, v_val_1048_);
v___x_1055_ = v_reuseFailAlloc_1056_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
return v___x_1055_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step(lean_object* v_00_u03b1_1059_, lean_object* v_inst_1060_, lean_object* v_it_1061_){
_start:
{
if (lean_obj_tag(v_it_1061_) == 0)
{
lean_object* v___x_1062_; 
lean_dec_ref(v_inst_1060_);
v___x_1062_ = lean_box(2);
return v___x_1062_;
}
else
{
lean_object* v_val_1063_; lean_object* v_succ_x3f_1064_; lean_object* v___x_1066_; uint8_t v_isShared_1067_; uint8_t v_isSharedCheck_1072_; 
v_val_1063_ = lean_ctor_get(v_it_1061_, 0);
lean_inc(v_val_1063_);
lean_dec_ref(v_it_1061_);
v_succ_x3f_1064_ = lean_ctor_get(v_inst_1060_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v_inst_1060_);
if (v_isSharedCheck_1072_ == 0)
{
lean_object* v_unused_1073_; 
v_unused_1073_ = lean_ctor_get(v_inst_1060_, 1);
lean_dec(v_unused_1073_);
v___x_1066_ = v_inst_1060_;
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
else
{
lean_inc(v_succ_x3f_1064_);
lean_dec(v_inst_1060_);
v___x_1066_ = lean_box(0);
v_isShared_1067_ = v_isSharedCheck_1072_;
goto v_resetjp_1065_;
}
v_resetjp_1065_:
{
lean_object* v___x_1068_; lean_object* v___x_1070_; 
lean_inc(v_val_1063_);
v___x_1068_ = lean_apply_1(v_succ_x3f_1064_, v_val_1063_);
if (v_isShared_1067_ == 0)
{
lean_ctor_set(v___x_1066_, 1, v_val_1063_);
lean_ctor_set(v___x_1066_, 0, v___x_1068_);
v___x_1070_ = v___x_1066_;
goto v_reusejp_1069_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v___x_1068_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_val_1063_);
v___x_1070_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1069_;
}
v_reusejp_1069_:
{
return v___x_1070_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0(lean_object* v_inst_1074_, lean_object* v_it_1075_){
_start:
{
if (lean_obj_tag(v_it_1075_) == 0)
{
lean_object* v___x_1076_; 
lean_dec_ref(v_inst_1074_);
v___x_1076_ = lean_box(2);
return v___x_1076_;
}
else
{
lean_object* v_val_1077_; lean_object* v_succ_x3f_1078_; lean_object* v___x_1080_; uint8_t v_isShared_1081_; uint8_t v_isSharedCheck_1086_; 
v_val_1077_ = lean_ctor_get(v_it_1075_, 0);
lean_inc(v_val_1077_);
lean_dec_ref(v_it_1075_);
v_succ_x3f_1078_ = lean_ctor_get(v_inst_1074_, 0);
v_isSharedCheck_1086_ = !lean_is_exclusive(v_inst_1074_);
if (v_isSharedCheck_1086_ == 0)
{
lean_object* v_unused_1087_; 
v_unused_1087_ = lean_ctor_get(v_inst_1074_, 1);
lean_dec(v_unused_1087_);
v___x_1080_ = v_inst_1074_;
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
else
{
lean_inc(v_succ_x3f_1078_);
lean_dec(v_inst_1074_);
v___x_1080_ = lean_box(0);
v_isShared_1081_ = v_isSharedCheck_1086_;
goto v_resetjp_1079_;
}
v_resetjp_1079_:
{
lean_object* v___x_1082_; lean_object* v___x_1084_; 
lean_inc(v_val_1077_);
v___x_1082_ = lean_apply_1(v_succ_x3f_1078_, v_val_1077_);
if (v_isShared_1081_ == 0)
{
lean_ctor_set(v___x_1080_, 1, v_val_1077_);
lean_ctor_set(v___x_1080_, 0, v___x_1082_);
v___x_1084_ = v___x_1080_;
goto v_reusejp_1083_;
}
else
{
lean_object* v_reuseFailAlloc_1085_; 
v_reuseFailAlloc_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1085_, 0, v___x_1082_);
lean_ctor_set(v_reuseFailAlloc_1085_, 1, v_val_1077_);
v___x_1084_ = v_reuseFailAlloc_1085_;
goto v_reusejp_1083_;
}
v_reusejp_1083_:
{
return v___x_1084_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg(lean_object* v_inst_1088_){
_start:
{
lean_object* v___f_1089_; 
v___f_1089_ = lean_alloc_closure((void*)(l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1089_, 0, v_inst_1088_);
return v___f_1089_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable(lean_object* v_00_u03b1_1090_, lean_object* v_inst_1091_){
_start:
{
lean_object* v___f_1092_; 
v___f_1092_ = lean_alloc_closure((void*)(l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1092_, 0, v_inst_1091_);
return v___f_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_1093_, lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_inst_1096_){
_start:
{
lean_object* v___x_1097_; 
v___x_1097_ = lean_box(0);
return v___x_1097_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_1098_, lean_object* v_inst_1099_, lean_object* v_inst_1100_, lean_object* v_inst_1101_){
_start:
{
lean_object* v_res_1102_; 
v_res_1102_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(v_00_u03b1_1098_, v_inst_1099_, v_inst_1100_, v_inst_1101_);
lean_dec_ref(v_inst_1099_);
return v_res_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_1103_, lean_object* v_inst_1104_, lean_object* v_inst_1105_){
_start:
{
lean_object* v___x_1106_; 
v___x_1106_ = lean_box(0);
return v___x_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_){
_start:
{
lean_object* v_res_1110_; 
v_res_1110_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(v_00_u03b1_1107_, v_inst_1108_, v_inst_1109_);
lean_dec_ref(v_inst_1108_);
return v_res_1110_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_1111_, lean_object* v_it_1112_, lean_object* v_n_1113_){
_start:
{
if (lean_obj_tag(v_it_1112_) == 0)
{
lean_object* v___x_1114_; 
lean_dec(v_n_1113_);
lean_dec_ref(v_inst_1111_);
v___x_1114_ = lean_box(2);
return v___x_1114_;
}
else
{
lean_object* v_succ_x3f_1115_; lean_object* v_succMany_x3f_1116_; lean_object* v___x_1118_; uint8_t v_isShared_1119_; uint8_t v_isSharedCheck_1128_; 
v_succ_x3f_1115_ = lean_ctor_get(v_inst_1111_, 0);
v_succMany_x3f_1116_ = lean_ctor_get(v_inst_1111_, 1);
v_isSharedCheck_1128_ = !lean_is_exclusive(v_inst_1111_);
if (v_isSharedCheck_1128_ == 0)
{
v___x_1118_ = v_inst_1111_;
v_isShared_1119_ = v_isSharedCheck_1128_;
goto v_resetjp_1117_;
}
else
{
lean_inc(v_succMany_x3f_1116_);
lean_inc(v_succ_x3f_1115_);
lean_dec(v_inst_1111_);
v___x_1118_ = lean_box(0);
v_isShared_1119_ = v_isSharedCheck_1128_;
goto v_resetjp_1117_;
}
v_resetjp_1117_:
{
lean_object* v_val_1120_; lean_object* v___x_1121_; 
v_val_1120_ = lean_ctor_get(v_it_1112_, 0);
lean_inc(v_val_1120_);
lean_dec_ref(v_it_1112_);
v___x_1121_ = lean_apply_2(v_succMany_x3f_1116_, v_n_1113_, v_val_1120_);
if (lean_obj_tag(v___x_1121_) == 0)
{
lean_object* v___x_1122_; 
lean_del_object(v___x_1118_);
lean_dec_ref(v_succ_x3f_1115_);
v___x_1122_ = lean_box(2);
return v___x_1122_;
}
else
{
lean_object* v_val_1123_; lean_object* v___x_1124_; lean_object* v___x_1126_; 
v_val_1123_ = lean_ctor_get(v___x_1121_, 0);
lean_inc_n(v_val_1123_, 2);
lean_dec_ref(v___x_1121_);
v___x_1124_ = lean_apply_1(v_succ_x3f_1115_, v_val_1123_);
if (v_isShared_1119_ == 0)
{
lean_ctor_set(v___x_1118_, 1, v_val_1123_);
lean_ctor_set(v___x_1118_, 0, v___x_1124_);
v___x_1126_ = v___x_1118_;
goto v_reusejp_1125_;
}
else
{
lean_object* v_reuseFailAlloc_1127_; 
v_reuseFailAlloc_1127_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1127_, 0, v___x_1124_);
lean_ctor_set(v_reuseFailAlloc_1127_, 1, v_val_1123_);
v___x_1126_ = v_reuseFailAlloc_1127_;
goto v_reusejp_1125_;
}
v_reusejp_1125_:
{
return v___x_1126_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg(lean_object* v_inst_1129_){
_start:
{
lean_object* v___f_1130_; 
v___f_1130_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1130_, 0, v_inst_1129_);
return v___f_1130_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess(lean_object* v_00_u03b1_1131_, lean_object* v_inst_1132_, lean_object* v_inst_1133_){
_start:
{
lean_object* v___f_1134_; 
v___f_1134_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1134_, 0, v_inst_1132_);
return v___f_1134_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object* v_toPure_1135_, lean_object* v_inst_1136_, lean_object* v_f_1137_, lean_object* v_toBind_1138_, lean_object* v_next_1139_, lean_object* v_acc_1140_, lean_object* v_h_1141_, lean_object* v_G_1142_){
_start:
{
lean_object* v___f_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
lean_inc(v_next_1139_);
v___f_1143_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1143_, 0, v_toPure_1135_);
lean_closure_set(v___f_1143_, 1, v_inst_1136_);
lean_closure_set(v___f_1143_, 2, v_next_1139_);
lean_closure_set(v___f_1143_, 3, v_G_1142_);
v___x_1144_ = lean_apply_3(v_f_1137_, v_next_1139_, lean_box(0), v_acc_1140_);
v___x_1145_ = lean_apply_4(v_toBind_1138_, lean_box(0), lean_box(0), v___x_1144_, v___f_1143_);
return v___x_1145_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_1146_, lean_object* v_inst_1147_, lean_object* v_acc_1148_, lean_object* v_next_1149_, lean_object* v_f_1150_){
_start:
{
lean_object* v_toApplicative_1151_; lean_object* v_toBind_1152_; lean_object* v_toPure_1153_; lean_object* v___f_1154_; lean_object* v___x_1155_; 
v_toApplicative_1151_ = lean_ctor_get(v_inst_1147_, 0);
lean_inc_ref(v_toApplicative_1151_);
v_toBind_1152_ = lean_ctor_get(v_inst_1147_, 1);
lean_inc(v_toBind_1152_);
lean_dec_ref(v_inst_1147_);
v_toPure_1153_ = lean_ctor_get(v_toApplicative_1151_, 1);
lean_inc(v_toPure_1153_);
lean_dec_ref(v_toApplicative_1151_);
v___f_1154_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1154_, 0, v_toPure_1153_);
lean_closure_set(v___f_1154_, 1, v_inst_1146_);
lean_closure_set(v___f_1154_, 2, v_f_1150_);
lean_closure_set(v___f_1154_, 3, v_toBind_1152_);
v___x_1155_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1154_, v_next_1149_, v_acc_1148_, lean_box(0));
return v___x_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_, lean_object* v_n_1159_, lean_object* v_inst_1160_, lean_object* v_00_u03b3_1161_, lean_object* v_Pl_1162_, lean_object* v_LargeEnough_1163_, lean_object* v_hl_1164_, lean_object* v_acc_1165_, lean_object* v_next_1166_, lean_object* v_h_1167_, lean_object* v_f_1168_){
_start:
{
lean_object* v_toApplicative_1169_; lean_object* v_toBind_1170_; lean_object* v_toPure_1171_; lean_object* v___f_1172_; lean_object* v___x_1173_; 
v_toApplicative_1169_ = lean_ctor_get(v_inst_1160_, 0);
lean_inc_ref(v_toApplicative_1169_);
v_toBind_1170_ = lean_ctor_get(v_inst_1160_, 1);
lean_inc(v_toBind_1170_);
lean_dec_ref(v_inst_1160_);
v_toPure_1171_ = lean_ctor_get(v_toApplicative_1169_, 1);
lean_inc(v_toPure_1171_);
lean_dec_ref(v_toApplicative_1169_);
v___f_1172_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1172_, 0, v_toPure_1171_);
lean_closure_set(v___f_1172_, 1, v_inst_1157_);
lean_closure_set(v___f_1172_, 2, v_f_1168_);
lean_closure_set(v___f_1172_, 3, v_toBind_1170_);
v___x_1173_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1172_, v_next_1166_, v_acc_1165_, lean_box(0));
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_1174_, lean_object* v_inst_1175_, lean_object* v_toBind_1176_, lean_object* v_x_1177_, lean_object* v_00_u03b3_1178_, lean_object* v_Pl_1179_, lean_object* v_it_1180_, lean_object* v_init_1181_, lean_object* v_f_1182_){
_start:
{
if (lean_obj_tag(v_it_1180_) == 0)
{
lean_object* v___x_1183_; 
lean_dec(v_f_1182_);
lean_dec(v_toBind_1176_);
lean_dec_ref(v_inst_1175_);
v___x_1183_ = lean_apply_2(v_toPure_1174_, lean_box(0), v_init_1181_);
return v___x_1183_;
}
else
{
lean_object* v_val_1184_; lean_object* v___f_1185_; lean_object* v___x_1186_; 
v_val_1184_ = lean_ctor_get(v_it_1180_, 0);
lean_inc(v_val_1184_);
lean_dec_ref(v_it_1180_);
v___f_1185_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1185_, 0, v_toPure_1174_);
lean_closure_set(v___f_1185_, 1, v_inst_1175_);
lean_closure_set(v___f_1185_, 2, v_f_1182_);
lean_closure_set(v___f_1185_, 3, v_toBind_1176_);
v___x_1186_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1185_, v_val_1184_, v_init_1181_, lean_box(0));
return v___x_1186_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_1187_, lean_object* v_inst_1188_, lean_object* v_toBind_1189_, lean_object* v_x_1190_, lean_object* v_00_u03b3_1191_, lean_object* v_Pl_1192_, lean_object* v_it_1193_, lean_object* v_init_1194_, lean_object* v_f_1195_){
_start:
{
lean_object* v_res_1196_; 
v_res_1196_ = l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_1187_, v_inst_1188_, v_toBind_1189_, v_x_1190_, v_00_u03b3_1191_, v_Pl_1192_, v_it_1193_, v_init_1194_, v_f_1195_);
lean_dec(v_x_1190_);
return v_res_1196_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg(lean_object* v_inst_1197_, lean_object* v_inst_1198_){
_start:
{
lean_object* v_toApplicative_1199_; lean_object* v_toBind_1200_; lean_object* v_toPure_1201_; lean_object* v___f_1202_; 
v_toApplicative_1199_ = lean_ctor_get(v_inst_1198_, 0);
lean_inc_ref(v_toApplicative_1199_);
v_toBind_1200_ = lean_ctor_get(v_inst_1198_, 1);
lean_inc(v_toBind_1200_);
lean_dec_ref(v_inst_1198_);
v_toPure_1201_ = lean_ctor_get(v_toApplicative_1199_, 1);
lean_inc(v_toPure_1201_);
lean_dec_ref(v_toApplicative_1199_);
v___f_1202_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1202_, 0, v_toPure_1201_);
lean_closure_set(v___f_1202_, 1, v_inst_1197_);
lean_closure_set(v___f_1202_, 2, v_toBind_1200_);
return v___f_1202_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop(lean_object* v_00_u03b1_1203_, lean_object* v_inst_1204_, lean_object* v_inst_1205_, lean_object* v_n_1206_, lean_object* v_inst_1207_){
_start:
{
lean_object* v_toApplicative_1208_; lean_object* v_toBind_1209_; lean_object* v_toPure_1210_; lean_object* v___f_1211_; 
v_toApplicative_1208_ = lean_ctor_get(v_inst_1207_, 0);
lean_inc_ref(v_toApplicative_1208_);
v_toBind_1209_ = lean_ctor_get(v_inst_1207_, 1);
lean_inc(v_toBind_1209_);
lean_dec_ref(v_inst_1207_);
v_toPure_1210_ = lean_ctor_get(v_toApplicative_1208_, 1);
lean_inc(v_toPure_1210_);
lean_dec_ref(v_toApplicative_1208_);
v___f_1211_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1211_, 0, v_toPure_1210_);
lean_closure_set(v___f_1211_, 1, v_inst_1204_);
lean_closure_set(v___f_1211_, 2, v_toBind_1209_);
return v___f_1211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_1212_, lean_object* v_f_1213_, lean_object* v_h__1_1214_, lean_object* v_h__2_1215_){
_start:
{
if (lean_obj_tag(v_it_1212_) == 0)
{
lean_object* v___x_1216_; 
lean_dec(v_h__1_1214_);
v___x_1216_ = lean_apply_1(v_h__2_1215_, v_f_1213_);
return v___x_1216_;
}
else
{
lean_object* v_val_1217_; lean_object* v___x_1218_; 
lean_dec(v_h__2_1215_);
v_val_1217_ = lean_ctor_get(v_it_1212_, 0);
lean_inc(v_val_1217_);
lean_dec_ref(v_it_1212_);
v___x_1218_ = lean_apply_2(v_h__1_1214_, v_val_1217_, v_f_1213_);
return v___x_1218_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_1219_, lean_object* v_inst_1220_, lean_object* v_n_1221_, lean_object* v_00_u03b3_1222_, lean_object* v_Pl_1223_, lean_object* v_motive_1224_, lean_object* v_it_1225_, lean_object* v_f_1226_, lean_object* v_h__1_1227_, lean_object* v_h__2_1228_){
_start:
{
if (lean_obj_tag(v_it_1225_) == 0)
{
lean_object* v___x_1229_; 
lean_dec(v_h__1_1227_);
v___x_1229_ = lean_apply_1(v_h__2_1228_, v_f_1226_);
return v___x_1229_;
}
else
{
lean_object* v_val_1230_; lean_object* v___x_1231_; 
lean_dec(v_h__2_1228_);
v_val_1230_ = lean_ctor_get(v_it_1225_, 0);
lean_inc(v_val_1230_);
lean_dec_ref(v_it_1225_);
v___x_1231_ = lean_apply_2(v_h__1_1227_, v_val_1230_, v_f_1226_);
return v___x_1231_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_1232_, lean_object* v_inst_1233_, lean_object* v_n_1234_, lean_object* v_00_u03b3_1235_, lean_object* v_Pl_1236_, lean_object* v_motive_1237_, lean_object* v_it_1238_, lean_object* v_f_1239_, lean_object* v_h__1_1240_, lean_object* v_h__2_1241_){
_start:
{
lean_object* v_res_1242_; 
v_res_1242_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_1232_, v_inst_1233_, v_n_1234_, v_00_u03b3_1235_, v_Pl_1236_, v_motive_1237_, v_it_1238_, v_f_1239_, v_h__1_1240_, v_h__2_1241_);
lean_dec_ref(v_inst_1233_);
return v_res_1242_;
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
