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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___redArg___boxed(lean_object*);
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
lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
return v___x_195_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_196_;
v_res_196_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___redArg();
stack->m_obj
 = v_res_196_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_197_){
_start:
{
lean_object* v_res_198_; 
v_res_198_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___redArg();
return v_res_198_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_inst_203_, lean_object* v_inst_204_){
_start:
{
lean_object* v___x_205_; 
v___x_205_ = lean_box(0);
return v___x_205_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_inst_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(v_00_u03b1_206_, v_inst_207_, v_inst_208_, v_inst_209_, v_inst_210_, v_inst_211_);
lean_dec_ref(v_inst_209_);
lean_dec_ref(v_inst_207_);
return v_res_212_;
}
}
lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(0);
return v___x_214_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_215_;
v_res_215_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___redArg();
stack->m_obj
 = v_res_215_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___redArg();
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_218_, lean_object* v_inst_219_, lean_object* v_inst_220_, lean_object* v_inst_221_, lean_object* v_inst_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(0);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_224_, lean_object* v_inst_225_, lean_object* v_inst_226_, lean_object* v_inst_227_, lean_object* v_inst_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(v_00_u03b1_224_, v_inst_225_, v_inst_226_, v_inst_227_, v_inst_228_);
lean_dec_ref(v_inst_227_);
lean_dec_ref(v_inst_225_);
return v_res_229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter___redArg(lean_object* v_x_230_, lean_object* v_h__1_231_, lean_object* v_h__2_232_){
_start:
{
if (lean_obj_tag(v_x_230_) == 0)
{
lean_object* v___x_233_; lean_object* v___x_234_; 
lean_dec(v_h__2_232_);
v___x_233_ = lean_box(0);
v___x_234_ = lean_apply_1(v_h__1_231_, v___x_233_);
return v___x_234_;
}
else
{
lean_object* v_val_235_; lean_object* v___x_236_; 
lean_dec(v_h__1_231_);
v_val_235_ = lean_ctor_get(v_x_230_, 0);
lean_inc(v_val_235_);
lean_dec_ref_known(v_x_230_, 1);
v___x_236_ = lean_apply_1(v_h__2_232_, v_val_235_);
return v___x_236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter(lean_object* v_00_u03b1_237_, lean_object* v_motive_238_, lean_object* v_x_239_, lean_object* v_h__1_240_, lean_object* v_h__2_241_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
lean_object* v___x_242_; lean_object* v___x_243_; 
lean_dec(v_h__2_241_);
v___x_242_ = lean_box(0);
v___x_243_ = lean_apply_1(v_h__1_240_, v___x_242_);
return v___x_243_;
}
else
{
lean_object* v_val_244_; lean_object* v___x_245_; 
lean_dec(v_h__1_240_);
v_val_244_ = lean_ctor_get(v_x_239_, 0);
lean_inc(v_val_244_);
lean_dec_ref_known(v_x_239_, 1);
v___x_245_ = lean_apply_1(v_h__2_241_, v_val_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_246_, lean_object* v_inst_247_, lean_object* v_it_248_, lean_object* v_n_249_){
_start:
{
lean_object* v_next_250_; 
v_next_250_ = lean_ctor_get(v_it_248_, 0);
lean_inc(v_next_250_);
if (lean_obj_tag(v_next_250_) == 0)
{
lean_object* v___x_251_; 
lean_dec(v_n_249_);
lean_dec_ref(v_it_248_);
lean_dec_ref(v_inst_247_);
lean_dec_ref(v_inst_246_);
v___x_251_ = lean_box(2);
return v___x_251_;
}
else
{
lean_object* v_upperBound_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_276_; 
v_upperBound_252_ = lean_ctor_get(v_it_248_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_it_248_);
if (v_isSharedCheck_276_ == 0)
{
lean_object* v_unused_277_; 
v_unused_277_ = lean_ctor_get(v_it_248_, 0);
lean_dec(v_unused_277_);
v___x_254_ = v_it_248_;
v_isShared_255_ = v_isSharedCheck_276_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_upperBound_252_);
lean_dec(v_it_248_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_276_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_succ_x3f_256_; lean_object* v_succMany_x3f_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_275_; 
v_succ_x3f_256_ = lean_ctor_get(v_inst_246_, 0);
v_succMany_x3f_257_ = lean_ctor_get(v_inst_246_, 1);
v_isSharedCheck_275_ = !lean_is_exclusive(v_inst_246_);
if (v_isSharedCheck_275_ == 0)
{
v___x_259_ = v_inst_246_;
v_isShared_260_ = v_isSharedCheck_275_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_succMany_x3f_257_);
lean_inc(v_succ_x3f_256_);
lean_dec(v_inst_246_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_275_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v_val_261_; lean_object* v___x_262_; 
v_val_261_ = lean_ctor_get(v_next_250_, 0);
lean_inc(v_val_261_);
lean_dec_ref_known(v_next_250_, 1);
v___x_262_ = lean_apply_2(v_succMany_x3f_257_, v_n_249_, v_val_261_);
if (lean_obj_tag(v___x_262_) == 0)
{
lean_object* v___x_263_; 
lean_del_object(v___x_259_);
lean_dec_ref(v_succ_x3f_256_);
lean_del_object(v___x_254_);
lean_dec(v_upperBound_252_);
lean_dec_ref(v_inst_247_);
v___x_263_ = lean_box(2);
return v___x_263_;
}
else
{
lean_object* v_val_264_; lean_object* v___x_265_; uint8_t v___x_266_; 
v_val_264_ = lean_ctor_get(v___x_262_, 0);
lean_inc_n(v_val_264_, 2);
lean_dec_ref_known(v___x_262_, 1);
lean_inc(v_upperBound_252_);
v___x_265_ = lean_apply_2(v_inst_247_, v_val_264_, v_upperBound_252_);
v___x_266_ = lean_unbox(v___x_265_);
if (v___x_266_ == 0)
{
lean_object* v___x_267_; 
lean_dec(v_val_264_);
lean_del_object(v___x_259_);
lean_dec_ref(v_succ_x3f_256_);
lean_del_object(v___x_254_);
lean_dec(v_upperBound_252_);
v___x_267_ = lean_box(2);
return v___x_267_;
}
else
{
lean_object* v___x_268_; lean_object* v___x_270_; 
lean_inc(v_val_264_);
v___x_268_ = lean_apply_1(v_succ_x3f_256_, v_val_264_);
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 0, v___x_268_);
v___x_270_ = v___x_254_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_274_; 
v_reuseFailAlloc_274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_274_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_274_, 1, v_upperBound_252_);
v___x_270_ = v_reuseFailAlloc_274_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
lean_object* v___x_272_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 1, v_val_264_);
lean_ctor_set(v___x_259_, 0, v___x_270_);
v___x_272_ = v___x_259_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_273_; 
v_reuseFailAlloc_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_273_, 0, v___x_270_);
lean_ctor_set(v_reuseFailAlloc_273_, 1, v_val_264_);
v___x_272_ = v_reuseFailAlloc_273_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
return v___x_272_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess___redArg(lean_object* v_inst_278_, lean_object* v_inst_279_){
_start:
{
lean_object* v___f_280_; 
v___f_280_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_280_, 0, v_inst_278_);
lean_closure_set(v___f_280_, 1, v_inst_279_);
return v___f_280_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess(lean_object* v_00_u03b1_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_inst_284_, lean_object* v_inst_285_, lean_object* v_inst_286_){
_start:
{
lean_object* v___f_287_; 
v___f_287_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_287_, 0, v_inst_282_);
lean_closure_set(v___f_287_, 1, v_inst_284_);
return v___f_287_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0(lean_object* v_toPure_288_, lean_object* v_inst_289_, lean_object* v_next_290_, lean_object* v_G_291_, lean_object* v_____do__lift_292_){
_start:
{
if (lean_obj_tag(v_____do__lift_292_) == 0)
{
lean_object* v_a_293_; lean_object* v___x_294_; 
lean_dec(v_G_291_);
lean_dec(v_next_290_);
lean_dec_ref(v_inst_289_);
v_a_293_ = lean_ctor_get(v_____do__lift_292_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v_____do__lift_292_, 1);
v___x_294_ = lean_apply_2(v_toPure_288_, lean_box(0), v_a_293_);
return v___x_294_;
}
else
{
lean_object* v_a_295_; lean_object* v_succ_x3f_296_; lean_object* v___x_297_; 
v_a_295_ = lean_ctor_get(v_____do__lift_292_, 0);
lean_inc(v_a_295_);
lean_dec_ref_known(v_____do__lift_292_, 1);
v_succ_x3f_296_ = lean_ctor_get(v_inst_289_, 0);
lean_inc_ref(v_succ_x3f_296_);
lean_dec_ref(v_inst_289_);
v___x_297_ = lean_apply_1(v_succ_x3f_296_, v_next_290_);
if (lean_obj_tag(v___x_297_) == 0)
{
lean_object* v___x_298_; 
lean_dec(v_G_291_);
v___x_298_ = lean_apply_2(v_toPure_288_, lean_box(0), v_a_295_);
return v___x_298_;
}
else
{
lean_object* v_val_299_; lean_object* v___x_300_; 
lean_dec(v_toPure_288_);
v_val_299_ = lean_ctor_get(v___x_297_, 0);
lean_inc(v_val_299_);
lean_dec_ref_known(v___x_297_, 1);
v___x_300_ = lean_apply_4(v_G_291_, v_val_299_, v_a_295_, lean_box(0), lean_box(0));
return v___x_300_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object* v_inst_301_, lean_object* v_upperBound_302_, lean_object* v_toPure_303_, lean_object* v_inst_304_, lean_object* v_f_305_, lean_object* v_toBind_306_, lean_object* v_next_307_, lean_object* v_acc_308_, lean_object* v_h_309_, lean_object* v_G_310_){
_start:
{
lean_object* v___x_311_; uint8_t v___x_312_; 
lean_inc(v_next_307_);
v___x_311_ = lean_apply_2(v_inst_301_, v_next_307_, v_upperBound_302_);
v___x_312_ = lean_unbox(v___x_311_);
if (v___x_312_ == 0)
{
lean_object* v___x_313_; 
lean_dec(v_G_310_);
lean_dec(v_next_307_);
lean_dec(v_toBind_306_);
lean_dec(v_f_305_);
lean_dec_ref(v_inst_304_);
v___x_313_ = lean_apply_2(v_toPure_303_, lean_box(0), v_acc_308_);
return v___x_313_;
}
else
{
lean_object* v___f_314_; lean_object* v___x_315_; lean_object* v___x_316_; 
lean_inc(v_next_307_);
v___f_314_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_314_, 0, v_toPure_303_);
lean_closure_set(v___f_314_, 1, v_inst_304_);
lean_closure_set(v___f_314_, 2, v_next_307_);
lean_closure_set(v___f_314_, 3, v_G_310_);
v___x_315_ = lean_apply_4(v_f_305_, v_next_307_, lean_box(0), lean_box(0), v_acc_308_);
v___x_316_ = lean_apply_4(v_toBind_306_, lean_box(0), lean_box(0), v___x_315_, v___f_314_);
return v___x_316_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_317_, lean_object* v_inst_318_, lean_object* v_inst_319_, lean_object* v_upperBound_320_, lean_object* v_acc_321_, lean_object* v_next_322_, lean_object* v_f_323_){
_start:
{
lean_object* v_toApplicative_324_; lean_object* v_toBind_325_; lean_object* v_toPure_326_; lean_object* v___f_327_; lean_object* v___x_328_; 
v_toApplicative_324_ = lean_ctor_get(v_inst_319_, 0);
lean_inc_ref(v_toApplicative_324_);
v_toBind_325_ = lean_ctor_get(v_inst_319_, 1);
lean_inc(v_toBind_325_);
lean_dec_ref(v_inst_319_);
v_toPure_326_ = lean_ctor_get(v_toApplicative_324_, 1);
lean_inc(v_toPure_326_);
lean_dec_ref(v_toApplicative_324_);
v___f_327_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_327_, 0, v_inst_318_);
lean_closure_set(v___f_327_, 1, v_upperBound_320_);
lean_closure_set(v___f_327_, 2, v_toPure_326_);
lean_closure_set(v___f_327_, 3, v_inst_317_);
lean_closure_set(v___f_327_, 4, v_f_323_);
lean_closure_set(v___f_327_, 5, v_toBind_325_);
v___x_328_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_327_, v_next_322_, v_acc_321_, lean_box(0));
return v___x_328_;
}
}
lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_inst_333_, lean_object* v_inst_334_, lean_object* v_n_335_, lean_object* v_inst_336_, lean_object* v_00_u03b3_337_, lean_object* v_Pl_338_, lean_object* v_LargeEnough_339_, lean_object* v_hl_340_, lean_object* v_upperBound_341_, lean_object* v_acc_342_, lean_object* v_next_343_, lean_object* v_h_344_, lean_object* v_f_345_){
_start:
{
lean_object* v_toApplicative_346_; lean_object* v_toBind_347_; lean_object* v_toPure_348_; lean_object* v___f_349_; lean_object* v___x_350_; 
v_toApplicative_346_ = lean_ctor_get(v_inst_336_, 0);
lean_inc_ref(v_toApplicative_346_);
v_toBind_347_ = lean_ctor_get(v_inst_336_, 1);
lean_inc(v_toBind_347_);
lean_dec_ref(v_inst_336_);
v_toPure_348_ = lean_ctor_get(v_toApplicative_346_, 1);
lean_inc(v_toPure_348_);
lean_dec_ref(v_toApplicative_346_);
v___f_349_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_349_, 0, v_inst_332_);
lean_closure_set(v___f_349_, 1, v_upperBound_341_);
lean_closure_set(v___f_349_, 2, v_toPure_348_);
lean_closure_set(v___f_349_, 3, v_inst_330_);
lean_closure_set(v___f_349_, 4, v_f_345_);
lean_closure_set(v___f_349_, 5, v_toBind_347_);
v___x_350_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_349_, v_next_343_, v_acc_342_, lean_box(0));
return v___x_350_;
}
}
LEAN_EXPORT void l_Std_Rxc_Iterator_instIteratorLoop_loop_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_330_ = stack[1].m_obj;
lean_object* v_inst_331_ = stack[2].m_obj;
lean_object* v_inst_332_ = stack[3].m_obj;
lean_object* v_inst_336_ = stack[7].m_obj;
lean_object* v_upperBound_341_ = stack[12].m_obj;
lean_object* v_acc_342_ = stack[13].m_obj;
lean_object* v_next_343_ = stack[14].m_obj;
lean_object* v_f_345_ = stack[16].m_obj;
lean_object* v_res_351_;
v_res_351_ = l_Std_Rxc_Iterator_instIteratorLoop_loop(lean_box(0), v_inst_330_, v_inst_331_, v_inst_332_, lean_box(0), lean_box(0), lean_box(0), v_inst_336_, lean_box(0), lean_box(0), lean_box(0), lean_box(0), v_upperBound_341_, v_acc_342_, v_next_343_, lean_box(0), v_f_345_);
stack->m_obj
 = v_res_351_;
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_352_ = _args[0];
lean_object* v_inst_353_ = _args[1];
lean_object* v_inst_354_ = _args[2];
lean_object* v_inst_355_ = _args[3];
lean_object* v_inst_356_ = _args[4];
lean_object* v_inst_357_ = _args[5];
lean_object* v_n_358_ = _args[6];
lean_object* v_inst_359_ = _args[7];
lean_object* v_00_u03b3_360_ = _args[8];
lean_object* v_Pl_361_ = _args[9];
lean_object* v_LargeEnough_362_ = _args[10];
lean_object* v_hl_363_ = _args[11];
lean_object* v_upperBound_364_ = _args[12];
lean_object* v_acc_365_ = _args[13];
lean_object* v_next_366_ = _args[14];
lean_object* v_h_367_ = _args[15];
lean_object* v_f_368_ = _args[16];
_start:
{
lean_object* v_res_369_; 
v_res_369_ = l_Std_Rxc_Iterator_instIteratorLoop_loop(v_00_u03b1_352_, v_inst_353_, v_inst_354_, v_inst_355_, v_inst_356_, v_inst_357_, v_n_358_, v_inst_359_, v_00_u03b3_360_, v_Pl_361_, v_LargeEnough_362_, v_hl_363_, v_upperBound_364_, v_acc_365_, v_next_366_, v_h_367_, v_f_368_);
return v_res_369_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1(lean_object* v_inst_370_, lean_object* v_upperBound_371_, lean_object* v_toPure_372_, lean_object* v_inst_373_, lean_object* v_f_374_, lean_object* v_toBind_375_, lean_object* v_next_376_, lean_object* v_acc_377_, lean_object* v_h_378_, lean_object* v_G_379_){
_start:
{
lean_object* v___x_380_; uint8_t v___x_381_; 
lean_inc(v_next_376_);
v___x_380_ = lean_apply_2(v_inst_370_, v_next_376_, v_upperBound_371_);
v___x_381_ = lean_unbox(v___x_380_);
if (v___x_381_ == 0)
{
lean_object* v___x_382_; 
lean_dec(v_G_379_);
lean_dec(v_next_376_);
lean_dec(v_toBind_375_);
lean_dec(v_f_374_);
lean_dec_ref(v_inst_373_);
v___x_382_ = lean_apply_2(v_toPure_372_, lean_box(0), v_acc_377_);
return v___x_382_;
}
else
{
lean_object* v___f_383_; lean_object* v___x_384_; lean_object* v___x_385_; 
lean_inc(v_next_376_);
v___f_383_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_383_, 0, v_toPure_372_);
lean_closure_set(v___f_383_, 1, v_inst_373_);
lean_closure_set(v___f_383_, 2, v_next_376_);
lean_closure_set(v___f_383_, 3, v_G_379_);
v___x_384_ = lean_apply_3(v_f_374_, v_next_376_, lean_box(0), v_acc_377_);
v___x_385_ = lean_apply_4(v_toBind_375_, lean_box(0), lean_box(0), v___x_384_, v___f_383_);
return v___x_385_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_386_, lean_object* v_inst_387_, lean_object* v_inst_388_, lean_object* v_toBind_389_, lean_object* v_x_390_, lean_object* v_00_u03b3_391_, lean_object* v_Pl_392_, lean_object* v_it_393_, lean_object* v_init_394_, lean_object* v_f_395_){
_start:
{
lean_object* v_next_396_; 
v_next_396_ = lean_ctor_get(v_it_393_, 0);
lean_inc(v_next_396_);
if (lean_obj_tag(v_next_396_) == 0)
{
lean_object* v___x_397_; 
lean_dec(v_f_395_);
lean_dec_ref(v_it_393_);
lean_dec(v_toBind_389_);
lean_dec_ref(v_inst_388_);
lean_dec_ref(v_inst_387_);
v___x_397_ = lean_apply_2(v_toPure_386_, lean_box(0), v_init_394_);
return v___x_397_;
}
else
{
lean_object* v_upperBound_398_; lean_object* v_val_399_; lean_object* v___f_400_; lean_object* v___x_401_; 
v_upperBound_398_ = lean_ctor_get(v_it_393_, 1);
lean_inc(v_upperBound_398_);
lean_dec_ref(v_it_393_);
v_val_399_ = lean_ctor_get(v_next_396_, 0);
lean_inc(v_val_399_);
lean_dec_ref_known(v_next_396_, 1);
v___f_400_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_400_, 0, v_inst_387_);
lean_closure_set(v___f_400_, 1, v_upperBound_398_);
lean_closure_set(v___f_400_, 2, v_toPure_386_);
lean_closure_set(v___f_400_, 3, v_inst_388_);
lean_closure_set(v___f_400_, 4, v_f_395_);
lean_closure_set(v___f_400_, 5, v_toBind_389_);
v___x_401_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_400_, v_val_399_, v_init_394_, lean_box(0));
return v___x_401_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0___boxed(lean_object* v_toPure_402_, lean_object* v_inst_403_, lean_object* v_inst_404_, lean_object* v_toBind_405_, lean_object* v_x_406_, lean_object* v_00_u03b3_407_, lean_object* v_Pl_408_, lean_object* v_it_409_, lean_object* v_init_410_, lean_object* v_f_411_){
_start:
{
lean_object* v_res_412_; 
v_res_412_ = l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0(v_toPure_402_, v_inst_403_, v_inst_404_, v_toBind_405_, v_x_406_, v_00_u03b3_407_, v_Pl_408_, v_it_409_, v_init_410_, v_f_411_);
lean_dec(v_x_406_);
return v_res_412_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg(lean_object* v_inst_413_, lean_object* v_inst_414_, lean_object* v_inst_415_){
_start:
{
lean_object* v_toApplicative_416_; lean_object* v_toBind_417_; lean_object* v_toPure_418_; lean_object* v___f_419_; 
v_toApplicative_416_ = lean_ctor_get(v_inst_415_, 0);
lean_inc_ref(v_toApplicative_416_);
v_toBind_417_ = lean_ctor_get(v_inst_415_, 1);
lean_inc(v_toBind_417_);
lean_dec_ref(v_inst_415_);
v_toPure_418_ = lean_ctor_get(v_toApplicative_416_, 1);
lean_inc(v_toPure_418_);
lean_dec_ref(v_toApplicative_416_);
v___f_419_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_419_, 0, v_toPure_418_);
lean_closure_set(v___f_419_, 1, v_inst_414_);
lean_closure_set(v___f_419_, 2, v_inst_413_);
lean_closure_set(v___f_419_, 3, v_toBind_417_);
return v___f_419_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop(lean_object* v_00_u03b1_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_inst_423_, lean_object* v_inst_424_, lean_object* v_inst_425_, lean_object* v_n_426_, lean_object* v_inst_427_){
_start:
{
lean_object* v_toApplicative_428_; lean_object* v_toBind_429_; lean_object* v_toPure_430_; lean_object* v___f_431_; 
v_toApplicative_428_ = lean_ctor_get(v_inst_427_, 0);
lean_inc_ref(v_toApplicative_428_);
v_toBind_429_ = lean_ctor_get(v_inst_427_, 1);
lean_inc(v_toBind_429_);
lean_dec_ref(v_inst_427_);
v_toPure_430_ = lean_ctor_get(v_toApplicative_428_, 1);
lean_inc(v_toPure_430_);
lean_dec_ref(v_toApplicative_428_);
v___f_431_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_431_, 0, v_toPure_430_);
lean_closure_set(v___f_431_, 1, v_inst_423_);
lean_closure_set(v___f_431_, 2, v_inst_421_);
lean_closure_set(v___f_431_, 3, v_toBind_429_);
return v___f_431_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___redArg(lean_object* v_____do__lift_432_, lean_object* v_h__1_433_, lean_object* v_h__2_434_){
_start:
{
if (lean_obj_tag(v_____do__lift_432_) == 0)
{
lean_object* v_a_435_; lean_object* v___x_436_; 
lean_dec(v_h__1_433_);
v_a_435_ = lean_ctor_get(v_____do__lift_432_, 0);
lean_inc(v_a_435_);
lean_dec_ref_known(v_____do__lift_432_, 1);
v___x_436_ = lean_apply_2(v_h__2_434_, v_a_435_, lean_box(0));
return v___x_436_;
}
else
{
lean_object* v_a_437_; lean_object* v___x_438_; 
lean_dec(v_h__2_434_);
v_a_437_ = lean_ctor_get(v_____do__lift_432_, 0);
lean_inc(v_a_437_);
lean_dec_ref_known(v_____do__lift_432_, 1);
v___x_438_ = lean_apply_2(v_h__1_433_, v_a_437_, lean_box(0));
return v___x_438_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(lean_object* v_00_u03b1_439_, lean_object* v_00_u03b3_440_, lean_object* v_Pl_441_, lean_object* v_acc_442_, lean_object* v_next_443_, lean_object* v_motive_444_, lean_object* v_____do__lift_445_, lean_object* v_h__1_446_, lean_object* v_h__2_447_){
_start:
{
if (lean_obj_tag(v_____do__lift_445_) == 0)
{
lean_object* v_a_448_; lean_object* v___x_449_; 
lean_dec(v_h__1_446_);
v_a_448_ = lean_ctor_get(v_____do__lift_445_, 0);
lean_inc(v_a_448_);
lean_dec_ref_known(v_____do__lift_445_, 1);
v___x_449_ = lean_apply_2(v_h__2_447_, v_a_448_, lean_box(0));
return v___x_449_;
}
else
{
lean_object* v_a_450_; lean_object* v___x_451_; 
lean_dec(v_h__2_447_);
v_a_450_ = lean_ctor_get(v_____do__lift_445_, 0);
lean_inc(v_a_450_);
lean_dec_ref_known(v_____do__lift_445_, 1);
v___x_451_ = lean_apply_2(v_h__1_446_, v_a_450_, lean_box(0));
return v___x_451_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___boxed(lean_object* v_00_u03b1_452_, lean_object* v_00_u03b3_453_, lean_object* v_Pl_454_, lean_object* v_acc_455_, lean_object* v_next_456_, lean_object* v_motive_457_, lean_object* v_____do__lift_458_, lean_object* v_h__1_459_, lean_object* v_h__2_460_){
_start:
{
lean_object* v_res_461_; 
v_res_461_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(v_00_u03b1_452_, v_00_u03b3_453_, v_Pl_454_, v_acc_455_, v_next_456_, v_motive_457_, v_____do__lift_458_, v_h__1_459_, v_h__2_460_);
lean_dec(v_next_456_);
lean_dec(v_acc_455_);
return v_res_461_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter___redArg(lean_object* v_x_462_, lean_object* v_h__1_463_, lean_object* v_h__2_464_){
_start:
{
if (lean_obj_tag(v_x_462_) == 0)
{
lean_object* v___x_465_; 
lean_dec(v_h__1_463_);
v___x_465_ = lean_apply_1(v_h__2_464_, lean_box(0));
return v___x_465_;
}
else
{
lean_object* v_val_466_; lean_object* v___x_467_; 
lean_dec(v_h__2_464_);
v_val_466_ = lean_ctor_get(v_x_462_, 0);
lean_inc(v_val_466_);
lean_dec_ref_known(v_x_462_, 1);
v___x_467_ = lean_apply_2(v_h__1_463_, v_val_466_, lean_box(0));
return v___x_467_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter(lean_object* v_00_u03b1_468_, lean_object* v_motive_469_, lean_object* v_x_470_, lean_object* v_h__1_471_, lean_object* v_h__2_472_){
_start:
{
if (lean_obj_tag(v_x_470_) == 0)
{
lean_object* v___x_473_; 
lean_dec(v_h__1_471_);
v___x_473_ = lean_apply_1(v_h__2_472_, lean_box(0));
return v___x_473_;
}
else
{
lean_object* v_val_474_; lean_object* v___x_475_; 
lean_dec(v_h__2_472_);
v_val_474_ = lean_ctor_get(v_x_470_, 0);
lean_inc(v_val_474_);
lean_dec_ref_known(v_x_470_, 1);
v___x_475_ = lean_apply_2(v_h__1_471_, v_val_474_, lean_box(0));
return v___x_475_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___redArg(lean_object* v_____do__lift_476_, lean_object* v_h__1_477_, lean_object* v_h__2_478_){
_start:
{
if (lean_obj_tag(v_____do__lift_476_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
lean_dec(v_h__1_477_);
v_a_479_ = lean_ctor_get(v_____do__lift_476_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v_____do__lift_476_, 1);
v___x_480_ = lean_apply_2(v_h__2_478_, v_a_479_, lean_box(0));
return v___x_480_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_482_; 
lean_dec(v_h__2_478_);
v_a_481_ = lean_ctor_get(v_____do__lift_476_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_____do__lift_476_, 1);
v___x_482_ = lean_apply_2(v_h__1_477_, v_a_481_, lean_box(0));
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(lean_object* v_00_u03b1_483_, lean_object* v_00_u03b3_484_, lean_object* v_Pl_485_, lean_object* v_next_486_, lean_object* v_acc_487_, lean_object* v_motive_488_, lean_object* v_____do__lift_489_, lean_object* v_h__1_490_, lean_object* v_h__2_491_){
_start:
{
if (lean_obj_tag(v_____do__lift_489_) == 0)
{
lean_object* v_a_492_; lean_object* v___x_493_; 
lean_dec(v_h__1_490_);
v_a_492_ = lean_ctor_get(v_____do__lift_489_, 0);
lean_inc(v_a_492_);
lean_dec_ref_known(v_____do__lift_489_, 1);
v___x_493_ = lean_apply_2(v_h__2_491_, v_a_492_, lean_box(0));
return v___x_493_;
}
else
{
lean_object* v_a_494_; lean_object* v___x_495_; 
lean_dec(v_h__2_491_);
v_a_494_ = lean_ctor_get(v_____do__lift_489_, 0);
lean_inc(v_a_494_);
lean_dec_ref_known(v_____do__lift_489_, 1);
v___x_495_ = lean_apply_2(v_h__1_490_, v_a_494_, lean_box(0));
return v___x_495_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_496_, lean_object* v_00_u03b3_497_, lean_object* v_Pl_498_, lean_object* v_next_499_, lean_object* v_acc_500_, lean_object* v_motive_501_, lean_object* v_____do__lift_502_, lean_object* v_h__1_503_, lean_object* v_h__2_504_){
_start:
{
lean_object* v_res_505_; 
v_res_505_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(v_00_u03b1_496_, v_00_u03b3_497_, v_Pl_498_, v_next_499_, v_acc_500_, v_motive_501_, v_____do__lift_502_, v_h__1_503_, v_h__2_504_);
lean_dec(v_acc_500_);
lean_dec(v_next_499_);
return v_res_505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_506_, lean_object* v_h__1_507_, lean_object* v_h__2_508_, lean_object* v_h__3_509_){
_start:
{
switch(lean_obj_tag(v_x_506_))
{
case 0:
{
lean_object* v_it_510_; lean_object* v_out_511_; lean_object* v___x_512_; 
lean_dec(v_h__3_509_);
lean_dec(v_h__2_508_);
v_it_510_ = lean_ctor_get(v_x_506_, 0);
lean_inc(v_it_510_);
v_out_511_ = lean_ctor_get(v_x_506_, 1);
lean_inc(v_out_511_);
lean_dec_ref_known(v_x_506_, 2);
v___x_512_ = lean_apply_3(v_h__1_507_, v_it_510_, v_out_511_, lean_box(0));
return v___x_512_;
}
case 1:
{
lean_object* v_it_513_; lean_object* v___x_514_; 
lean_dec(v_h__3_509_);
lean_dec(v_h__1_507_);
v_it_513_ = lean_ctor_get(v_x_506_, 0);
lean_inc(v_it_513_);
lean_dec_ref_known(v_x_506_, 1);
v___x_514_ = lean_apply_2(v_h__2_508_, v_it_513_, lean_box(0));
return v___x_514_;
}
default: 
{
lean_object* v___x_515_; 
lean_dec(v_h__2_508_);
lean_dec(v_h__1_507_);
v___x_515_ = lean_apply_1(v_h__3_509_, lean_box(0));
return v___x_515_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_516_, lean_object* v_00_u03b2_517_, lean_object* v_m_518_, lean_object* v_inst_519_, lean_object* v_it_520_, lean_object* v_motive_521_, lean_object* v_x_522_, lean_object* v_h__1_523_, lean_object* v_h__2_524_, lean_object* v_h__3_525_){
_start:
{
switch(lean_obj_tag(v_x_522_))
{
case 0:
{
lean_object* v_it_526_; lean_object* v_out_527_; lean_object* v___x_528_; 
lean_dec(v_h__3_525_);
lean_dec(v_h__2_524_);
v_it_526_ = lean_ctor_get(v_x_522_, 0);
lean_inc(v_it_526_);
v_out_527_ = lean_ctor_get(v_x_522_, 1);
lean_inc(v_out_527_);
lean_dec_ref_known(v_x_522_, 2);
v___x_528_ = lean_apply_3(v_h__1_523_, v_it_526_, v_out_527_, lean_box(0));
return v___x_528_;
}
case 1:
{
lean_object* v_it_529_; lean_object* v___x_530_; 
lean_dec(v_h__3_525_);
lean_dec(v_h__1_523_);
v_it_529_ = lean_ctor_get(v_x_522_, 0);
lean_inc(v_it_529_);
lean_dec_ref_known(v_x_522_, 1);
v___x_530_ = lean_apply_2(v_h__2_524_, v_it_529_, lean_box(0));
return v___x_530_;
}
default: 
{
lean_object* v___x_531_; 
lean_dec(v_h__2_524_);
lean_dec(v_h__1_523_);
v___x_531_ = lean_apply_1(v_h__3_525_, lean_box(0));
return v___x_531_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_532_, lean_object* v_00_u03b2_533_, lean_object* v_m_534_, lean_object* v_inst_535_, lean_object* v_it_536_, lean_object* v_motive_537_, lean_object* v_x_538_, lean_object* v_h__1_539_, lean_object* v_h__2_540_, lean_object* v_h__3_541_){
_start:
{
lean_object* v_res_542_; 
v_res_542_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_532_, v_00_u03b2_533_, v_m_534_, v_inst_535_, v_it_536_, v_motive_537_, v_x_538_, v_h__1_539_, v_h__2_540_, v_h__3_541_);
lean_dec(v_it_536_);
lean_dec(v_inst_535_);
return v_res_542_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_543_, lean_object* v_h__1_544_, lean_object* v_h__2_545_){
_start:
{
if (lean_obj_tag(v_____do__lift_543_) == 0)
{
lean_object* v_a_546_; lean_object* v___x_547_; 
lean_dec(v_h__1_544_);
v_a_546_ = lean_ctor_get(v_____do__lift_543_, 0);
lean_inc(v_a_546_);
lean_dec_ref_known(v_____do__lift_543_, 1);
v___x_547_ = lean_apply_2(v_h__2_545_, v_a_546_, lean_box(0));
return v___x_547_;
}
else
{
lean_object* v_a_548_; lean_object* v___x_549_; 
lean_dec(v_h__2_545_);
v_a_548_ = lean_ctor_get(v_____do__lift_543_, 0);
lean_inc(v_a_548_);
lean_dec_ref_known(v_____do__lift_543_, 1);
v___x_549_ = lean_apply_2(v_h__1_544_, v_a_548_, lean_box(0));
return v___x_549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b2_550_, lean_object* v_00_u03b3_551_, lean_object* v_init_552_, lean_object* v_PlausibleForInStep_553_, lean_object* v_out_554_, lean_object* v_motive_555_, lean_object* v_____do__lift_556_, lean_object* v_h__1_557_, lean_object* v_h__2_558_){
_start:
{
if (lean_obj_tag(v_____do__lift_556_) == 0)
{
lean_object* v_a_559_; lean_object* v___x_560_; 
lean_dec(v_h__1_557_);
v_a_559_ = lean_ctor_get(v_____do__lift_556_, 0);
lean_inc(v_a_559_);
lean_dec_ref_known(v_____do__lift_556_, 1);
v___x_560_ = lean_apply_2(v_h__2_558_, v_a_559_, lean_box(0));
return v___x_560_;
}
else
{
lean_object* v_a_561_; lean_object* v___x_562_; 
lean_dec(v_h__2_558_);
v_a_561_ = lean_ctor_get(v_____do__lift_556_, 0);
lean_inc(v_a_561_);
lean_dec_ref_known(v_____do__lift_556_, 1);
v___x_562_ = lean_apply_2(v_h__1_557_, v_a_561_, lean_box(0));
return v___x_562_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(lean_object* v_00_u03b2_563_, lean_object* v_00_u03b3_564_, lean_object* v_init_565_, lean_object* v_PlausibleForInStep_566_, lean_object* v_out_567_, lean_object* v_motive_568_, lean_object* v_____do__lift_569_, lean_object* v_h__1_570_, lean_object* v_h__2_571_){
_start:
{
lean_object* v_res_572_; 
v_res_572_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_563_, v_00_u03b3_564_, v_init_565_, v_PlausibleForInStep_566_, v_out_567_, v_motive_568_, v_____do__lift_569_, v_h__1_570_, v_h__2_571_);
lean_dec(v_out_567_);
lean_dec(v_init_565_);
return v_res_572_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_573_, lean_object* v_f_574_, lean_object* v_h__1_575_, lean_object* v_h__2_576_){
_start:
{
lean_object* v_next_577_; 
v_next_577_ = lean_ctor_get(v_it_573_, 0);
if (lean_obj_tag(v_next_577_) == 0)
{
lean_object* v_upperBound_578_; lean_object* v___x_579_; 
lean_dec(v_h__1_575_);
v_upperBound_578_ = lean_ctor_get(v_it_573_, 1);
lean_inc(v_upperBound_578_);
lean_dec_ref(v_it_573_);
v___x_579_ = lean_apply_2(v_h__2_576_, v_upperBound_578_, v_f_574_);
return v___x_579_;
}
else
{
lean_object* v_upperBound_580_; lean_object* v_val_581_; lean_object* v___x_582_; 
lean_inc_ref(v_next_577_);
lean_dec(v_h__2_576_);
v_upperBound_580_ = lean_ctor_get(v_it_573_, 1);
lean_inc(v_upperBound_580_);
lean_dec_ref(v_it_573_);
v_val_581_ = lean_ctor_get(v_next_577_, 0);
lean_inc(v_val_581_);
lean_dec_ref_known(v_next_577_, 1);
v___x_582_ = lean_apply_3(v_h__1_575_, v_val_581_, v_upperBound_580_, v_f_574_);
return v___x_582_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_583_, lean_object* v_inst_584_, lean_object* v_inst_585_, lean_object* v_inst_586_, lean_object* v_n_587_, lean_object* v_00_u03b3_588_, lean_object* v_Pl_589_, lean_object* v_motive_590_, lean_object* v_it_591_, lean_object* v_f_592_, lean_object* v_h__1_593_, lean_object* v_h__2_594_){
_start:
{
lean_object* v_next_595_; 
v_next_595_ = lean_ctor_get(v_it_591_, 0);
if (lean_obj_tag(v_next_595_) == 0)
{
lean_object* v_upperBound_596_; lean_object* v___x_597_; 
lean_dec(v_h__1_593_);
v_upperBound_596_ = lean_ctor_get(v_it_591_, 1);
lean_inc(v_upperBound_596_);
lean_dec_ref(v_it_591_);
v___x_597_ = lean_apply_2(v_h__2_594_, v_upperBound_596_, v_f_592_);
return v___x_597_;
}
else
{
lean_object* v_upperBound_598_; lean_object* v_val_599_; lean_object* v___x_600_; 
lean_inc_ref(v_next_595_);
lean_dec(v_h__2_594_);
v_upperBound_598_ = lean_ctor_get(v_it_591_, 1);
lean_inc(v_upperBound_598_);
lean_dec_ref(v_it_591_);
v_val_599_ = lean_ctor_get(v_next_595_, 0);
lean_inc(v_val_599_);
lean_dec_ref_known(v_next_595_, 1);
v___x_600_ = lean_apply_3(v_h__1_593_, v_val_599_, v_upperBound_598_, v_f_592_);
return v___x_600_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_601_, lean_object* v_inst_602_, lean_object* v_inst_603_, lean_object* v_inst_604_, lean_object* v_n_605_, lean_object* v_00_u03b3_606_, lean_object* v_Pl_607_, lean_object* v_motive_608_, lean_object* v_it_609_, lean_object* v_f_610_, lean_object* v_h__1_611_, lean_object* v_h__2_612_){
_start:
{
lean_object* v_res_613_; 
v_res_613_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_601_, v_inst_602_, v_inst_603_, v_inst_604_, v_n_605_, v_00_u03b3_606_, v_Pl_607_, v_motive_608_, v_it_609_, v_f_610_, v_h__1_611_, v_h__2_612_);
lean_dec_ref(v_inst_604_);
lean_dec_ref(v_inst_602_);
return v_res_613_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object* v_x_614_, lean_object* v_h__1_615_, lean_object* v_h__2_616_, lean_object* v_h__3_617_){
_start:
{
switch(lean_obj_tag(v_x_614_))
{
case 0:
{
lean_object* v_it_618_; lean_object* v_out_619_; lean_object* v___x_620_; 
lean_dec(v_h__3_617_);
lean_dec(v_h__2_616_);
v_it_618_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_it_618_);
v_out_619_ = lean_ctor_get(v_x_614_, 1);
lean_inc(v_out_619_);
lean_dec_ref_known(v_x_614_, 2);
v___x_620_ = lean_apply_3(v_h__1_615_, v_it_618_, v_out_619_, lean_box(0));
return v___x_620_;
}
case 1:
{
lean_object* v_it_621_; lean_object* v___x_622_; 
lean_dec(v_h__3_617_);
lean_dec(v_h__1_615_);
v_it_621_ = lean_ctor_get(v_x_614_, 0);
lean_inc(v_it_621_);
lean_dec_ref_known(v_x_614_, 1);
v___x_622_ = lean_apply_2(v_h__2_616_, v_it_621_, lean_box(0));
return v___x_622_;
}
default: 
{
lean_object* v___x_623_; 
lean_dec(v_h__2_616_);
lean_dec(v_h__1_615_);
v___x_623_ = lean_apply_1(v_h__3_617_, lean_box(0));
return v___x_623_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object* v_m_624_, lean_object* v_00_u03b1_625_, lean_object* v_00_u03b2_626_, lean_object* v_inst_627_, lean_object* v_it_628_, lean_object* v_motive_629_, lean_object* v_x_630_, lean_object* v_h__1_631_, lean_object* v_h__2_632_, lean_object* v_h__3_633_){
_start:
{
switch(lean_obj_tag(v_x_630_))
{
case 0:
{
lean_object* v_it_634_; lean_object* v_out_635_; lean_object* v___x_636_; 
lean_dec(v_h__3_633_);
lean_dec(v_h__2_632_);
v_it_634_ = lean_ctor_get(v_x_630_, 0);
lean_inc(v_it_634_);
v_out_635_ = lean_ctor_get(v_x_630_, 1);
lean_inc(v_out_635_);
lean_dec_ref_known(v_x_630_, 2);
v___x_636_ = lean_apply_3(v_h__1_631_, v_it_634_, v_out_635_, lean_box(0));
return v___x_636_;
}
case 1:
{
lean_object* v_it_637_; lean_object* v___x_638_; 
lean_dec(v_h__3_633_);
lean_dec(v_h__1_631_);
v_it_637_ = lean_ctor_get(v_x_630_, 0);
lean_inc(v_it_637_);
lean_dec_ref_known(v_x_630_, 1);
v___x_638_ = lean_apply_2(v_h__2_632_, v_it_637_, lean_box(0));
return v___x_638_;
}
default: 
{
lean_object* v___x_639_; 
lean_dec(v_h__2_632_);
lean_dec(v_h__1_631_);
v___x_639_ = lean_apply_1(v_h__3_633_, lean_box(0));
return v___x_639_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object* v_m_640_, lean_object* v_00_u03b1_641_, lean_object* v_00_u03b2_642_, lean_object* v_inst_643_, lean_object* v_it_644_, lean_object* v_motive_645_, lean_object* v_x_646_, lean_object* v_h__1_647_, lean_object* v_h__2_648_, lean_object* v_h__3_649_){
_start:
{
lean_object* v_res_650_; 
v_res_650_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_640_, v_00_u03b1_641_, v_00_u03b2_642_, v_inst_643_, v_it_644_, v_motive_645_, v_x_646_, v_h__1_647_, v_h__2_648_, v_h__3_649_);
lean_dec(v_it_644_);
lean_dec(v_inst_643_);
return v_res_650_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object* v_____do__lift_651_, lean_object* v_h__1_652_, lean_object* v_h__2_653_){
_start:
{
if (lean_obj_tag(v_____do__lift_651_) == 0)
{
lean_object* v_a_654_; lean_object* v___x_655_; 
lean_dec(v_h__1_652_);
v_a_654_ = lean_ctor_get(v_____do__lift_651_, 0);
lean_inc(v_a_654_);
lean_dec_ref_known(v_____do__lift_651_, 1);
v___x_655_ = lean_apply_2(v_h__2_653_, v_a_654_, lean_box(0));
return v___x_655_;
}
else
{
lean_object* v_a_656_; lean_object* v___x_657_; 
lean_dec(v_h__2_653_);
v_a_656_ = lean_ctor_get(v_____do__lift_651_, 0);
lean_inc(v_a_656_);
lean_dec_ref_known(v_____do__lift_651_, 1);
v___x_657_ = lean_apply_2(v_h__1_652_, v_a_656_, lean_box(0));
return v___x_657_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object* v_00_u03b2_658_, lean_object* v_00_u03b3_659_, lean_object* v_PlausibleForInStep_660_, lean_object* v_acc_661_, lean_object* v_out_662_, lean_object* v_motive_663_, lean_object* v_____do__lift_664_, lean_object* v_h__1_665_, lean_object* v_h__2_666_){
_start:
{
if (lean_obj_tag(v_____do__lift_664_) == 0)
{
lean_object* v_a_667_; lean_object* v___x_668_; 
lean_dec(v_h__1_665_);
v_a_667_ = lean_ctor_get(v_____do__lift_664_, 0);
lean_inc(v_a_667_);
lean_dec_ref_known(v_____do__lift_664_, 1);
v___x_668_ = lean_apply_2(v_h__2_666_, v_a_667_, lean_box(0));
return v___x_668_;
}
else
{
lean_object* v_a_669_; lean_object* v___x_670_; 
lean_dec(v_h__2_666_);
v_a_669_ = lean_ctor_get(v_____do__lift_664_, 0);
lean_inc(v_a_669_);
lean_dec_ref_known(v_____do__lift_664_, 1);
v___x_670_ = lean_apply_2(v_h__1_665_, v_a_669_, lean_box(0));
return v___x_670_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object* v_00_u03b2_671_, lean_object* v_00_u03b3_672_, lean_object* v_PlausibleForInStep_673_, lean_object* v_acc_674_, lean_object* v_out_675_, lean_object* v_motive_676_, lean_object* v_____do__lift_677_, lean_object* v_h__1_678_, lean_object* v_h__2_679_){
_start:
{
lean_object* v_res_680_; 
v_res_680_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_671_, v_00_u03b3_672_, v_PlausibleForInStep_673_, v_acc_674_, v_out_675_, v_motive_676_, v_____do__lift_677_, v_h__1_678_, v_h__2_679_);
lean_dec(v_out_675_);
lean_dec(v_acc_674_);
return v_res_680_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step___redArg(lean_object* v_inst_681_, lean_object* v_inst_682_, lean_object* v_it_683_){
_start:
{
lean_object* v_next_684_; 
v_next_684_ = lean_ctor_get(v_it_683_, 0);
lean_inc(v_next_684_);
if (lean_obj_tag(v_next_684_) == 0)
{
lean_object* v___x_685_; 
lean_dec_ref(v_it_683_);
lean_dec_ref(v_inst_682_);
lean_dec_ref(v_inst_681_);
v___x_685_ = lean_box(2);
return v___x_685_;
}
else
{
lean_object* v_upperBound_686_; lean_object* v___x_688_; uint8_t v_isShared_689_; uint8_t v_isSharedCheck_707_; 
v_upperBound_686_ = lean_ctor_get(v_it_683_, 1);
v_isSharedCheck_707_ = !lean_is_exclusive(v_it_683_);
if (v_isSharedCheck_707_ == 0)
{
lean_object* v_unused_708_; 
v_unused_708_ = lean_ctor_get(v_it_683_, 0);
lean_dec(v_unused_708_);
v___x_688_ = v_it_683_;
v_isShared_689_ = v_isSharedCheck_707_;
goto v_resetjp_687_;
}
else
{
lean_inc(v_upperBound_686_);
lean_dec(v_it_683_);
v___x_688_ = lean_box(0);
v_isShared_689_ = v_isSharedCheck_707_;
goto v_resetjp_687_;
}
v_resetjp_687_:
{
lean_object* v_val_690_; lean_object* v___x_691_; uint8_t v___x_692_; 
v_val_690_ = lean_ctor_get(v_next_684_, 0);
lean_inc_n(v_val_690_, 2);
lean_dec_ref_known(v_next_684_, 1);
lean_inc(v_upperBound_686_);
v___x_691_ = lean_apply_2(v_inst_682_, v_val_690_, v_upperBound_686_);
v___x_692_ = lean_unbox(v___x_691_);
if (v___x_692_ == 0)
{
lean_object* v___x_693_; 
lean_dec(v_val_690_);
lean_del_object(v___x_688_);
lean_dec(v_upperBound_686_);
lean_dec_ref(v_inst_681_);
v___x_693_ = lean_box(2);
return v___x_693_;
}
else
{
lean_object* v_succ_x3f_694_; lean_object* v___x_696_; uint8_t v_isShared_697_; uint8_t v_isSharedCheck_705_; 
v_succ_x3f_694_ = lean_ctor_get(v_inst_681_, 0);
v_isSharedCheck_705_ = !lean_is_exclusive(v_inst_681_);
if (v_isSharedCheck_705_ == 0)
{
lean_object* v_unused_706_; 
v_unused_706_ = lean_ctor_get(v_inst_681_, 1);
lean_dec(v_unused_706_);
v___x_696_ = v_inst_681_;
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
else
{
lean_inc(v_succ_x3f_694_);
lean_dec(v_inst_681_);
v___x_696_ = lean_box(0);
v_isShared_697_ = v_isSharedCheck_705_;
goto v_resetjp_695_;
}
v_resetjp_695_:
{
lean_object* v___x_698_; lean_object* v___x_700_; 
lean_inc(v_val_690_);
v___x_698_ = lean_apply_1(v_succ_x3f_694_, v_val_690_);
if (v_isShared_689_ == 0)
{
lean_ctor_set(v___x_688_, 0, v___x_698_);
v___x_700_ = v___x_688_;
goto v_reusejp_699_;
}
else
{
lean_object* v_reuseFailAlloc_704_; 
v_reuseFailAlloc_704_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_704_, 0, v___x_698_);
lean_ctor_set(v_reuseFailAlloc_704_, 1, v_upperBound_686_);
v___x_700_ = v_reuseFailAlloc_704_;
goto v_reusejp_699_;
}
v_reusejp_699_:
{
lean_object* v___x_702_; 
if (v_isShared_697_ == 0)
{
lean_ctor_set(v___x_696_, 1, v_val_690_);
lean_ctor_set(v___x_696_, 0, v___x_700_);
v___x_702_ = v___x_696_;
goto v_reusejp_701_;
}
else
{
lean_object* v_reuseFailAlloc_703_; 
v_reuseFailAlloc_703_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_703_, 0, v___x_700_);
lean_ctor_set(v_reuseFailAlloc_703_, 1, v_val_690_);
v___x_702_ = v_reuseFailAlloc_703_;
goto v_reusejp_701_;
}
v_reusejp_701_:
{
return v___x_702_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step(lean_object* v_00_u03b1_709_, lean_object* v_inst_710_, lean_object* v_inst_711_, lean_object* v_inst_712_, lean_object* v_it_713_){
_start:
{
lean_object* v_next_714_; 
v_next_714_ = lean_ctor_get(v_it_713_, 0);
lean_inc(v_next_714_);
if (lean_obj_tag(v_next_714_) == 0)
{
lean_object* v___x_715_; 
lean_dec_ref(v_it_713_);
lean_dec_ref(v_inst_712_);
lean_dec_ref(v_inst_710_);
v___x_715_ = lean_box(2);
return v___x_715_;
}
else
{
lean_object* v_upperBound_716_; lean_object* v___x_718_; uint8_t v_isShared_719_; uint8_t v_isSharedCheck_737_; 
v_upperBound_716_ = lean_ctor_get(v_it_713_, 1);
v_isSharedCheck_737_ = !lean_is_exclusive(v_it_713_);
if (v_isSharedCheck_737_ == 0)
{
lean_object* v_unused_738_; 
v_unused_738_ = lean_ctor_get(v_it_713_, 0);
lean_dec(v_unused_738_);
v___x_718_ = v_it_713_;
v_isShared_719_ = v_isSharedCheck_737_;
goto v_resetjp_717_;
}
else
{
lean_inc(v_upperBound_716_);
lean_dec(v_it_713_);
v___x_718_ = lean_box(0);
v_isShared_719_ = v_isSharedCheck_737_;
goto v_resetjp_717_;
}
v_resetjp_717_:
{
lean_object* v_val_720_; lean_object* v___x_721_; uint8_t v___x_722_; 
v_val_720_ = lean_ctor_get(v_next_714_, 0);
lean_inc_n(v_val_720_, 2);
lean_dec_ref_known(v_next_714_, 1);
lean_inc(v_upperBound_716_);
v___x_721_ = lean_apply_2(v_inst_712_, v_val_720_, v_upperBound_716_);
v___x_722_ = lean_unbox(v___x_721_);
if (v___x_722_ == 0)
{
lean_object* v___x_723_; 
lean_dec(v_val_720_);
lean_del_object(v___x_718_);
lean_dec(v_upperBound_716_);
lean_dec_ref(v_inst_710_);
v___x_723_ = lean_box(2);
return v___x_723_;
}
else
{
lean_object* v_succ_x3f_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_735_; 
v_succ_x3f_724_ = lean_ctor_get(v_inst_710_, 0);
v_isSharedCheck_735_ = !lean_is_exclusive(v_inst_710_);
if (v_isSharedCheck_735_ == 0)
{
lean_object* v_unused_736_; 
v_unused_736_ = lean_ctor_get(v_inst_710_, 1);
lean_dec(v_unused_736_);
v___x_726_ = v_inst_710_;
v_isShared_727_ = v_isSharedCheck_735_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_succ_x3f_724_);
lean_dec(v_inst_710_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_735_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; lean_object* v___x_730_; 
lean_inc(v_val_720_);
v___x_728_ = lean_apply_1(v_succ_x3f_724_, v_val_720_);
if (v_isShared_719_ == 0)
{
lean_ctor_set(v___x_718_, 0, v___x_728_);
v___x_730_ = v___x_718_;
goto v_reusejp_729_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v___x_728_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_upperBound_716_);
v___x_730_ = v_reuseFailAlloc_734_;
goto v_reusejp_729_;
}
v_reusejp_729_:
{
lean_object* v___x_732_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v_val_720_);
lean_ctor_set(v___x_726_, 0, v___x_730_);
v___x_732_ = v___x_726_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_733_; 
v_reuseFailAlloc_733_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_733_, 0, v___x_730_);
lean_ctor_set(v_reuseFailAlloc_733_, 1, v_val_720_);
v___x_732_ = v_reuseFailAlloc_733_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
return v___x_732_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step___redArg(lean_object* v_inst_739_, lean_object* v_inst_740_, lean_object* v_it_741_){
_start:
{
lean_object* v_next_742_; 
v_next_742_ = lean_ctor_get(v_it_741_, 0);
lean_inc(v_next_742_);
if (lean_obj_tag(v_next_742_) == 0)
{
lean_object* v___x_743_; 
lean_dec_ref(v_it_741_);
lean_dec_ref(v_inst_740_);
lean_dec_ref(v_inst_739_);
v___x_743_ = lean_box(2);
return v___x_743_;
}
else
{
lean_object* v_upperBound_744_; lean_object* v___x_746_; uint8_t v_isShared_747_; uint8_t v_isSharedCheck_765_; 
v_upperBound_744_ = lean_ctor_get(v_it_741_, 1);
v_isSharedCheck_765_ = !lean_is_exclusive(v_it_741_);
if (v_isSharedCheck_765_ == 0)
{
lean_object* v_unused_766_; 
v_unused_766_ = lean_ctor_get(v_it_741_, 0);
lean_dec(v_unused_766_);
v___x_746_ = v_it_741_;
v_isShared_747_ = v_isSharedCheck_765_;
goto v_resetjp_745_;
}
else
{
lean_inc(v_upperBound_744_);
lean_dec(v_it_741_);
v___x_746_ = lean_box(0);
v_isShared_747_ = v_isSharedCheck_765_;
goto v_resetjp_745_;
}
v_resetjp_745_:
{
lean_object* v_val_748_; lean_object* v___x_749_; uint8_t v___x_750_; 
v_val_748_ = lean_ctor_get(v_next_742_, 0);
lean_inc_n(v_val_748_, 2);
lean_dec_ref_known(v_next_742_, 1);
lean_inc(v_upperBound_744_);
v___x_749_ = lean_apply_2(v_inst_740_, v_val_748_, v_upperBound_744_);
v___x_750_ = lean_unbox(v___x_749_);
if (v___x_750_ == 0)
{
lean_object* v___x_751_; 
lean_dec(v_val_748_);
lean_del_object(v___x_746_);
lean_dec(v_upperBound_744_);
lean_dec_ref(v_inst_739_);
v___x_751_ = lean_box(2);
return v___x_751_;
}
else
{
lean_object* v_succ_x3f_752_; lean_object* v___x_754_; uint8_t v_isShared_755_; uint8_t v_isSharedCheck_763_; 
v_succ_x3f_752_ = lean_ctor_get(v_inst_739_, 0);
v_isSharedCheck_763_ = !lean_is_exclusive(v_inst_739_);
if (v_isSharedCheck_763_ == 0)
{
lean_object* v_unused_764_; 
v_unused_764_ = lean_ctor_get(v_inst_739_, 1);
lean_dec(v_unused_764_);
v___x_754_ = v_inst_739_;
v_isShared_755_ = v_isSharedCheck_763_;
goto v_resetjp_753_;
}
else
{
lean_inc(v_succ_x3f_752_);
lean_dec(v_inst_739_);
v___x_754_ = lean_box(0);
v_isShared_755_ = v_isSharedCheck_763_;
goto v_resetjp_753_;
}
v_resetjp_753_:
{
lean_object* v___x_756_; lean_object* v___x_758_; 
lean_inc(v_val_748_);
v___x_756_ = lean_apply_1(v_succ_x3f_752_, v_val_748_);
if (v_isShared_747_ == 0)
{
lean_ctor_set(v___x_746_, 0, v___x_756_);
v___x_758_ = v___x_746_;
goto v_reusejp_757_;
}
else
{
lean_object* v_reuseFailAlloc_762_; 
v_reuseFailAlloc_762_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_762_, 0, v___x_756_);
lean_ctor_set(v_reuseFailAlloc_762_, 1, v_upperBound_744_);
v___x_758_ = v_reuseFailAlloc_762_;
goto v_reusejp_757_;
}
v_reusejp_757_:
{
lean_object* v___x_760_; 
if (v_isShared_755_ == 0)
{
lean_ctor_set(v___x_754_, 1, v_val_748_);
lean_ctor_set(v___x_754_, 0, v___x_758_);
v___x_760_ = v___x_754_;
goto v_reusejp_759_;
}
else
{
lean_object* v_reuseFailAlloc_761_; 
v_reuseFailAlloc_761_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_761_, 0, v___x_758_);
lean_ctor_set(v_reuseFailAlloc_761_, 1, v_val_748_);
v___x_760_ = v_reuseFailAlloc_761_;
goto v_reusejp_759_;
}
v_reusejp_759_:
{
return v___x_760_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step(lean_object* v_00_u03b1_767_, lean_object* v_inst_768_, lean_object* v_inst_769_, lean_object* v_inst_770_, lean_object* v_it_771_){
_start:
{
lean_object* v_next_772_; 
v_next_772_ = lean_ctor_get(v_it_771_, 0);
lean_inc(v_next_772_);
if (lean_obj_tag(v_next_772_) == 0)
{
lean_object* v___x_773_; 
lean_dec_ref(v_it_771_);
lean_dec_ref(v_inst_770_);
lean_dec_ref(v_inst_768_);
v___x_773_ = lean_box(2);
return v___x_773_;
}
else
{
lean_object* v_upperBound_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_795_; 
v_upperBound_774_ = lean_ctor_get(v_it_771_, 1);
v_isSharedCheck_795_ = !lean_is_exclusive(v_it_771_);
if (v_isSharedCheck_795_ == 0)
{
lean_object* v_unused_796_; 
v_unused_796_ = lean_ctor_get(v_it_771_, 0);
lean_dec(v_unused_796_);
v___x_776_ = v_it_771_;
v_isShared_777_ = v_isSharedCheck_795_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_upperBound_774_);
lean_dec(v_it_771_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_795_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_val_778_; lean_object* v___x_779_; uint8_t v___x_780_; 
v_val_778_ = lean_ctor_get(v_next_772_, 0);
lean_inc_n(v_val_778_, 2);
lean_dec_ref_known(v_next_772_, 1);
lean_inc(v_upperBound_774_);
v___x_779_ = lean_apply_2(v_inst_770_, v_val_778_, v_upperBound_774_);
v___x_780_ = lean_unbox(v___x_779_);
if (v___x_780_ == 0)
{
lean_object* v___x_781_; 
lean_dec(v_val_778_);
lean_del_object(v___x_776_);
lean_dec(v_upperBound_774_);
lean_dec_ref(v_inst_768_);
v___x_781_ = lean_box(2);
return v___x_781_;
}
else
{
lean_object* v_succ_x3f_782_; lean_object* v___x_784_; uint8_t v_isShared_785_; uint8_t v_isSharedCheck_793_; 
v_succ_x3f_782_ = lean_ctor_get(v_inst_768_, 0);
v_isSharedCheck_793_ = !lean_is_exclusive(v_inst_768_);
if (v_isSharedCheck_793_ == 0)
{
lean_object* v_unused_794_; 
v_unused_794_ = lean_ctor_get(v_inst_768_, 1);
lean_dec(v_unused_794_);
v___x_784_ = v_inst_768_;
v_isShared_785_ = v_isSharedCheck_793_;
goto v_resetjp_783_;
}
else
{
lean_inc(v_succ_x3f_782_);
lean_dec(v_inst_768_);
v___x_784_ = lean_box(0);
v_isShared_785_ = v_isSharedCheck_793_;
goto v_resetjp_783_;
}
v_resetjp_783_:
{
lean_object* v___x_786_; lean_object* v___x_788_; 
lean_inc(v_val_778_);
v___x_786_ = lean_apply_1(v_succ_x3f_782_, v_val_778_);
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 0, v___x_786_);
v___x_788_ = v___x_776_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_792_; 
v_reuseFailAlloc_792_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_792_, 0, v___x_786_);
lean_ctor_set(v_reuseFailAlloc_792_, 1, v_upperBound_774_);
v___x_788_ = v_reuseFailAlloc_792_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
lean_object* v___x_790_; 
if (v_isShared_785_ == 0)
{
lean_ctor_set(v___x_784_, 1, v_val_778_);
lean_ctor_set(v___x_784_, 0, v___x_788_);
v___x_790_ = v___x_784_;
goto v_reusejp_789_;
}
else
{
lean_object* v_reuseFailAlloc_791_; 
v_reuseFailAlloc_791_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_791_, 0, v___x_788_);
lean_ctor_set(v_reuseFailAlloc_791_, 1, v_val_778_);
v___x_790_ = v_reuseFailAlloc_791_;
goto v_reusejp_789_;
}
v_reusejp_789_:
{
return v___x_790_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0(lean_object* v_inst_797_, lean_object* v_inst_798_, lean_object* v_it_799_){
_start:
{
lean_object* v_next_800_; 
v_next_800_ = lean_ctor_get(v_it_799_, 0);
lean_inc(v_next_800_);
if (lean_obj_tag(v_next_800_) == 0)
{
lean_object* v___x_801_; 
lean_dec_ref(v_it_799_);
lean_dec_ref(v_inst_798_);
lean_dec_ref(v_inst_797_);
v___x_801_ = lean_box(2);
return v___x_801_;
}
else
{
lean_object* v_upperBound_802_; lean_object* v___x_804_; uint8_t v_isShared_805_; uint8_t v_isSharedCheck_823_; 
v_upperBound_802_ = lean_ctor_get(v_it_799_, 1);
v_isSharedCheck_823_ = !lean_is_exclusive(v_it_799_);
if (v_isSharedCheck_823_ == 0)
{
lean_object* v_unused_824_; 
v_unused_824_ = lean_ctor_get(v_it_799_, 0);
lean_dec(v_unused_824_);
v___x_804_ = v_it_799_;
v_isShared_805_ = v_isSharedCheck_823_;
goto v_resetjp_803_;
}
else
{
lean_inc(v_upperBound_802_);
lean_dec(v_it_799_);
v___x_804_ = lean_box(0);
v_isShared_805_ = v_isSharedCheck_823_;
goto v_resetjp_803_;
}
v_resetjp_803_:
{
lean_object* v_val_806_; lean_object* v___x_807_; uint8_t v___x_808_; 
v_val_806_ = lean_ctor_get(v_next_800_, 0);
lean_inc_n(v_val_806_, 2);
lean_dec_ref_known(v_next_800_, 1);
lean_inc(v_upperBound_802_);
v___x_807_ = lean_apply_2(v_inst_797_, v_val_806_, v_upperBound_802_);
v___x_808_ = lean_unbox(v___x_807_);
if (v___x_808_ == 0)
{
lean_object* v___x_809_; 
lean_dec(v_val_806_);
lean_del_object(v___x_804_);
lean_dec(v_upperBound_802_);
lean_dec_ref(v_inst_798_);
v___x_809_ = lean_box(2);
return v___x_809_;
}
else
{
lean_object* v_succ_x3f_810_; lean_object* v___x_812_; uint8_t v_isShared_813_; uint8_t v_isSharedCheck_821_; 
v_succ_x3f_810_ = lean_ctor_get(v_inst_798_, 0);
v_isSharedCheck_821_ = !lean_is_exclusive(v_inst_798_);
if (v_isSharedCheck_821_ == 0)
{
lean_object* v_unused_822_; 
v_unused_822_ = lean_ctor_get(v_inst_798_, 1);
lean_dec(v_unused_822_);
v___x_812_ = v_inst_798_;
v_isShared_813_ = v_isSharedCheck_821_;
goto v_resetjp_811_;
}
else
{
lean_inc(v_succ_x3f_810_);
lean_dec(v_inst_798_);
v___x_812_ = lean_box(0);
v_isShared_813_ = v_isSharedCheck_821_;
goto v_resetjp_811_;
}
v_resetjp_811_:
{
lean_object* v___x_814_; lean_object* v___x_816_; 
lean_inc(v_val_806_);
v___x_814_ = lean_apply_1(v_succ_x3f_810_, v_val_806_);
if (v_isShared_805_ == 0)
{
lean_ctor_set(v___x_804_, 0, v___x_814_);
v___x_816_ = v___x_804_;
goto v_reusejp_815_;
}
else
{
lean_object* v_reuseFailAlloc_820_; 
v_reuseFailAlloc_820_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_820_, 0, v___x_814_);
lean_ctor_set(v_reuseFailAlloc_820_, 1, v_upperBound_802_);
v___x_816_ = v_reuseFailAlloc_820_;
goto v_reusejp_815_;
}
v_reusejp_815_:
{
lean_object* v___x_818_; 
if (v_isShared_813_ == 0)
{
lean_ctor_set(v___x_812_, 1, v_val_806_);
lean_ctor_set(v___x_812_, 0, v___x_816_);
v___x_818_ = v___x_812_;
goto v_reusejp_817_;
}
else
{
lean_object* v_reuseFailAlloc_819_; 
v_reuseFailAlloc_819_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_819_, 0, v___x_816_);
lean_ctor_set(v_reuseFailAlloc_819_, 1, v_val_806_);
v___x_818_ = v_reuseFailAlloc_819_;
goto v_reusejp_817_;
}
v_reusejp_817_:
{
return v___x_818_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg(lean_object* v_inst_825_, lean_object* v_inst_826_){
_start:
{
lean_object* v___f_827_; 
v___f_827_ = lean_alloc_closure((void*)(l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_827_, 0, v_inst_826_);
lean_closure_set(v___f_827_, 1, v_inst_825_);
return v___f_827_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT(lean_object* v_00_u03b1_828_, lean_object* v_inst_829_, lean_object* v_inst_830_, lean_object* v_inst_831_){
_start:
{
lean_object* v___f_832_; 
v___f_832_ = lean_alloc_closure((void*)(l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_832_, 0, v_inst_831_);
lean_closure_set(v___f_832_, 1, v_inst_829_);
return v___f_832_;
}
}
lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_834_; 
v___x_834_ = lean_box(0);
return v___x_834_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_835_;
v_res_835_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___redArg();
stack->m_obj
 = v_res_835_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_836_){
_start:
{
lean_object* v_res_837_; 
v_res_837_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___redArg();
return v_res_837_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_838_, lean_object* v_inst_839_, lean_object* v_inst_840_, lean_object* v_inst_841_, lean_object* v_inst_842_, lean_object* v_inst_843_){
_start:
{
lean_object* v___x_844_; 
v___x_844_ = lean_box(0);
return v___x_844_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_845_, lean_object* v_inst_846_, lean_object* v_inst_847_, lean_object* v_inst_848_, lean_object* v_inst_849_, lean_object* v_inst_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation(v_00_u03b1_845_, v_inst_846_, v_inst_847_, v_inst_848_, v_inst_849_, v_inst_850_);
lean_dec_ref(v_inst_848_);
lean_dec_ref(v_inst_846_);
return v_res_851_;
}
}
lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_853_; 
v___x_853_ = lean_box(0);
return v___x_853_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_854_;
v_res_854_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___redArg();
stack->m_obj
 = v_res_854_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_855_){
_start:
{
lean_object* v_res_856_; 
v_res_856_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___redArg();
return v_res_856_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_857_, lean_object* v_inst_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_inst_861_){
_start:
{
lean_object* v___x_862_; 
v___x_862_ = lean_box(0);
return v___x_862_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_863_, lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_inst_866_, lean_object* v_inst_867_){
_start:
{
lean_object* v_res_868_; 
v_res_868_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(v_00_u03b1_863_, v_inst_864_, v_inst_865_, v_inst_866_, v_inst_867_);
lean_dec_ref(v_inst_866_);
lean_dec_ref(v_inst_864_);
return v_res_868_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_869_, lean_object* v_inst_870_, lean_object* v_it_871_, lean_object* v_n_872_){
_start:
{
lean_object* v_next_873_; 
v_next_873_ = lean_ctor_get(v_it_871_, 0);
lean_inc(v_next_873_);
if (lean_obj_tag(v_next_873_) == 0)
{
lean_object* v___x_874_; 
lean_dec(v_n_872_);
lean_dec_ref(v_it_871_);
lean_dec_ref(v_inst_870_);
lean_dec_ref(v_inst_869_);
v___x_874_ = lean_box(2);
return v___x_874_;
}
else
{
lean_object* v_upperBound_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_899_; 
v_upperBound_875_ = lean_ctor_get(v_it_871_, 1);
v_isSharedCheck_899_ = !lean_is_exclusive(v_it_871_);
if (v_isSharedCheck_899_ == 0)
{
lean_object* v_unused_900_; 
v_unused_900_ = lean_ctor_get(v_it_871_, 0);
lean_dec(v_unused_900_);
v___x_877_ = v_it_871_;
v_isShared_878_ = v_isSharedCheck_899_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_upperBound_875_);
lean_dec(v_it_871_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_899_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_succ_x3f_879_; lean_object* v_succMany_x3f_880_; lean_object* v___x_882_; uint8_t v_isShared_883_; uint8_t v_isSharedCheck_898_; 
v_succ_x3f_879_ = lean_ctor_get(v_inst_869_, 0);
v_succMany_x3f_880_ = lean_ctor_get(v_inst_869_, 1);
v_isSharedCheck_898_ = !lean_is_exclusive(v_inst_869_);
if (v_isSharedCheck_898_ == 0)
{
v___x_882_ = v_inst_869_;
v_isShared_883_ = v_isSharedCheck_898_;
goto v_resetjp_881_;
}
else
{
lean_inc(v_succMany_x3f_880_);
lean_inc(v_succ_x3f_879_);
lean_dec(v_inst_869_);
v___x_882_ = lean_box(0);
v_isShared_883_ = v_isSharedCheck_898_;
goto v_resetjp_881_;
}
v_resetjp_881_:
{
lean_object* v_val_884_; lean_object* v___x_885_; 
v_val_884_ = lean_ctor_get(v_next_873_, 0);
lean_inc(v_val_884_);
lean_dec_ref_known(v_next_873_, 1);
v___x_885_ = lean_apply_2(v_succMany_x3f_880_, v_n_872_, v_val_884_);
if (lean_obj_tag(v___x_885_) == 0)
{
lean_object* v___x_886_; 
lean_del_object(v___x_882_);
lean_dec_ref(v_succ_x3f_879_);
lean_del_object(v___x_877_);
lean_dec(v_upperBound_875_);
lean_dec_ref(v_inst_870_);
v___x_886_ = lean_box(2);
return v___x_886_;
}
else
{
lean_object* v_val_887_; lean_object* v___x_888_; uint8_t v___x_889_; 
v_val_887_ = lean_ctor_get(v___x_885_, 0);
lean_inc_n(v_val_887_, 2);
lean_dec_ref_known(v___x_885_, 1);
lean_inc(v_upperBound_875_);
v___x_888_ = lean_apply_2(v_inst_870_, v_val_887_, v_upperBound_875_);
v___x_889_ = lean_unbox(v___x_888_);
if (v___x_889_ == 0)
{
lean_object* v___x_890_; 
lean_dec(v_val_887_);
lean_del_object(v___x_882_);
lean_dec_ref(v_succ_x3f_879_);
lean_del_object(v___x_877_);
lean_dec(v_upperBound_875_);
v___x_890_ = lean_box(2);
return v___x_890_;
}
else
{
lean_object* v___x_891_; lean_object* v___x_893_; 
lean_inc(v_val_887_);
v___x_891_ = lean_apply_1(v_succ_x3f_879_, v_val_887_);
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 0, v___x_891_);
v___x_893_ = v___x_877_;
goto v_reusejp_892_;
}
else
{
lean_object* v_reuseFailAlloc_897_; 
v_reuseFailAlloc_897_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_897_, 0, v___x_891_);
lean_ctor_set(v_reuseFailAlloc_897_, 1, v_upperBound_875_);
v___x_893_ = v_reuseFailAlloc_897_;
goto v_reusejp_892_;
}
v_reusejp_892_:
{
lean_object* v___x_895_; 
if (v_isShared_883_ == 0)
{
lean_ctor_set(v___x_882_, 1, v_val_887_);
lean_ctor_set(v___x_882_, 0, v___x_893_);
v___x_895_ = v___x_882_;
goto v_reusejp_894_;
}
else
{
lean_object* v_reuseFailAlloc_896_; 
v_reuseFailAlloc_896_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_896_, 0, v___x_893_);
lean_ctor_set(v_reuseFailAlloc_896_, 1, v_val_887_);
v___x_895_ = v_reuseFailAlloc_896_;
goto v_reusejp_894_;
}
v_reusejp_894_:
{
return v___x_895_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg(lean_object* v_inst_901_, lean_object* v_inst_902_){
_start:
{
lean_object* v___f_903_; 
v___f_903_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_903_, 0, v_inst_901_);
lean_closure_set(v___f_903_, 1, v_inst_902_);
return v___f_903_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess(lean_object* v_00_u03b1_904_, lean_object* v_inst_905_, lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_inst_909_){
_start:
{
lean_object* v___f_910_; 
v___f_910_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_910_, 0, v_inst_905_);
lean_closure_set(v___f_910_, 1, v_inst_907_);
return v___f_910_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_911_, lean_object* v_inst_912_, lean_object* v_inst_913_, lean_object* v_upperBound_914_, lean_object* v_acc_915_, lean_object* v_next_916_, lean_object* v_f_917_){
_start:
{
lean_object* v_toApplicative_918_; lean_object* v_toBind_919_; lean_object* v_toPure_920_; lean_object* v___f_921_; lean_object* v___x_922_; 
v_toApplicative_918_ = lean_ctor_get(v_inst_913_, 0);
lean_inc_ref(v_toApplicative_918_);
v_toBind_919_ = lean_ctor_get(v_inst_913_, 1);
lean_inc(v_toBind_919_);
lean_dec_ref(v_inst_913_);
v_toPure_920_ = lean_ctor_get(v_toApplicative_918_, 1);
lean_inc(v_toPure_920_);
lean_dec_ref(v_toApplicative_918_);
v___f_921_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_921_, 0, v_inst_912_);
lean_closure_set(v___f_921_, 1, v_upperBound_914_);
lean_closure_set(v___f_921_, 2, v_toPure_920_);
lean_closure_set(v___f_921_, 3, v_inst_911_);
lean_closure_set(v___f_921_, 4, v_f_917_);
lean_closure_set(v___f_921_, 5, v_toBind_919_);
v___x_922_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_921_, v_next_916_, v_acc_915_, lean_box(0));
return v___x_922_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_923_, lean_object* v_inst_924_, lean_object* v_inst_925_, lean_object* v_inst_926_, lean_object* v_inst_927_, lean_object* v_n_928_, lean_object* v_inst_929_, lean_object* v_00_u03b3_930_, lean_object* v_Pl_931_, lean_object* v_LargeEnough_932_, lean_object* v_hl_933_, lean_object* v_upperBound_934_, lean_object* v_acc_935_, lean_object* v_next_936_, lean_object* v_h_937_, lean_object* v_f_938_){
_start:
{
lean_object* v_toApplicative_939_; lean_object* v_toBind_940_; lean_object* v_toPure_941_; lean_object* v___f_942_; lean_object* v___x_943_; 
v_toApplicative_939_ = lean_ctor_get(v_inst_929_, 0);
lean_inc_ref(v_toApplicative_939_);
v_toBind_940_ = lean_ctor_get(v_inst_929_, 1);
lean_inc(v_toBind_940_);
lean_dec_ref(v_inst_929_);
v_toPure_941_ = lean_ctor_get(v_toApplicative_939_, 1);
lean_inc(v_toPure_941_);
lean_dec_ref(v_toApplicative_939_);
v___f_942_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_942_, 0, v_inst_926_);
lean_closure_set(v___f_942_, 1, v_upperBound_934_);
lean_closure_set(v___f_942_, 2, v_toPure_941_);
lean_closure_set(v___f_942_, 3, v_inst_924_);
lean_closure_set(v___f_942_, 4, v_f_938_);
lean_closure_set(v___f_942_, 5, v_toBind_940_);
v___x_943_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_942_, v_next_936_, v_acc_935_, lean_box(0));
return v___x_943_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_944_, lean_object* v_inst_945_, lean_object* v_inst_946_, lean_object* v_toBind_947_, lean_object* v_x_948_, lean_object* v_00_u03b3_949_, lean_object* v_Pl_950_, lean_object* v_it_951_, lean_object* v_init_952_, lean_object* v_f_953_){
_start:
{
lean_object* v_next_954_; 
v_next_954_ = lean_ctor_get(v_it_951_, 0);
lean_inc(v_next_954_);
if (lean_obj_tag(v_next_954_) == 0)
{
lean_object* v___x_955_; 
lean_dec(v_f_953_);
lean_dec_ref(v_it_951_);
lean_dec(v_toBind_947_);
lean_dec_ref(v_inst_946_);
lean_dec_ref(v_inst_945_);
v___x_955_ = lean_apply_2(v_toPure_944_, lean_box(0), v_init_952_);
return v___x_955_;
}
else
{
lean_object* v_upperBound_956_; lean_object* v_val_957_; lean_object* v___f_958_; lean_object* v___x_959_; 
v_upperBound_956_ = lean_ctor_get(v_it_951_, 1);
lean_inc(v_upperBound_956_);
lean_dec_ref(v_it_951_);
v_val_957_ = lean_ctor_get(v_next_954_, 0);
lean_inc(v_val_957_);
lean_dec_ref_known(v_next_954_, 1);
v___f_958_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_958_, 0, v_inst_945_);
lean_closure_set(v___f_958_, 1, v_upperBound_956_);
lean_closure_set(v___f_958_, 2, v_toPure_944_);
lean_closure_set(v___f_958_, 3, v_inst_946_);
lean_closure_set(v___f_958_, 4, v_f_953_);
lean_closure_set(v___f_958_, 5, v_toBind_947_);
v___x_959_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_958_, v_val_957_, v_init_952_, lean_box(0));
return v___x_959_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_960_, lean_object* v_inst_961_, lean_object* v_inst_962_, lean_object* v_toBind_963_, lean_object* v_x_964_, lean_object* v_00_u03b3_965_, lean_object* v_Pl_966_, lean_object* v_it_967_, lean_object* v_init_968_, lean_object* v_f_969_){
_start:
{
lean_object* v_res_970_; 
v_res_970_ = l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_960_, v_inst_961_, v_inst_962_, v_toBind_963_, v_x_964_, v_00_u03b3_965_, v_Pl_966_, v_it_967_, v_init_968_, v_f_969_);
lean_dec(v_x_964_);
return v_res_970_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg(lean_object* v_inst_971_, lean_object* v_inst_972_, lean_object* v_inst_973_){
_start:
{
lean_object* v_toApplicative_974_; lean_object* v_toBind_975_; lean_object* v_toPure_976_; lean_object* v___f_977_; 
v_toApplicative_974_ = lean_ctor_get(v_inst_973_, 0);
lean_inc_ref(v_toApplicative_974_);
v_toBind_975_ = lean_ctor_get(v_inst_973_, 1);
lean_inc(v_toBind_975_);
lean_dec_ref(v_inst_973_);
v_toPure_976_ = lean_ctor_get(v_toApplicative_974_, 1);
lean_inc(v_toPure_976_);
lean_dec_ref(v_toApplicative_974_);
v___f_977_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_977_, 0, v_toPure_976_);
lean_closure_set(v___f_977_, 1, v_inst_972_);
lean_closure_set(v___f_977_, 2, v_inst_971_);
lean_closure_set(v___f_977_, 3, v_toBind_975_);
return v___f_977_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop(lean_object* v_00_u03b1_978_, lean_object* v_inst_979_, lean_object* v_inst_980_, lean_object* v_inst_981_, lean_object* v_inst_982_, lean_object* v_inst_983_, lean_object* v_n_984_, lean_object* v_inst_985_){
_start:
{
lean_object* v_toApplicative_986_; lean_object* v_toBind_987_; lean_object* v_toPure_988_; lean_object* v___f_989_; 
v_toApplicative_986_ = lean_ctor_get(v_inst_985_, 0);
lean_inc_ref(v_toApplicative_986_);
v_toBind_987_ = lean_ctor_get(v_inst_985_, 1);
lean_inc(v_toBind_987_);
lean_dec_ref(v_inst_985_);
v_toPure_988_ = lean_ctor_get(v_toApplicative_986_, 1);
lean_inc(v_toPure_988_);
lean_dec_ref(v_toApplicative_986_);
v___f_989_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_989_, 0, v_toPure_988_);
lean_closure_set(v___f_989_, 1, v_inst_981_);
lean_closure_set(v___f_989_, 2, v_inst_979_);
lean_closure_set(v___f_989_, 3, v_toBind_987_);
return v___f_989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_990_, lean_object* v_f_991_, lean_object* v_h__1_992_, lean_object* v_h__2_993_){
_start:
{
lean_object* v_next_994_; 
v_next_994_ = lean_ctor_get(v_it_990_, 0);
if (lean_obj_tag(v_next_994_) == 0)
{
lean_object* v_upperBound_995_; lean_object* v___x_996_; 
lean_dec(v_h__1_992_);
v_upperBound_995_ = lean_ctor_get(v_it_990_, 1);
lean_inc(v_upperBound_995_);
lean_dec_ref(v_it_990_);
v___x_996_ = lean_apply_2(v_h__2_993_, v_upperBound_995_, v_f_991_);
return v___x_996_;
}
else
{
lean_object* v_upperBound_997_; lean_object* v_val_998_; lean_object* v___x_999_; 
lean_inc_ref(v_next_994_);
lean_dec(v_h__2_993_);
v_upperBound_997_ = lean_ctor_get(v_it_990_, 1);
lean_inc(v_upperBound_997_);
lean_dec_ref(v_it_990_);
v_val_998_ = lean_ctor_get(v_next_994_, 0);
lean_inc(v_val_998_);
lean_dec_ref_known(v_next_994_, 1);
v___x_999_ = lean_apply_3(v_h__1_992_, v_val_998_, v_upperBound_997_, v_f_991_);
return v___x_999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_1000_, lean_object* v_inst_1001_, lean_object* v_inst_1002_, lean_object* v_inst_1003_, lean_object* v_n_1004_, lean_object* v_00_u03b3_1005_, lean_object* v_Pl_1006_, lean_object* v_motive_1007_, lean_object* v_it_1008_, lean_object* v_f_1009_, lean_object* v_h__1_1010_, lean_object* v_h__2_1011_){
_start:
{
lean_object* v_next_1012_; 
v_next_1012_ = lean_ctor_get(v_it_1008_, 0);
if (lean_obj_tag(v_next_1012_) == 0)
{
lean_object* v_upperBound_1013_; lean_object* v___x_1014_; 
lean_dec(v_h__1_1010_);
v_upperBound_1013_ = lean_ctor_get(v_it_1008_, 1);
lean_inc(v_upperBound_1013_);
lean_dec_ref(v_it_1008_);
v___x_1014_ = lean_apply_2(v_h__2_1011_, v_upperBound_1013_, v_f_1009_);
return v___x_1014_;
}
else
{
lean_object* v_upperBound_1015_; lean_object* v_val_1016_; lean_object* v___x_1017_; 
lean_inc_ref(v_next_1012_);
lean_dec(v_h__2_1011_);
v_upperBound_1015_ = lean_ctor_get(v_it_1008_, 1);
lean_inc(v_upperBound_1015_);
lean_dec_ref(v_it_1008_);
v_val_1016_ = lean_ctor_get(v_next_1012_, 0);
lean_inc(v_val_1016_);
lean_dec_ref_known(v_next_1012_, 1);
v___x_1017_ = lean_apply_3(v_h__1_1010_, v_val_1016_, v_upperBound_1015_, v_f_1009_);
return v___x_1017_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_1018_, lean_object* v_inst_1019_, lean_object* v_inst_1020_, lean_object* v_inst_1021_, lean_object* v_n_1022_, lean_object* v_00_u03b3_1023_, lean_object* v_Pl_1024_, lean_object* v_motive_1025_, lean_object* v_it_1026_, lean_object* v_f_1027_, lean_object* v_h__1_1028_, lean_object* v_h__2_1029_){
_start:
{
lean_object* v_res_1030_; 
v_res_1030_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_1018_, v_inst_1019_, v_inst_1020_, v_inst_1021_, v_n_1022_, v_00_u03b3_1023_, v_Pl_1024_, v_motive_1025_, v_it_1026_, v_f_1027_, v_h__1_1028_, v_h__2_1029_);
lean_dec_ref(v_inst_1021_);
lean_dec_ref(v_inst_1019_);
return v_res_1030_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step___redArg(lean_object* v_inst_1031_, lean_object* v_it_1032_){
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
lean_dec_ref_known(v_it_1032_, 1);
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
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step(lean_object* v_00_u03b1_1045_, lean_object* v_inst_1046_, lean_object* v_it_1047_){
_start:
{
if (lean_obj_tag(v_it_1047_) == 0)
{
lean_object* v___x_1048_; 
lean_dec_ref(v_inst_1046_);
v___x_1048_ = lean_box(2);
return v___x_1048_;
}
else
{
lean_object* v_val_1049_; lean_object* v_succ_x3f_1050_; lean_object* v___x_1052_; uint8_t v_isShared_1053_; uint8_t v_isSharedCheck_1058_; 
v_val_1049_ = lean_ctor_get(v_it_1047_, 0);
lean_inc(v_val_1049_);
lean_dec_ref_known(v_it_1047_, 1);
v_succ_x3f_1050_ = lean_ctor_get(v_inst_1046_, 0);
v_isSharedCheck_1058_ = !lean_is_exclusive(v_inst_1046_);
if (v_isSharedCheck_1058_ == 0)
{
lean_object* v_unused_1059_; 
v_unused_1059_ = lean_ctor_get(v_inst_1046_, 1);
lean_dec(v_unused_1059_);
v___x_1052_ = v_inst_1046_;
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
else
{
lean_inc(v_succ_x3f_1050_);
lean_dec(v_inst_1046_);
v___x_1052_ = lean_box(0);
v_isShared_1053_ = v_isSharedCheck_1058_;
goto v_resetjp_1051_;
}
v_resetjp_1051_:
{
lean_object* v___x_1054_; lean_object* v___x_1056_; 
lean_inc(v_val_1049_);
v___x_1054_ = lean_apply_1(v_succ_x3f_1050_, v_val_1049_);
if (v_isShared_1053_ == 0)
{
lean_ctor_set(v___x_1052_, 1, v_val_1049_);
lean_ctor_set(v___x_1052_, 0, v___x_1054_);
v___x_1056_ = v___x_1052_;
goto v_reusejp_1055_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v___x_1054_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_val_1049_);
v___x_1056_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1055_;
}
v_reusejp_1055_:
{
return v___x_1056_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step___redArg(lean_object* v_inst_1060_, lean_object* v_it_1061_){
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
lean_dec_ref_known(v_it_1061_, 1);
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
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step(lean_object* v_00_u03b1_1074_, lean_object* v_inst_1075_, lean_object* v_it_1076_){
_start:
{
if (lean_obj_tag(v_it_1076_) == 0)
{
lean_object* v___x_1077_; 
lean_dec_ref(v_inst_1075_);
v___x_1077_ = lean_box(2);
return v___x_1077_;
}
else
{
lean_object* v_val_1078_; lean_object* v_succ_x3f_1079_; lean_object* v___x_1081_; uint8_t v_isShared_1082_; uint8_t v_isSharedCheck_1087_; 
v_val_1078_ = lean_ctor_get(v_it_1076_, 0);
lean_inc(v_val_1078_);
lean_dec_ref_known(v_it_1076_, 1);
v_succ_x3f_1079_ = lean_ctor_get(v_inst_1075_, 0);
v_isSharedCheck_1087_ = !lean_is_exclusive(v_inst_1075_);
if (v_isSharedCheck_1087_ == 0)
{
lean_object* v_unused_1088_; 
v_unused_1088_ = lean_ctor_get(v_inst_1075_, 1);
lean_dec(v_unused_1088_);
v___x_1081_ = v_inst_1075_;
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
else
{
lean_inc(v_succ_x3f_1079_);
lean_dec(v_inst_1075_);
v___x_1081_ = lean_box(0);
v_isShared_1082_ = v_isSharedCheck_1087_;
goto v_resetjp_1080_;
}
v_resetjp_1080_:
{
lean_object* v___x_1083_; lean_object* v___x_1085_; 
lean_inc(v_val_1078_);
v___x_1083_ = lean_apply_1(v_succ_x3f_1079_, v_val_1078_);
if (v_isShared_1082_ == 0)
{
lean_ctor_set(v___x_1081_, 1, v_val_1078_);
lean_ctor_set(v___x_1081_, 0, v___x_1083_);
v___x_1085_ = v___x_1081_;
goto v_reusejp_1084_;
}
else
{
lean_object* v_reuseFailAlloc_1086_; 
v_reuseFailAlloc_1086_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1086_, 0, v___x_1083_);
lean_ctor_set(v_reuseFailAlloc_1086_, 1, v_val_1078_);
v___x_1085_ = v_reuseFailAlloc_1086_;
goto v_reusejp_1084_;
}
v_reusejp_1084_:
{
return v___x_1085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0(lean_object* v_inst_1089_, lean_object* v_it_1090_){
_start:
{
if (lean_obj_tag(v_it_1090_) == 0)
{
lean_object* v___x_1091_; 
lean_dec_ref(v_inst_1089_);
v___x_1091_ = lean_box(2);
return v___x_1091_;
}
else
{
lean_object* v_val_1092_; lean_object* v_succ_x3f_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1101_; 
v_val_1092_ = lean_ctor_get(v_it_1090_, 0);
lean_inc(v_val_1092_);
lean_dec_ref_known(v_it_1090_, 1);
v_succ_x3f_1093_ = lean_ctor_get(v_inst_1089_, 0);
v_isSharedCheck_1101_ = !lean_is_exclusive(v_inst_1089_);
if (v_isSharedCheck_1101_ == 0)
{
lean_object* v_unused_1102_; 
v_unused_1102_ = lean_ctor_get(v_inst_1089_, 1);
lean_dec(v_unused_1102_);
v___x_1095_ = v_inst_1089_;
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_succ_x3f_1093_);
lean_dec(v_inst_1089_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1101_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; lean_object* v___x_1099_; 
lean_inc(v_val_1092_);
v___x_1097_ = lean_apply_1(v_succ_x3f_1093_, v_val_1092_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v_val_1092_);
lean_ctor_set(v___x_1095_, 0, v___x_1097_);
v___x_1099_ = v___x_1095_;
goto v_reusejp_1098_;
}
else
{
lean_object* v_reuseFailAlloc_1100_; 
v_reuseFailAlloc_1100_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1100_, 0, v___x_1097_);
lean_ctor_set(v_reuseFailAlloc_1100_, 1, v_val_1092_);
v___x_1099_ = v_reuseFailAlloc_1100_;
goto v_reusejp_1098_;
}
v_reusejp_1098_:
{
return v___x_1099_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg(lean_object* v_inst_1103_){
_start:
{
lean_object* v___f_1104_; 
v___f_1104_ = lean_alloc_closure((void*)(l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1104_, 0, v_inst_1103_);
return v___f_1104_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable(lean_object* v_00_u03b1_1105_, lean_object* v_inst_1106_){
_start:
{
lean_object* v___f_1107_; 
v___f_1107_ = lean_alloc_closure((void*)(l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1107_, 0, v_inst_1106_);
return v___f_1107_;
}
}
lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_1109_; 
v___x_1109_ = lean_box(0);
return v___x_1109_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1110_;
v_res_1110_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___redArg();
stack->m_obj
 = v_res_1110_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_1111_){
_start:
{
lean_object* v_res_1112_; 
v_res_1112_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___redArg();
return v_res_1112_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_, lean_object* v_inst_1116_){
_start:
{
lean_object* v___x_1117_; 
v___x_1117_ = lean_box(0);
return v___x_1117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_1118_, lean_object* v_inst_1119_, lean_object* v_inst_1120_, lean_object* v_inst_1121_){
_start:
{
lean_object* v_res_1122_; 
v_res_1122_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(v_00_u03b1_1118_, v_inst_1119_, v_inst_1120_, v_inst_1121_);
lean_dec_ref(v_inst_1119_);
return v_res_1122_;
}
}
lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_box(0);
return v___x_1124_;
}
}
LEAN_EXPORT void l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1125_;
v_res_1125_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___redArg();
stack->m_obj
 = v_res_1125_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_1126_){
_start:
{
lean_object* v_res_1127_; 
v_res_1127_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___redArg();
return v_res_1127_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_1128_, lean_object* v_inst_1129_, lean_object* v_inst_1130_){
_start:
{
lean_object* v___x_1131_; 
v___x_1131_ = lean_box(0);
return v___x_1131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_1132_, lean_object* v_inst_1133_, lean_object* v_inst_1134_){
_start:
{
lean_object* v_res_1135_; 
v_res_1135_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(v_00_u03b1_1132_, v_inst_1133_, v_inst_1134_);
lean_dec_ref(v_inst_1133_);
return v_res_1135_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_1136_, lean_object* v_it_1137_, lean_object* v_n_1138_){
_start:
{
if (lean_obj_tag(v_it_1137_) == 0)
{
lean_object* v___x_1139_; 
lean_dec(v_n_1138_);
lean_dec_ref(v_inst_1136_);
v___x_1139_ = lean_box(2);
return v___x_1139_;
}
else
{
lean_object* v_succ_x3f_1140_; lean_object* v_succMany_x3f_1141_; lean_object* v___x_1143_; uint8_t v_isShared_1144_; uint8_t v_isSharedCheck_1153_; 
v_succ_x3f_1140_ = lean_ctor_get(v_inst_1136_, 0);
v_succMany_x3f_1141_ = lean_ctor_get(v_inst_1136_, 1);
v_isSharedCheck_1153_ = !lean_is_exclusive(v_inst_1136_);
if (v_isSharedCheck_1153_ == 0)
{
v___x_1143_ = v_inst_1136_;
v_isShared_1144_ = v_isSharedCheck_1153_;
goto v_resetjp_1142_;
}
else
{
lean_inc(v_succMany_x3f_1141_);
lean_inc(v_succ_x3f_1140_);
lean_dec(v_inst_1136_);
v___x_1143_ = lean_box(0);
v_isShared_1144_ = v_isSharedCheck_1153_;
goto v_resetjp_1142_;
}
v_resetjp_1142_:
{
lean_object* v_val_1145_; lean_object* v___x_1146_; 
v_val_1145_ = lean_ctor_get(v_it_1137_, 0);
lean_inc(v_val_1145_);
lean_dec_ref_known(v_it_1137_, 1);
v___x_1146_ = lean_apply_2(v_succMany_x3f_1141_, v_n_1138_, v_val_1145_);
if (lean_obj_tag(v___x_1146_) == 0)
{
lean_object* v___x_1147_; 
lean_del_object(v___x_1143_);
lean_dec_ref(v_succ_x3f_1140_);
v___x_1147_ = lean_box(2);
return v___x_1147_;
}
else
{
lean_object* v_val_1148_; lean_object* v___x_1149_; lean_object* v___x_1151_; 
v_val_1148_ = lean_ctor_get(v___x_1146_, 0);
lean_inc_n(v_val_1148_, 2);
lean_dec_ref_known(v___x_1146_, 1);
v___x_1149_ = lean_apply_1(v_succ_x3f_1140_, v_val_1148_);
if (v_isShared_1144_ == 0)
{
lean_ctor_set(v___x_1143_, 1, v_val_1148_);
lean_ctor_set(v___x_1143_, 0, v___x_1149_);
v___x_1151_ = v___x_1143_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1152_; 
v_reuseFailAlloc_1152_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1152_, 0, v___x_1149_);
lean_ctor_set(v_reuseFailAlloc_1152_, 1, v_val_1148_);
v___x_1151_ = v_reuseFailAlloc_1152_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
return v___x_1151_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg(lean_object* v_inst_1154_){
_start:
{
lean_object* v___f_1155_; 
v___f_1155_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1155_, 0, v_inst_1154_);
return v___f_1155_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess(lean_object* v_00_u03b1_1156_, lean_object* v_inst_1157_, lean_object* v_inst_1158_){
_start:
{
lean_object* v___f_1159_; 
v___f_1159_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1159_, 0, v_inst_1157_);
return v___f_1159_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object* v_toPure_1160_, lean_object* v_inst_1161_, lean_object* v_f_1162_, lean_object* v_toBind_1163_, lean_object* v_next_1164_, lean_object* v_acc_1165_, lean_object* v_h_1166_, lean_object* v_G_1167_){
_start:
{
lean_object* v___f_1168_; lean_object* v___x_1169_; lean_object* v___x_1170_; 
lean_inc(v_next_1164_);
v___f_1168_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1168_, 0, v_toPure_1160_);
lean_closure_set(v___f_1168_, 1, v_inst_1161_);
lean_closure_set(v___f_1168_, 2, v_next_1164_);
lean_closure_set(v___f_1168_, 3, v_G_1167_);
v___x_1169_ = lean_apply_3(v_f_1162_, v_next_1164_, lean_box(0), v_acc_1165_);
v___x_1170_ = lean_apply_4(v_toBind_1163_, lean_box(0), lean_box(0), v___x_1169_, v___f_1168_);
return v___x_1170_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_1171_, lean_object* v_inst_1172_, lean_object* v_acc_1173_, lean_object* v_next_1174_, lean_object* v_f_1175_){
_start:
{
lean_object* v_toApplicative_1176_; lean_object* v_toBind_1177_; lean_object* v_toPure_1178_; lean_object* v___f_1179_; lean_object* v___x_1180_; 
v_toApplicative_1176_ = lean_ctor_get(v_inst_1172_, 0);
lean_inc_ref(v_toApplicative_1176_);
v_toBind_1177_ = lean_ctor_get(v_inst_1172_, 1);
lean_inc(v_toBind_1177_);
lean_dec_ref(v_inst_1172_);
v_toPure_1178_ = lean_ctor_get(v_toApplicative_1176_, 1);
lean_inc(v_toPure_1178_);
lean_dec_ref(v_toApplicative_1176_);
v___f_1179_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1179_, 0, v_toPure_1178_);
lean_closure_set(v___f_1179_, 1, v_inst_1171_);
lean_closure_set(v___f_1179_, 2, v_f_1175_);
lean_closure_set(v___f_1179_, 3, v_toBind_1177_);
v___x_1180_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1179_, v_next_1174_, v_acc_1173_, lean_box(0));
return v___x_1180_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_1181_, lean_object* v_inst_1182_, lean_object* v_inst_1183_, lean_object* v_n_1184_, lean_object* v_inst_1185_, lean_object* v_00_u03b3_1186_, lean_object* v_Pl_1187_, lean_object* v_LargeEnough_1188_, lean_object* v_hl_1189_, lean_object* v_acc_1190_, lean_object* v_next_1191_, lean_object* v_h_1192_, lean_object* v_f_1193_){
_start:
{
lean_object* v_toApplicative_1194_; lean_object* v_toBind_1195_; lean_object* v_toPure_1196_; lean_object* v___f_1197_; lean_object* v___x_1198_; 
v_toApplicative_1194_ = lean_ctor_get(v_inst_1185_, 0);
lean_inc_ref(v_toApplicative_1194_);
v_toBind_1195_ = lean_ctor_get(v_inst_1185_, 1);
lean_inc(v_toBind_1195_);
lean_dec_ref(v_inst_1185_);
v_toPure_1196_ = lean_ctor_get(v_toApplicative_1194_, 1);
lean_inc(v_toPure_1196_);
lean_dec_ref(v_toApplicative_1194_);
v___f_1197_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1197_, 0, v_toPure_1196_);
lean_closure_set(v___f_1197_, 1, v_inst_1182_);
lean_closure_set(v___f_1197_, 2, v_f_1193_);
lean_closure_set(v___f_1197_, 3, v_toBind_1195_);
v___x_1198_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1197_, v_next_1191_, v_acc_1190_, lean_box(0));
return v___x_1198_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_1199_, lean_object* v_inst_1200_, lean_object* v_toBind_1201_, lean_object* v_x_1202_, lean_object* v_00_u03b3_1203_, lean_object* v_Pl_1204_, lean_object* v_it_1205_, lean_object* v_init_1206_, lean_object* v_f_1207_){
_start:
{
if (lean_obj_tag(v_it_1205_) == 0)
{
lean_object* v___x_1208_; 
lean_dec(v_f_1207_);
lean_dec(v_toBind_1201_);
lean_dec_ref(v_inst_1200_);
v___x_1208_ = lean_apply_2(v_toPure_1199_, lean_box(0), v_init_1206_);
return v___x_1208_;
}
else
{
lean_object* v_val_1209_; lean_object* v___f_1210_; lean_object* v___x_1211_; 
v_val_1209_ = lean_ctor_get(v_it_1205_, 0);
lean_inc(v_val_1209_);
lean_dec_ref_known(v_it_1205_, 1);
v___f_1210_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1210_, 0, v_toPure_1199_);
lean_closure_set(v___f_1210_, 1, v_inst_1200_);
lean_closure_set(v___f_1210_, 2, v_f_1207_);
lean_closure_set(v___f_1210_, 3, v_toBind_1201_);
v___x_1211_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1210_, v_val_1209_, v_init_1206_, lean_box(0));
return v___x_1211_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_1212_, lean_object* v_inst_1213_, lean_object* v_toBind_1214_, lean_object* v_x_1215_, lean_object* v_00_u03b3_1216_, lean_object* v_Pl_1217_, lean_object* v_it_1218_, lean_object* v_init_1219_, lean_object* v_f_1220_){
_start:
{
lean_object* v_res_1221_; 
v_res_1221_ = l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_1212_, v_inst_1213_, v_toBind_1214_, v_x_1215_, v_00_u03b3_1216_, v_Pl_1217_, v_it_1218_, v_init_1219_, v_f_1220_);
lean_dec(v_x_1215_);
return v_res_1221_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg(lean_object* v_inst_1222_, lean_object* v_inst_1223_){
_start:
{
lean_object* v_toApplicative_1224_; lean_object* v_toBind_1225_; lean_object* v_toPure_1226_; lean_object* v___f_1227_; 
v_toApplicative_1224_ = lean_ctor_get(v_inst_1223_, 0);
lean_inc_ref(v_toApplicative_1224_);
v_toBind_1225_ = lean_ctor_get(v_inst_1223_, 1);
lean_inc(v_toBind_1225_);
lean_dec_ref(v_inst_1223_);
v_toPure_1226_ = lean_ctor_get(v_toApplicative_1224_, 1);
lean_inc(v_toPure_1226_);
lean_dec_ref(v_toApplicative_1224_);
v___f_1227_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1227_, 0, v_toPure_1226_);
lean_closure_set(v___f_1227_, 1, v_inst_1222_);
lean_closure_set(v___f_1227_, 2, v_toBind_1225_);
return v___f_1227_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop(lean_object* v_00_u03b1_1228_, lean_object* v_inst_1229_, lean_object* v_inst_1230_, lean_object* v_n_1231_, lean_object* v_inst_1232_){
_start:
{
lean_object* v_toApplicative_1233_; lean_object* v_toBind_1234_; lean_object* v_toPure_1235_; lean_object* v___f_1236_; 
v_toApplicative_1233_ = lean_ctor_get(v_inst_1232_, 0);
lean_inc_ref(v_toApplicative_1233_);
v_toBind_1234_ = lean_ctor_get(v_inst_1232_, 1);
lean_inc(v_toBind_1234_);
lean_dec_ref(v_inst_1232_);
v_toPure_1235_ = lean_ctor_get(v_toApplicative_1233_, 1);
lean_inc(v_toPure_1235_);
lean_dec_ref(v_toApplicative_1233_);
v___f_1236_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1236_, 0, v_toPure_1235_);
lean_closure_set(v___f_1236_, 1, v_inst_1229_);
lean_closure_set(v___f_1236_, 2, v_toBind_1234_);
return v___f_1236_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_1237_, lean_object* v_f_1238_, lean_object* v_h__1_1239_, lean_object* v_h__2_1240_){
_start:
{
if (lean_obj_tag(v_it_1237_) == 0)
{
lean_object* v___x_1241_; 
lean_dec(v_h__1_1239_);
v___x_1241_ = lean_apply_1(v_h__2_1240_, v_f_1238_);
return v___x_1241_;
}
else
{
lean_object* v_val_1242_; lean_object* v___x_1243_; 
lean_dec(v_h__2_1240_);
v_val_1242_ = lean_ctor_get(v_it_1237_, 0);
lean_inc(v_val_1242_);
lean_dec_ref_known(v_it_1237_, 1);
v___x_1243_ = lean_apply_2(v_h__1_1239_, v_val_1242_, v_f_1238_);
return v___x_1243_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_1244_, lean_object* v_inst_1245_, lean_object* v_n_1246_, lean_object* v_00_u03b3_1247_, lean_object* v_Pl_1248_, lean_object* v_motive_1249_, lean_object* v_it_1250_, lean_object* v_f_1251_, lean_object* v_h__1_1252_, lean_object* v_h__2_1253_){
_start:
{
if (lean_obj_tag(v_it_1250_) == 0)
{
lean_object* v___x_1254_; 
lean_dec(v_h__1_1252_);
v___x_1254_ = lean_apply_1(v_h__2_1253_, v_f_1251_);
return v___x_1254_;
}
else
{
lean_object* v_val_1255_; lean_object* v___x_1256_; 
lean_dec(v_h__2_1253_);
v_val_1255_ = lean_ctor_get(v_it_1250_, 0);
lean_inc(v_val_1255_);
lean_dec_ref_known(v_it_1250_, 1);
v___x_1256_ = lean_apply_2(v_h__1_1252_, v_val_1255_, v_f_1251_);
return v___x_1256_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_1257_, lean_object* v_inst_1258_, lean_object* v_n_1259_, lean_object* v_00_u03b3_1260_, lean_object* v_Pl_1261_, lean_object* v_motive_1262_, lean_object* v_it_1263_, lean_object* v_f_1264_, lean_object* v_h__1_1265_, lean_object* v_h__2_1266_){
_start:
{
lean_object* v_res_1267_; 
v_res_1267_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_1257_, v_inst_1258_, v_n_1259_, v_00_u03b3_1260_, v_Pl_1261_, v_motive_1262_, v_it_1263_, v_f_1264_, v_h__1_1265_, v_h__2_1266_);
lean_dec_ref(v_inst_1258_);
return v_res_1267_;
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
