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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(0);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_196_){
_start:
{
lean_object* v_res_197_; 
v_res_197_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___redArg();
return v_res_197_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_198_, lean_object* v_inst_199_, lean_object* v_inst_200_, lean_object* v_inst_201_, lean_object* v_inst_202_, lean_object* v_inst_203_){
_start:
{
lean_object* v___x_204_; 
v___x_204_ = lean_box(0);
return v___x_204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_205_, lean_object* v_inst_206_, lean_object* v_inst_207_, lean_object* v_inst_208_, lean_object* v_inst_209_, lean_object* v_inst_210_){
_start:
{
lean_object* v_res_211_; 
v_res_211_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instFinitenessRelation(v_00_u03b1_205_, v_inst_206_, v_inst_207_, v_inst_208_, v_inst_209_, v_inst_210_);
lean_dec_ref(v_inst_208_);
lean_dec_ref(v_inst_206_);
return v_res_211_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_213_; 
v___x_213_ = lean_box(0);
return v___x_213_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_214_){
_start:
{
lean_object* v_res_215_; 
v_res_215_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___redArg();
return v_res_215_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_216_, lean_object* v_inst_217_, lean_object* v_inst_218_, lean_object* v_inst_219_, lean_object* v_inst_220_){
_start:
{
lean_object* v___x_221_; 
v___x_221_ = lean_box(0);
return v___x_221_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_222_, lean_object* v_inst_223_, lean_object* v_inst_224_, lean_object* v_inst_225_, lean_object* v_inst_226_){
_start:
{
lean_object* v_res_227_; 
v_res_227_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instProductivenessRelation(v_00_u03b1_222_, v_inst_223_, v_inst_224_, v_inst_225_, v_inst_226_);
lean_dec_ref(v_inst_225_);
lean_dec_ref(v_inst_223_);
return v_res_227_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter___redArg(lean_object* v_x_228_, lean_object* v_h__1_229_, lean_object* v_h__2_230_){
_start:
{
if (lean_obj_tag(v_x_228_) == 0)
{
lean_object* v___x_231_; lean_object* v___x_232_; 
lean_dec(v_h__2_230_);
v___x_231_ = lean_box(0);
v___x_232_ = lean_apply_1(v_h__1_229_, v___x_231_);
return v___x_232_;
}
else
{
lean_object* v_val_233_; lean_object* v___x_234_; 
lean_dec(v_h__1_229_);
v_val_233_ = lean_ctor_get(v_x_228_, 0);
lean_inc(v_val_233_);
lean_dec_ref_known(v_x_228_, 1);
v___x_234_ = lean_apply_1(v_h__2_230_, v_val_233_);
return v___x_234_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorAccess_match__1_splitter(lean_object* v_00_u03b1_235_, lean_object* v_motive_236_, lean_object* v_x_237_, lean_object* v_h__1_238_, lean_object* v_h__2_239_){
_start:
{
if (lean_obj_tag(v_x_237_) == 0)
{
lean_object* v___x_240_; lean_object* v___x_241_; 
lean_dec(v_h__2_239_);
v___x_240_ = lean_box(0);
v___x_241_ = lean_apply_1(v_h__1_238_, v___x_240_);
return v___x_241_;
}
else
{
lean_object* v_val_242_; lean_object* v___x_243_; 
lean_dec(v_h__1_238_);
v_val_242_ = lean_ctor_get(v_x_237_, 0);
lean_inc(v_val_242_);
lean_dec_ref_known(v_x_237_, 1);
v___x_243_ = lean_apply_1(v_h__2_239_, v_val_242_);
return v___x_243_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_244_, lean_object* v_inst_245_, lean_object* v_it_246_, lean_object* v_n_247_){
_start:
{
lean_object* v_next_248_; 
v_next_248_ = lean_ctor_get(v_it_246_, 0);
lean_inc(v_next_248_);
if (lean_obj_tag(v_next_248_) == 0)
{
lean_object* v___x_249_; 
lean_dec(v_n_247_);
lean_dec_ref(v_it_246_);
lean_dec_ref(v_inst_245_);
lean_dec_ref(v_inst_244_);
v___x_249_ = lean_box(2);
return v___x_249_;
}
else
{
lean_object* v_upperBound_250_; lean_object* v___x_252_; uint8_t v_isShared_253_; uint8_t v_isSharedCheck_274_; 
v_upperBound_250_ = lean_ctor_get(v_it_246_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_it_246_);
if (v_isSharedCheck_274_ == 0)
{
lean_object* v_unused_275_; 
v_unused_275_ = lean_ctor_get(v_it_246_, 0);
lean_dec(v_unused_275_);
v___x_252_ = v_it_246_;
v_isShared_253_ = v_isSharedCheck_274_;
goto v_resetjp_251_;
}
else
{
lean_inc(v_upperBound_250_);
lean_dec(v_it_246_);
v___x_252_ = lean_box(0);
v_isShared_253_ = v_isSharedCheck_274_;
goto v_resetjp_251_;
}
v_resetjp_251_:
{
lean_object* v_succ_x3f_254_; lean_object* v_succMany_x3f_255_; lean_object* v___x_257_; uint8_t v_isShared_258_; uint8_t v_isSharedCheck_273_; 
v_succ_x3f_254_ = lean_ctor_get(v_inst_244_, 0);
v_succMany_x3f_255_ = lean_ctor_get(v_inst_244_, 1);
v_isSharedCheck_273_ = !lean_is_exclusive(v_inst_244_);
if (v_isSharedCheck_273_ == 0)
{
v___x_257_ = v_inst_244_;
v_isShared_258_ = v_isSharedCheck_273_;
goto v_resetjp_256_;
}
else
{
lean_inc(v_succMany_x3f_255_);
lean_inc(v_succ_x3f_254_);
lean_dec(v_inst_244_);
v___x_257_ = lean_box(0);
v_isShared_258_ = v_isSharedCheck_273_;
goto v_resetjp_256_;
}
v_resetjp_256_:
{
lean_object* v_val_259_; lean_object* v___x_260_; 
v_val_259_ = lean_ctor_get(v_next_248_, 0);
lean_inc(v_val_259_);
lean_dec_ref_known(v_next_248_, 1);
v___x_260_ = lean_apply_2(v_succMany_x3f_255_, v_n_247_, v_val_259_);
if (lean_obj_tag(v___x_260_) == 0)
{
lean_object* v___x_261_; 
lean_del_object(v___x_257_);
lean_dec_ref(v_succ_x3f_254_);
lean_del_object(v___x_252_);
lean_dec(v_upperBound_250_);
lean_dec_ref(v_inst_245_);
v___x_261_ = lean_box(2);
return v___x_261_;
}
else
{
lean_object* v_val_262_; lean_object* v___x_263_; uint8_t v___x_264_; 
v_val_262_ = lean_ctor_get(v___x_260_, 0);
lean_inc_n(v_val_262_, 2);
lean_dec_ref_known(v___x_260_, 1);
lean_inc(v_upperBound_250_);
v___x_263_ = lean_apply_2(v_inst_245_, v_val_262_, v_upperBound_250_);
v___x_264_ = lean_unbox(v___x_263_);
if (v___x_264_ == 0)
{
lean_object* v___x_265_; 
lean_dec(v_val_262_);
lean_del_object(v___x_257_);
lean_dec_ref(v_succ_x3f_254_);
lean_del_object(v___x_252_);
lean_dec(v_upperBound_250_);
v___x_265_ = lean_box(2);
return v___x_265_;
}
else
{
lean_object* v___x_266_; lean_object* v___x_268_; 
lean_inc(v_val_262_);
v___x_266_ = lean_apply_1(v_succ_x3f_254_, v_val_262_);
if (v_isShared_253_ == 0)
{
lean_ctor_set(v___x_252_, 0, v___x_266_);
v___x_268_ = v___x_252_;
goto v_reusejp_267_;
}
else
{
lean_object* v_reuseFailAlloc_272_; 
v_reuseFailAlloc_272_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_272_, 0, v___x_266_);
lean_ctor_set(v_reuseFailAlloc_272_, 1, v_upperBound_250_);
v___x_268_ = v_reuseFailAlloc_272_;
goto v_reusejp_267_;
}
v_reusejp_267_:
{
lean_object* v___x_270_; 
if (v_isShared_258_ == 0)
{
lean_ctor_set(v___x_257_, 1, v_val_262_);
lean_ctor_set(v___x_257_, 0, v___x_268_);
v___x_270_ = v___x_257_;
goto v_reusejp_269_;
}
else
{
lean_object* v_reuseFailAlloc_271_; 
v_reuseFailAlloc_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_271_, 0, v___x_268_);
lean_ctor_set(v_reuseFailAlloc_271_, 1, v_val_262_);
v___x_270_ = v_reuseFailAlloc_271_;
goto v_reusejp_269_;
}
v_reusejp_269_:
{
return v___x_270_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess___redArg(lean_object* v_inst_276_, lean_object* v_inst_277_){
_start:
{
lean_object* v___f_278_; 
v___f_278_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_278_, 0, v_inst_276_);
lean_closure_set(v___f_278_, 1, v_inst_277_);
return v___f_278_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorAccess(lean_object* v_00_u03b1_279_, lean_object* v_inst_280_, lean_object* v_inst_281_, lean_object* v_inst_282_, lean_object* v_inst_283_, lean_object* v_inst_284_){
_start:
{
lean_object* v___f_285_; 
v___f_285_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_285_, 0, v_inst_280_);
lean_closure_set(v___f_285_, 1, v_inst_282_);
return v___f_285_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0(lean_object* v_toPure_286_, lean_object* v_inst_287_, lean_object* v_next_288_, lean_object* v_G_289_, lean_object* v_____do__lift_290_){
_start:
{
if (lean_obj_tag(v_____do__lift_290_) == 0)
{
lean_object* v_a_291_; lean_object* v___x_292_; 
lean_dec(v_G_289_);
lean_dec(v_next_288_);
lean_dec_ref(v_inst_287_);
v_a_291_ = lean_ctor_get(v_____do__lift_290_, 0);
lean_inc(v_a_291_);
lean_dec_ref_known(v_____do__lift_290_, 1);
v___x_292_ = lean_apply_2(v_toPure_286_, lean_box(0), v_a_291_);
return v___x_292_;
}
else
{
lean_object* v_a_293_; lean_object* v_succ_x3f_294_; lean_object* v___x_295_; 
v_a_293_ = lean_ctor_get(v_____do__lift_290_, 0);
lean_inc(v_a_293_);
lean_dec_ref_known(v_____do__lift_290_, 1);
v_succ_x3f_294_ = lean_ctor_get(v_inst_287_, 0);
lean_inc_ref(v_succ_x3f_294_);
lean_dec_ref(v_inst_287_);
v___x_295_ = lean_apply_1(v_succ_x3f_294_, v_next_288_);
if (lean_obj_tag(v___x_295_) == 0)
{
lean_object* v___x_296_; 
lean_dec(v_G_289_);
v___x_296_ = lean_apply_2(v_toPure_286_, lean_box(0), v_a_293_);
return v___x_296_;
}
else
{
lean_object* v_val_297_; lean_object* v___x_298_; 
lean_dec(v_toPure_286_);
v_val_297_ = lean_ctor_get(v___x_295_, 0);
lean_inc(v_val_297_);
lean_dec_ref_known(v___x_295_, 1);
v___x_298_ = lean_apply_4(v_G_289_, v_val_297_, v_a_293_, lean_box(0), lean_box(0));
return v___x_298_;
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object* v_inst_299_, lean_object* v_upperBound_300_, lean_object* v_toPure_301_, lean_object* v_inst_302_, lean_object* v_f_303_, lean_object* v_toBind_304_, lean_object* v_next_305_, lean_object* v_acc_306_, lean_object* v_h_307_, lean_object* v_G_308_){
_start:
{
lean_object* v___x_309_; uint8_t v___x_310_; 
lean_inc(v_next_305_);
v___x_309_ = lean_apply_2(v_inst_299_, v_next_305_, v_upperBound_300_);
v___x_310_ = lean_unbox(v___x_309_);
if (v___x_310_ == 0)
{
lean_object* v___x_311_; 
lean_dec(v_G_308_);
lean_dec(v_next_305_);
lean_dec(v_toBind_304_);
lean_dec(v_f_303_);
lean_dec_ref(v_inst_302_);
v___x_311_ = lean_apply_2(v_toPure_301_, lean_box(0), v_acc_306_);
return v___x_311_;
}
else
{
lean_object* v___f_312_; lean_object* v___x_313_; lean_object* v___x_314_; 
lean_inc(v_next_305_);
v___f_312_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_312_, 0, v_toPure_301_);
lean_closure_set(v___f_312_, 1, v_inst_302_);
lean_closure_set(v___f_312_, 2, v_next_305_);
lean_closure_set(v___f_312_, 3, v_G_308_);
v___x_313_ = lean_apply_4(v_f_303_, v_next_305_, lean_box(0), lean_box(0), v_acc_306_);
v___x_314_ = lean_apply_4(v_toBind_304_, lean_box(0), lean_box(0), v___x_313_, v___f_312_);
return v___x_314_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_315_, lean_object* v_inst_316_, lean_object* v_inst_317_, lean_object* v_upperBound_318_, lean_object* v_acc_319_, lean_object* v_next_320_, lean_object* v_f_321_){
_start:
{
lean_object* v_toApplicative_322_; lean_object* v_toBind_323_; lean_object* v_toPure_324_; lean_object* v___f_325_; lean_object* v___x_326_; 
v_toApplicative_322_ = lean_ctor_get(v_inst_317_, 0);
lean_inc_ref(v_toApplicative_322_);
v_toBind_323_ = lean_ctor_get(v_inst_317_, 1);
lean_inc(v_toBind_323_);
lean_dec_ref(v_inst_317_);
v_toPure_324_ = lean_ctor_get(v_toApplicative_322_, 1);
lean_inc(v_toPure_324_);
lean_dec_ref(v_toApplicative_322_);
v___f_325_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_325_, 0, v_inst_316_);
lean_closure_set(v___f_325_, 1, v_upperBound_318_);
lean_closure_set(v___f_325_, 2, v_toPure_324_);
lean_closure_set(v___f_325_, 3, v_inst_315_);
lean_closure_set(v___f_325_, 4, v_f_321_);
lean_closure_set(v___f_325_, 5, v_toBind_323_);
v___x_326_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_325_, v_next_320_, v_acc_319_, lean_box(0));
return v___x_326_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_327_, lean_object* v_inst_328_, lean_object* v_inst_329_, lean_object* v_inst_330_, lean_object* v_inst_331_, lean_object* v_inst_332_, lean_object* v_n_333_, lean_object* v_inst_334_, lean_object* v_00_u03b3_335_, lean_object* v_Pl_336_, lean_object* v_LargeEnough_337_, lean_object* v_hl_338_, lean_object* v_upperBound_339_, lean_object* v_acc_340_, lean_object* v_next_341_, lean_object* v_h_342_, lean_object* v_f_343_){
_start:
{
lean_object* v_toApplicative_344_; lean_object* v_toBind_345_; lean_object* v_toPure_346_; lean_object* v___f_347_; lean_object* v___x_348_; 
v_toApplicative_344_ = lean_ctor_get(v_inst_334_, 0);
lean_inc_ref(v_toApplicative_344_);
v_toBind_345_ = lean_ctor_get(v_inst_334_, 1);
lean_inc(v_toBind_345_);
lean_dec_ref(v_inst_334_);
v_toPure_346_ = lean_ctor_get(v_toApplicative_344_, 1);
lean_inc(v_toPure_346_);
lean_dec_ref(v_toApplicative_344_);
v___f_347_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_347_, 0, v_inst_330_);
lean_closure_set(v___f_347_, 1, v_upperBound_339_);
lean_closure_set(v___f_347_, 2, v_toPure_346_);
lean_closure_set(v___f_347_, 3, v_inst_328_);
lean_closure_set(v___f_347_, 4, v_f_343_);
lean_closure_set(v___f_347_, 5, v_toBind_345_);
v___x_348_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_347_, v_next_341_, v_acc_340_, lean_box(0));
return v___x_348_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop_loop___boxed(lean_object** _args){
lean_object* v_00_u03b1_349_ = _args[0];
lean_object* v_inst_350_ = _args[1];
lean_object* v_inst_351_ = _args[2];
lean_object* v_inst_352_ = _args[3];
lean_object* v_inst_353_ = _args[4];
lean_object* v_inst_354_ = _args[5];
lean_object* v_n_355_ = _args[6];
lean_object* v_inst_356_ = _args[7];
lean_object* v_00_u03b3_357_ = _args[8];
lean_object* v_Pl_358_ = _args[9];
lean_object* v_LargeEnough_359_ = _args[10];
lean_object* v_hl_360_ = _args[11];
lean_object* v_upperBound_361_ = _args[12];
lean_object* v_acc_362_ = _args[13];
lean_object* v_next_363_ = _args[14];
lean_object* v_h_364_ = _args[15];
lean_object* v_f_365_ = _args[16];
_start:
{
lean_object* v_res_366_; 
v_res_366_ = l_Std_Rxc_Iterator_instIteratorLoop_loop(v_00_u03b1_349_, v_inst_350_, v_inst_351_, v_inst_352_, v_inst_353_, v_inst_354_, v_n_355_, v_inst_356_, v_00_u03b3_357_, v_Pl_358_, v_LargeEnough_359_, v_hl_360_, v_upperBound_361_, v_acc_362_, v_next_363_, v_h_364_, v_f_365_);
return v_res_366_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1(lean_object* v_inst_367_, lean_object* v_upperBound_368_, lean_object* v_toPure_369_, lean_object* v_inst_370_, lean_object* v_f_371_, lean_object* v_toBind_372_, lean_object* v_next_373_, lean_object* v_acc_374_, lean_object* v_h_375_, lean_object* v_G_376_){
_start:
{
lean_object* v___x_377_; uint8_t v___x_378_; 
lean_inc(v_next_373_);
v___x_377_ = lean_apply_2(v_inst_367_, v_next_373_, v_upperBound_368_);
v___x_378_ = lean_unbox(v___x_377_);
if (v___x_378_ == 0)
{
lean_object* v___x_379_; 
lean_dec(v_G_376_);
lean_dec(v_next_373_);
lean_dec(v_toBind_372_);
lean_dec(v_f_371_);
lean_dec_ref(v_inst_370_);
v___x_379_ = lean_apply_2(v_toPure_369_, lean_box(0), v_acc_374_);
return v___x_379_;
}
else
{
lean_object* v___f_380_; lean_object* v___x_381_; lean_object* v___x_382_; 
lean_inc(v_next_373_);
v___f_380_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_380_, 0, v_toPure_369_);
lean_closure_set(v___f_380_, 1, v_inst_370_);
lean_closure_set(v___f_380_, 2, v_next_373_);
lean_closure_set(v___f_380_, 3, v_G_376_);
v___x_381_ = lean_apply_3(v_f_371_, v_next_373_, lean_box(0), v_acc_374_);
v___x_382_ = lean_apply_4(v_toBind_372_, lean_box(0), lean_box(0), v___x_381_, v___f_380_);
return v___x_382_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0(lean_object* v_toPure_383_, lean_object* v_inst_384_, lean_object* v_inst_385_, lean_object* v_toBind_386_, lean_object* v_x_387_, lean_object* v_00_u03b3_388_, lean_object* v_Pl_389_, lean_object* v_it_390_, lean_object* v_init_391_, lean_object* v_f_392_){
_start:
{
lean_object* v_next_393_; 
v_next_393_ = lean_ctor_get(v_it_390_, 0);
lean_inc(v_next_393_);
if (lean_obj_tag(v_next_393_) == 0)
{
lean_object* v___x_394_; 
lean_dec(v_f_392_);
lean_dec_ref(v_it_390_);
lean_dec(v_toBind_386_);
lean_dec_ref(v_inst_385_);
lean_dec_ref(v_inst_384_);
v___x_394_ = lean_apply_2(v_toPure_383_, lean_box(0), v_init_391_);
return v___x_394_;
}
else
{
lean_object* v_upperBound_395_; lean_object* v_val_396_; lean_object* v___f_397_; lean_object* v___x_398_; 
v_upperBound_395_ = lean_ctor_get(v_it_390_, 1);
lean_inc(v_upperBound_395_);
lean_dec_ref(v_it_390_);
v_val_396_ = lean_ctor_get(v_next_393_, 0);
lean_inc(v_val_396_);
lean_dec_ref_known(v_next_393_, 1);
v___f_397_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_397_, 0, v_inst_384_);
lean_closure_set(v___f_397_, 1, v_upperBound_395_);
lean_closure_set(v___f_397_, 2, v_toPure_383_);
lean_closure_set(v___f_397_, 3, v_inst_385_);
lean_closure_set(v___f_397_, 4, v_f_392_);
lean_closure_set(v___f_397_, 5, v_toBind_386_);
v___x_398_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_397_, v_val_396_, v_init_391_, lean_box(0));
return v___x_398_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0___boxed(lean_object* v_toPure_399_, lean_object* v_inst_400_, lean_object* v_inst_401_, lean_object* v_toBind_402_, lean_object* v_x_403_, lean_object* v_00_u03b3_404_, lean_object* v_Pl_405_, lean_object* v_it_406_, lean_object* v_init_407_, lean_object* v_f_408_){
_start:
{
lean_object* v_res_409_; 
v_res_409_ = l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0(v_toPure_399_, v_inst_400_, v_inst_401_, v_toBind_402_, v_x_403_, v_00_u03b3_404_, v_Pl_405_, v_it_406_, v_init_407_, v_f_408_);
lean_dec(v_x_403_);
return v_res_409_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop___redArg(lean_object* v_inst_410_, lean_object* v_inst_411_, lean_object* v_inst_412_){
_start:
{
lean_object* v_toApplicative_413_; lean_object* v_toBind_414_; lean_object* v_toPure_415_; lean_object* v___f_416_; 
v_toApplicative_413_ = lean_ctor_get(v_inst_412_, 0);
lean_inc_ref(v_toApplicative_413_);
v_toBind_414_ = lean_ctor_get(v_inst_412_, 1);
lean_inc(v_toBind_414_);
lean_dec_ref(v_inst_412_);
v_toPure_415_ = lean_ctor_get(v_toApplicative_413_, 1);
lean_inc(v_toPure_415_);
lean_dec_ref(v_toApplicative_413_);
v___f_416_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_416_, 0, v_toPure_415_);
lean_closure_set(v___f_416_, 1, v_inst_411_);
lean_closure_set(v___f_416_, 2, v_inst_410_);
lean_closure_set(v___f_416_, 3, v_toBind_414_);
return v___f_416_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxc_Iterator_instIteratorLoop(lean_object* v_00_u03b1_417_, lean_object* v_inst_418_, lean_object* v_inst_419_, lean_object* v_inst_420_, lean_object* v_inst_421_, lean_object* v_inst_422_, lean_object* v_n_423_, lean_object* v_inst_424_){
_start:
{
lean_object* v_toApplicative_425_; lean_object* v_toBind_426_; lean_object* v_toPure_427_; lean_object* v___f_428_; 
v_toApplicative_425_ = lean_ctor_get(v_inst_424_, 0);
lean_inc_ref(v_toApplicative_425_);
v_toBind_426_ = lean_ctor_get(v_inst_424_, 1);
lean_inc(v_toBind_426_);
lean_dec_ref(v_inst_424_);
v_toPure_427_ = lean_ctor_get(v_toApplicative_425_, 1);
lean_inc(v_toPure_427_);
lean_dec_ref(v_toApplicative_425_);
v___f_428_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__0___boxed), 10, 4);
lean_closure_set(v___f_428_, 0, v_toPure_427_);
lean_closure_set(v___f_428_, 1, v_inst_420_);
lean_closure_set(v___f_428_, 2, v_inst_418_);
lean_closure_set(v___f_428_, 3, v_toBind_426_);
return v___f_428_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___redArg(lean_object* v_____do__lift_429_, lean_object* v_h__1_430_, lean_object* v_h__2_431_){
_start:
{
if (lean_obj_tag(v_____do__lift_429_) == 0)
{
lean_object* v_a_432_; lean_object* v___x_433_; 
lean_dec(v_h__1_430_);
v_a_432_ = lean_ctor_get(v_____do__lift_429_, 0);
lean_inc(v_a_432_);
lean_dec_ref_known(v_____do__lift_429_, 1);
v___x_433_ = lean_apply_2(v_h__2_431_, v_a_432_, lean_box(0));
return v___x_433_;
}
else
{
lean_object* v_a_434_; lean_object* v___x_435_; 
lean_dec(v_h__2_431_);
v_a_434_ = lean_ctor_get(v_____do__lift_429_, 0);
lean_inc(v_a_434_);
lean_dec_ref_known(v_____do__lift_429_, 1);
v___x_435_ = lean_apply_2(v_h__1_430_, v_a_434_, lean_box(0));
return v___x_435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(lean_object* v_00_u03b1_436_, lean_object* v_00_u03b3_437_, lean_object* v_Pl_438_, lean_object* v_acc_439_, lean_object* v_next_440_, lean_object* v_motive_441_, lean_object* v_____do__lift_442_, lean_object* v_h__1_443_, lean_object* v_h__2_444_){
_start:
{
if (lean_obj_tag(v_____do__lift_442_) == 0)
{
lean_object* v_a_445_; lean_object* v___x_446_; 
lean_dec(v_h__1_443_);
v_a_445_ = lean_ctor_get(v_____do__lift_442_, 0);
lean_inc(v_a_445_);
lean_dec_ref_known(v_____do__lift_442_, 1);
v___x_446_ = lean_apply_2(v_h__2_444_, v_a_445_, lean_box(0));
return v___x_446_;
}
else
{
lean_object* v_a_447_; lean_object* v___x_448_; 
lean_dec(v_h__2_444_);
v_a_447_ = lean_ctor_get(v_____do__lift_442_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v_____do__lift_442_, 1);
v___x_448_ = lean_apply_2(v_h__1_443_, v_a_447_, lean_box(0));
return v___x_448_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter___boxed(lean_object* v_00_u03b1_449_, lean_object* v_00_u03b3_450_, lean_object* v_Pl_451_, lean_object* v_acc_452_, lean_object* v_next_453_, lean_object* v_motive_454_, lean_object* v_____do__lift_455_, lean_object* v_h__1_456_, lean_object* v_h__2_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_wf_match__1_splitter(v_00_u03b1_449_, v_00_u03b3_450_, v_Pl_451_, v_acc_452_, v_next_453_, v_motive_454_, v_____do__lift_455_, v_h__1_456_, v_h__2_457_);
lean_dec(v_next_453_);
lean_dec(v_acc_452_);
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter___redArg(lean_object* v_x_459_, lean_object* v_h__1_460_, lean_object* v_h__2_461_){
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__1_splitter(lean_object* v_00_u03b1_465_, lean_object* v_motive_466_, lean_object* v_x_467_, lean_object* v_h__1_468_, lean_object* v_h__2_469_){
_start:
{
if (lean_obj_tag(v_x_467_) == 0)
{
lean_object* v___x_470_; 
lean_dec(v_h__1_468_);
v___x_470_ = lean_apply_1(v_h__2_469_, lean_box(0));
return v___x_470_;
}
else
{
lean_object* v_val_471_; lean_object* v___x_472_; 
lean_dec(v_h__2_469_);
v_val_471_ = lean_ctor_get(v_x_467_, 0);
lean_inc(v_val_471_);
lean_dec_ref_known(v_x_467_, 1);
v___x_472_ = lean_apply_2(v_h__1_468_, v_val_471_, lean_box(0));
return v___x_472_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___redArg(lean_object* v_____do__lift_473_, lean_object* v_h__1_474_, lean_object* v_h__2_475_){
_start:
{
if (lean_obj_tag(v_____do__lift_473_) == 0)
{
lean_object* v_a_476_; lean_object* v___x_477_; 
lean_dec(v_h__1_474_);
v_a_476_ = lean_ctor_get(v_____do__lift_473_, 0);
lean_inc(v_a_476_);
lean_dec_ref_known(v_____do__lift_473_, 1);
v___x_477_ = lean_apply_2(v_h__2_475_, v_a_476_, lean_box(0));
return v___x_477_;
}
else
{
lean_object* v_a_478_; lean_object* v___x_479_; 
lean_dec(v_h__2_475_);
v_a_478_ = lean_ctor_get(v_____do__lift_473_, 0);
lean_inc(v_a_478_);
lean_dec_ref_known(v_____do__lift_473_, 1);
v___x_479_ = lean_apply_2(v_h__1_474_, v_a_478_, lean_box(0));
return v___x_479_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(lean_object* v_00_u03b1_480_, lean_object* v_00_u03b3_481_, lean_object* v_Pl_482_, lean_object* v_next_483_, lean_object* v_acc_484_, lean_object* v_motive_485_, lean_object* v_____do__lift_486_, lean_object* v_h__1_487_, lean_object* v_h__2_488_){
_start:
{
if (lean_obj_tag(v_____do__lift_486_) == 0)
{
lean_object* v_a_489_; lean_object* v___x_490_; 
lean_dec(v_h__1_487_);
v_a_489_ = lean_ctor_get(v_____do__lift_486_, 0);
lean_inc(v_a_489_);
lean_dec_ref_known(v_____do__lift_486_, 1);
v___x_490_ = lean_apply_2(v_h__2_488_, v_a_489_, lean_box(0));
return v___x_490_;
}
else
{
lean_object* v_a_491_; lean_object* v___x_492_; 
lean_dec(v_h__2_488_);
v_a_491_ = lean_ctor_get(v_____do__lift_486_, 0);
lean_inc(v_a_491_);
lean_dec_ref_known(v_____do__lift_486_, 1);
v___x_492_ = lean_apply_2(v_h__1_487_, v_a_491_, lean_box(0));
return v___x_492_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter___boxed(lean_object* v_00_u03b1_493_, lean_object* v_00_u03b3_494_, lean_object* v_Pl_495_, lean_object* v_next_496_, lean_object* v_acc_497_, lean_object* v_motive_498_, lean_object* v_____do__lift_499_, lean_object* v_h__1_500_, lean_object* v_h__2_501_){
_start:
{
lean_object* v_res_502_; 
v_res_502_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_loop_match__3_splitter(v_00_u03b1_493_, v_00_u03b3_494_, v_Pl_495_, v_next_496_, v_acc_497_, v_motive_498_, v_____do__lift_499_, v_h__1_500_, v_h__2_501_);
lean_dec(v_acc_497_);
lean_dec(v_next_496_);
return v_res_502_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___redArg(lean_object* v_x_503_, lean_object* v_h__1_504_, lean_object* v_h__2_505_, lean_object* v_h__3_506_){
_start:
{
switch(lean_obj_tag(v_x_503_))
{
case 0:
{
lean_object* v_it_507_; lean_object* v_out_508_; lean_object* v___x_509_; 
lean_dec(v_h__3_506_);
lean_dec(v_h__2_505_);
v_it_507_ = lean_ctor_get(v_x_503_, 0);
lean_inc(v_it_507_);
v_out_508_ = lean_ctor_get(v_x_503_, 1);
lean_inc(v_out_508_);
lean_dec_ref_known(v_x_503_, 2);
v___x_509_ = lean_apply_3(v_h__1_504_, v_it_507_, v_out_508_, lean_box(0));
return v___x_509_;
}
case 1:
{
lean_object* v_it_510_; lean_object* v___x_511_; 
lean_dec(v_h__3_506_);
lean_dec(v_h__1_504_);
v_it_510_ = lean_ctor_get(v_x_503_, 0);
lean_inc(v_it_510_);
lean_dec_ref_known(v_x_503_, 1);
v___x_511_ = lean_apply_2(v_h__2_505_, v_it_510_, lean_box(0));
return v___x_511_;
}
default: 
{
lean_object* v___x_512_; 
lean_dec(v_h__2_505_);
lean_dec(v_h__1_504_);
v___x_512_ = lean_apply_1(v_h__3_506_, lean_box(0));
return v___x_512_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(lean_object* v_00_u03b1_513_, lean_object* v_00_u03b2_514_, lean_object* v_m_515_, lean_object* v_inst_516_, lean_object* v_it_517_, lean_object* v_motive_518_, lean_object* v_x_519_, lean_object* v_h__1_520_, lean_object* v_h__2_521_, lean_object* v_h__3_522_){
_start:
{
switch(lean_obj_tag(v_x_519_))
{
case 0:
{
lean_object* v_it_523_; lean_object* v_out_524_; lean_object* v___x_525_; 
lean_dec(v_h__3_522_);
lean_dec(v_h__2_521_);
v_it_523_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_it_523_);
v_out_524_ = lean_ctor_get(v_x_519_, 1);
lean_inc(v_out_524_);
lean_dec_ref_known(v_x_519_, 2);
v___x_525_ = lean_apply_3(v_h__1_520_, v_it_523_, v_out_524_, lean_box(0));
return v___x_525_;
}
case 1:
{
lean_object* v_it_526_; lean_object* v___x_527_; 
lean_dec(v_h__3_522_);
lean_dec(v_h__1_520_);
v_it_526_ = lean_ctor_get(v_x_519_, 0);
lean_inc(v_it_526_);
lean_dec_ref_known(v_x_519_, 1);
v___x_527_ = lean_apply_2(v_h__2_521_, v_it_526_, lean_box(0));
return v___x_527_;
}
default: 
{
lean_object* v___x_528_; 
lean_dec(v_h__2_521_);
lean_dec(v_h__1_520_);
v___x_528_ = lean_apply_1(v_h__3_522_, lean_box(0));
return v___x_528_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter___boxed(lean_object* v_00_u03b1_529_, lean_object* v_00_u03b2_530_, lean_object* v_m_531_, lean_object* v_inst_532_, lean_object* v_it_533_, lean_object* v_motive_534_, lean_object* v_x_535_, lean_object* v_h__1_536_, lean_object* v_h__2_537_, lean_object* v_h__3_538_){
_start:
{
lean_object* v_res_539_; 
v_res_539_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__3_splitter(v_00_u03b1_529_, v_00_u03b2_530_, v_m_531_, v_inst_532_, v_it_533_, v_motive_534_, v_x_535_, v_h__1_536_, v_h__2_537_, v_h__3_538_);
lean_dec(v_it_533_);
lean_dec(v_inst_532_);
return v_res_539_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___redArg(lean_object* v_____do__lift_540_, lean_object* v_h__1_541_, lean_object* v_h__2_542_){
_start:
{
if (lean_obj_tag(v_____do__lift_540_) == 0)
{
lean_object* v_a_543_; lean_object* v___x_544_; 
lean_dec(v_h__1_541_);
v_a_543_ = lean_ctor_get(v_____do__lift_540_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v_____do__lift_540_, 1);
v___x_544_ = lean_apply_2(v_h__2_542_, v_a_543_, lean_box(0));
return v___x_544_;
}
else
{
lean_object* v_a_545_; lean_object* v___x_546_; 
lean_dec(v_h__2_542_);
v_a_545_ = lean_ctor_get(v_____do__lift_540_, 0);
lean_inc(v_a_545_);
lean_dec_ref_known(v_____do__lift_540_, 1);
v___x_546_ = lean_apply_2(v_h__1_541_, v_a_545_, lean_box(0));
return v___x_546_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(lean_object* v_00_u03b2_547_, lean_object* v_00_u03b3_548_, lean_object* v_init_549_, lean_object* v_PlausibleForInStep_550_, lean_object* v_out_551_, lean_object* v_motive_552_, lean_object* v_____do__lift_553_, lean_object* v_h__1_554_, lean_object* v_h__2_555_){
_start:
{
if (lean_obj_tag(v_____do__lift_553_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_557_; 
lean_dec(v_h__1_554_);
v_a_556_ = lean_ctor_get(v_____do__lift_553_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v_____do__lift_553_, 1);
v___x_557_ = lean_apply_2(v_h__2_555_, v_a_556_, lean_box(0));
return v___x_557_;
}
else
{
lean_object* v_a_558_; lean_object* v___x_559_; 
lean_dec(v_h__2_555_);
v_a_558_ = lean_ctor_get(v_____do__lift_553_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v_____do__lift_553_, 1);
v___x_559_ = lean_apply_2(v_h__1_554_, v_a_558_, lean_box(0));
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter___boxed(lean_object* v_00_u03b2_560_, lean_object* v_00_u03b3_561_, lean_object* v_init_562_, lean_object* v_PlausibleForInStep_563_, lean_object* v_out_564_, lean_object* v_motive_565_, lean_object* v_____do__lift_566_, lean_object* v_h__1_567_, lean_object* v_h__2_568_){
_start:
{
lean_object* v_res_569_; 
v_res_569_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27__eq__match__step_match__1_splitter(v_00_u03b2_560_, v_00_u03b3_561_, v_init_562_, v_PlausibleForInStep_563_, v_out_564_, v_motive_565_, v_____do__lift_566_, v_h__1_567_, v_h__2_568_);
lean_dec(v_out_564_);
lean_dec(v_init_562_);
return v_res_569_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_570_, lean_object* v_f_571_, lean_object* v_h__1_572_, lean_object* v_h__2_573_){
_start:
{
lean_object* v_next_574_; 
v_next_574_ = lean_ctor_get(v_it_570_, 0);
if (lean_obj_tag(v_next_574_) == 0)
{
lean_object* v_upperBound_575_; lean_object* v___x_576_; 
lean_dec(v_h__1_572_);
v_upperBound_575_ = lean_ctor_get(v_it_570_, 1);
lean_inc(v_upperBound_575_);
lean_dec_ref(v_it_570_);
v___x_576_ = lean_apply_2(v_h__2_573_, v_upperBound_575_, v_f_571_);
return v___x_576_;
}
else
{
lean_object* v_upperBound_577_; lean_object* v_val_578_; lean_object* v___x_579_; 
lean_inc_ref(v_next_574_);
lean_dec(v_h__2_573_);
v_upperBound_577_ = lean_ctor_get(v_it_570_, 1);
lean_inc(v_upperBound_577_);
lean_dec_ref(v_it_570_);
v_val_578_ = lean_ctor_get(v_next_574_, 0);
lean_inc(v_val_578_);
lean_dec_ref_known(v_next_574_, 1);
v___x_579_ = lean_apply_3(v_h__1_572_, v_val_578_, v_upperBound_577_, v_f_571_);
return v___x_579_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_580_, lean_object* v_inst_581_, lean_object* v_inst_582_, lean_object* v_inst_583_, lean_object* v_n_584_, lean_object* v_00_u03b3_585_, lean_object* v_Pl_586_, lean_object* v_motive_587_, lean_object* v_it_588_, lean_object* v_f_589_, lean_object* v_h__1_590_, lean_object* v_h__2_591_){
_start:
{
lean_object* v_next_592_; 
v_next_592_ = lean_ctor_get(v_it_588_, 0);
if (lean_obj_tag(v_next_592_) == 0)
{
lean_object* v_upperBound_593_; lean_object* v___x_594_; 
lean_dec(v_h__1_590_);
v_upperBound_593_ = lean_ctor_get(v_it_588_, 1);
lean_inc(v_upperBound_593_);
lean_dec_ref(v_it_588_);
v___x_594_ = lean_apply_2(v_h__2_591_, v_upperBound_593_, v_f_589_);
return v___x_594_;
}
else
{
lean_object* v_upperBound_595_; lean_object* v_val_596_; lean_object* v___x_597_; 
lean_inc_ref(v_next_592_);
lean_dec(v_h__2_591_);
v_upperBound_595_ = lean_ctor_get(v_it_588_, 1);
lean_inc(v_upperBound_595_);
lean_dec_ref(v_it_588_);
v_val_596_ = lean_ctor_get(v_next_592_, 0);
lean_inc(v_val_596_);
lean_dec_ref_known(v_next_592_, 1);
v___x_597_ = lean_apply_3(v_h__1_590_, v_val_596_, v_upperBound_595_, v_f_589_);
return v___x_597_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_598_, lean_object* v_inst_599_, lean_object* v_inst_600_, lean_object* v_inst_601_, lean_object* v_n_602_, lean_object* v_00_u03b3_603_, lean_object* v_Pl_604_, lean_object* v_motive_605_, lean_object* v_it_606_, lean_object* v_f_607_, lean_object* v_h__1_608_, lean_object* v_h__2_609_){
_start:
{
lean_object* v_res_610_; 
v_res_610_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxc_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_598_, v_inst_599_, v_inst_600_, v_inst_601_, v_n_602_, v_00_u03b3_603_, v_Pl_604_, v_motive_605_, v_it_606_, v_f_607_, v_h__1_608_, v_h__2_609_);
lean_dec_ref(v_inst_601_);
lean_dec_ref(v_inst_599_);
return v_res_610_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___redArg(lean_object* v_x_611_, lean_object* v_h__1_612_, lean_object* v_h__2_613_, lean_object* v_h__3_614_){
_start:
{
switch(lean_obj_tag(v_x_611_))
{
case 0:
{
lean_object* v_it_615_; lean_object* v_out_616_; lean_object* v___x_617_; 
lean_dec(v_h__3_614_);
lean_dec(v_h__2_613_);
v_it_615_ = lean_ctor_get(v_x_611_, 0);
lean_inc(v_it_615_);
v_out_616_ = lean_ctor_get(v_x_611_, 1);
lean_inc(v_out_616_);
lean_dec_ref_known(v_x_611_, 2);
v___x_617_ = lean_apply_3(v_h__1_612_, v_it_615_, v_out_616_, lean_box(0));
return v___x_617_;
}
case 1:
{
lean_object* v_it_618_; lean_object* v___x_619_; 
lean_dec(v_h__3_614_);
lean_dec(v_h__1_612_);
v_it_618_ = lean_ctor_get(v_x_611_, 0);
lean_inc(v_it_618_);
lean_dec_ref_known(v_x_611_, 1);
v___x_619_ = lean_apply_2(v_h__2_613_, v_it_618_, lean_box(0));
return v___x_619_;
}
default: 
{
lean_object* v___x_620_; 
lean_dec(v_h__2_613_);
lean_dec(v_h__1_612_);
v___x_620_ = lean_apply_1(v_h__3_614_, lean_box(0));
return v___x_620_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(lean_object* v_m_621_, lean_object* v_00_u03b1_622_, lean_object* v_00_u03b2_623_, lean_object* v_inst_624_, lean_object* v_it_625_, lean_object* v_motive_626_, lean_object* v_x_627_, lean_object* v_h__1_628_, lean_object* v_h__2_629_, lean_object* v_h__3_630_){
_start:
{
switch(lean_obj_tag(v_x_627_))
{
case 0:
{
lean_object* v_it_631_; lean_object* v_out_632_; lean_object* v___x_633_; 
lean_dec(v_h__3_630_);
lean_dec(v_h__2_629_);
v_it_631_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_it_631_);
v_out_632_ = lean_ctor_get(v_x_627_, 1);
lean_inc(v_out_632_);
lean_dec_ref_known(v_x_627_, 2);
v___x_633_ = lean_apply_3(v_h__1_628_, v_it_631_, v_out_632_, lean_box(0));
return v___x_633_;
}
case 1:
{
lean_object* v_it_634_; lean_object* v___x_635_; 
lean_dec(v_h__3_630_);
lean_dec(v_h__1_628_);
v_it_634_ = lean_ctor_get(v_x_627_, 0);
lean_inc(v_it_634_);
lean_dec_ref_known(v_x_627_, 1);
v___x_635_ = lean_apply_2(v_h__2_629_, v_it_634_, lean_box(0));
return v___x_635_;
}
default: 
{
lean_object* v___x_636_; 
lean_dec(v_h__2_629_);
lean_dec(v_h__1_628_);
v___x_636_ = lean_apply_1(v_h__3_630_, lean_box(0));
return v___x_636_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter___boxed(lean_object* v_m_637_, lean_object* v_00_u03b1_638_, lean_object* v_00_u03b2_639_, lean_object* v_inst_640_, lean_object* v_it_641_, lean_object* v_motive_642_, lean_object* v_x_643_, lean_object* v_h__1_644_, lean_object* v_h__2_645_, lean_object* v_h__3_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__3_splitter(v_m_637_, v_00_u03b1_638_, v_00_u03b2_639_, v_inst_640_, v_it_641_, v_motive_642_, v_x_643_, v_h__1_644_, v_h__2_645_, v_h__3_646_);
lean_dec(v_it_641_);
lean_dec(v_inst_640_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___redArg(lean_object* v_____do__lift_648_, lean_object* v_h__1_649_, lean_object* v_h__2_650_){
_start:
{
if (lean_obj_tag(v_____do__lift_648_) == 0)
{
lean_object* v_a_651_; lean_object* v___x_652_; 
lean_dec(v_h__1_649_);
v_a_651_ = lean_ctor_get(v_____do__lift_648_, 0);
lean_inc(v_a_651_);
lean_dec_ref_known(v_____do__lift_648_, 1);
v___x_652_ = lean_apply_2(v_h__2_650_, v_a_651_, lean_box(0));
return v___x_652_;
}
else
{
lean_object* v_a_653_; lean_object* v___x_654_; 
lean_dec(v_h__2_650_);
v_a_653_ = lean_ctor_get(v_____do__lift_648_, 0);
lean_inc(v_a_653_);
lean_dec_ref_known(v_____do__lift_648_, 1);
v___x_654_ = lean_apply_2(v_h__1_649_, v_a_653_, lean_box(0));
return v___x_654_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(lean_object* v_00_u03b2_655_, lean_object* v_00_u03b3_656_, lean_object* v_PlausibleForInStep_657_, lean_object* v_acc_658_, lean_object* v_out_659_, lean_object* v_motive_660_, lean_object* v_____do__lift_661_, lean_object* v_h__1_662_, lean_object* v_h__2_663_){
_start:
{
if (lean_obj_tag(v_____do__lift_661_) == 0)
{
lean_object* v_a_664_; lean_object* v___x_665_; 
lean_dec(v_h__1_662_);
v_a_664_ = lean_ctor_get(v_____do__lift_661_, 0);
lean_inc(v_a_664_);
lean_dec_ref_known(v_____do__lift_661_, 1);
v___x_665_ = lean_apply_2(v_h__2_663_, v_a_664_, lean_box(0));
return v___x_665_;
}
else
{
lean_object* v_a_666_; lean_object* v___x_667_; 
lean_dec(v_h__2_663_);
v_a_666_ = lean_ctor_get(v_____do__lift_661_, 0);
lean_inc(v_a_666_);
lean_dec_ref_known(v_____do__lift_661_, 1);
v___x_667_ = lean_apply_2(v_h__1_662_, v_a_666_, lean_box(0));
return v___x_667_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter___boxed(lean_object* v_00_u03b2_668_, lean_object* v_00_u03b3_669_, lean_object* v_PlausibleForInStep_670_, lean_object* v_acc_671_, lean_object* v_out_672_, lean_object* v_motive_673_, lean_object* v_____do__lift_674_, lean_object* v_h__1_675_, lean_object* v_h__2_676_){
_start:
{
lean_object* v_res_677_; 
v_res_677_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_IterM_DefaultConsumers_forIn_x27_match__1_splitter(v_00_u03b2_668_, v_00_u03b3_669_, v_PlausibleForInStep_670_, v_acc_671_, v_out_672_, v_motive_673_, v_____do__lift_674_, v_h__1_675_, v_h__2_676_);
lean_dec(v_out_672_);
lean_dec(v_acc_671_);
return v_res_677_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step___redArg(lean_object* v_inst_678_, lean_object* v_inst_679_, lean_object* v_it_680_){
_start:
{
lean_object* v_next_681_; 
v_next_681_ = lean_ctor_get(v_it_680_, 0);
lean_inc(v_next_681_);
if (lean_obj_tag(v_next_681_) == 0)
{
lean_object* v___x_682_; 
lean_dec_ref(v_it_680_);
lean_dec_ref(v_inst_679_);
lean_dec_ref(v_inst_678_);
v___x_682_ = lean_box(2);
return v___x_682_;
}
else
{
lean_object* v_upperBound_683_; lean_object* v___x_685_; uint8_t v_isShared_686_; uint8_t v_isSharedCheck_704_; 
v_upperBound_683_ = lean_ctor_get(v_it_680_, 1);
v_isSharedCheck_704_ = !lean_is_exclusive(v_it_680_);
if (v_isSharedCheck_704_ == 0)
{
lean_object* v_unused_705_; 
v_unused_705_ = lean_ctor_get(v_it_680_, 0);
lean_dec(v_unused_705_);
v___x_685_ = v_it_680_;
v_isShared_686_ = v_isSharedCheck_704_;
goto v_resetjp_684_;
}
else
{
lean_inc(v_upperBound_683_);
lean_dec(v_it_680_);
v___x_685_ = lean_box(0);
v_isShared_686_ = v_isSharedCheck_704_;
goto v_resetjp_684_;
}
v_resetjp_684_:
{
lean_object* v_val_687_; lean_object* v___x_688_; uint8_t v___x_689_; 
v_val_687_ = lean_ctor_get(v_next_681_, 0);
lean_inc_n(v_val_687_, 2);
lean_dec_ref_known(v_next_681_, 1);
lean_inc(v_upperBound_683_);
v___x_688_ = lean_apply_2(v_inst_679_, v_val_687_, v_upperBound_683_);
v___x_689_ = lean_unbox(v___x_688_);
if (v___x_689_ == 0)
{
lean_object* v___x_690_; 
lean_dec(v_val_687_);
lean_del_object(v___x_685_);
lean_dec(v_upperBound_683_);
lean_dec_ref(v_inst_678_);
v___x_690_ = lean_box(2);
return v___x_690_;
}
else
{
lean_object* v_succ_x3f_691_; lean_object* v___x_693_; uint8_t v_isShared_694_; uint8_t v_isSharedCheck_702_; 
v_succ_x3f_691_ = lean_ctor_get(v_inst_678_, 0);
v_isSharedCheck_702_ = !lean_is_exclusive(v_inst_678_);
if (v_isSharedCheck_702_ == 0)
{
lean_object* v_unused_703_; 
v_unused_703_ = lean_ctor_get(v_inst_678_, 1);
lean_dec(v_unused_703_);
v___x_693_ = v_inst_678_;
v_isShared_694_ = v_isSharedCheck_702_;
goto v_resetjp_692_;
}
else
{
lean_inc(v_succ_x3f_691_);
lean_dec(v_inst_678_);
v___x_693_ = lean_box(0);
v_isShared_694_ = v_isSharedCheck_702_;
goto v_resetjp_692_;
}
v_resetjp_692_:
{
lean_object* v___x_695_; lean_object* v___x_697_; 
lean_inc(v_val_687_);
v___x_695_ = lean_apply_1(v_succ_x3f_691_, v_val_687_);
if (v_isShared_686_ == 0)
{
lean_ctor_set(v___x_685_, 0, v___x_695_);
v___x_697_ = v___x_685_;
goto v_reusejp_696_;
}
else
{
lean_object* v_reuseFailAlloc_701_; 
v_reuseFailAlloc_701_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_701_, 0, v___x_695_);
lean_ctor_set(v_reuseFailAlloc_701_, 1, v_upperBound_683_);
v___x_697_ = v_reuseFailAlloc_701_;
goto v_reusejp_696_;
}
v_reusejp_696_:
{
lean_object* v___x_699_; 
if (v_isShared_694_ == 0)
{
lean_ctor_set(v___x_693_, 1, v_val_687_);
lean_ctor_set(v___x_693_, 0, v___x_697_);
v___x_699_ = v___x_693_;
goto v_reusejp_698_;
}
else
{
lean_object* v_reuseFailAlloc_700_; 
v_reuseFailAlloc_700_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_700_, 0, v___x_697_);
lean_ctor_set(v_reuseFailAlloc_700_, 1, v_val_687_);
v___x_699_ = v_reuseFailAlloc_700_;
goto v_reusejp_698_;
}
v_reusejp_698_:
{
return v___x_699_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_Monadic_step(lean_object* v_00_u03b1_706_, lean_object* v_inst_707_, lean_object* v_inst_708_, lean_object* v_inst_709_, lean_object* v_it_710_){
_start:
{
lean_object* v_next_711_; 
v_next_711_ = lean_ctor_get(v_it_710_, 0);
lean_inc(v_next_711_);
if (lean_obj_tag(v_next_711_) == 0)
{
lean_object* v___x_712_; 
lean_dec_ref(v_it_710_);
lean_dec_ref(v_inst_709_);
lean_dec_ref(v_inst_707_);
v___x_712_ = lean_box(2);
return v___x_712_;
}
else
{
lean_object* v_upperBound_713_; lean_object* v___x_715_; uint8_t v_isShared_716_; uint8_t v_isSharedCheck_734_; 
v_upperBound_713_ = lean_ctor_get(v_it_710_, 1);
v_isSharedCheck_734_ = !lean_is_exclusive(v_it_710_);
if (v_isSharedCheck_734_ == 0)
{
lean_object* v_unused_735_; 
v_unused_735_ = lean_ctor_get(v_it_710_, 0);
lean_dec(v_unused_735_);
v___x_715_ = v_it_710_;
v_isShared_716_ = v_isSharedCheck_734_;
goto v_resetjp_714_;
}
else
{
lean_inc(v_upperBound_713_);
lean_dec(v_it_710_);
v___x_715_ = lean_box(0);
v_isShared_716_ = v_isSharedCheck_734_;
goto v_resetjp_714_;
}
v_resetjp_714_:
{
lean_object* v_val_717_; lean_object* v___x_718_; uint8_t v___x_719_; 
v_val_717_ = lean_ctor_get(v_next_711_, 0);
lean_inc_n(v_val_717_, 2);
lean_dec_ref_known(v_next_711_, 1);
lean_inc(v_upperBound_713_);
v___x_718_ = lean_apply_2(v_inst_709_, v_val_717_, v_upperBound_713_);
v___x_719_ = lean_unbox(v___x_718_);
if (v___x_719_ == 0)
{
lean_object* v___x_720_; 
lean_dec(v_val_717_);
lean_del_object(v___x_715_);
lean_dec(v_upperBound_713_);
lean_dec_ref(v_inst_707_);
v___x_720_ = lean_box(2);
return v___x_720_;
}
else
{
lean_object* v_succ_x3f_721_; lean_object* v___x_723_; uint8_t v_isShared_724_; uint8_t v_isSharedCheck_732_; 
v_succ_x3f_721_ = lean_ctor_get(v_inst_707_, 0);
v_isSharedCheck_732_ = !lean_is_exclusive(v_inst_707_);
if (v_isSharedCheck_732_ == 0)
{
lean_object* v_unused_733_; 
v_unused_733_ = lean_ctor_get(v_inst_707_, 1);
lean_dec(v_unused_733_);
v___x_723_ = v_inst_707_;
v_isShared_724_ = v_isSharedCheck_732_;
goto v_resetjp_722_;
}
else
{
lean_inc(v_succ_x3f_721_);
lean_dec(v_inst_707_);
v___x_723_ = lean_box(0);
v_isShared_724_ = v_isSharedCheck_732_;
goto v_resetjp_722_;
}
v_resetjp_722_:
{
lean_object* v___x_725_; lean_object* v___x_727_; 
lean_inc(v_val_717_);
v___x_725_ = lean_apply_1(v_succ_x3f_721_, v_val_717_);
if (v_isShared_716_ == 0)
{
lean_ctor_set(v___x_715_, 0, v___x_725_);
v___x_727_ = v___x_715_;
goto v_reusejp_726_;
}
else
{
lean_object* v_reuseFailAlloc_731_; 
v_reuseFailAlloc_731_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_731_, 0, v___x_725_);
lean_ctor_set(v_reuseFailAlloc_731_, 1, v_upperBound_713_);
v___x_727_ = v_reuseFailAlloc_731_;
goto v_reusejp_726_;
}
v_reusejp_726_:
{
lean_object* v___x_729_; 
if (v_isShared_724_ == 0)
{
lean_ctor_set(v___x_723_, 1, v_val_717_);
lean_ctor_set(v___x_723_, 0, v___x_727_);
v___x_729_ = v___x_723_;
goto v_reusejp_728_;
}
else
{
lean_object* v_reuseFailAlloc_730_; 
v_reuseFailAlloc_730_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_730_, 0, v___x_727_);
lean_ctor_set(v_reuseFailAlloc_730_, 1, v_val_717_);
v___x_729_ = v_reuseFailAlloc_730_;
goto v_reusejp_728_;
}
v_reusejp_728_:
{
return v___x_729_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step___redArg(lean_object* v_inst_736_, lean_object* v_inst_737_, lean_object* v_it_738_){
_start:
{
lean_object* v_next_739_; 
v_next_739_ = lean_ctor_get(v_it_738_, 0);
lean_inc(v_next_739_);
if (lean_obj_tag(v_next_739_) == 0)
{
lean_object* v___x_740_; 
lean_dec_ref(v_it_738_);
lean_dec_ref(v_inst_737_);
lean_dec_ref(v_inst_736_);
v___x_740_ = lean_box(2);
return v___x_740_;
}
else
{
lean_object* v_upperBound_741_; lean_object* v___x_743_; uint8_t v_isShared_744_; uint8_t v_isSharedCheck_762_; 
v_upperBound_741_ = lean_ctor_get(v_it_738_, 1);
v_isSharedCheck_762_ = !lean_is_exclusive(v_it_738_);
if (v_isSharedCheck_762_ == 0)
{
lean_object* v_unused_763_; 
v_unused_763_ = lean_ctor_get(v_it_738_, 0);
lean_dec(v_unused_763_);
v___x_743_ = v_it_738_;
v_isShared_744_ = v_isSharedCheck_762_;
goto v_resetjp_742_;
}
else
{
lean_inc(v_upperBound_741_);
lean_dec(v_it_738_);
v___x_743_ = lean_box(0);
v_isShared_744_ = v_isSharedCheck_762_;
goto v_resetjp_742_;
}
v_resetjp_742_:
{
lean_object* v_val_745_; lean_object* v___x_746_; uint8_t v___x_747_; 
v_val_745_ = lean_ctor_get(v_next_739_, 0);
lean_inc_n(v_val_745_, 2);
lean_dec_ref_known(v_next_739_, 1);
lean_inc(v_upperBound_741_);
v___x_746_ = lean_apply_2(v_inst_737_, v_val_745_, v_upperBound_741_);
v___x_747_ = lean_unbox(v___x_746_);
if (v___x_747_ == 0)
{
lean_object* v___x_748_; 
lean_dec(v_val_745_);
lean_del_object(v___x_743_);
lean_dec(v_upperBound_741_);
lean_dec_ref(v_inst_736_);
v___x_748_ = lean_box(2);
return v___x_748_;
}
else
{
lean_object* v_succ_x3f_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_760_; 
v_succ_x3f_749_ = lean_ctor_get(v_inst_736_, 0);
v_isSharedCheck_760_ = !lean_is_exclusive(v_inst_736_);
if (v_isSharedCheck_760_ == 0)
{
lean_object* v_unused_761_; 
v_unused_761_ = lean_ctor_get(v_inst_736_, 1);
lean_dec(v_unused_761_);
v___x_751_ = v_inst_736_;
v_isShared_752_ = v_isSharedCheck_760_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_succ_x3f_749_);
lean_dec(v_inst_736_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_760_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_753_; lean_object* v___x_755_; 
lean_inc(v_val_745_);
v___x_753_ = lean_apply_1(v_succ_x3f_749_, v_val_745_);
if (v_isShared_744_ == 0)
{
lean_ctor_set(v___x_743_, 0, v___x_753_);
v___x_755_ = v___x_743_;
goto v_reusejp_754_;
}
else
{
lean_object* v_reuseFailAlloc_759_; 
v_reuseFailAlloc_759_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_759_, 0, v___x_753_);
lean_ctor_set(v_reuseFailAlloc_759_, 1, v_upperBound_741_);
v___x_755_ = v_reuseFailAlloc_759_;
goto v_reusejp_754_;
}
v_reusejp_754_:
{
lean_object* v___x_757_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 1, v_val_745_);
lean_ctor_set(v___x_751_, 0, v___x_755_);
v___x_757_ = v___x_751_;
goto v_reusejp_756_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v___x_755_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_val_745_);
v___x_757_ = v_reuseFailAlloc_758_;
goto v_reusejp_756_;
}
v_reusejp_756_:
{
return v___x_757_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_step(lean_object* v_00_u03b1_764_, lean_object* v_inst_765_, lean_object* v_inst_766_, lean_object* v_inst_767_, lean_object* v_it_768_){
_start:
{
lean_object* v_next_769_; 
v_next_769_ = lean_ctor_get(v_it_768_, 0);
lean_inc(v_next_769_);
if (lean_obj_tag(v_next_769_) == 0)
{
lean_object* v___x_770_; 
lean_dec_ref(v_it_768_);
lean_dec_ref(v_inst_767_);
lean_dec_ref(v_inst_765_);
v___x_770_ = lean_box(2);
return v___x_770_;
}
else
{
lean_object* v_upperBound_771_; lean_object* v___x_773_; uint8_t v_isShared_774_; uint8_t v_isSharedCheck_792_; 
v_upperBound_771_ = lean_ctor_get(v_it_768_, 1);
v_isSharedCheck_792_ = !lean_is_exclusive(v_it_768_);
if (v_isSharedCheck_792_ == 0)
{
lean_object* v_unused_793_; 
v_unused_793_ = lean_ctor_get(v_it_768_, 0);
lean_dec(v_unused_793_);
v___x_773_ = v_it_768_;
v_isShared_774_ = v_isSharedCheck_792_;
goto v_resetjp_772_;
}
else
{
lean_inc(v_upperBound_771_);
lean_dec(v_it_768_);
v___x_773_ = lean_box(0);
v_isShared_774_ = v_isSharedCheck_792_;
goto v_resetjp_772_;
}
v_resetjp_772_:
{
lean_object* v_val_775_; lean_object* v___x_776_; uint8_t v___x_777_; 
v_val_775_ = lean_ctor_get(v_next_769_, 0);
lean_inc_n(v_val_775_, 2);
lean_dec_ref_known(v_next_769_, 1);
lean_inc(v_upperBound_771_);
v___x_776_ = lean_apply_2(v_inst_767_, v_val_775_, v_upperBound_771_);
v___x_777_ = lean_unbox(v___x_776_);
if (v___x_777_ == 0)
{
lean_object* v___x_778_; 
lean_dec(v_val_775_);
lean_del_object(v___x_773_);
lean_dec(v_upperBound_771_);
lean_dec_ref(v_inst_765_);
v___x_778_ = lean_box(2);
return v___x_778_;
}
else
{
lean_object* v_succ_x3f_779_; lean_object* v___x_781_; uint8_t v_isShared_782_; uint8_t v_isSharedCheck_790_; 
v_succ_x3f_779_ = lean_ctor_get(v_inst_765_, 0);
v_isSharedCheck_790_ = !lean_is_exclusive(v_inst_765_);
if (v_isSharedCheck_790_ == 0)
{
lean_object* v_unused_791_; 
v_unused_791_ = lean_ctor_get(v_inst_765_, 1);
lean_dec(v_unused_791_);
v___x_781_ = v_inst_765_;
v_isShared_782_ = v_isSharedCheck_790_;
goto v_resetjp_780_;
}
else
{
lean_inc(v_succ_x3f_779_);
lean_dec(v_inst_765_);
v___x_781_ = lean_box(0);
v_isShared_782_ = v_isSharedCheck_790_;
goto v_resetjp_780_;
}
v_resetjp_780_:
{
lean_object* v___x_783_; lean_object* v___x_785_; 
lean_inc(v_val_775_);
v___x_783_ = lean_apply_1(v_succ_x3f_779_, v_val_775_);
if (v_isShared_774_ == 0)
{
lean_ctor_set(v___x_773_, 0, v___x_783_);
v___x_785_ = v___x_773_;
goto v_reusejp_784_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_783_);
lean_ctor_set(v_reuseFailAlloc_789_, 1, v_upperBound_771_);
v___x_785_ = v_reuseFailAlloc_789_;
goto v_reusejp_784_;
}
v_reusejp_784_:
{
lean_object* v___x_787_; 
if (v_isShared_782_ == 0)
{
lean_ctor_set(v___x_781_, 1, v_val_775_);
lean_ctor_set(v___x_781_, 0, v___x_785_);
v___x_787_ = v___x_781_;
goto v_reusejp_786_;
}
else
{
lean_object* v_reuseFailAlloc_788_; 
v_reuseFailAlloc_788_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_788_, 0, v___x_785_);
lean_ctor_set(v_reuseFailAlloc_788_, 1, v_val_775_);
v___x_787_ = v_reuseFailAlloc_788_;
goto v_reusejp_786_;
}
v_reusejp_786_:
{
return v___x_787_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0(lean_object* v_inst_794_, lean_object* v_inst_795_, lean_object* v_it_796_){
_start:
{
lean_object* v_next_797_; 
v_next_797_ = lean_ctor_get(v_it_796_, 0);
lean_inc(v_next_797_);
if (lean_obj_tag(v_next_797_) == 0)
{
lean_object* v___x_798_; 
lean_dec_ref(v_it_796_);
lean_dec_ref(v_inst_795_);
lean_dec_ref(v_inst_794_);
v___x_798_ = lean_box(2);
return v___x_798_;
}
else
{
lean_object* v_upperBound_799_; lean_object* v___x_801_; uint8_t v_isShared_802_; uint8_t v_isSharedCheck_820_; 
v_upperBound_799_ = lean_ctor_get(v_it_796_, 1);
v_isSharedCheck_820_ = !lean_is_exclusive(v_it_796_);
if (v_isSharedCheck_820_ == 0)
{
lean_object* v_unused_821_; 
v_unused_821_ = lean_ctor_get(v_it_796_, 0);
lean_dec(v_unused_821_);
v___x_801_ = v_it_796_;
v_isShared_802_ = v_isSharedCheck_820_;
goto v_resetjp_800_;
}
else
{
lean_inc(v_upperBound_799_);
lean_dec(v_it_796_);
v___x_801_ = lean_box(0);
v_isShared_802_ = v_isSharedCheck_820_;
goto v_resetjp_800_;
}
v_resetjp_800_:
{
lean_object* v_val_803_; lean_object* v___x_804_; uint8_t v___x_805_; 
v_val_803_ = lean_ctor_get(v_next_797_, 0);
lean_inc_n(v_val_803_, 2);
lean_dec_ref_known(v_next_797_, 1);
lean_inc(v_upperBound_799_);
v___x_804_ = lean_apply_2(v_inst_794_, v_val_803_, v_upperBound_799_);
v___x_805_ = lean_unbox(v___x_804_);
if (v___x_805_ == 0)
{
lean_object* v___x_806_; 
lean_dec(v_val_803_);
lean_del_object(v___x_801_);
lean_dec(v_upperBound_799_);
lean_dec_ref(v_inst_795_);
v___x_806_ = lean_box(2);
return v___x_806_;
}
else
{
lean_object* v_succ_x3f_807_; lean_object* v___x_809_; uint8_t v_isShared_810_; uint8_t v_isSharedCheck_818_; 
v_succ_x3f_807_ = lean_ctor_get(v_inst_795_, 0);
v_isSharedCheck_818_ = !lean_is_exclusive(v_inst_795_);
if (v_isSharedCheck_818_ == 0)
{
lean_object* v_unused_819_; 
v_unused_819_ = lean_ctor_get(v_inst_795_, 1);
lean_dec(v_unused_819_);
v___x_809_ = v_inst_795_;
v_isShared_810_ = v_isSharedCheck_818_;
goto v_resetjp_808_;
}
else
{
lean_inc(v_succ_x3f_807_);
lean_dec(v_inst_795_);
v___x_809_ = lean_box(0);
v_isShared_810_ = v_isSharedCheck_818_;
goto v_resetjp_808_;
}
v_resetjp_808_:
{
lean_object* v___x_811_; lean_object* v___x_813_; 
lean_inc(v_val_803_);
v___x_811_ = lean_apply_1(v_succ_x3f_807_, v_val_803_);
if (v_isShared_802_ == 0)
{
lean_ctor_set(v___x_801_, 0, v___x_811_);
v___x_813_ = v___x_801_;
goto v_reusejp_812_;
}
else
{
lean_object* v_reuseFailAlloc_817_; 
v_reuseFailAlloc_817_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_817_, 0, v___x_811_);
lean_ctor_set(v_reuseFailAlloc_817_, 1, v_upperBound_799_);
v___x_813_ = v_reuseFailAlloc_817_;
goto v_reusejp_812_;
}
v_reusejp_812_:
{
lean_object* v___x_815_; 
if (v_isShared_810_ == 0)
{
lean_ctor_set(v___x_809_, 1, v_val_803_);
lean_ctor_set(v___x_809_, 0, v___x_813_);
v___x_815_ = v___x_809_;
goto v_reusejp_814_;
}
else
{
lean_object* v_reuseFailAlloc_816_; 
v_reuseFailAlloc_816_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_816_, 0, v___x_813_);
lean_ctor_set(v_reuseFailAlloc_816_, 1, v_val_803_);
v___x_815_ = v_reuseFailAlloc_816_;
goto v_reusejp_814_;
}
v_reusejp_814_:
{
return v___x_815_;
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg(lean_object* v_inst_822_, lean_object* v_inst_823_){
_start:
{
lean_object* v___f_824_; 
v___f_824_ = lean_alloc_closure((void*)(l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_824_, 0, v_inst_823_);
lean_closure_set(v___f_824_, 1, v_inst_822_);
return v___f_824_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT(lean_object* v_00_u03b1_825_, lean_object* v_inst_826_, lean_object* v_inst_827_, lean_object* v_inst_828_){
_start:
{
lean_object* v___f_829_; 
v___f_829_ = lean_alloc_closure((void*)(l_Std_Rxo_instIteratorIteratorIdOfUpwardEnumerableOfDecidableLT___redArg___lam__0), 3, 2);
lean_closure_set(v___f_829_, 0, v_inst_828_);
lean_closure_set(v___f_829_, 1, v_inst_826_);
return v___f_829_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_831_; 
v___x_831_ = lean_box(0);
return v___x_831_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instFinitenessRelation___redArg();
return v_res_833_;
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
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_849_; 
v___x_849_ = lean_box(0);
return v___x_849_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_850_){
_start:
{
lean_object* v_res_851_; 
v_res_851_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___redArg();
return v_res_851_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_852_, lean_object* v_inst_853_, lean_object* v_inst_854_, lean_object* v_inst_855_, lean_object* v_inst_856_){
_start:
{
lean_object* v___x_857_; 
v___x_857_ = lean_box(0);
return v___x_857_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_858_, lean_object* v_inst_859_, lean_object* v_inst_860_, lean_object* v_inst_861_, lean_object* v_inst_862_){
_start:
{
lean_object* v_res_863_; 
v_res_863_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instProductivenessRelation(v_00_u03b1_858_, v_inst_859_, v_inst_860_, v_inst_861_, v_inst_862_);
lean_dec_ref(v_inst_861_);
lean_dec_ref(v_inst_859_);
return v_res_863_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_864_, lean_object* v_inst_865_, lean_object* v_it_866_, lean_object* v_n_867_){
_start:
{
lean_object* v_next_868_; 
v_next_868_ = lean_ctor_get(v_it_866_, 0);
lean_inc(v_next_868_);
if (lean_obj_tag(v_next_868_) == 0)
{
lean_object* v___x_869_; 
lean_dec(v_n_867_);
lean_dec_ref(v_it_866_);
lean_dec_ref(v_inst_865_);
lean_dec_ref(v_inst_864_);
v___x_869_ = lean_box(2);
return v___x_869_;
}
else
{
lean_object* v_upperBound_870_; lean_object* v___x_872_; uint8_t v_isShared_873_; uint8_t v_isSharedCheck_894_; 
v_upperBound_870_ = lean_ctor_get(v_it_866_, 1);
v_isSharedCheck_894_ = !lean_is_exclusive(v_it_866_);
if (v_isSharedCheck_894_ == 0)
{
lean_object* v_unused_895_; 
v_unused_895_ = lean_ctor_get(v_it_866_, 0);
lean_dec(v_unused_895_);
v___x_872_ = v_it_866_;
v_isShared_873_ = v_isSharedCheck_894_;
goto v_resetjp_871_;
}
else
{
lean_inc(v_upperBound_870_);
lean_dec(v_it_866_);
v___x_872_ = lean_box(0);
v_isShared_873_ = v_isSharedCheck_894_;
goto v_resetjp_871_;
}
v_resetjp_871_:
{
lean_object* v_succ_x3f_874_; lean_object* v_succMany_x3f_875_; lean_object* v___x_877_; uint8_t v_isShared_878_; uint8_t v_isSharedCheck_893_; 
v_succ_x3f_874_ = lean_ctor_get(v_inst_864_, 0);
v_succMany_x3f_875_ = lean_ctor_get(v_inst_864_, 1);
v_isSharedCheck_893_ = !lean_is_exclusive(v_inst_864_);
if (v_isSharedCheck_893_ == 0)
{
v___x_877_ = v_inst_864_;
v_isShared_878_ = v_isSharedCheck_893_;
goto v_resetjp_876_;
}
else
{
lean_inc(v_succMany_x3f_875_);
lean_inc(v_succ_x3f_874_);
lean_dec(v_inst_864_);
v___x_877_ = lean_box(0);
v_isShared_878_ = v_isSharedCheck_893_;
goto v_resetjp_876_;
}
v_resetjp_876_:
{
lean_object* v_val_879_; lean_object* v___x_880_; 
v_val_879_ = lean_ctor_get(v_next_868_, 0);
lean_inc(v_val_879_);
lean_dec_ref_known(v_next_868_, 1);
v___x_880_ = lean_apply_2(v_succMany_x3f_875_, v_n_867_, v_val_879_);
if (lean_obj_tag(v___x_880_) == 0)
{
lean_object* v___x_881_; 
lean_del_object(v___x_877_);
lean_dec_ref(v_succ_x3f_874_);
lean_del_object(v___x_872_);
lean_dec(v_upperBound_870_);
lean_dec_ref(v_inst_865_);
v___x_881_ = lean_box(2);
return v___x_881_;
}
else
{
lean_object* v_val_882_; lean_object* v___x_883_; uint8_t v___x_884_; 
v_val_882_ = lean_ctor_get(v___x_880_, 0);
lean_inc_n(v_val_882_, 2);
lean_dec_ref_known(v___x_880_, 1);
lean_inc(v_upperBound_870_);
v___x_883_ = lean_apply_2(v_inst_865_, v_val_882_, v_upperBound_870_);
v___x_884_ = lean_unbox(v___x_883_);
if (v___x_884_ == 0)
{
lean_object* v___x_885_; 
lean_dec(v_val_882_);
lean_del_object(v___x_877_);
lean_dec_ref(v_succ_x3f_874_);
lean_del_object(v___x_872_);
lean_dec(v_upperBound_870_);
v___x_885_ = lean_box(2);
return v___x_885_;
}
else
{
lean_object* v___x_886_; lean_object* v___x_888_; 
lean_inc(v_val_882_);
v___x_886_ = lean_apply_1(v_succ_x3f_874_, v_val_882_);
if (v_isShared_873_ == 0)
{
lean_ctor_set(v___x_872_, 0, v___x_886_);
v___x_888_ = v___x_872_;
goto v_reusejp_887_;
}
else
{
lean_object* v_reuseFailAlloc_892_; 
v_reuseFailAlloc_892_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_892_, 0, v___x_886_);
lean_ctor_set(v_reuseFailAlloc_892_, 1, v_upperBound_870_);
v___x_888_ = v_reuseFailAlloc_892_;
goto v_reusejp_887_;
}
v_reusejp_887_:
{
lean_object* v___x_890_; 
if (v_isShared_878_ == 0)
{
lean_ctor_set(v___x_877_, 1, v_val_882_);
lean_ctor_set(v___x_877_, 0, v___x_888_);
v___x_890_ = v___x_877_;
goto v_reusejp_889_;
}
else
{
lean_object* v_reuseFailAlloc_891_; 
v_reuseFailAlloc_891_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_891_, 0, v___x_888_);
lean_ctor_set(v_reuseFailAlloc_891_, 1, v_val_882_);
v___x_890_ = v_reuseFailAlloc_891_;
goto v_reusejp_889_;
}
v_reusejp_889_:
{
return v___x_890_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess___redArg(lean_object* v_inst_896_, lean_object* v_inst_897_){
_start:
{
lean_object* v___f_898_; 
v___f_898_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_898_, 0, v_inst_896_);
lean_closure_set(v___f_898_, 1, v_inst_897_);
return v___f_898_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorAccess(lean_object* v_00_u03b1_899_, lean_object* v_inst_900_, lean_object* v_inst_901_, lean_object* v_inst_902_, lean_object* v_inst_903_, lean_object* v_inst_904_){
_start:
{
lean_object* v___f_905_; 
v___f_905_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorAccess___redArg___lam__0), 4, 2);
lean_closure_set(v___f_905_, 0, v_inst_900_);
lean_closure_set(v___f_905_, 1, v_inst_902_);
return v___f_905_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_906_, lean_object* v_inst_907_, lean_object* v_inst_908_, lean_object* v_upperBound_909_, lean_object* v_acc_910_, lean_object* v_next_911_, lean_object* v_f_912_){
_start:
{
lean_object* v_toApplicative_913_; lean_object* v_toBind_914_; lean_object* v_toPure_915_; lean_object* v___f_916_; lean_object* v___x_917_; 
v_toApplicative_913_ = lean_ctor_get(v_inst_908_, 0);
lean_inc_ref(v_toApplicative_913_);
v_toBind_914_ = lean_ctor_get(v_inst_908_, 1);
lean_inc(v_toBind_914_);
lean_dec_ref(v_inst_908_);
v_toPure_915_ = lean_ctor_get(v_toApplicative_913_, 1);
lean_inc(v_toPure_915_);
lean_dec_ref(v_toApplicative_913_);
v___f_916_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_916_, 0, v_inst_907_);
lean_closure_set(v___f_916_, 1, v_upperBound_909_);
lean_closure_set(v___f_916_, 2, v_toPure_915_);
lean_closure_set(v___f_916_, 3, v_inst_906_);
lean_closure_set(v___f_916_, 4, v_f_912_);
lean_closure_set(v___f_916_, 5, v_toBind_914_);
v___x_917_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_916_, v_next_911_, v_acc_910_, lean_box(0));
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_918_, lean_object* v_inst_919_, lean_object* v_inst_920_, lean_object* v_inst_921_, lean_object* v_inst_922_, lean_object* v_n_923_, lean_object* v_inst_924_, lean_object* v_00_u03b3_925_, lean_object* v_Pl_926_, lean_object* v_LargeEnough_927_, lean_object* v_hl_928_, lean_object* v_upperBound_929_, lean_object* v_acc_930_, lean_object* v_next_931_, lean_object* v_h_932_, lean_object* v_f_933_){
_start:
{
lean_object* v_toApplicative_934_; lean_object* v_toBind_935_; lean_object* v_toPure_936_; lean_object* v___f_937_; lean_object* v___x_938_; 
v_toApplicative_934_ = lean_ctor_get(v_inst_924_, 0);
lean_inc_ref(v_toApplicative_934_);
v_toBind_935_ = lean_ctor_get(v_inst_924_, 1);
lean_inc(v_toBind_935_);
lean_dec_ref(v_inst_924_);
v_toPure_936_ = lean_ctor_get(v_toApplicative_934_, 1);
lean_inc(v_toPure_936_);
lean_dec_ref(v_toApplicative_934_);
v___f_937_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_937_, 0, v_inst_921_);
lean_closure_set(v___f_937_, 1, v_upperBound_929_);
lean_closure_set(v___f_937_, 2, v_toPure_936_);
lean_closure_set(v___f_937_, 3, v_inst_919_);
lean_closure_set(v___f_937_, 4, v_f_933_);
lean_closure_set(v___f_937_, 5, v_toBind_935_);
v___x_938_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_937_, v_next_931_, v_acc_930_, lean_box(0));
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_939_, lean_object* v_inst_940_, lean_object* v_inst_941_, lean_object* v_toBind_942_, lean_object* v_x_943_, lean_object* v_00_u03b3_944_, lean_object* v_Pl_945_, lean_object* v_it_946_, lean_object* v_init_947_, lean_object* v_f_948_){
_start:
{
lean_object* v_next_949_; 
v_next_949_ = lean_ctor_get(v_it_946_, 0);
lean_inc(v_next_949_);
if (lean_obj_tag(v_next_949_) == 0)
{
lean_object* v___x_950_; 
lean_dec(v_f_948_);
lean_dec_ref(v_it_946_);
lean_dec(v_toBind_942_);
lean_dec_ref(v_inst_941_);
lean_dec_ref(v_inst_940_);
v___x_950_ = lean_apply_2(v_toPure_939_, lean_box(0), v_init_947_);
return v___x_950_;
}
else
{
lean_object* v_upperBound_951_; lean_object* v_val_952_; lean_object* v___f_953_; lean_object* v___x_954_; 
v_upperBound_951_ = lean_ctor_get(v_it_946_, 1);
lean_inc(v_upperBound_951_);
lean_dec_ref(v_it_946_);
v_val_952_ = lean_ctor_get(v_next_949_, 0);
lean_inc(v_val_952_);
lean_dec_ref_known(v_next_949_, 1);
v___f_953_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop___redArg___lam__1), 10, 6);
lean_closure_set(v___f_953_, 0, v_inst_940_);
lean_closure_set(v___f_953_, 1, v_upperBound_951_);
lean_closure_set(v___f_953_, 2, v_toPure_939_);
lean_closure_set(v___f_953_, 3, v_inst_941_);
lean_closure_set(v___f_953_, 4, v_f_948_);
lean_closure_set(v___f_953_, 5, v_toBind_942_);
v___x_954_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_953_, v_val_952_, v_init_947_, lean_box(0));
return v___x_954_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_955_, lean_object* v_inst_956_, lean_object* v_inst_957_, lean_object* v_toBind_958_, lean_object* v_x_959_, lean_object* v_00_u03b3_960_, lean_object* v_Pl_961_, lean_object* v_it_962_, lean_object* v_init_963_, lean_object* v_f_964_){
_start:
{
lean_object* v_res_965_; 
v_res_965_ = l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_955_, v_inst_956_, v_inst_957_, v_toBind_958_, v_x_959_, v_00_u03b3_960_, v_Pl_961_, v_it_962_, v_init_963_, v_f_964_);
lean_dec(v_x_959_);
return v_res_965_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop___redArg(lean_object* v_inst_966_, lean_object* v_inst_967_, lean_object* v_inst_968_){
_start:
{
lean_object* v_toApplicative_969_; lean_object* v_toBind_970_; lean_object* v_toPure_971_; lean_object* v___f_972_; 
v_toApplicative_969_ = lean_ctor_get(v_inst_968_, 0);
lean_inc_ref(v_toApplicative_969_);
v_toBind_970_ = lean_ctor_get(v_inst_968_, 1);
lean_inc(v_toBind_970_);
lean_dec_ref(v_inst_968_);
v_toPure_971_ = lean_ctor_get(v_toApplicative_969_, 1);
lean_inc(v_toPure_971_);
lean_dec_ref(v_toApplicative_969_);
v___f_972_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_972_, 0, v_toPure_971_);
lean_closure_set(v___f_972_, 1, v_inst_967_);
lean_closure_set(v___f_972_, 2, v_inst_966_);
lean_closure_set(v___f_972_, 3, v_toBind_970_);
return v___f_972_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxo_Iterator_instIteratorLoop(lean_object* v_00_u03b1_973_, lean_object* v_inst_974_, lean_object* v_inst_975_, lean_object* v_inst_976_, lean_object* v_inst_977_, lean_object* v_inst_978_, lean_object* v_n_979_, lean_object* v_inst_980_){
_start:
{
lean_object* v_toApplicative_981_; lean_object* v_toBind_982_; lean_object* v_toPure_983_; lean_object* v___f_984_; 
v_toApplicative_981_ = lean_ctor_get(v_inst_980_, 0);
lean_inc_ref(v_toApplicative_981_);
v_toBind_982_ = lean_ctor_get(v_inst_980_, 1);
lean_inc(v_toBind_982_);
lean_dec_ref(v_inst_980_);
v_toPure_983_ = lean_ctor_get(v_toApplicative_981_, 1);
lean_inc(v_toPure_983_);
lean_dec_ref(v_toApplicative_981_);
v___f_984_ = lean_alloc_closure((void*)(l_Std_Rxo_Iterator_instIteratorLoop___redArg___lam__2___boxed), 10, 4);
lean_closure_set(v___f_984_, 0, v_toPure_983_);
lean_closure_set(v___f_984_, 1, v_inst_976_);
lean_closure_set(v___f_984_, 2, v_inst_974_);
lean_closure_set(v___f_984_, 3, v_toBind_982_);
return v___f_984_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_985_, lean_object* v_f_986_, lean_object* v_h__1_987_, lean_object* v_h__2_988_){
_start:
{
lean_object* v_next_989_; 
v_next_989_ = lean_ctor_get(v_it_985_, 0);
if (lean_obj_tag(v_next_989_) == 0)
{
lean_object* v_upperBound_990_; lean_object* v___x_991_; 
lean_dec(v_h__1_987_);
v_upperBound_990_ = lean_ctor_get(v_it_985_, 1);
lean_inc(v_upperBound_990_);
lean_dec_ref(v_it_985_);
v___x_991_ = lean_apply_2(v_h__2_988_, v_upperBound_990_, v_f_986_);
return v___x_991_;
}
else
{
lean_object* v_upperBound_992_; lean_object* v_val_993_; lean_object* v___x_994_; 
lean_inc_ref(v_next_989_);
lean_dec(v_h__2_988_);
v_upperBound_992_ = lean_ctor_get(v_it_985_, 1);
lean_inc(v_upperBound_992_);
lean_dec_ref(v_it_985_);
v_val_993_ = lean_ctor_get(v_next_989_, 0);
lean_inc(v_val_993_);
lean_dec_ref_known(v_next_989_, 1);
v___x_994_ = lean_apply_3(v_h__1_987_, v_val_993_, v_upperBound_992_, v_f_986_);
return v___x_994_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_995_, lean_object* v_inst_996_, lean_object* v_inst_997_, lean_object* v_inst_998_, lean_object* v_n_999_, lean_object* v_00_u03b3_1000_, lean_object* v_Pl_1001_, lean_object* v_motive_1002_, lean_object* v_it_1003_, lean_object* v_f_1004_, lean_object* v_h__1_1005_, lean_object* v_h__2_1006_){
_start:
{
lean_object* v_next_1007_; 
v_next_1007_ = lean_ctor_get(v_it_1003_, 0);
if (lean_obj_tag(v_next_1007_) == 0)
{
lean_object* v_upperBound_1008_; lean_object* v___x_1009_; 
lean_dec(v_h__1_1005_);
v_upperBound_1008_ = lean_ctor_get(v_it_1003_, 1);
lean_inc(v_upperBound_1008_);
lean_dec_ref(v_it_1003_);
v___x_1009_ = lean_apply_2(v_h__2_1006_, v_upperBound_1008_, v_f_1004_);
return v___x_1009_;
}
else
{
lean_object* v_upperBound_1010_; lean_object* v_val_1011_; lean_object* v___x_1012_; 
lean_inc_ref(v_next_1007_);
lean_dec(v_h__2_1006_);
v_upperBound_1010_ = lean_ctor_get(v_it_1003_, 1);
lean_inc(v_upperBound_1010_);
lean_dec_ref(v_it_1003_);
v_val_1011_ = lean_ctor_get(v_next_1007_, 0);
lean_inc(v_val_1011_);
lean_dec_ref_known(v_next_1007_, 1);
v___x_1012_ = lean_apply_3(v_h__1_1005_, v_val_1011_, v_upperBound_1010_, v_f_1004_);
return v___x_1012_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_1013_, lean_object* v_inst_1014_, lean_object* v_inst_1015_, lean_object* v_inst_1016_, lean_object* v_n_1017_, lean_object* v_00_u03b3_1018_, lean_object* v_Pl_1019_, lean_object* v_motive_1020_, lean_object* v_it_1021_, lean_object* v_f_1022_, lean_object* v_h__1_1023_, lean_object* v_h__2_1024_){
_start:
{
lean_object* v_res_1025_; 
v_res_1025_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxo_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_1013_, v_inst_1014_, v_inst_1015_, v_inst_1016_, v_n_1017_, v_00_u03b3_1018_, v_Pl_1019_, v_motive_1020_, v_it_1021_, v_f_1022_, v_h__1_1023_, v_h__2_1024_);
lean_dec_ref(v_inst_1016_);
lean_dec_ref(v_inst_1014_);
return v_res_1025_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step___redArg(lean_object* v_inst_1026_, lean_object* v_it_1027_){
_start:
{
if (lean_obj_tag(v_it_1027_) == 0)
{
lean_object* v___x_1028_; 
lean_dec_ref(v_inst_1026_);
v___x_1028_ = lean_box(2);
return v___x_1028_;
}
else
{
lean_object* v_val_1029_; lean_object* v_succ_x3f_1030_; lean_object* v___x_1032_; uint8_t v_isShared_1033_; uint8_t v_isSharedCheck_1038_; 
v_val_1029_ = lean_ctor_get(v_it_1027_, 0);
lean_inc(v_val_1029_);
lean_dec_ref_known(v_it_1027_, 1);
v_succ_x3f_1030_ = lean_ctor_get(v_inst_1026_, 0);
v_isSharedCheck_1038_ = !lean_is_exclusive(v_inst_1026_);
if (v_isSharedCheck_1038_ == 0)
{
lean_object* v_unused_1039_; 
v_unused_1039_ = lean_ctor_get(v_inst_1026_, 1);
lean_dec(v_unused_1039_);
v___x_1032_ = v_inst_1026_;
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
else
{
lean_inc(v_succ_x3f_1030_);
lean_dec(v_inst_1026_);
v___x_1032_ = lean_box(0);
v_isShared_1033_ = v_isSharedCheck_1038_;
goto v_resetjp_1031_;
}
v_resetjp_1031_:
{
lean_object* v___x_1034_; lean_object* v___x_1036_; 
lean_inc(v_val_1029_);
v___x_1034_ = lean_apply_1(v_succ_x3f_1030_, v_val_1029_);
if (v_isShared_1033_ == 0)
{
lean_ctor_set(v___x_1032_, 1, v_val_1029_);
lean_ctor_set(v___x_1032_, 0, v___x_1034_);
v___x_1036_ = v___x_1032_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1037_; 
v_reuseFailAlloc_1037_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1037_, 0, v___x_1034_);
lean_ctor_set(v_reuseFailAlloc_1037_, 1, v_val_1029_);
v___x_1036_ = v_reuseFailAlloc_1037_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
return v___x_1036_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_Monadic_step(lean_object* v_00_u03b1_1040_, lean_object* v_inst_1041_, lean_object* v_it_1042_){
_start:
{
if (lean_obj_tag(v_it_1042_) == 0)
{
lean_object* v___x_1043_; 
lean_dec_ref(v_inst_1041_);
v___x_1043_ = lean_box(2);
return v___x_1043_;
}
else
{
lean_object* v_val_1044_; lean_object* v_succ_x3f_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1053_; 
v_val_1044_ = lean_ctor_get(v_it_1042_, 0);
lean_inc(v_val_1044_);
lean_dec_ref_known(v_it_1042_, 1);
v_succ_x3f_1045_ = lean_ctor_get(v_inst_1041_, 0);
v_isSharedCheck_1053_ = !lean_is_exclusive(v_inst_1041_);
if (v_isSharedCheck_1053_ == 0)
{
lean_object* v_unused_1054_; 
v_unused_1054_ = lean_ctor_get(v_inst_1041_, 1);
lean_dec(v_unused_1054_);
v___x_1047_ = v_inst_1041_;
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_succ_x3f_1045_);
lean_dec(v_inst_1041_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1053_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; lean_object* v___x_1051_; 
lean_inc(v_val_1044_);
v___x_1049_ = lean_apply_1(v_succ_x3f_1045_, v_val_1044_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v_val_1044_);
lean_ctor_set(v___x_1047_, 0, v___x_1049_);
v___x_1051_ = v___x_1047_;
goto v_reusejp_1050_;
}
else
{
lean_object* v_reuseFailAlloc_1052_; 
v_reuseFailAlloc_1052_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1052_, 0, v___x_1049_);
lean_ctor_set(v_reuseFailAlloc_1052_, 1, v_val_1044_);
v___x_1051_ = v_reuseFailAlloc_1052_;
goto v_reusejp_1050_;
}
v_reusejp_1050_:
{
return v___x_1051_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step___redArg(lean_object* v_inst_1055_, lean_object* v_it_1056_){
_start:
{
if (lean_obj_tag(v_it_1056_) == 0)
{
lean_object* v___x_1057_; 
lean_dec_ref(v_inst_1055_);
v___x_1057_ = lean_box(2);
return v___x_1057_;
}
else
{
lean_object* v_val_1058_; lean_object* v_succ_x3f_1059_; lean_object* v___x_1061_; uint8_t v_isShared_1062_; uint8_t v_isSharedCheck_1067_; 
v_val_1058_ = lean_ctor_get(v_it_1056_, 0);
lean_inc(v_val_1058_);
lean_dec_ref_known(v_it_1056_, 1);
v_succ_x3f_1059_ = lean_ctor_get(v_inst_1055_, 0);
v_isSharedCheck_1067_ = !lean_is_exclusive(v_inst_1055_);
if (v_isSharedCheck_1067_ == 0)
{
lean_object* v_unused_1068_; 
v_unused_1068_ = lean_ctor_get(v_inst_1055_, 1);
lean_dec(v_unused_1068_);
v___x_1061_ = v_inst_1055_;
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
else
{
lean_inc(v_succ_x3f_1059_);
lean_dec(v_inst_1055_);
v___x_1061_ = lean_box(0);
v_isShared_1062_ = v_isSharedCheck_1067_;
goto v_resetjp_1060_;
}
v_resetjp_1060_:
{
lean_object* v___x_1063_; lean_object* v___x_1065_; 
lean_inc(v_val_1058_);
v___x_1063_ = lean_apply_1(v_succ_x3f_1059_, v_val_1058_);
if (v_isShared_1062_ == 0)
{
lean_ctor_set(v___x_1061_, 1, v_val_1058_);
lean_ctor_set(v___x_1061_, 0, v___x_1063_);
v___x_1065_ = v___x_1061_;
goto v_reusejp_1064_;
}
else
{
lean_object* v_reuseFailAlloc_1066_; 
v_reuseFailAlloc_1066_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1066_, 0, v___x_1063_);
lean_ctor_set(v_reuseFailAlloc_1066_, 1, v_val_1058_);
v___x_1065_ = v_reuseFailAlloc_1066_;
goto v_reusejp_1064_;
}
v_reusejp_1064_:
{
return v___x_1065_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_step(lean_object* v_00_u03b1_1069_, lean_object* v_inst_1070_, lean_object* v_it_1071_){
_start:
{
if (lean_obj_tag(v_it_1071_) == 0)
{
lean_object* v___x_1072_; 
lean_dec_ref(v_inst_1070_);
v___x_1072_ = lean_box(2);
return v___x_1072_;
}
else
{
lean_object* v_val_1073_; lean_object* v_succ_x3f_1074_; lean_object* v___x_1076_; uint8_t v_isShared_1077_; uint8_t v_isSharedCheck_1082_; 
v_val_1073_ = lean_ctor_get(v_it_1071_, 0);
lean_inc(v_val_1073_);
lean_dec_ref_known(v_it_1071_, 1);
v_succ_x3f_1074_ = lean_ctor_get(v_inst_1070_, 0);
v_isSharedCheck_1082_ = !lean_is_exclusive(v_inst_1070_);
if (v_isSharedCheck_1082_ == 0)
{
lean_object* v_unused_1083_; 
v_unused_1083_ = lean_ctor_get(v_inst_1070_, 1);
lean_dec(v_unused_1083_);
v___x_1076_ = v_inst_1070_;
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
else
{
lean_inc(v_succ_x3f_1074_);
lean_dec(v_inst_1070_);
v___x_1076_ = lean_box(0);
v_isShared_1077_ = v_isSharedCheck_1082_;
goto v_resetjp_1075_;
}
v_resetjp_1075_:
{
lean_object* v___x_1078_; lean_object* v___x_1080_; 
lean_inc(v_val_1073_);
v___x_1078_ = lean_apply_1(v_succ_x3f_1074_, v_val_1073_);
if (v_isShared_1077_ == 0)
{
lean_ctor_set(v___x_1076_, 1, v_val_1073_);
lean_ctor_set(v___x_1076_, 0, v___x_1078_);
v___x_1080_ = v___x_1076_;
goto v_reusejp_1079_;
}
else
{
lean_object* v_reuseFailAlloc_1081_; 
v_reuseFailAlloc_1081_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1081_, 0, v___x_1078_);
lean_ctor_set(v_reuseFailAlloc_1081_, 1, v_val_1073_);
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
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0(lean_object* v_inst_1084_, lean_object* v_it_1085_){
_start:
{
if (lean_obj_tag(v_it_1085_) == 0)
{
lean_object* v___x_1086_; 
lean_dec_ref(v_inst_1084_);
v___x_1086_ = lean_box(2);
return v___x_1086_;
}
else
{
lean_object* v_val_1087_; lean_object* v_succ_x3f_1088_; lean_object* v___x_1090_; uint8_t v_isShared_1091_; uint8_t v_isSharedCheck_1096_; 
v_val_1087_ = lean_ctor_get(v_it_1085_, 0);
lean_inc(v_val_1087_);
lean_dec_ref_known(v_it_1085_, 1);
v_succ_x3f_1088_ = lean_ctor_get(v_inst_1084_, 0);
v_isSharedCheck_1096_ = !lean_is_exclusive(v_inst_1084_);
if (v_isSharedCheck_1096_ == 0)
{
lean_object* v_unused_1097_; 
v_unused_1097_ = lean_ctor_get(v_inst_1084_, 1);
lean_dec(v_unused_1097_);
v___x_1090_ = v_inst_1084_;
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
else
{
lean_inc(v_succ_x3f_1088_);
lean_dec(v_inst_1084_);
v___x_1090_ = lean_box(0);
v_isShared_1091_ = v_isSharedCheck_1096_;
goto v_resetjp_1089_;
}
v_resetjp_1089_:
{
lean_object* v___x_1092_; lean_object* v___x_1094_; 
lean_inc(v_val_1087_);
v___x_1092_ = lean_apply_1(v_succ_x3f_1088_, v_val_1087_);
if (v_isShared_1091_ == 0)
{
lean_ctor_set(v___x_1090_, 1, v_val_1087_);
lean_ctor_set(v___x_1090_, 0, v___x_1092_);
v___x_1094_ = v___x_1090_;
goto v_reusejp_1093_;
}
else
{
lean_object* v_reuseFailAlloc_1095_; 
v_reuseFailAlloc_1095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1095_, 0, v___x_1092_);
lean_ctor_set(v_reuseFailAlloc_1095_, 1, v_val_1087_);
v___x_1094_ = v_reuseFailAlloc_1095_;
goto v_reusejp_1093_;
}
v_reusejp_1093_:
{
return v___x_1094_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg(lean_object* v_inst_1098_){
_start:
{
lean_object* v___f_1099_; 
v___f_1099_ = lean_alloc_closure((void*)(l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1099_, 0, v_inst_1098_);
return v___f_1099_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable(lean_object* v_00_u03b1_1100_, lean_object* v_inst_1101_){
_start:
{
lean_object* v___f_1102_; 
v___f_1102_ = lean_alloc_closure((void*)(l_Std_Rxi_instIteratorIteratorIdOfUpwardEnumerable___redArg___lam__0), 2, 1);
lean_closure_set(v___f_1102_, 0, v_inst_1101_);
return v___f_1102_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___redArg(){
_start:
{
lean_object* v___x_1104_; 
v___x_1104_ = lean_box(0);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___redArg___boxed(lean_object* v___dummy_1105_){
_start:
{
lean_object* v_res_1106_; 
v_res_1106_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___redArg();
return v_res_1106_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(lean_object* v_00_u03b1_1107_, lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_inst_1110_){
_start:
{
lean_object* v___x_1111_; 
v___x_1111_ = lean_box(0);
return v___x_1111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation___boxed(lean_object* v_00_u03b1_1112_, lean_object* v_inst_1113_, lean_object* v_inst_1114_, lean_object* v_inst_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instFinitenessRelation(v_00_u03b1_1112_, v_inst_1113_, v_inst_1114_, v_inst_1115_);
lean_dec_ref(v_inst_1113_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___redArg(){
_start:
{
lean_object* v___x_1118_; 
v___x_1118_ = lean_box(0);
return v___x_1118_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___redArg___boxed(lean_object* v___dummy_1119_){
_start:
{
lean_object* v_res_1120_; 
v_res_1120_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___redArg();
return v_res_1120_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(lean_object* v_00_u03b1_1121_, lean_object* v_inst_1122_, lean_object* v_inst_1123_){
_start:
{
lean_object* v___x_1124_; 
v___x_1124_ = lean_box(0);
return v___x_1124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation___boxed(lean_object* v_00_u03b1_1125_, lean_object* v_inst_1126_, lean_object* v_inst_1127_){
_start:
{
lean_object* v_res_1128_; 
v_res_1128_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instProductivenessRelation(v_00_u03b1_1125_, v_inst_1126_, v_inst_1127_);
lean_dec_ref(v_inst_1126_);
return v_res_1128_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0(lean_object* v_inst_1129_, lean_object* v_it_1130_, lean_object* v_n_1131_){
_start:
{
if (lean_obj_tag(v_it_1130_) == 0)
{
lean_object* v___x_1132_; 
lean_dec(v_n_1131_);
lean_dec_ref(v_inst_1129_);
v___x_1132_ = lean_box(2);
return v___x_1132_;
}
else
{
lean_object* v_succ_x3f_1133_; lean_object* v_succMany_x3f_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1146_; 
v_succ_x3f_1133_ = lean_ctor_get(v_inst_1129_, 0);
v_succMany_x3f_1134_ = lean_ctor_get(v_inst_1129_, 1);
v_isSharedCheck_1146_ = !lean_is_exclusive(v_inst_1129_);
if (v_isSharedCheck_1146_ == 0)
{
v___x_1136_ = v_inst_1129_;
v_isShared_1137_ = v_isSharedCheck_1146_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_succMany_x3f_1134_);
lean_inc(v_succ_x3f_1133_);
lean_dec(v_inst_1129_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1146_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v_val_1138_; lean_object* v___x_1139_; 
v_val_1138_ = lean_ctor_get(v_it_1130_, 0);
lean_inc(v_val_1138_);
lean_dec_ref_known(v_it_1130_, 1);
v___x_1139_ = lean_apply_2(v_succMany_x3f_1134_, v_n_1131_, v_val_1138_);
if (lean_obj_tag(v___x_1139_) == 0)
{
lean_object* v___x_1140_; 
lean_del_object(v___x_1136_);
lean_dec_ref(v_succ_x3f_1133_);
v___x_1140_ = lean_box(2);
return v___x_1140_;
}
else
{
lean_object* v_val_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v_val_1141_ = lean_ctor_get(v___x_1139_, 0);
lean_inc_n(v_val_1141_, 2);
lean_dec_ref_known(v___x_1139_, 1);
v___x_1142_ = lean_apply_1(v_succ_x3f_1133_, v_val_1141_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v_val_1141_);
lean_ctor_set(v___x_1136_, 0, v___x_1142_);
v___x_1144_ = v___x_1136_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1145_; 
v_reuseFailAlloc_1145_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1145_, 0, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1145_, 1, v_val_1141_);
v___x_1144_ = v_reuseFailAlloc_1145_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
return v___x_1144_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess___redArg(lean_object* v_inst_1147_){
_start:
{
lean_object* v___f_1148_; 
v___f_1148_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1148_, 0, v_inst_1147_);
return v___f_1148_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorAccess(lean_object* v_00_u03b1_1149_, lean_object* v_inst_1150_, lean_object* v_inst_1151_){
_start:
{
lean_object* v___f_1152_; 
v___f_1152_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorAccess___redArg___lam__0), 3, 1);
lean_closure_set(v___f_1152_, 0, v_inst_1150_);
return v___f_1152_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1(lean_object* v_toPure_1153_, lean_object* v_inst_1154_, lean_object* v_f_1155_, lean_object* v_toBind_1156_, lean_object* v_next_1157_, lean_object* v_acc_1158_, lean_object* v_h_1159_, lean_object* v_G_1160_){
_start:
{
lean_object* v___f_1161_; lean_object* v___x_1162_; lean_object* v___x_1163_; 
lean_inc(v_next_1157_);
v___f_1161_ = lean_alloc_closure((void*)(l_Std_Rxc_Iterator_instIteratorLoop_loop___redArg___lam__0), 5, 4);
lean_closure_set(v___f_1161_, 0, v_toPure_1153_);
lean_closure_set(v___f_1161_, 1, v_inst_1154_);
lean_closure_set(v___f_1161_, 2, v_next_1157_);
lean_closure_set(v___f_1161_, 3, v_G_1160_);
v___x_1162_ = lean_apply_3(v_f_1155_, v_next_1157_, lean_box(0), v_acc_1158_);
v___x_1163_ = lean_apply_4(v_toBind_1156_, lean_box(0), lean_box(0), v___x_1162_, v___f_1161_);
return v___x_1163_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg(lean_object* v_inst_1164_, lean_object* v_inst_1165_, lean_object* v_acc_1166_, lean_object* v_next_1167_, lean_object* v_f_1168_){
_start:
{
lean_object* v_toApplicative_1169_; lean_object* v_toBind_1170_; lean_object* v_toPure_1171_; lean_object* v___f_1172_; lean_object* v___x_1173_; 
v_toApplicative_1169_ = lean_ctor_get(v_inst_1165_, 0);
lean_inc_ref(v_toApplicative_1169_);
v_toBind_1170_ = lean_ctor_get(v_inst_1165_, 1);
lean_inc(v_toBind_1170_);
lean_dec_ref(v_inst_1165_);
v_toPure_1171_ = lean_ctor_get(v_toApplicative_1169_, 1);
lean_inc(v_toPure_1171_);
lean_dec_ref(v_toApplicative_1169_);
v___f_1172_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1172_, 0, v_toPure_1171_);
lean_closure_set(v___f_1172_, 1, v_inst_1164_);
lean_closure_set(v___f_1172_, 2, v_f_1168_);
lean_closure_set(v___f_1172_, 3, v_toBind_1170_);
v___x_1173_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1172_, v_next_1167_, v_acc_1166_, lean_box(0));
return v___x_1173_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop_loop(lean_object* v_00_u03b1_1174_, lean_object* v_inst_1175_, lean_object* v_inst_1176_, lean_object* v_n_1177_, lean_object* v_inst_1178_, lean_object* v_00_u03b3_1179_, lean_object* v_Pl_1180_, lean_object* v_LargeEnough_1181_, lean_object* v_hl_1182_, lean_object* v_acc_1183_, lean_object* v_next_1184_, lean_object* v_h_1185_, lean_object* v_f_1186_){
_start:
{
lean_object* v_toApplicative_1187_; lean_object* v_toBind_1188_; lean_object* v_toPure_1189_; lean_object* v___f_1190_; lean_object* v___x_1191_; 
v_toApplicative_1187_ = lean_ctor_get(v_inst_1178_, 0);
lean_inc_ref(v_toApplicative_1187_);
v_toBind_1188_ = lean_ctor_get(v_inst_1178_, 1);
lean_inc(v_toBind_1188_);
lean_dec_ref(v_inst_1178_);
v_toPure_1189_ = lean_ctor_get(v_toApplicative_1187_, 1);
lean_inc(v_toPure_1189_);
lean_dec_ref(v_toApplicative_1187_);
v___f_1190_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1190_, 0, v_toPure_1189_);
lean_closure_set(v___f_1190_, 1, v_inst_1175_);
lean_closure_set(v___f_1190_, 2, v_f_1186_);
lean_closure_set(v___f_1190_, 3, v_toBind_1188_);
v___x_1191_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1190_, v_next_1184_, v_acc_1183_, lean_box(0));
return v___x_1191_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(lean_object* v_toPure_1192_, lean_object* v_inst_1193_, lean_object* v_toBind_1194_, lean_object* v_x_1195_, lean_object* v_00_u03b3_1196_, lean_object* v_Pl_1197_, lean_object* v_it_1198_, lean_object* v_init_1199_, lean_object* v_f_1200_){
_start:
{
if (lean_obj_tag(v_it_1198_) == 0)
{
lean_object* v___x_1201_; 
lean_dec(v_f_1200_);
lean_dec(v_toBind_1194_);
lean_dec_ref(v_inst_1193_);
v___x_1201_ = lean_apply_2(v_toPure_1192_, lean_box(0), v_init_1199_);
return v___x_1201_;
}
else
{
lean_object* v_val_1202_; lean_object* v___f_1203_; lean_object* v___x_1204_; 
v_val_1202_ = lean_ctor_get(v_it_1198_, 0);
lean_inc(v_val_1202_);
lean_dec_ref_known(v_it_1198_, 1);
v___f_1203_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop_loop___redArg___lam__1), 8, 4);
lean_closure_set(v___f_1203_, 0, v_toPure_1192_);
lean_closure_set(v___f_1203_, 1, v_inst_1193_);
lean_closure_set(v___f_1203_, 2, v_f_1200_);
lean_closure_set(v___f_1203_, 3, v_toBind_1194_);
v___x_1204_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1203_, v_val_1202_, v_init_1199_, lean_box(0));
return v___x_1204_;
}
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed(lean_object* v_toPure_1205_, lean_object* v_inst_1206_, lean_object* v_toBind_1207_, lean_object* v_x_1208_, lean_object* v_00_u03b3_1209_, lean_object* v_Pl_1210_, lean_object* v_it_1211_, lean_object* v_init_1212_, lean_object* v_f_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2(v_toPure_1205_, v_inst_1206_, v_toBind_1207_, v_x_1208_, v_00_u03b3_1209_, v_Pl_1210_, v_it_1211_, v_init_1212_, v_f_1213_);
lean_dec(v_x_1208_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop___redArg(lean_object* v_inst_1215_, lean_object* v_inst_1216_){
_start:
{
lean_object* v_toApplicative_1217_; lean_object* v_toBind_1218_; lean_object* v_toPure_1219_; lean_object* v___f_1220_; 
v_toApplicative_1217_ = lean_ctor_get(v_inst_1216_, 0);
lean_inc_ref(v_toApplicative_1217_);
v_toBind_1218_ = lean_ctor_get(v_inst_1216_, 1);
lean_inc(v_toBind_1218_);
lean_dec_ref(v_inst_1216_);
v_toPure_1219_ = lean_ctor_get(v_toApplicative_1217_, 1);
lean_inc(v_toPure_1219_);
lean_dec_ref(v_toApplicative_1217_);
v___f_1220_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1220_, 0, v_toPure_1219_);
lean_closure_set(v___f_1220_, 1, v_inst_1215_);
lean_closure_set(v___f_1220_, 2, v_toBind_1218_);
return v___f_1220_;
}
}
LEAN_EXPORT lean_object* l_Std_Rxi_Iterator_instIteratorLoop(lean_object* v_00_u03b1_1221_, lean_object* v_inst_1222_, lean_object* v_inst_1223_, lean_object* v_n_1224_, lean_object* v_inst_1225_){
_start:
{
lean_object* v_toApplicative_1226_; lean_object* v_toBind_1227_; lean_object* v_toPure_1228_; lean_object* v___f_1229_; 
v_toApplicative_1226_ = lean_ctor_get(v_inst_1225_, 0);
lean_inc_ref(v_toApplicative_1226_);
v_toBind_1227_ = lean_ctor_get(v_inst_1225_, 1);
lean_inc(v_toBind_1227_);
lean_dec_ref(v_inst_1225_);
v_toPure_1228_ = lean_ctor_get(v_toApplicative_1226_, 1);
lean_inc(v_toPure_1228_);
lean_dec_ref(v_toApplicative_1226_);
v___f_1229_ = lean_alloc_closure((void*)(l_Std_Rxi_Iterator_instIteratorLoop___redArg___lam__2___boxed), 9, 3);
lean_closure_set(v___f_1229_, 0, v_toPure_1228_);
lean_closure_set(v___f_1229_, 1, v_inst_1222_);
lean_closure_set(v___f_1229_, 2, v_toBind_1227_);
return v___f_1229_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___redArg(lean_object* v_it_1230_, lean_object* v_f_1231_, lean_object* v_h__1_1232_, lean_object* v_h__2_1233_){
_start:
{
if (lean_obj_tag(v_it_1230_) == 0)
{
lean_object* v___x_1234_; 
lean_dec(v_h__1_1232_);
v___x_1234_ = lean_apply_1(v_h__2_1233_, v_f_1231_);
return v___x_1234_;
}
else
{
lean_object* v_val_1235_; lean_object* v___x_1236_; 
lean_dec(v_h__2_1233_);
v_val_1235_ = lean_ctor_get(v_it_1230_, 0);
lean_inc(v_val_1235_);
lean_dec_ref_known(v_it_1230_, 1);
v___x_1236_ = lean_apply_2(v_h__1_1232_, v_val_1235_, v_f_1231_);
return v___x_1236_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(lean_object* v_00_u03b1_1237_, lean_object* v_inst_1238_, lean_object* v_n_1239_, lean_object* v_00_u03b3_1240_, lean_object* v_Pl_1241_, lean_object* v_motive_1242_, lean_object* v_it_1243_, lean_object* v_f_1244_, lean_object* v_h__1_1245_, lean_object* v_h__2_1246_){
_start:
{
if (lean_obj_tag(v_it_1243_) == 0)
{
lean_object* v___x_1247_; 
lean_dec(v_h__1_1245_);
v___x_1247_ = lean_apply_1(v_h__2_1246_, v_f_1244_);
return v___x_1247_;
}
else
{
lean_object* v_val_1248_; lean_object* v___x_1249_; 
lean_dec(v_h__2_1246_);
v_val_1248_ = lean_ctor_get(v_it_1243_, 0);
lean_inc(v_val_1248_);
lean_dec_ref_known(v_it_1243_, 1);
v___x_1249_ = lean_apply_2(v_h__1_1245_, v_val_1248_, v_f_1244_);
return v___x_1249_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter___boxed(lean_object* v_00_u03b1_1250_, lean_object* v_inst_1251_, lean_object* v_n_1252_, lean_object* v_00_u03b3_1253_, lean_object* v_Pl_1254_, lean_object* v_motive_1255_, lean_object* v_it_1256_, lean_object* v_f_1257_, lean_object* v_h__1_1258_, lean_object* v_h__2_1259_){
_start:
{
lean_object* v_res_1260_; 
v_res_1260_ = l___private_Init_Data_Range_Polymorphic_RangeIterator_0__Std_Rxi_Iterator_instIteratorLoop_match__1_splitter(v_00_u03b1_1250_, v_inst_1251_, v_n_1252_, v_00_u03b3_1253_, v_Pl_1254_, v_motive_1255_, v_it_1256_, v_f_1257_, v_h__1_1258_, v_h__2_1259_);
lean_dec_ref(v_inst_1251_);
return v_res_1260_;
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
