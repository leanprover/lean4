// Lean compiler output
// Module: Init.Data.String.Slice.Pattern
// Imports: public import Init.Data.String.Slice.Basic public import Init.Data.String.Pattern public import Init.Data.String.ToSlice public import Init.Data.String.Subslice public import Init.Data.Iterators.Combinators.FilterMap public import Init.Data.String.Iter.Basic import Init.Data.Iterators.Consumers.Collect import Init.Data.Iterators.Consumers.Loop import Init.Data.Option.Lemmas import Init.Data.String.Termination
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
lean_object* l_String_Slice_slice_x21(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
lean_object* lean_obj_tag_nat(lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_startsWith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_startsWith___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_startsWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_startsWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl(uint8_t);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_split___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_replace___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_replace___redArg___lam__0, .m_arity = 4, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_replace___redArg___closed__0 = (const lean_object*)&l_String_Slice_replace___redArg___closed__0_value;
static const lean_string_object l_String_Slice_replace___redArg___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 1, .m_capacity = 1, .m_length = 0, .m_data = ""};
static const lean_object* l_String_Slice_replace___redArg___closed__1 = (const lean_object*)&l_String_Slice_replace___redArg___closed__1_value;
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_replace___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_trimAsciiStart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_isWhitespace___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_trimAsciiStart___closed__0 = (const lean_object*)&l_String_Slice_trimAsciiStart___closed__0_value;
static lean_once_cell_t l_String_Slice_trimAsciiStart___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_trimAsciiStart___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_find_x3f___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_find_x3f___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_String_Slice_find_x3f___redArg___closed__0 = (const lean_object*)&l_String_Slice_find_x3f___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_find_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_find___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_find(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_find___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_contains___redArg___lam__1___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*1 + 0, .m_other = 1, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(1) << 1) | 1))}};
static const lean_object* l_String_Slice_contains___redArg___lam__1___closed__0 = (const lean_object*)&l_String_Slice_contains___redArg___lam__1___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1(uint8_t, lean_object*, lean_object*, uint8_t);
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_contains___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*1, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_contains___redArg___lam__1___boxed, .m_arity = 4, .m_num_fixed = 1, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1))} };
static const lean_object* l_String_Slice_contains___redArg___closed__0 = (const lean_object*)&l_String_Slice_contains___redArg___closed__0_value;
LEAN_EXPORT uint8_t l_String_Slice_contains___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_contains(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_contains___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_any___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_any___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_any(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_any___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_all___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_all___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_all(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_all___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_endsWith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_endsWith___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_endsWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_endsWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revSplit___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revSplit(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revSplit___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_revAll___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revAll___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_revAll(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revAll___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_String_Slice_trimAsciiEnd___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_trimAsciiEnd___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimAscii(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_lines_lineMap(lean_object*);
static const lean_ctor_object l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___closed__0 = (const lean_object*)&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___boxed(lean_object*);
static lean_once_cell_t l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_lines(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_lines___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_startsWith___redArg(lean_object* v_s_1_, lean_object* v_inst_2_){
_start:
{
lean_object* v_startsWith_3_; lean_object* v___x_4_; uint8_t v___x_5_; 
v_startsWith_3_ = lean_ctor_get(v_inst_2_, 2);
lean_inc_ref(v_startsWith_3_);
lean_dec_ref(v_inst_2_);
v___x_4_ = lean_apply_1(v_startsWith_3_, v_s_1_);
v___x_5_ = lean_unbox(v___x_4_);
return v___x_5_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startsWith___redArg___boxed(lean_object* v_s_6_, lean_object* v_inst_7_){
_start:
{
uint8_t v_res_8_; lean_object* v_r_9_; 
v_res_8_ = l_String_Slice_startsWith___redArg(v_s_6_, v_inst_7_);
v_r_9_ = lean_box(v_res_8_);
return v_r_9_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_startsWith(lean_object* v_00_u03c1_10_, lean_object* v_s_11_, lean_object* v_pat_12_, lean_object* v_inst_13_){
_start:
{
lean_object* v_startsWith_14_; lean_object* v___x_15_; uint8_t v___x_16_; 
v_startsWith_14_ = lean_ctor_get(v_inst_13_, 2);
lean_inc_ref(v_startsWith_14_);
lean_dec_ref(v_inst_13_);
v___x_15_ = lean_apply_1(v_startsWith_14_, v_s_11_);
v___x_16_ = lean_unbox(v___x_15_);
return v___x_16_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startsWith___boxed(lean_object* v_00_u03c1_17_, lean_object* v_s_18_, lean_object* v_pat_19_, lean_object* v_inst_20_){
_start:
{
uint8_t v_res_21_; lean_object* v_r_22_; 
v_res_21_ = l_String_Slice_startsWith(v_00_u03c1_17_, v_s_18_, v_pat_19_, v_inst_20_);
lean_dec(v_pat_19_);
v_r_22_ = lean_box(v_res_21_);
return v_r_22_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___redArg(lean_object* v_x_23_){
_start:
{
lean_object* v___x_24_; 
v___x_24_ = lean_obj_tag_nat(v_x_23_);
return v___x_24_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___redArg___boxed(lean_object* v_x_25_){
_start:
{
lean_object* v_res_26_; 
v_res_26_ = l_String_Slice_SplitIterator_ctorIdx___impl___redArg(v_x_25_);
lean_dec(v_x_25_);
return v_res_26_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl(lean_object* v_00_u03c3_27_, lean_object* v_00_u03c1_28_, lean_object* v_pat_29_, lean_object* v_s_30_, lean_object* v_inst_31_, lean_object* v_x_32_){
_start:
{
lean_object* v___x_33_; 
v___x_33_ = lean_obj_tag_nat(v_x_32_);
return v___x_33_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___boxed(lean_object* v_00_u03c3_34_, lean_object* v_00_u03c1_35_, lean_object* v_pat_36_, lean_object* v_s_37_, lean_object* v_inst_38_, lean_object* v_x_39_){
_start:
{
lean_object* v_res_40_; 
v_res_40_ = l_String_Slice_SplitIterator_ctorIdx___impl(v_00_u03c3_34_, v_00_u03c1_35_, v_pat_36_, v_s_37_, v_inst_38_, v_x_39_);
lean_dec(v_x_39_);
lean_dec(v_inst_38_);
lean_dec_ref(v_s_37_);
lean_dec(v_pat_36_);
return v_res_40_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___redArg(lean_object* v_t_41_, lean_object* v_k_42_){
_start:
{
if (lean_obj_tag(v_t_41_) == 0)
{
lean_object* v_currPos_43_; lean_object* v_searcher_44_; lean_object* v___x_45_; 
v_currPos_43_ = lean_ctor_get(v_t_41_, 0);
lean_inc(v_currPos_43_);
v_searcher_44_ = lean_ctor_get(v_t_41_, 1);
lean_inc(v_searcher_44_);
lean_dec_ref_known(v_t_41_, 2);
v___x_45_ = lean_apply_2(v_k_42_, v_currPos_43_, v_searcher_44_);
return v___x_45_;
}
else
{
return v_k_42_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim(lean_object* v_00_u03c3_46_, lean_object* v_00_u03c1_47_, lean_object* v_pat_48_, lean_object* v_s_49_, lean_object* v_inst_50_, lean_object* v_motive_51_, lean_object* v_ctorIdx_52_, lean_object* v_t_53_, lean_object* v_h_54_, lean_object* v_k_55_){
_start:
{
lean_object* v___x_56_; 
v___x_56_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_53_, v_k_55_);
return v___x_56_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_57_, lean_object* v_00_u03c1_58_, lean_object* v_pat_59_, lean_object* v_s_60_, lean_object* v_inst_61_, lean_object* v_motive_62_, lean_object* v_ctorIdx_63_, lean_object* v_t_64_, lean_object* v_h_65_, lean_object* v_k_66_){
_start:
{
lean_object* v_res_67_; 
v_res_67_ = l_String_Slice_SplitIterator_ctorElim(v_00_u03c3_57_, v_00_u03c1_58_, v_pat_59_, v_s_60_, v_inst_61_, v_motive_62_, v_ctorIdx_63_, v_t_64_, v_h_65_, v_k_66_);
lean_dec(v_ctorIdx_63_);
lean_dec(v_inst_61_);
lean_dec_ref(v_s_60_);
lean_dec(v_pat_59_);
return v_res_67_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___redArg(lean_object* v_t_68_, lean_object* v_operating_69_){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_68_, v_operating_69_);
return v___x_70_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim(lean_object* v_00_u03c3_71_, lean_object* v_00_u03c1_72_, lean_object* v_pat_73_, lean_object* v_s_74_, lean_object* v_inst_75_, lean_object* v_motive_76_, lean_object* v_t_77_, lean_object* v_h_78_, lean_object* v_operating_79_){
_start:
{
lean_object* v___x_80_; 
v___x_80_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_77_, v_operating_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_81_, lean_object* v_00_u03c1_82_, lean_object* v_pat_83_, lean_object* v_s_84_, lean_object* v_inst_85_, lean_object* v_motive_86_, lean_object* v_t_87_, lean_object* v_h_88_, lean_object* v_operating_89_){
_start:
{
lean_object* v_res_90_; 
v_res_90_ = l_String_Slice_SplitIterator_operating_elim(v_00_u03c3_81_, v_00_u03c1_82_, v_pat_83_, v_s_84_, v_inst_85_, v_motive_86_, v_t_87_, v_h_88_, v_operating_89_);
lean_dec(v_inst_85_);
lean_dec_ref(v_s_84_);
lean_dec(v_pat_83_);
return v_res_90_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___redArg(lean_object* v_t_91_, lean_object* v_atEnd_92_){
_start:
{
lean_object* v___x_93_; 
v___x_93_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_91_, v_atEnd_92_);
return v___x_93_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim(lean_object* v_00_u03c3_94_, lean_object* v_00_u03c1_95_, lean_object* v_pat_96_, lean_object* v_s_97_, lean_object* v_inst_98_, lean_object* v_motive_99_, lean_object* v_t_100_, lean_object* v_h_101_, lean_object* v_atEnd_102_){
_start:
{
lean_object* v___x_103_; 
v___x_103_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_100_, v_atEnd_102_);
return v___x_103_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_104_, lean_object* v_00_u03c1_105_, lean_object* v_pat_106_, lean_object* v_s_107_, lean_object* v_inst_108_, lean_object* v_motive_109_, lean_object* v_t_110_, lean_object* v_h_111_, lean_object* v_atEnd_112_){
_start:
{
lean_object* v_res_113_; 
v_res_113_ = l_String_Slice_SplitIterator_atEnd_elim(v_00_u03c3_104_, v_00_u03c1_105_, v_pat_106_, v_s_107_, v_inst_108_, v_motive_109_, v_t_110_, v_h_111_, v_atEnd_112_);
lean_dec(v_inst_108_);
lean_dec_ref(v_s_107_);
lean_dec(v_pat_106_);
return v_res_113_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg(){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_box(1);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg___boxed(lean_object* v___dummy_116_){
_start:
{
lean_object* v_res_117_; 
v_res_117_ = l_String_Slice_instInhabitedSplitIterator_default___redArg();
return v_res_117_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default(lean_object* v_00_u03c3_118_, lean_object* v_00_u03c1_119_, lean_object* v_pat_120_, lean_object* v_s_121_, lean_object* v_inst_122_){
_start:
{
lean_object* v___x_123_; 
v___x_123_ = lean_box(1);
return v___x_123_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___boxed(lean_object* v_00_u03c3_124_, lean_object* v_00_u03c1_125_, lean_object* v_pat_126_, lean_object* v_s_127_, lean_object* v_inst_128_){
_start:
{
lean_object* v_res_129_; 
v_res_129_ = l_String_Slice_instInhabitedSplitIterator_default(v_00_u03c3_124_, v_00_u03c1_125_, v_pat_126_, v_s_127_, v_inst_128_);
lean_dec(v_inst_128_);
lean_dec_ref(v_s_127_);
lean_dec(v_pat_126_);
return v_res_129_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___redArg(){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = lean_box(1);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___redArg___boxed(lean_object* v___dummy_132_){
_start:
{
lean_object* v_res_133_; 
v_res_133_ = l_String_Slice_instInhabitedSplitIterator___redArg();
return v_res_133_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator(lean_object* v_a_134_, lean_object* v_a_135_, lean_object* v_a_136_, lean_object* v_a_137_, lean_object* v_a_138_){
_start:
{
lean_object* v___x_139_; 
v___x_139_ = lean_box(1);
return v___x_139_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___boxed(lean_object* v_a_140_, lean_object* v_a_141_, lean_object* v_a_142_, lean_object* v_a_143_, lean_object* v_a_144_){
_start:
{
lean_object* v_res_145_; 
v_res_145_ = l_String_Slice_instInhabitedSplitIterator(v_a_140_, v_a_141_, v_a_142_, v_a_143_, v_a_144_);
lean_dec(v_a_144_);
lean_dec_ref(v_a_143_);
lean_dec(v_a_142_);
return v_res_145_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl(uint8_t v_x_146_){
_start:
{
lean_object* v___x_147_; lean_object* v___x_148_; 
v___x_147_ = lean_box(v_x_146_);
v___x_148_ = lean_obj_tag_nat(v___x_147_);
lean_dec(v___x_147_);
return v___x_148_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl___boxed(lean_object* v_x_149_){
_start:
{
uint8_t v_x_4__boxed_150_; lean_object* v_res_151_; 
v_x_4__boxed_150_ = lean_unbox(v_x_149_);
v_res_151_ = l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl(v_x_4__boxed_150_);
return v_res_151_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0(lean_object* v_inst_152_, lean_object* v_s_153_, lean_object* v_x_154_){
_start:
{
if (lean_obj_tag(v_x_154_) == 0)
{
lean_object* v_currPos_155_; lean_object* v_searcher_156_; lean_object* v___x_158_; uint8_t v_isShared_159_; uint8_t v_isSharedCheck_199_; 
v_currPos_155_ = lean_ctor_get(v_x_154_, 0);
v_searcher_156_ = lean_ctor_get(v_x_154_, 1);
v_isSharedCheck_199_ = !lean_is_exclusive(v_x_154_);
if (v_isSharedCheck_199_ == 0)
{
v___x_158_ = v_x_154_;
v_isShared_159_ = v_isSharedCheck_199_;
goto v_resetjp_157_;
}
else
{
lean_inc(v_searcher_156_);
lean_inc(v_currPos_155_);
lean_dec(v_x_154_);
v___x_158_ = lean_box(0);
v_isShared_159_ = v_isSharedCheck_199_;
goto v_resetjp_157_;
}
v_resetjp_157_:
{
lean_object* v___x_160_; 
lean_inc_ref(v_s_153_);
v___x_160_ = lean_apply_2(v_inst_152_, v_s_153_, v_searcher_156_);
switch(lean_obj_tag(v___x_160_))
{
case 0:
{
lean_object* v_out_161_; 
v_out_161_ = lean_ctor_get(v___x_160_, 1);
lean_inc(v_out_161_);
if (lean_obj_tag(v_out_161_) == 0)
{
lean_object* v_it_162_; lean_object* v___x_164_; 
lean_dec_ref_known(v_out_161_, 2);
lean_dec_ref(v_s_153_);
v_it_162_ = lean_ctor_get(v___x_160_, 0);
lean_inc(v_it_162_);
lean_dec_ref_known(v___x_160_, 2);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v_it_162_);
v___x_164_ = v___x_158_;
goto v_reusejp_163_;
}
else
{
lean_object* v_reuseFailAlloc_166_; 
v_reuseFailAlloc_166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_166_, 0, v_currPos_155_);
lean_ctor_set(v_reuseFailAlloc_166_, 1, v_it_162_);
v___x_164_ = v_reuseFailAlloc_166_;
goto v_reusejp_163_;
}
v_reusejp_163_:
{
lean_object* v___x_165_; 
v___x_165_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_165_, 0, v___x_164_);
return v___x_165_;
}
}
else
{
lean_object* v_it_167_; lean_object* v___x_169_; uint8_t v_isShared_170_; uint8_t v_isSharedCheck_180_; 
v_it_167_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_180_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_180_ == 0)
{
lean_object* v_unused_181_; 
v_unused_181_ = lean_ctor_get(v___x_160_, 1);
lean_dec(v_unused_181_);
v___x_169_ = v___x_160_;
v_isShared_170_ = v_isSharedCheck_180_;
goto v_resetjp_168_;
}
else
{
lean_inc(v_it_167_);
lean_dec(v___x_160_);
v___x_169_ = lean_box(0);
v_isShared_170_ = v_isSharedCheck_180_;
goto v_resetjp_168_;
}
v_resetjp_168_:
{
lean_object* v_startPos_171_; lean_object* v_endPos_172_; lean_object* v_slice_173_; lean_object* v_nextIt_175_; 
v_startPos_171_ = lean_ctor_get(v_out_161_, 0);
lean_inc(v_startPos_171_);
v_endPos_172_ = lean_ctor_get(v_out_161_, 1);
lean_inc(v_endPos_172_);
lean_dec_ref_known(v_out_161_, 2);
v_slice_173_ = l_String_Slice_subslice_x21(v_s_153_, v_currPos_155_, v_startPos_171_);
lean_dec_ref(v_s_153_);
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v_it_167_);
lean_ctor_set(v___x_158_, 0, v_endPos_172_);
v_nextIt_175_ = v___x_158_;
goto v_reusejp_174_;
}
else
{
lean_object* v_reuseFailAlloc_179_; 
v_reuseFailAlloc_179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_179_, 0, v_endPos_172_);
lean_ctor_set(v_reuseFailAlloc_179_, 1, v_it_167_);
v_nextIt_175_ = v_reuseFailAlloc_179_;
goto v_reusejp_174_;
}
v_reusejp_174_:
{
lean_object* v___x_177_; 
if (v_isShared_170_ == 0)
{
lean_ctor_set(v___x_169_, 1, v_slice_173_);
lean_ctor_set(v___x_169_, 0, v_nextIt_175_);
v___x_177_ = v___x_169_;
goto v_reusejp_176_;
}
else
{
lean_object* v_reuseFailAlloc_178_; 
v_reuseFailAlloc_178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_178_, 0, v_nextIt_175_);
lean_ctor_set(v_reuseFailAlloc_178_, 1, v_slice_173_);
v___x_177_ = v_reuseFailAlloc_178_;
goto v_reusejp_176_;
}
v_reusejp_176_:
{
return v___x_177_;
}
}
}
}
}
case 1:
{
lean_object* v_it_182_; lean_object* v___x_184_; uint8_t v_isShared_185_; uint8_t v_isSharedCheck_192_; 
lean_dec_ref(v_s_153_);
v_it_182_ = lean_ctor_get(v___x_160_, 0);
v_isSharedCheck_192_ = !lean_is_exclusive(v___x_160_);
if (v_isSharedCheck_192_ == 0)
{
v___x_184_ = v___x_160_;
v_isShared_185_ = v_isSharedCheck_192_;
goto v_resetjp_183_;
}
else
{
lean_inc(v_it_182_);
lean_dec(v___x_160_);
v___x_184_ = lean_box(0);
v_isShared_185_ = v_isSharedCheck_192_;
goto v_resetjp_183_;
}
v_resetjp_183_:
{
lean_object* v___x_187_; 
if (v_isShared_159_ == 0)
{
lean_ctor_set(v___x_158_, 1, v_it_182_);
v___x_187_ = v___x_158_;
goto v_reusejp_186_;
}
else
{
lean_object* v_reuseFailAlloc_191_; 
v_reuseFailAlloc_191_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_191_, 0, v_currPos_155_);
lean_ctor_set(v_reuseFailAlloc_191_, 1, v_it_182_);
v___x_187_ = v_reuseFailAlloc_191_;
goto v_reusejp_186_;
}
v_reusejp_186_:
{
lean_object* v___x_189_; 
if (v_isShared_185_ == 0)
{
lean_ctor_set(v___x_184_, 0, v___x_187_);
v___x_189_ = v___x_184_;
goto v_reusejp_188_;
}
else
{
lean_object* v_reuseFailAlloc_190_; 
v_reuseFailAlloc_190_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_190_, 0, v___x_187_);
v___x_189_ = v_reuseFailAlloc_190_;
goto v_reusejp_188_;
}
v_reusejp_188_:
{
return v___x_189_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_193_; lean_object* v_endExclusive_194_; lean_object* v___x_195_; lean_object* v_slice_196_; lean_object* v___x_197_; lean_object* v___x_198_; 
lean_del_object(v___x_158_);
v_startInclusive_193_ = lean_ctor_get(v_s_153_, 1);
lean_inc(v_startInclusive_193_);
v_endExclusive_194_ = lean_ctor_get(v_s_153_, 2);
lean_inc(v_endExclusive_194_);
lean_dec_ref(v_s_153_);
v___x_195_ = lean_nat_sub(v_endExclusive_194_, v_startInclusive_193_);
lean_dec(v_startInclusive_193_);
lean_dec(v_endExclusive_194_);
v_slice_196_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_196_, 0, v_currPos_155_);
lean_ctor_set(v_slice_196_, 1, v___x_195_);
v___x_197_ = lean_box(1);
v___x_198_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_198_, 0, v___x_197_);
lean_ctor_set(v___x_198_, 1, v_slice_196_);
return v___x_198_;
}
}
}
}
else
{
lean_object* v___x_200_; 
lean_dec_ref(v_s_153_);
lean_dec(v_inst_152_);
v___x_200_ = lean_box(2);
return v___x_200_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg(lean_object* v_inst_201_, lean_object* v_s_202_){
_start:
{
lean_object* v___f_203_; 
v___f_203_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0), 3, 2);
lean_closure_set(v___f_203_, 0, v_inst_201_);
lean_closure_set(v___f_203_, 1, v_s_202_);
return v___f_203_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice(lean_object* v_00_u03c1_204_, lean_object* v_00_u03c3_205_, lean_object* v_inst_206_, lean_object* v_pat_207_, lean_object* v_inst_208_, lean_object* v_s_209_){
_start:
{
lean_object* v___f_210_; 
v___f_210_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0), 3, 2);
lean_closure_set(v___f_210_, 0, v_inst_206_);
lean_closure_set(v___f_210_, 1, v_s_209_);
return v___f_210_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___boxed(lean_object* v_00_u03c1_211_, lean_object* v_00_u03c3_212_, lean_object* v_inst_213_, lean_object* v_pat_214_, lean_object* v_inst_215_, lean_object* v_s_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_String_Slice_SplitIterator_instIteratorIdSubslice(v_00_u03c1_211_, v_00_u03c3_212_, v_inst_213_, v_pat_214_, v_inst_215_, v_s_216_);
lean_dec(v_inst_215_);
lean_dec(v_pat_214_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption___redArg(lean_object* v_x_218_){
_start:
{
if (lean_obj_tag(v_x_218_) == 0)
{
lean_object* v_searcher_219_; lean_object* v___x_220_; 
v_searcher_219_ = lean_ctor_get(v_x_218_, 1);
lean_inc(v_searcher_219_);
v___x_220_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_220_, 0, v_searcher_219_);
return v___x_220_;
}
else
{
lean_object* v___x_221_; 
v___x_221_ = lean_box(0);
return v___x_221_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption___redArg___boxed(lean_object* v_x_222_){
_start:
{
lean_object* v_res_223_; 
v_res_223_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption___redArg(v_x_222_);
lean_dec(v_x_222_);
return v_res_223_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption(lean_object* v_00_u03c1_224_, lean_object* v_00_u03c3_225_, lean_object* v_pat_226_, lean_object* v_inst_227_, lean_object* v_s_228_, lean_object* v_x_229_){
_start:
{
lean_object* v___x_230_; 
v___x_230_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption___redArg(v_x_229_);
return v___x_230_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption___boxed(lean_object* v_00_u03c1_231_, lean_object* v_00_u03c3_232_, lean_object* v_pat_233_, lean_object* v_inst_234_, lean_object* v_s_235_, lean_object* v_x_236_){
_start:
{
lean_object* v_res_237_; 
v_res_237_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption(v_00_u03c1_231_, v_00_u03c3_232_, v_pat_233_, v_inst_234_, v_s_235_, v_x_236_);
lean_dec(v_x_236_);
lean_dec_ref(v_s_235_);
lean_dec(v_inst_234_);
lean_dec(v_pat_233_);
return v_res_237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___redArg(lean_object* v_x_238_, lean_object* v_h__1_239_, lean_object* v_h__2_240_){
_start:
{
if (lean_obj_tag(v_x_238_) == 0)
{
lean_object* v_currPos_241_; lean_object* v_searcher_242_; lean_object* v___x_243_; 
lean_dec(v_h__2_240_);
v_currPos_241_ = lean_ctor_get(v_x_238_, 0);
lean_inc(v_currPos_241_);
v_searcher_242_ = lean_ctor_get(v_x_238_, 1);
lean_inc(v_searcher_242_);
lean_dec_ref_known(v_x_238_, 2);
v___x_243_ = lean_apply_2(v_h__1_239_, v_currPos_241_, v_searcher_242_);
return v___x_243_;
}
else
{
lean_object* v___x_244_; lean_object* v___x_245_; 
lean_dec(v_h__1_239_);
v___x_244_ = lean_box(0);
v___x_245_ = lean_apply_1(v_h__2_240_, v___x_244_);
return v___x_245_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(lean_object* v_00_u03c1_246_, lean_object* v_00_u03c3_247_, lean_object* v_pat_248_, lean_object* v_inst_249_, lean_object* v_s_250_, lean_object* v_motive_251_, lean_object* v_x_252_, lean_object* v_h__1_253_, lean_object* v_h__2_254_){
_start:
{
if (lean_obj_tag(v_x_252_) == 0)
{
lean_object* v_currPos_255_; lean_object* v_searcher_256_; lean_object* v___x_257_; 
lean_dec(v_h__2_254_);
v_currPos_255_ = lean_ctor_get(v_x_252_, 0);
lean_inc(v_currPos_255_);
v_searcher_256_ = lean_ctor_get(v_x_252_, 1);
lean_inc(v_searcher_256_);
lean_dec_ref_known(v_x_252_, 2);
v___x_257_ = lean_apply_2(v_h__1_253_, v_currPos_255_, v_searcher_256_);
return v___x_257_;
}
else
{
lean_object* v___x_258_; lean_object* v___x_259_; 
lean_dec(v_h__1_253_);
v___x_258_ = lean_box(0);
v___x_259_ = lean_apply_1(v_h__2_254_, v___x_258_);
return v___x_259_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___boxed(lean_object* v_00_u03c1_260_, lean_object* v_00_u03c3_261_, lean_object* v_pat_262_, lean_object* v_inst_263_, lean_object* v_s_264_, lean_object* v_motive_265_, lean_object* v_x_266_, lean_object* v_h__1_267_, lean_object* v_h__2_268_){
_start:
{
lean_object* v_res_269_; 
v_res_269_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(v_00_u03c1_260_, v_00_u03c3_261_, v_pat_262_, v_inst_263_, v_s_264_, v_motive_265_, v_x_266_, v_h__1_267_, v_h__2_268_);
lean_dec_ref(v_s_264_);
lean_dec(v_inst_263_);
lean_dec(v_pat_262_);
return v_res_269_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object* v_x_270_, lean_object* v_h__1_271_, lean_object* v_h__2_272_, lean_object* v_h__3_273_, lean_object* v_h__4_274_){
_start:
{
switch(lean_obj_tag(v_x_270_))
{
case 0:
{
lean_object* v_out_275_; 
lean_dec(v_h__4_274_);
lean_dec(v_h__3_273_);
v_out_275_ = lean_ctor_get(v_x_270_, 1);
lean_inc(v_out_275_);
if (lean_obj_tag(v_out_275_) == 0)
{
lean_object* v_it_276_; lean_object* v_startPos_277_; lean_object* v_endPos_278_; lean_object* v___x_279_; 
lean_dec(v_h__1_271_);
v_it_276_ = lean_ctor_get(v_x_270_, 0);
lean_inc(v_it_276_);
lean_dec_ref_known(v_x_270_, 2);
v_startPos_277_ = lean_ctor_get(v_out_275_, 0);
lean_inc(v_startPos_277_);
v_endPos_278_ = lean_ctor_get(v_out_275_, 1);
lean_inc(v_endPos_278_);
lean_dec_ref_known(v_out_275_, 2);
v___x_279_ = lean_apply_5(v_h__2_272_, v_it_276_, v_startPos_277_, v_endPos_278_, lean_box(0), lean_box(0));
return v___x_279_;
}
else
{
lean_object* v_it_280_; lean_object* v_startPos_281_; lean_object* v_endPos_282_; lean_object* v___x_283_; 
lean_dec(v_h__2_272_);
v_it_280_ = lean_ctor_get(v_x_270_, 0);
lean_inc(v_it_280_);
lean_dec_ref_known(v_x_270_, 2);
v_startPos_281_ = lean_ctor_get(v_out_275_, 0);
lean_inc(v_startPos_281_);
v_endPos_282_ = lean_ctor_get(v_out_275_, 1);
lean_inc(v_endPos_282_);
lean_dec_ref_known(v_out_275_, 2);
v___x_283_ = lean_apply_5(v_h__1_271_, v_it_280_, v_startPos_281_, v_endPos_282_, lean_box(0), lean_box(0));
return v___x_283_;
}
}
case 1:
{
lean_object* v_it_284_; lean_object* v___x_285_; 
lean_dec(v_h__4_274_);
lean_dec(v_h__2_272_);
lean_dec(v_h__1_271_);
v_it_284_ = lean_ctor_get(v_x_270_, 0);
lean_inc(v_it_284_);
lean_dec_ref_known(v_x_270_, 1);
v___x_285_ = lean_apply_3(v_h__3_273_, v_it_284_, lean_box(0), lean_box(0));
return v___x_285_;
}
default: 
{
lean_object* v___x_286_; 
lean_dec(v_h__3_273_);
lean_dec(v_h__2_272_);
lean_dec(v_h__1_271_);
v___x_286_ = lean_apply_2(v_h__4_274_, lean_box(0), lean_box(0));
return v___x_286_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object* v_00_u03c3_287_, lean_object* v_inst_288_, lean_object* v_s_289_, lean_object* v_searcher_290_, lean_object* v_motive_291_, lean_object* v_x_292_, lean_object* v_h__1_293_, lean_object* v_h__2_294_, lean_object* v_h__3_295_, lean_object* v_h__4_296_){
_start:
{
switch(lean_obj_tag(v_x_292_))
{
case 0:
{
lean_object* v_out_297_; 
lean_dec(v_h__4_296_);
lean_dec(v_h__3_295_);
v_out_297_ = lean_ctor_get(v_x_292_, 1);
lean_inc(v_out_297_);
if (lean_obj_tag(v_out_297_) == 0)
{
lean_object* v_it_298_; lean_object* v_startPos_299_; lean_object* v_endPos_300_; lean_object* v___x_301_; 
lean_dec(v_h__1_293_);
v_it_298_ = lean_ctor_get(v_x_292_, 0);
lean_inc(v_it_298_);
lean_dec_ref_known(v_x_292_, 2);
v_startPos_299_ = lean_ctor_get(v_out_297_, 0);
lean_inc(v_startPos_299_);
v_endPos_300_ = lean_ctor_get(v_out_297_, 1);
lean_inc(v_endPos_300_);
lean_dec_ref_known(v_out_297_, 2);
v___x_301_ = lean_apply_5(v_h__2_294_, v_it_298_, v_startPos_299_, v_endPos_300_, lean_box(0), lean_box(0));
return v___x_301_;
}
else
{
lean_object* v_it_302_; lean_object* v_startPos_303_; lean_object* v_endPos_304_; lean_object* v___x_305_; 
lean_dec(v_h__2_294_);
v_it_302_ = lean_ctor_get(v_x_292_, 0);
lean_inc(v_it_302_);
lean_dec_ref_known(v_x_292_, 2);
v_startPos_303_ = lean_ctor_get(v_out_297_, 0);
lean_inc(v_startPos_303_);
v_endPos_304_ = lean_ctor_get(v_out_297_, 1);
lean_inc(v_endPos_304_);
lean_dec_ref_known(v_out_297_, 2);
v___x_305_ = lean_apply_5(v_h__1_293_, v_it_302_, v_startPos_303_, v_endPos_304_, lean_box(0), lean_box(0));
return v___x_305_;
}
}
case 1:
{
lean_object* v_it_306_; lean_object* v___x_307_; 
lean_dec(v_h__4_296_);
lean_dec(v_h__2_294_);
lean_dec(v_h__1_293_);
v_it_306_ = lean_ctor_get(v_x_292_, 0);
lean_inc(v_it_306_);
lean_dec_ref_known(v_x_292_, 1);
v___x_307_ = lean_apply_3(v_h__3_295_, v_it_306_, lean_box(0), lean_box(0));
return v___x_307_;
}
default: 
{
lean_object* v___x_308_; 
lean_dec(v_h__3_295_);
lean_dec(v_h__2_294_);
lean_dec(v_h__1_293_);
v___x_308_ = lean_apply_2(v_h__4_296_, lean_box(0), lean_box(0));
return v___x_308_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object* v_00_u03c3_309_, lean_object* v_inst_310_, lean_object* v_s_311_, lean_object* v_searcher_312_, lean_object* v_motive_313_, lean_object* v_x_314_, lean_object* v_h__1_315_, lean_object* v_h__2_316_, lean_object* v_h__3_317_, lean_object* v_h__4_318_){
_start:
{
lean_object* v_res_319_; 
v_res_319_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(v_00_u03c3_309_, v_inst_310_, v_s_311_, v_searcher_312_, v_motive_313_, v_x_314_, v_h__1_315_, v_h__2_316_, v_h__3_317_, v_h__4_318_);
lean_dec(v_searcher_312_);
lean_dec_ref(v_s_311_);
lean_dec(v_inst_310_);
return v_res_319_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___redArg(lean_object* v_x_320_, lean_object* v_x_321_, lean_object* v_h__1_322_, lean_object* v_h__2_323_, lean_object* v_h__3_324_, lean_object* v_h__4_325_, lean_object* v_h__5_326_, lean_object* v_h__6_327_, lean_object* v_h__7_328_, lean_object* v_h__8_329_){
_start:
{
if (lean_obj_tag(v_x_320_) == 0)
{
lean_dec(v_h__8_329_);
lean_dec(v_h__7_328_);
lean_dec(v_h__6_327_);
switch(lean_obj_tag(v_x_321_))
{
case 0:
{
lean_object* v_it_330_; 
lean_dec(v_h__5_326_);
lean_dec(v_h__4_325_);
lean_dec(v_h__3_324_);
v_it_330_ = lean_ctor_get(v_x_321_, 0);
if (lean_obj_tag(v_it_330_) == 0)
{
lean_object* v_currPos_331_; lean_object* v_searcher_332_; lean_object* v_out_333_; lean_object* v_currPos_334_; lean_object* v_searcher_335_; lean_object* v___x_336_; 
lean_inc_ref(v_it_330_);
lean_dec(v_h__2_323_);
v_currPos_331_ = lean_ctor_get(v_x_320_, 0);
lean_inc(v_currPos_331_);
v_searcher_332_ = lean_ctor_get(v_x_320_, 1);
lean_inc(v_searcher_332_);
lean_dec_ref_known(v_x_320_, 2);
v_out_333_ = lean_ctor_get(v_x_321_, 1);
lean_inc(v_out_333_);
lean_dec_ref_known(v_x_321_, 2);
v_currPos_334_ = lean_ctor_get(v_it_330_, 0);
lean_inc(v_currPos_334_);
v_searcher_335_ = lean_ctor_get(v_it_330_, 1);
lean_inc(v_searcher_335_);
lean_dec_ref_known(v_it_330_, 2);
v___x_336_ = lean_apply_5(v_h__1_322_, v_currPos_331_, v_searcher_332_, v_currPos_334_, v_searcher_335_, v_out_333_);
return v___x_336_;
}
else
{
lean_object* v_currPos_337_; lean_object* v_searcher_338_; lean_object* v_out_339_; lean_object* v___x_340_; 
lean_dec(v_h__1_322_);
v_currPos_337_ = lean_ctor_get(v_x_320_, 0);
lean_inc(v_currPos_337_);
v_searcher_338_ = lean_ctor_get(v_x_320_, 1);
lean_inc(v_searcher_338_);
lean_dec_ref_known(v_x_320_, 2);
v_out_339_ = lean_ctor_get(v_x_321_, 1);
lean_inc(v_out_339_);
lean_dec_ref_known(v_x_321_, 2);
v___x_340_ = lean_apply_3(v_h__2_323_, v_currPos_337_, v_searcher_338_, v_out_339_);
return v___x_340_;
}
}
case 1:
{
lean_object* v_it_341_; 
lean_dec(v_h__5_326_);
lean_dec(v_h__2_323_);
lean_dec(v_h__1_322_);
v_it_341_ = lean_ctor_get(v_x_321_, 0);
lean_inc(v_it_341_);
lean_dec_ref_known(v_x_321_, 1);
if (lean_obj_tag(v_it_341_) == 0)
{
lean_object* v_currPos_342_; lean_object* v_searcher_343_; lean_object* v_currPos_344_; lean_object* v_searcher_345_; lean_object* v___x_346_; 
lean_dec(v_h__4_325_);
v_currPos_342_ = lean_ctor_get(v_x_320_, 0);
lean_inc(v_currPos_342_);
v_searcher_343_ = lean_ctor_get(v_x_320_, 1);
lean_inc(v_searcher_343_);
lean_dec_ref_known(v_x_320_, 2);
v_currPos_344_ = lean_ctor_get(v_it_341_, 0);
lean_inc(v_currPos_344_);
v_searcher_345_ = lean_ctor_get(v_it_341_, 1);
lean_inc(v_searcher_345_);
lean_dec_ref_known(v_it_341_, 2);
v___x_346_ = lean_apply_4(v_h__3_324_, v_currPos_342_, v_searcher_343_, v_currPos_344_, v_searcher_345_);
return v___x_346_;
}
else
{
lean_object* v_currPos_347_; lean_object* v_searcher_348_; lean_object* v___x_349_; 
lean_dec(v_h__3_324_);
v_currPos_347_ = lean_ctor_get(v_x_320_, 0);
lean_inc(v_currPos_347_);
v_searcher_348_ = lean_ctor_get(v_x_320_, 1);
lean_inc(v_searcher_348_);
lean_dec_ref_known(v_x_320_, 2);
v___x_349_ = lean_apply_2(v_h__4_325_, v_currPos_347_, v_searcher_348_);
return v___x_349_;
}
}
default: 
{
lean_object* v_currPos_350_; lean_object* v_searcher_351_; lean_object* v___x_352_; 
lean_dec(v_h__4_325_);
lean_dec(v_h__3_324_);
lean_dec(v_h__2_323_);
lean_dec(v_h__1_322_);
v_currPos_350_ = lean_ctor_get(v_x_320_, 0);
lean_inc(v_currPos_350_);
v_searcher_351_ = lean_ctor_get(v_x_320_, 1);
lean_inc(v_searcher_351_);
lean_dec_ref_known(v_x_320_, 2);
v___x_352_ = lean_apply_2(v_h__5_326_, v_currPos_350_, v_searcher_351_);
return v___x_352_;
}
}
}
else
{
lean_dec(v_h__5_326_);
lean_dec(v_h__4_325_);
lean_dec(v_h__3_324_);
lean_dec(v_h__2_323_);
lean_dec(v_h__1_322_);
switch(lean_obj_tag(v_x_321_))
{
case 0:
{
lean_object* v_it_353_; lean_object* v_out_354_; lean_object* v___x_355_; 
lean_dec(v_h__8_329_);
lean_dec(v_h__7_328_);
v_it_353_ = lean_ctor_get(v_x_321_, 0);
lean_inc(v_it_353_);
v_out_354_ = lean_ctor_get(v_x_321_, 1);
lean_inc(v_out_354_);
lean_dec_ref_known(v_x_321_, 2);
v___x_355_ = lean_apply_2(v_h__6_327_, v_it_353_, v_out_354_);
return v___x_355_;
}
case 1:
{
lean_object* v_it_356_; lean_object* v___x_357_; 
lean_dec(v_h__8_329_);
lean_dec(v_h__6_327_);
v_it_356_ = lean_ctor_get(v_x_321_, 0);
lean_inc(v_it_356_);
lean_dec_ref_known(v_x_321_, 1);
v___x_357_ = lean_apply_1(v_h__7_328_, v_it_356_);
return v___x_357_;
}
default: 
{
lean_object* v___x_358_; lean_object* v___x_359_; 
lean_dec(v_h__7_328_);
lean_dec(v_h__6_327_);
v___x_358_ = lean_box(0);
v___x_359_ = lean_apply_1(v_h__8_329_, v___x_358_);
return v___x_359_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(lean_object* v_00_u03c1_360_, lean_object* v_00_u03c3_361_, lean_object* v_pat_362_, lean_object* v_inst_363_, lean_object* v_s_364_, lean_object* v_motive_365_, lean_object* v_x_366_, lean_object* v_x_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_, lean_object* v_h__3_370_, lean_object* v_h__4_371_, lean_object* v_h__5_372_, lean_object* v_h__6_373_, lean_object* v_h__7_374_, lean_object* v_h__8_375_){
_start:
{
if (lean_obj_tag(v_x_366_) == 0)
{
lean_dec(v_h__8_375_);
lean_dec(v_h__7_374_);
lean_dec(v_h__6_373_);
switch(lean_obj_tag(v_x_367_))
{
case 0:
{
lean_object* v_it_376_; 
lean_dec(v_h__5_372_);
lean_dec(v_h__4_371_);
lean_dec(v_h__3_370_);
v_it_376_ = lean_ctor_get(v_x_367_, 0);
if (lean_obj_tag(v_it_376_) == 0)
{
lean_object* v_currPos_377_; lean_object* v_searcher_378_; lean_object* v_out_379_; lean_object* v_currPos_380_; lean_object* v_searcher_381_; lean_object* v___x_382_; 
lean_inc_ref(v_it_376_);
lean_dec(v_h__2_369_);
v_currPos_377_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_currPos_377_);
v_searcher_378_ = lean_ctor_get(v_x_366_, 1);
lean_inc(v_searcher_378_);
lean_dec_ref_known(v_x_366_, 2);
v_out_379_ = lean_ctor_get(v_x_367_, 1);
lean_inc(v_out_379_);
lean_dec_ref_known(v_x_367_, 2);
v_currPos_380_ = lean_ctor_get(v_it_376_, 0);
lean_inc(v_currPos_380_);
v_searcher_381_ = lean_ctor_get(v_it_376_, 1);
lean_inc(v_searcher_381_);
lean_dec_ref_known(v_it_376_, 2);
v___x_382_ = lean_apply_5(v_h__1_368_, v_currPos_377_, v_searcher_378_, v_currPos_380_, v_searcher_381_, v_out_379_);
return v___x_382_;
}
else
{
lean_object* v_currPos_383_; lean_object* v_searcher_384_; lean_object* v_out_385_; lean_object* v___x_386_; 
lean_dec(v_h__1_368_);
v_currPos_383_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_currPos_383_);
v_searcher_384_ = lean_ctor_get(v_x_366_, 1);
lean_inc(v_searcher_384_);
lean_dec_ref_known(v_x_366_, 2);
v_out_385_ = lean_ctor_get(v_x_367_, 1);
lean_inc(v_out_385_);
lean_dec_ref_known(v_x_367_, 2);
v___x_386_ = lean_apply_3(v_h__2_369_, v_currPos_383_, v_searcher_384_, v_out_385_);
return v___x_386_;
}
}
case 1:
{
lean_object* v_it_387_; 
lean_dec(v_h__5_372_);
lean_dec(v_h__2_369_);
lean_dec(v_h__1_368_);
v_it_387_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_it_387_);
lean_dec_ref_known(v_x_367_, 1);
if (lean_obj_tag(v_it_387_) == 0)
{
lean_object* v_currPos_388_; lean_object* v_searcher_389_; lean_object* v_currPos_390_; lean_object* v_searcher_391_; lean_object* v___x_392_; 
lean_dec(v_h__4_371_);
v_currPos_388_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_currPos_388_);
v_searcher_389_ = lean_ctor_get(v_x_366_, 1);
lean_inc(v_searcher_389_);
lean_dec_ref_known(v_x_366_, 2);
v_currPos_390_ = lean_ctor_get(v_it_387_, 0);
lean_inc(v_currPos_390_);
v_searcher_391_ = lean_ctor_get(v_it_387_, 1);
lean_inc(v_searcher_391_);
lean_dec_ref_known(v_it_387_, 2);
v___x_392_ = lean_apply_4(v_h__3_370_, v_currPos_388_, v_searcher_389_, v_currPos_390_, v_searcher_391_);
return v___x_392_;
}
else
{
lean_object* v_currPos_393_; lean_object* v_searcher_394_; lean_object* v___x_395_; 
lean_dec(v_h__3_370_);
v_currPos_393_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_currPos_393_);
v_searcher_394_ = lean_ctor_get(v_x_366_, 1);
lean_inc(v_searcher_394_);
lean_dec_ref_known(v_x_366_, 2);
v___x_395_ = lean_apply_2(v_h__4_371_, v_currPos_393_, v_searcher_394_);
return v___x_395_;
}
}
default: 
{
lean_object* v_currPos_396_; lean_object* v_searcher_397_; lean_object* v___x_398_; 
lean_dec(v_h__4_371_);
lean_dec(v_h__3_370_);
lean_dec(v_h__2_369_);
lean_dec(v_h__1_368_);
v_currPos_396_ = lean_ctor_get(v_x_366_, 0);
lean_inc(v_currPos_396_);
v_searcher_397_ = lean_ctor_get(v_x_366_, 1);
lean_inc(v_searcher_397_);
lean_dec_ref_known(v_x_366_, 2);
v___x_398_ = lean_apply_2(v_h__5_372_, v_currPos_396_, v_searcher_397_);
return v___x_398_;
}
}
}
else
{
lean_dec(v_h__5_372_);
lean_dec(v_h__4_371_);
lean_dec(v_h__3_370_);
lean_dec(v_h__2_369_);
lean_dec(v_h__1_368_);
switch(lean_obj_tag(v_x_367_))
{
case 0:
{
lean_object* v_it_399_; lean_object* v_out_400_; lean_object* v___x_401_; 
lean_dec(v_h__8_375_);
lean_dec(v_h__7_374_);
v_it_399_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_it_399_);
v_out_400_ = lean_ctor_get(v_x_367_, 1);
lean_inc(v_out_400_);
lean_dec_ref_known(v_x_367_, 2);
v___x_401_ = lean_apply_2(v_h__6_373_, v_it_399_, v_out_400_);
return v___x_401_;
}
case 1:
{
lean_object* v_it_402_; lean_object* v___x_403_; 
lean_dec(v_h__8_375_);
lean_dec(v_h__6_373_);
v_it_402_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_it_402_);
lean_dec_ref_known(v_x_367_, 1);
v___x_403_ = lean_apply_1(v_h__7_374_, v_it_402_);
return v___x_403_;
}
default: 
{
lean_object* v___x_404_; lean_object* v___x_405_; 
lean_dec(v_h__7_374_);
lean_dec(v_h__6_373_);
v___x_404_ = lean_box(0);
v___x_405_ = lean_apply_1(v_h__8_375_, v___x_404_);
return v___x_405_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___boxed(lean_object* v_00_u03c1_406_, lean_object* v_00_u03c3_407_, lean_object* v_pat_408_, lean_object* v_inst_409_, lean_object* v_s_410_, lean_object* v_motive_411_, lean_object* v_x_412_, lean_object* v_x_413_, lean_object* v_h__1_414_, lean_object* v_h__2_415_, lean_object* v_h__3_416_, lean_object* v_h__4_417_, lean_object* v_h__5_418_, lean_object* v_h__6_419_, lean_object* v_h__7_420_, lean_object* v_h__8_421_){
_start:
{
lean_object* v_res_422_; 
v_res_422_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(v_00_u03c1_406_, v_00_u03c3_407_, v_pat_408_, v_inst_409_, v_s_410_, v_motive_411_, v_x_412_, v_x_413_, v_h__1_414_, v_h__2_415_, v_h__3_416_, v_h__4_417_, v_h__5_418_, v_h__6_419_, v_h__7_420_, v_h__8_421_);
lean_dec_ref(v_s_410_);
lean_dec(v_inst_409_);
lean_dec(v_pat_408_);
return v_res_422_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption_match__1_splitter___redArg(lean_object* v_x_423_, lean_object* v_h__1_424_, lean_object* v_h__2_425_){
_start:
{
if (lean_obj_tag(v_x_423_) == 0)
{
lean_object* v_currPos_426_; lean_object* v_searcher_427_; lean_object* v___x_428_; 
lean_dec(v_h__2_425_);
v_currPos_426_ = lean_ctor_get(v_x_423_, 0);
lean_inc(v_currPos_426_);
v_searcher_427_ = lean_ctor_get(v_x_423_, 1);
lean_inc(v_searcher_427_);
lean_dec_ref_known(v_x_423_, 2);
v___x_428_ = lean_apply_2(v_h__1_424_, v_currPos_426_, v_searcher_427_);
return v___x_428_;
}
else
{
lean_object* v___x_429_; lean_object* v___x_430_; 
lean_dec(v_h__1_424_);
v___x_429_ = lean_box(0);
v___x_430_ = lean_apply_1(v_h__2_425_, v___x_429_);
return v___x_430_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_431_, lean_object* v_00_u03c3_432_, lean_object* v_pat_433_, lean_object* v_inst_434_, lean_object* v_s_435_, lean_object* v_motive_436_, lean_object* v_x_437_, lean_object* v_h__1_438_, lean_object* v_h__2_439_){
_start:
{
if (lean_obj_tag(v_x_437_) == 0)
{
lean_object* v_currPos_440_; lean_object* v_searcher_441_; lean_object* v___x_442_; 
lean_dec(v_h__2_439_);
v_currPos_440_ = lean_ctor_get(v_x_437_, 0);
lean_inc(v_currPos_440_);
v_searcher_441_ = lean_ctor_get(v_x_437_, 1);
lean_inc(v_searcher_441_);
lean_dec_ref_known(v_x_437_, 2);
v___x_442_ = lean_apply_2(v_h__1_438_, v_currPos_440_, v_searcher_441_);
return v___x_442_;
}
else
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v_h__1_438_);
v___x_443_ = lean_box(0);
v___x_444_ = lean_apply_1(v_h__2_439_, v___x_443_);
return v___x_444_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_445_, lean_object* v_00_u03c3_446_, lean_object* v_pat_447_, lean_object* v_inst_448_, lean_object* v_s_449_, lean_object* v_motive_450_, lean_object* v_x_451_, lean_object* v_h__1_452_, lean_object* v_h__2_453_){
_start:
{
lean_object* v_res_454_; 
v_res_454_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_toOption_match__1_splitter(v_00_u03c1_445_, v_00_u03c3_446_, v_pat_447_, v_inst_448_, v_s_449_, v_motive_450_, v_x_451_, v_h__1_452_, v_h__2_453_);
lean_dec_ref(v_s_449_);
lean_dec(v_inst_448_);
lean_dec(v_pat_447_);
return v_res_454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_456_; 
v___x_456_ = lean_box(0);
return v___x_456_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_457_){
_start:
{
lean_object* v_res_458_; 
v_res_458_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation___redArg();
return v_res_458_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation(lean_object* v_00_u03c1_459_, lean_object* v_00_u03c3_460_, lean_object* v_inst_461_, lean_object* v_pat_462_, lean_object* v_inst_463_, lean_object* v_s_464_, lean_object* v_inst_465_){
_start:
{
lean_object* v___x_466_; 
v___x_466_ = lean_box(0);
return v___x_466_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_467_, lean_object* v_00_u03c3_468_, lean_object* v_inst_469_, lean_object* v_pat_470_, lean_object* v_inst_471_, lean_object* v_s_472_, lean_object* v_inst_473_){
_start:
{
lean_object* v_res_474_; 
v_res_474_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation(v_00_u03c1_467_, v_00_u03c3_468_, v_inst_469_, v_pat_470_, v_inst_471_, v_s_472_, v_inst_473_);
lean_dec_ref(v_s_472_);
lean_dec(v_inst_471_);
lean_dec(v_pat_470_);
lean_dec(v_inst_469_);
return v_res_474_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0(lean_object* v_toPure_475_, lean_object* v_recur_476_, lean_object* v_it_477_, lean_object* v_____do__lift_478_){
_start:
{
if (lean_obj_tag(v_____do__lift_478_) == 0)
{
lean_object* v_a_479_; lean_object* v___x_480_; 
lean_dec(v_it_477_);
lean_dec(v_recur_476_);
v_a_479_ = lean_ctor_get(v_____do__lift_478_, 0);
lean_inc(v_a_479_);
lean_dec_ref_known(v_____do__lift_478_, 1);
v___x_480_ = lean_apply_2(v_toPure_475_, lean_box(0), v_a_479_);
return v___x_480_;
}
else
{
lean_object* v_a_481_; lean_object* v___x_482_; 
lean_dec(v_toPure_475_);
v_a_481_ = lean_ctor_get(v_____do__lift_478_, 0);
lean_inc(v_a_481_);
lean_dec_ref_known(v_____do__lift_478_, 1);
v___x_482_ = lean_apply_4(v_recur_476_, v_it_477_, v_a_481_, lean_box(0), lean_box(0));
return v___x_482_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1(lean_object* v_toPure_483_, lean_object* v_recur_484_, lean_object* v___y_485_, lean_object* v_acc_486_, lean_object* v_toBind_487_, lean_object* v_s_488_){
_start:
{
switch(lean_obj_tag(v_s_488_))
{
case 0:
{
lean_object* v_it_489_; lean_object* v_out_490_; lean_object* v___f_491_; lean_object* v___x_492_; lean_object* v___x_493_; 
v_it_489_ = lean_ctor_get(v_s_488_, 0);
lean_inc(v_it_489_);
v_out_490_ = lean_ctor_get(v_s_488_, 1);
lean_inc(v_out_490_);
lean_dec_ref_known(v_s_488_, 2);
v___f_491_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_491_, 0, v_toPure_483_);
lean_closure_set(v___f_491_, 1, v_recur_484_);
lean_closure_set(v___f_491_, 2, v_it_489_);
v___x_492_ = lean_apply_3(v___y_485_, v_out_490_, lean_box(0), v_acc_486_);
v___x_493_ = lean_apply_4(v_toBind_487_, lean_box(0), lean_box(0), v___x_492_, v___f_491_);
return v___x_493_;
}
case 1:
{
lean_object* v_it_494_; lean_object* v___x_495_; 
lean_dec(v_toBind_487_);
lean_dec(v___y_485_);
lean_dec(v_toPure_483_);
v_it_494_ = lean_ctor_get(v_s_488_, 0);
lean_inc(v_it_494_);
lean_dec_ref_known(v_s_488_, 1);
v___x_495_ = lean_apply_4(v_recur_484_, v_it_494_, v_acc_486_, lean_box(0), lean_box(0));
return v___x_495_;
}
default: 
{
lean_object* v___x_496_; 
lean_dec(v_toBind_487_);
lean_dec(v___y_485_);
lean_dec(v_recur_484_);
v___x_496_ = lean_apply_2(v_toPure_483_, lean_box(0), v_acc_486_);
return v___x_496_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2(lean_object* v_toPure_497_, lean_object* v___y_498_, lean_object* v_toBind_499_, lean_object* v_inst_500_, lean_object* v_s_501_, lean_object* v_lift_502_, lean_object* v_it_503_, lean_object* v_acc_504_, lean_object* v_hP_505_, lean_object* v_recur_506_){
_start:
{
lean_object* v___f_507_; 
v___f_507_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_507_, 0, v_toPure_497_);
lean_closure_set(v___f_507_, 1, v_recur_506_);
lean_closure_set(v___f_507_, 2, v___y_498_);
lean_closure_set(v___f_507_, 3, v_acc_504_);
lean_closure_set(v___f_507_, 4, v_toBind_499_);
if (lean_obj_tag(v_it_503_) == 0)
{
lean_object* v_currPos_508_; lean_object* v_searcher_509_; lean_object* v___x_511_; uint8_t v_isShared_512_; uint8_t v_isSharedCheck_556_; 
v_currPos_508_ = lean_ctor_get(v_it_503_, 0);
v_searcher_509_ = lean_ctor_get(v_it_503_, 1);
v_isSharedCheck_556_ = !lean_is_exclusive(v_it_503_);
if (v_isSharedCheck_556_ == 0)
{
v___x_511_ = v_it_503_;
v_isShared_512_ = v_isSharedCheck_556_;
goto v_resetjp_510_;
}
else
{
lean_inc(v_searcher_509_);
lean_inc(v_currPos_508_);
lean_dec(v_it_503_);
v___x_511_ = lean_box(0);
v_isShared_512_ = v_isSharedCheck_556_;
goto v_resetjp_510_;
}
v_resetjp_510_:
{
lean_object* v___x_513_; 
lean_inc_ref(v_s_501_);
v___x_513_ = lean_apply_2(v_inst_500_, v_s_501_, v_searcher_509_);
switch(lean_obj_tag(v___x_513_))
{
case 0:
{
lean_object* v_out_514_; 
v_out_514_ = lean_ctor_get(v___x_513_, 1);
lean_inc(v_out_514_);
if (lean_obj_tag(v_out_514_) == 0)
{
lean_object* v_it_515_; lean_object* v___x_517_; 
lean_dec_ref_known(v_out_514_, 2);
lean_dec_ref(v_s_501_);
v_it_515_ = lean_ctor_get(v___x_513_, 0);
lean_inc(v_it_515_);
lean_dec_ref_known(v___x_513_, 2);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v_it_515_);
v___x_517_ = v___x_511_;
goto v_reusejp_516_;
}
else
{
lean_object* v_reuseFailAlloc_520_; 
v_reuseFailAlloc_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_520_, 0, v_currPos_508_);
lean_ctor_set(v_reuseFailAlloc_520_, 1, v_it_515_);
v___x_517_ = v_reuseFailAlloc_520_;
goto v_reusejp_516_;
}
v_reusejp_516_:
{
lean_object* v___x_518_; lean_object* v___x_519_; 
v___x_518_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_518_, 0, v___x_517_);
v___x_519_ = lean_apply_4(v_lift_502_, lean_box(0), lean_box(0), v___f_507_, v___x_518_);
return v___x_519_;
}
}
else
{
lean_object* v_it_521_; lean_object* v___x_523_; uint8_t v_isShared_524_; uint8_t v_isSharedCheck_535_; 
v_it_521_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_535_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_535_ == 0)
{
lean_object* v_unused_536_; 
v_unused_536_ = lean_ctor_get(v___x_513_, 1);
lean_dec(v_unused_536_);
v___x_523_ = v___x_513_;
v_isShared_524_ = v_isSharedCheck_535_;
goto v_resetjp_522_;
}
else
{
lean_inc(v_it_521_);
lean_dec(v___x_513_);
v___x_523_ = lean_box(0);
v_isShared_524_ = v_isSharedCheck_535_;
goto v_resetjp_522_;
}
v_resetjp_522_:
{
lean_object* v_startPos_525_; lean_object* v_endPos_526_; lean_object* v_slice_527_; lean_object* v_nextIt_529_; 
v_startPos_525_ = lean_ctor_get(v_out_514_, 0);
lean_inc(v_startPos_525_);
v_endPos_526_ = lean_ctor_get(v_out_514_, 1);
lean_inc(v_endPos_526_);
lean_dec_ref_known(v_out_514_, 2);
v_slice_527_ = l_String_Slice_subslice_x21(v_s_501_, v_currPos_508_, v_startPos_525_);
lean_dec_ref(v_s_501_);
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v_it_521_);
lean_ctor_set(v___x_511_, 0, v_endPos_526_);
v_nextIt_529_ = v___x_511_;
goto v_reusejp_528_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_endPos_526_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_it_521_);
v_nextIt_529_ = v_reuseFailAlloc_534_;
goto v_reusejp_528_;
}
v_reusejp_528_:
{
lean_object* v___x_531_; 
if (v_isShared_524_ == 0)
{
lean_ctor_set(v___x_523_, 1, v_slice_527_);
lean_ctor_set(v___x_523_, 0, v_nextIt_529_);
v___x_531_ = v___x_523_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_533_; 
v_reuseFailAlloc_533_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_533_, 0, v_nextIt_529_);
lean_ctor_set(v_reuseFailAlloc_533_, 1, v_slice_527_);
v___x_531_ = v_reuseFailAlloc_533_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; 
v___x_532_ = lean_apply_4(v_lift_502_, lean_box(0), lean_box(0), v___f_507_, v___x_531_);
return v___x_532_;
}
}
}
}
}
case 1:
{
lean_object* v_it_537_; lean_object* v___x_539_; uint8_t v_isShared_540_; uint8_t v_isSharedCheck_548_; 
lean_dec_ref(v_s_501_);
v_it_537_ = lean_ctor_get(v___x_513_, 0);
v_isSharedCheck_548_ = !lean_is_exclusive(v___x_513_);
if (v_isSharedCheck_548_ == 0)
{
v___x_539_ = v___x_513_;
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
else
{
lean_inc(v_it_537_);
lean_dec(v___x_513_);
v___x_539_ = lean_box(0);
v_isShared_540_ = v_isSharedCheck_548_;
goto v_resetjp_538_;
}
v_resetjp_538_:
{
lean_object* v___x_542_; 
if (v_isShared_512_ == 0)
{
lean_ctor_set(v___x_511_, 1, v_it_537_);
v___x_542_ = v___x_511_;
goto v_reusejp_541_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_currPos_508_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_it_537_);
v___x_542_ = v_reuseFailAlloc_547_;
goto v_reusejp_541_;
}
v_reusejp_541_:
{
lean_object* v___x_544_; 
if (v_isShared_540_ == 0)
{
lean_ctor_set(v___x_539_, 0, v___x_542_);
v___x_544_ = v___x_539_;
goto v_reusejp_543_;
}
else
{
lean_object* v_reuseFailAlloc_546_; 
v_reuseFailAlloc_546_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_546_, 0, v___x_542_);
v___x_544_ = v_reuseFailAlloc_546_;
goto v_reusejp_543_;
}
v_reusejp_543_:
{
lean_object* v___x_545_; 
v___x_545_ = lean_apply_4(v_lift_502_, lean_box(0), lean_box(0), v___f_507_, v___x_544_);
return v___x_545_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_549_; lean_object* v_endExclusive_550_; lean_object* v___x_551_; lean_object* v_slice_552_; lean_object* v___x_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
lean_del_object(v___x_511_);
v_startInclusive_549_ = lean_ctor_get(v_s_501_, 1);
lean_inc(v_startInclusive_549_);
v_endExclusive_550_ = lean_ctor_get(v_s_501_, 2);
lean_inc(v_endExclusive_550_);
lean_dec_ref(v_s_501_);
v___x_551_ = lean_nat_sub(v_endExclusive_550_, v_startInclusive_549_);
lean_dec(v_startInclusive_549_);
lean_dec(v_endExclusive_550_);
v_slice_552_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_552_, 0, v_currPos_508_);
lean_ctor_set(v_slice_552_, 1, v___x_551_);
v___x_553_ = lean_box(1);
v___x_554_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_554_, 0, v___x_553_);
lean_ctor_set(v___x_554_, 1, v_slice_552_);
v___x_555_ = lean_apply_4(v_lift_502_, lean_box(0), lean_box(0), v___f_507_, v___x_554_);
return v___x_555_;
}
}
}
}
else
{
lean_object* v___x_557_; lean_object* v___x_558_; 
lean_dec_ref(v_s_501_);
lean_dec(v_inst_500_);
v___x_557_ = lean_box(2);
v___x_558_ = lean_apply_4(v_lift_502_, lean_box(0), lean_box(0), v___f_507_, v___x_557_);
return v___x_558_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3(lean_object* v_inst_559_, lean_object* v_inst_560_, lean_object* v_s_561_, lean_object* v_lift_562_, lean_object* v_00_u03b3_563_, lean_object* v_Pl_564_, lean_object* v_it_565_, lean_object* v_init_566_, lean_object* v___y_567_){
_start:
{
lean_object* v_toApplicative_568_; lean_object* v_toBind_569_; lean_object* v_toPure_570_; lean_object* v___f_571_; lean_object* v___x_572_; 
v_toApplicative_568_ = lean_ctor_get(v_inst_559_, 0);
lean_inc_ref(v_toApplicative_568_);
v_toBind_569_ = lean_ctor_get(v_inst_559_, 1);
lean_inc(v_toBind_569_);
lean_dec_ref(v_inst_559_);
v_toPure_570_ = lean_ctor_get(v_toApplicative_568_, 1);
lean_inc(v_toPure_570_);
lean_dec_ref(v_toApplicative_568_);
v___f_571_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_571_, 0, v_toPure_570_);
lean_closure_set(v___f_571_, 1, v___y_567_);
lean_closure_set(v___f_571_, 2, v_toBind_569_);
lean_closure_set(v___f_571_, 3, v_inst_560_);
lean_closure_set(v___f_571_, 4, v_s_561_);
lean_closure_set(v___f_571_, 5, v_lift_562_);
v___x_572_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_571_, v_it_565_, v_init_566_, lean_box(0));
return v___x_572_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg(lean_object* v_inst_573_, lean_object* v_s_574_, lean_object* v_inst_575_){
_start:
{
lean_object* v___f_576_; 
v___f_576_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_576_, 0, v_inst_575_);
lean_closure_set(v___f_576_, 1, v_inst_573_);
lean_closure_set(v___f_576_, 2, v_s_574_);
return v___f_576_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(lean_object* v_00_u03c1_577_, lean_object* v_00_u03c3_578_, lean_object* v_inst_579_, lean_object* v_pat_580_, lean_object* v_inst_581_, lean_object* v_n_582_, lean_object* v_s_583_, lean_object* v_inst_584_){
_start:
{
lean_object* v___f_585_; 
v___f_585_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_585_, 0, v_inst_584_);
lean_closure_set(v___f_585_, 1, v_inst_579_);
lean_closure_set(v___f_585_, 2, v_s_583_);
return v___f_585_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___boxed(lean_object* v_00_u03c1_586_, lean_object* v_00_u03c3_587_, lean_object* v_inst_588_, lean_object* v_pat_589_, lean_object* v_inst_590_, lean_object* v_n_591_, lean_object* v_s_592_, lean_object* v_inst_593_){
_start:
{
lean_object* v_res_594_; 
v_res_594_ = l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(v_00_u03c1_586_, v_00_u03c3_587_, v_inst_588_, v_pat_589_, v_inst_590_, v_n_591_, v_s_592_, v_inst_593_);
lean_dec(v_inst_590_);
lean_dec(v_pat_589_);
return v_res_594_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___redArg(lean_object* v_s_595_, lean_object* v_inst_596_){
_start:
{
lean_object* v___x_597_; lean_object* v___x_598_; lean_object* v___x_599_; 
v___x_597_ = lean_unsigned_to_nat(0u);
v___x_598_ = lean_apply_1(v_inst_596_, v_s_595_);
v___x_599_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_599_, 0, v___x_597_);
lean_ctor_set(v___x_599_, 1, v___x_598_);
return v___x_599_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice(lean_object* v_00_u03c1_600_, lean_object* v_00_u03c3_601_, lean_object* v_s_602_, lean_object* v_pat_603_, lean_object* v_inst_604_){
_start:
{
lean_object* v___x_605_; 
v___x_605_ = l_String_Slice_splitToSubslice___redArg(v_s_602_, v_inst_604_);
return v___x_605_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___boxed(lean_object* v_00_u03c1_606_, lean_object* v_00_u03c3_607_, lean_object* v_s_608_, lean_object* v_pat_609_, lean_object* v_inst_610_){
_start:
{
lean_object* v_res_611_; 
v_res_611_ = l_String_Slice_splitToSubslice(v_00_u03c1_606_, v_00_u03c3_607_, v_s_608_, v_pat_609_, v_inst_610_);
lean_dec(v_pat_609_);
return v_res_611_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___redArg(lean_object* v_s_612_, lean_object* v_inst_613_){
_start:
{
lean_object* v___x_614_; 
v___x_614_ = l_String_Slice_splitToSubslice___redArg(v_s_612_, v_inst_613_);
return v___x_614_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split(lean_object* v_00_u03c1_615_, lean_object* v_00_u03c3_616_, lean_object* v_inst_617_, lean_object* v_s_618_, lean_object* v_pat_619_, lean_object* v_inst_620_){
_start:
{
lean_object* v___x_621_; 
v___x_621_ = l_String_Slice_splitToSubslice___redArg(v_s_618_, v_inst_620_);
return v___x_621_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___boxed(lean_object* v_00_u03c1_622_, lean_object* v_00_u03c3_623_, lean_object* v_inst_624_, lean_object* v_s_625_, lean_object* v_pat_626_, lean_object* v_inst_627_){
_start:
{
lean_object* v_res_628_; 
v_res_628_ = l_String_Slice_split(v_00_u03c1_622_, v_00_u03c3_623_, v_inst_624_, v_s_625_, v_pat_626_, v_inst_627_);
lean_dec(v_pat_626_);
lean_dec(v_inst_624_);
return v_res_628_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg(lean_object* v_x_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = lean_obj_tag_nat(v_x_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg___boxed(lean_object* v_x_631_){
_start:
{
lean_object* v_res_632_; 
v_res_632_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg(v_x_631_);
lean_dec(v_x_631_);
return v_res_632_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl(lean_object* v_00_u03c3_633_, lean_object* v_00_u03c1_634_, lean_object* v_pat_635_, lean_object* v_s_636_, lean_object* v_inst_637_, lean_object* v_x_638_){
_start:
{
lean_object* v___x_639_; 
v___x_639_ = lean_obj_tag_nat(v_x_638_);
return v___x_639_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___boxed(lean_object* v_00_u03c3_640_, lean_object* v_00_u03c1_641_, lean_object* v_pat_642_, lean_object* v_s_643_, lean_object* v_inst_644_, lean_object* v_x_645_){
_start:
{
lean_object* v_res_646_; 
v_res_646_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___impl(v_00_u03c3_640_, v_00_u03c1_641_, v_pat_642_, v_s_643_, v_inst_644_, v_x_645_);
lean_dec(v_x_645_);
lean_dec(v_inst_644_);
lean_dec_ref(v_s_643_);
lean_dec(v_pat_642_);
return v_res_646_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(lean_object* v_t_647_, lean_object* v_k_648_){
_start:
{
if (lean_obj_tag(v_t_647_) == 0)
{
lean_object* v_currPos_649_; lean_object* v_searcher_650_; lean_object* v___x_651_; 
v_currPos_649_ = lean_ctor_get(v_t_647_, 0);
lean_inc(v_currPos_649_);
v_searcher_650_ = lean_ctor_get(v_t_647_, 1);
lean_inc(v_searcher_650_);
lean_dec_ref_known(v_t_647_, 2);
v___x_651_ = lean_apply_2(v_k_648_, v_currPos_649_, v_searcher_650_);
return v___x_651_;
}
else
{
return v_k_648_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim(lean_object* v_00_u03c3_652_, lean_object* v_00_u03c1_653_, lean_object* v_pat_654_, lean_object* v_s_655_, lean_object* v_inst_656_, lean_object* v_motive_657_, lean_object* v_ctorIdx_658_, lean_object* v_t_659_, lean_object* v_h_660_, lean_object* v_k_661_){
_start:
{
lean_object* v___x_662_; 
v___x_662_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_659_, v_k_661_);
return v___x_662_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___boxed(lean_object* v_00_u03c3_663_, lean_object* v_00_u03c1_664_, lean_object* v_pat_665_, lean_object* v_s_666_, lean_object* v_inst_667_, lean_object* v_motive_668_, lean_object* v_ctorIdx_669_, lean_object* v_t_670_, lean_object* v_h_671_, lean_object* v_k_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_String_Slice_SplitInclusiveIterator_ctorElim(v_00_u03c3_663_, v_00_u03c1_664_, v_pat_665_, v_s_666_, v_inst_667_, v_motive_668_, v_ctorIdx_669_, v_t_670_, v_h_671_, v_k_672_);
lean_dec(v_ctorIdx_669_);
lean_dec(v_inst_667_);
lean_dec_ref(v_s_666_);
lean_dec(v_pat_665_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___redArg(lean_object* v_t_674_, lean_object* v_operating_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_674_, v_operating_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim(lean_object* v_00_u03c3_677_, lean_object* v_00_u03c1_678_, lean_object* v_pat_679_, lean_object* v_s_680_, lean_object* v_inst_681_, lean_object* v_motive_682_, lean_object* v_t_683_, lean_object* v_h_684_, lean_object* v_operating_685_){
_start:
{
lean_object* v___x_686_; 
v___x_686_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_683_, v_operating_685_);
return v___x_686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___boxed(lean_object* v_00_u03c3_687_, lean_object* v_00_u03c1_688_, lean_object* v_pat_689_, lean_object* v_s_690_, lean_object* v_inst_691_, lean_object* v_motive_692_, lean_object* v_t_693_, lean_object* v_h_694_, lean_object* v_operating_695_){
_start:
{
lean_object* v_res_696_; 
v_res_696_ = l_String_Slice_SplitInclusiveIterator_operating_elim(v_00_u03c3_687_, v_00_u03c1_688_, v_pat_689_, v_s_690_, v_inst_691_, v_motive_692_, v_t_693_, v_h_694_, v_operating_695_);
lean_dec(v_inst_691_);
lean_dec_ref(v_s_690_);
lean_dec(v_pat_689_);
return v_res_696_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___redArg(lean_object* v_t_697_, lean_object* v_atEnd_698_){
_start:
{
lean_object* v___x_699_; 
v___x_699_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_697_, v_atEnd_698_);
return v___x_699_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim(lean_object* v_00_u03c3_700_, lean_object* v_00_u03c1_701_, lean_object* v_pat_702_, lean_object* v_s_703_, lean_object* v_inst_704_, lean_object* v_motive_705_, lean_object* v_t_706_, lean_object* v_h_707_, lean_object* v_atEnd_708_){
_start:
{
lean_object* v___x_709_; 
v___x_709_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_706_, v_atEnd_708_);
return v___x_709_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_710_, lean_object* v_00_u03c1_711_, lean_object* v_pat_712_, lean_object* v_s_713_, lean_object* v_inst_714_, lean_object* v_motive_715_, lean_object* v_t_716_, lean_object* v_h_717_, lean_object* v_atEnd_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_String_Slice_SplitInclusiveIterator_atEnd_elim(v_00_u03c3_710_, v_00_u03c1_711_, v_pat_712_, v_s_713_, v_inst_714_, v_motive_715_, v_t_716_, v_h_717_, v_atEnd_718_);
lean_dec(v_inst_714_);
lean_dec_ref(v_s_713_);
lean_dec(v_pat_712_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg(){
_start:
{
lean_object* v___x_721_; 
v___x_721_ = lean_box(1);
return v___x_721_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg___boxed(lean_object* v___dummy_722_){
_start:
{
lean_object* v_res_723_; 
v_res_723_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg();
return v_res_723_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default(lean_object* v_00_u03c3_724_, lean_object* v_00_u03c1_725_, lean_object* v_pat_726_, lean_object* v_s_727_, lean_object* v_inst_728_){
_start:
{
lean_object* v___x_729_; 
v___x_729_ = lean_box(1);
return v___x_729_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___boxed(lean_object* v_00_u03c3_730_, lean_object* v_00_u03c1_731_, lean_object* v_pat_732_, lean_object* v_s_733_, lean_object* v_inst_734_){
_start:
{
lean_object* v_res_735_; 
v_res_735_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default(v_00_u03c3_730_, v_00_u03c1_731_, v_pat_732_, v_s_733_, v_inst_734_);
lean_dec(v_inst_734_);
lean_dec_ref(v_s_733_);
lean_dec(v_pat_732_);
return v_res_735_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg(){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = lean_box(1);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg___boxed(lean_object* v___dummy_738_){
_start:
{
lean_object* v_res_739_; 
v_res_739_ = l_String_Slice_instInhabitedSplitInclusiveIterator___redArg();
return v_res_739_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator(lean_object* v_a_740_, lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_){
_start:
{
lean_object* v___x_745_; 
v___x_745_ = lean_box(1);
return v___x_745_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___boxed(lean_object* v_a_746_, lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_String_Slice_instInhabitedSplitInclusiveIterator(v_a_746_, v_a_747_, v_a_748_, v_a_749_, v_a_750_);
lean_dec(v_a_750_);
lean_dec_ref(v_a_749_);
lean_dec(v_a_748_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0(lean_object* v_inst_752_, lean_object* v_s_753_, lean_object* v_x_754_){
_start:
{
if (lean_obj_tag(v_x_754_) == 0)
{
lean_object* v_currPos_755_; lean_object* v_searcher_756_; lean_object* v___x_758_; uint8_t v_isShared_759_; uint8_t v_isSharedCheck_808_; 
v_currPos_755_ = lean_ctor_get(v_x_754_, 0);
v_searcher_756_ = lean_ctor_get(v_x_754_, 1);
v_isSharedCheck_808_ = !lean_is_exclusive(v_x_754_);
if (v_isSharedCheck_808_ == 0)
{
v___x_758_ = v_x_754_;
v_isShared_759_ = v_isSharedCheck_808_;
goto v_resetjp_757_;
}
else
{
lean_inc(v_searcher_756_);
lean_inc(v_currPos_755_);
lean_dec(v_x_754_);
v___x_758_ = lean_box(0);
v_isShared_759_ = v_isSharedCheck_808_;
goto v_resetjp_757_;
}
v_resetjp_757_:
{
lean_object* v___x_760_; 
lean_inc_ref(v_s_753_);
v___x_760_ = lean_apply_2(v_inst_752_, v_s_753_, v_searcher_756_);
switch(lean_obj_tag(v___x_760_))
{
case 0:
{
lean_object* v_out_761_; 
v_out_761_ = lean_ctor_get(v___x_760_, 1);
lean_inc(v_out_761_);
if (lean_obj_tag(v_out_761_) == 0)
{
lean_object* v_it_762_; lean_object* v___x_764_; 
lean_dec_ref_known(v_out_761_, 2);
lean_dec_ref(v_s_753_);
v_it_762_ = lean_ctor_get(v___x_760_, 0);
lean_inc(v_it_762_);
lean_dec_ref_known(v___x_760_, 2);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v_it_762_);
v___x_764_ = v___x_758_;
goto v_reusejp_763_;
}
else
{
lean_object* v_reuseFailAlloc_766_; 
v_reuseFailAlloc_766_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_766_, 0, v_currPos_755_);
lean_ctor_set(v_reuseFailAlloc_766_, 1, v_it_762_);
v___x_764_ = v_reuseFailAlloc_766_;
goto v_reusejp_763_;
}
v_reusejp_763_:
{
lean_object* v___x_765_; 
v___x_765_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_765_, 0, v___x_764_);
return v___x_765_;
}
}
else
{
lean_object* v_it_767_; lean_object* v___x_769_; uint8_t v_isShared_770_; uint8_t v_isSharedCheck_779_; 
v_it_767_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_779_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_779_ == 0)
{
lean_object* v_unused_780_; 
v_unused_780_ = lean_ctor_get(v___x_760_, 1);
lean_dec(v_unused_780_);
v___x_769_ = v___x_760_;
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
else
{
lean_inc(v_it_767_);
lean_dec(v___x_760_);
v___x_769_ = lean_box(0);
v_isShared_770_ = v_isSharedCheck_779_;
goto v_resetjp_768_;
}
v_resetjp_768_:
{
lean_object* v_endPos_771_; lean_object* v_slice_772_; lean_object* v_nextIt_774_; 
v_endPos_771_ = lean_ctor_get(v_out_761_, 1);
lean_inc(v_endPos_771_);
lean_dec_ref_known(v_out_761_, 2);
v_slice_772_ = l_String_Slice_slice_x21(v_s_753_, v_currPos_755_, v_endPos_771_);
lean_dec(v_currPos_755_);
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v_it_767_);
lean_ctor_set(v___x_758_, 0, v_endPos_771_);
v_nextIt_774_ = v___x_758_;
goto v_reusejp_773_;
}
else
{
lean_object* v_reuseFailAlloc_778_; 
v_reuseFailAlloc_778_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_778_, 0, v_endPos_771_);
lean_ctor_set(v_reuseFailAlloc_778_, 1, v_it_767_);
v_nextIt_774_ = v_reuseFailAlloc_778_;
goto v_reusejp_773_;
}
v_reusejp_773_:
{
lean_object* v___x_776_; 
if (v_isShared_770_ == 0)
{
lean_ctor_set(v___x_769_, 1, v_slice_772_);
lean_ctor_set(v___x_769_, 0, v_nextIt_774_);
v___x_776_ = v___x_769_;
goto v_reusejp_775_;
}
else
{
lean_object* v_reuseFailAlloc_777_; 
v_reuseFailAlloc_777_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_777_, 0, v_nextIt_774_);
lean_ctor_set(v_reuseFailAlloc_777_, 1, v_slice_772_);
v___x_776_ = v_reuseFailAlloc_777_;
goto v_reusejp_775_;
}
v_reusejp_775_:
{
return v___x_776_;
}
}
}
}
}
case 1:
{
lean_object* v_it_781_; lean_object* v___x_783_; uint8_t v_isShared_784_; uint8_t v_isSharedCheck_791_; 
lean_dec_ref(v_s_753_);
v_it_781_ = lean_ctor_get(v___x_760_, 0);
v_isSharedCheck_791_ = !lean_is_exclusive(v___x_760_);
if (v_isSharedCheck_791_ == 0)
{
v___x_783_ = v___x_760_;
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
else
{
lean_inc(v_it_781_);
lean_dec(v___x_760_);
v___x_783_ = lean_box(0);
v_isShared_784_ = v_isSharedCheck_791_;
goto v_resetjp_782_;
}
v_resetjp_782_:
{
lean_object* v___x_786_; 
if (v_isShared_759_ == 0)
{
lean_ctor_set(v___x_758_, 1, v_it_781_);
v___x_786_ = v___x_758_;
goto v_reusejp_785_;
}
else
{
lean_object* v_reuseFailAlloc_790_; 
v_reuseFailAlloc_790_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_790_, 0, v_currPos_755_);
lean_ctor_set(v_reuseFailAlloc_790_, 1, v_it_781_);
v___x_786_ = v_reuseFailAlloc_790_;
goto v_reusejp_785_;
}
v_reusejp_785_:
{
lean_object* v___x_788_; 
if (v_isShared_784_ == 0)
{
lean_ctor_set(v___x_783_, 0, v___x_786_);
v___x_788_ = v___x_783_;
goto v_reusejp_787_;
}
else
{
lean_object* v_reuseFailAlloc_789_; 
v_reuseFailAlloc_789_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_789_, 0, v___x_786_);
v___x_788_ = v_reuseFailAlloc_789_;
goto v_reusejp_787_;
}
v_reusejp_787_:
{
return v___x_788_;
}
}
}
}
default: 
{
lean_object* v_str_792_; lean_object* v_startInclusive_793_; lean_object* v_endExclusive_794_; lean_object* v___x_796_; uint8_t v_isShared_797_; uint8_t v_isSharedCheck_807_; 
lean_del_object(v___x_758_);
v_str_792_ = lean_ctor_get(v_s_753_, 0);
v_startInclusive_793_ = lean_ctor_get(v_s_753_, 1);
v_endExclusive_794_ = lean_ctor_get(v_s_753_, 2);
v_isSharedCheck_807_ = !lean_is_exclusive(v_s_753_);
if (v_isSharedCheck_807_ == 0)
{
v___x_796_ = v_s_753_;
v_isShared_797_ = v_isSharedCheck_807_;
goto v_resetjp_795_;
}
else
{
lean_inc(v_endExclusive_794_);
lean_inc(v_startInclusive_793_);
lean_inc(v_str_792_);
lean_dec(v_s_753_);
v___x_796_ = lean_box(0);
v_isShared_797_ = v_isSharedCheck_807_;
goto v_resetjp_795_;
}
v_resetjp_795_:
{
lean_object* v___x_798_; uint8_t v_decide_799_; 
v___x_798_ = lean_nat_sub(v_endExclusive_794_, v_startInclusive_793_);
v_decide_799_ = lean_nat_dec_eq(v_currPos_755_, v___x_798_);
lean_dec(v___x_798_);
if (v_decide_799_ == 0)
{
lean_object* v___x_800_; lean_object* v_slice_802_; 
v___x_800_ = lean_nat_add(v_startInclusive_793_, v_currPos_755_);
lean_dec(v_currPos_755_);
lean_dec(v_startInclusive_793_);
if (v_isShared_797_ == 0)
{
lean_ctor_set(v___x_796_, 1, v___x_800_);
v_slice_802_ = v___x_796_;
goto v_reusejp_801_;
}
else
{
lean_object* v_reuseFailAlloc_805_; 
v_reuseFailAlloc_805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_805_, 0, v_str_792_);
lean_ctor_set(v_reuseFailAlloc_805_, 1, v___x_800_);
lean_ctor_set(v_reuseFailAlloc_805_, 2, v_endExclusive_794_);
v_slice_802_ = v_reuseFailAlloc_805_;
goto v_reusejp_801_;
}
v_reusejp_801_:
{
lean_object* v___x_803_; lean_object* v___x_804_; 
v___x_803_ = lean_box(1);
v___x_804_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_804_, 0, v___x_803_);
lean_ctor_set(v___x_804_, 1, v_slice_802_);
return v___x_804_;
}
}
else
{
lean_object* v___x_806_; 
lean_del_object(v___x_796_);
lean_dec(v_endExclusive_794_);
lean_dec(v_startInclusive_793_);
lean_dec_ref(v_str_792_);
lean_dec(v_currPos_755_);
v___x_806_ = lean_box(2);
return v___x_806_;
}
}
}
}
}
}
else
{
lean_object* v___x_809_; 
lean_dec_ref(v_s_753_);
lean_dec(v_inst_752_);
v___x_809_ = lean_box(2);
return v___x_809_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg(lean_object* v_inst_810_, lean_object* v_s_811_){
_start:
{
lean_object* v___f_812_; 
v___f_812_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_812_, 0, v_inst_810_);
lean_closure_set(v___f_812_, 1, v_s_811_);
return v___f_812_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId(lean_object* v_00_u03c1_813_, lean_object* v_00_u03c3_814_, lean_object* v_inst_815_, lean_object* v_pat_816_, lean_object* v_inst_817_, lean_object* v_s_818_){
_start:
{
lean_object* v___f_819_; 
v___f_819_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_819_, 0, v_inst_815_);
lean_closure_set(v___f_819_, 1, v_s_818_);
return v___f_819_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___boxed(lean_object* v_00_u03c1_820_, lean_object* v_00_u03c3_821_, lean_object* v_inst_822_, lean_object* v_pat_823_, lean_object* v_inst_824_, lean_object* v_s_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_String_Slice_SplitInclusiveIterator_instIteratorId(v_00_u03c1_820_, v_00_u03c3_821_, v_inst_822_, v_pat_823_, v_inst_824_, v_s_825_);
lean_dec(v_inst_824_);
lean_dec(v_pat_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___redArg(lean_object* v_x_827_){
_start:
{
if (lean_obj_tag(v_x_827_) == 0)
{
lean_object* v_searcher_828_; lean_object* v___x_829_; 
v_searcher_828_ = lean_ctor_get(v_x_827_, 1);
lean_inc(v_searcher_828_);
v___x_829_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_829_, 0, v_searcher_828_);
return v___x_829_;
}
else
{
lean_object* v___x_830_; 
v___x_830_ = lean_box(0);
return v___x_830_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___redArg___boxed(lean_object* v_x_831_){
_start:
{
lean_object* v_res_832_; 
v_res_832_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_831_);
lean_dec(v_x_831_);
return v_res_832_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption(lean_object* v_00_u03c1_833_, lean_object* v_00_u03c3_834_, lean_object* v_pat_835_, lean_object* v_inst_836_, lean_object* v_s_837_, lean_object* v_x_838_){
_start:
{
lean_object* v___x_839_; 
v___x_839_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_838_);
return v___x_839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___boxed(lean_object* v_00_u03c1_840_, lean_object* v_00_u03c3_841_, lean_object* v_pat_842_, lean_object* v_inst_843_, lean_object* v_s_844_, lean_object* v_x_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption(v_00_u03c1_840_, v_00_u03c3_841_, v_pat_842_, v_inst_843_, v_s_844_, v_x_845_);
lean_dec(v_x_845_);
lean_dec_ref(v_s_844_);
lean_dec(v_inst_843_);
lean_dec(v_pat_842_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___redArg(lean_object* v_x_847_, lean_object* v_h__1_848_, lean_object* v_h__2_849_){
_start:
{
if (lean_obj_tag(v_x_847_) == 0)
{
lean_object* v_currPos_850_; lean_object* v_searcher_851_; lean_object* v___x_852_; 
lean_dec(v_h__2_849_);
v_currPos_850_ = lean_ctor_get(v_x_847_, 0);
lean_inc(v_currPos_850_);
v_searcher_851_ = lean_ctor_get(v_x_847_, 1);
lean_inc(v_searcher_851_);
lean_dec_ref_known(v_x_847_, 2);
v___x_852_ = lean_apply_2(v_h__1_848_, v_currPos_850_, v_searcher_851_);
return v___x_852_;
}
else
{
lean_object* v___x_853_; lean_object* v___x_854_; 
lean_dec(v_h__1_848_);
v___x_853_ = lean_box(0);
v___x_854_ = lean_apply_1(v_h__2_849_, v___x_853_);
return v___x_854_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(lean_object* v_00_u03c1_855_, lean_object* v_00_u03c3_856_, lean_object* v_pat_857_, lean_object* v_inst_858_, lean_object* v_s_859_, lean_object* v_motive_860_, lean_object* v_x_861_, lean_object* v_h__1_862_, lean_object* v_h__2_863_){
_start:
{
if (lean_obj_tag(v_x_861_) == 0)
{
lean_object* v_currPos_864_; lean_object* v_searcher_865_; lean_object* v___x_866_; 
lean_dec(v_h__2_863_);
v_currPos_864_ = lean_ctor_get(v_x_861_, 0);
lean_inc(v_currPos_864_);
v_searcher_865_ = lean_ctor_get(v_x_861_, 1);
lean_inc(v_searcher_865_);
lean_dec_ref_known(v_x_861_, 2);
v___x_866_ = lean_apply_2(v_h__1_862_, v_currPos_864_, v_searcher_865_);
return v___x_866_;
}
else
{
lean_object* v___x_867_; lean_object* v___x_868_; 
lean_dec(v_h__1_862_);
v___x_867_ = lean_box(0);
v___x_868_ = lean_apply_1(v_h__2_863_, v___x_867_);
return v___x_868_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___boxed(lean_object* v_00_u03c1_869_, lean_object* v_00_u03c3_870_, lean_object* v_pat_871_, lean_object* v_inst_872_, lean_object* v_s_873_, lean_object* v_motive_874_, lean_object* v_x_875_, lean_object* v_h__1_876_, lean_object* v_h__2_877_){
_start:
{
lean_object* v_res_878_; 
v_res_878_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(v_00_u03c1_869_, v_00_u03c3_870_, v_pat_871_, v_inst_872_, v_s_873_, v_motive_874_, v_x_875_, v_h__1_876_, v_h__2_877_);
lean_dec_ref(v_s_873_);
lean_dec(v_inst_872_);
lean_dec(v_pat_871_);
return v_res_878_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___redArg(lean_object* v_x_879_, lean_object* v_x_880_, lean_object* v_h__1_881_, lean_object* v_h__2_882_, lean_object* v_h__3_883_, lean_object* v_h__4_884_, lean_object* v_h__5_885_, lean_object* v_h__6_886_, lean_object* v_h__7_887_, lean_object* v_h__8_888_){
_start:
{
if (lean_obj_tag(v_x_879_) == 0)
{
lean_dec(v_h__8_888_);
lean_dec(v_h__7_887_);
lean_dec(v_h__6_886_);
switch(lean_obj_tag(v_x_880_))
{
case 0:
{
lean_object* v_it_889_; 
lean_dec(v_h__5_885_);
lean_dec(v_h__4_884_);
lean_dec(v_h__3_883_);
v_it_889_ = lean_ctor_get(v_x_880_, 0);
if (lean_obj_tag(v_it_889_) == 0)
{
lean_object* v_currPos_890_; lean_object* v_searcher_891_; lean_object* v_out_892_; lean_object* v_currPos_893_; lean_object* v_searcher_894_; lean_object* v___x_895_; 
lean_inc_ref(v_it_889_);
lean_dec(v_h__2_882_);
v_currPos_890_ = lean_ctor_get(v_x_879_, 0);
lean_inc(v_currPos_890_);
v_searcher_891_ = lean_ctor_get(v_x_879_, 1);
lean_inc(v_searcher_891_);
lean_dec_ref_known(v_x_879_, 2);
v_out_892_ = lean_ctor_get(v_x_880_, 1);
lean_inc(v_out_892_);
lean_dec_ref_known(v_x_880_, 2);
v_currPos_893_ = lean_ctor_get(v_it_889_, 0);
lean_inc(v_currPos_893_);
v_searcher_894_ = lean_ctor_get(v_it_889_, 1);
lean_inc(v_searcher_894_);
lean_dec_ref_known(v_it_889_, 2);
v___x_895_ = lean_apply_5(v_h__1_881_, v_currPos_890_, v_searcher_891_, v_currPos_893_, v_searcher_894_, v_out_892_);
return v___x_895_;
}
else
{
lean_object* v_currPos_896_; lean_object* v_searcher_897_; lean_object* v_out_898_; lean_object* v___x_899_; 
lean_dec(v_h__1_881_);
v_currPos_896_ = lean_ctor_get(v_x_879_, 0);
lean_inc(v_currPos_896_);
v_searcher_897_ = lean_ctor_get(v_x_879_, 1);
lean_inc(v_searcher_897_);
lean_dec_ref_known(v_x_879_, 2);
v_out_898_ = lean_ctor_get(v_x_880_, 1);
lean_inc(v_out_898_);
lean_dec_ref_known(v_x_880_, 2);
v___x_899_ = lean_apply_3(v_h__2_882_, v_currPos_896_, v_searcher_897_, v_out_898_);
return v___x_899_;
}
}
case 1:
{
lean_object* v_it_900_; 
lean_dec(v_h__5_885_);
lean_dec(v_h__2_882_);
lean_dec(v_h__1_881_);
v_it_900_ = lean_ctor_get(v_x_880_, 0);
lean_inc(v_it_900_);
lean_dec_ref_known(v_x_880_, 1);
if (lean_obj_tag(v_it_900_) == 0)
{
lean_object* v_currPos_901_; lean_object* v_searcher_902_; lean_object* v_currPos_903_; lean_object* v_searcher_904_; lean_object* v___x_905_; 
lean_dec(v_h__4_884_);
v_currPos_901_ = lean_ctor_get(v_x_879_, 0);
lean_inc(v_currPos_901_);
v_searcher_902_ = lean_ctor_get(v_x_879_, 1);
lean_inc(v_searcher_902_);
lean_dec_ref_known(v_x_879_, 2);
v_currPos_903_ = lean_ctor_get(v_it_900_, 0);
lean_inc(v_currPos_903_);
v_searcher_904_ = lean_ctor_get(v_it_900_, 1);
lean_inc(v_searcher_904_);
lean_dec_ref_known(v_it_900_, 2);
v___x_905_ = lean_apply_4(v_h__3_883_, v_currPos_901_, v_searcher_902_, v_currPos_903_, v_searcher_904_);
return v___x_905_;
}
else
{
lean_object* v_currPos_906_; lean_object* v_searcher_907_; lean_object* v___x_908_; 
lean_dec(v_h__3_883_);
v_currPos_906_ = lean_ctor_get(v_x_879_, 0);
lean_inc(v_currPos_906_);
v_searcher_907_ = lean_ctor_get(v_x_879_, 1);
lean_inc(v_searcher_907_);
lean_dec_ref_known(v_x_879_, 2);
v___x_908_ = lean_apply_2(v_h__4_884_, v_currPos_906_, v_searcher_907_);
return v___x_908_;
}
}
default: 
{
lean_object* v_currPos_909_; lean_object* v_searcher_910_; lean_object* v___x_911_; 
lean_dec(v_h__4_884_);
lean_dec(v_h__3_883_);
lean_dec(v_h__2_882_);
lean_dec(v_h__1_881_);
v_currPos_909_ = lean_ctor_get(v_x_879_, 0);
lean_inc(v_currPos_909_);
v_searcher_910_ = lean_ctor_get(v_x_879_, 1);
lean_inc(v_searcher_910_);
lean_dec_ref_known(v_x_879_, 2);
v___x_911_ = lean_apply_2(v_h__5_885_, v_currPos_909_, v_searcher_910_);
return v___x_911_;
}
}
}
else
{
lean_dec(v_h__5_885_);
lean_dec(v_h__4_884_);
lean_dec(v_h__3_883_);
lean_dec(v_h__2_882_);
lean_dec(v_h__1_881_);
switch(lean_obj_tag(v_x_880_))
{
case 0:
{
lean_object* v_it_912_; lean_object* v_out_913_; lean_object* v___x_914_; 
lean_dec(v_h__8_888_);
lean_dec(v_h__7_887_);
v_it_912_ = lean_ctor_get(v_x_880_, 0);
lean_inc(v_it_912_);
v_out_913_ = lean_ctor_get(v_x_880_, 1);
lean_inc(v_out_913_);
lean_dec_ref_known(v_x_880_, 2);
v___x_914_ = lean_apply_2(v_h__6_886_, v_it_912_, v_out_913_);
return v___x_914_;
}
case 1:
{
lean_object* v_it_915_; lean_object* v___x_916_; 
lean_dec(v_h__8_888_);
lean_dec(v_h__6_886_);
v_it_915_ = lean_ctor_get(v_x_880_, 0);
lean_inc(v_it_915_);
lean_dec_ref_known(v_x_880_, 1);
v___x_916_ = lean_apply_1(v_h__7_887_, v_it_915_);
return v___x_916_;
}
default: 
{
lean_object* v___x_917_; lean_object* v___x_918_; 
lean_dec(v_h__7_887_);
lean_dec(v_h__6_886_);
v___x_917_ = lean_box(0);
v___x_918_ = lean_apply_1(v_h__8_888_, v___x_917_);
return v___x_918_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(lean_object* v_00_u03c1_919_, lean_object* v_00_u03c3_920_, lean_object* v_pat_921_, lean_object* v_inst_922_, lean_object* v_s_923_, lean_object* v_motive_924_, lean_object* v_x_925_, lean_object* v_x_926_, lean_object* v_h__1_927_, lean_object* v_h__2_928_, lean_object* v_h__3_929_, lean_object* v_h__4_930_, lean_object* v_h__5_931_, lean_object* v_h__6_932_, lean_object* v_h__7_933_, lean_object* v_h__8_934_){
_start:
{
if (lean_obj_tag(v_x_925_) == 0)
{
lean_dec(v_h__8_934_);
lean_dec(v_h__7_933_);
lean_dec(v_h__6_932_);
switch(lean_obj_tag(v_x_926_))
{
case 0:
{
lean_object* v_it_935_; 
lean_dec(v_h__5_931_);
lean_dec(v_h__4_930_);
lean_dec(v_h__3_929_);
v_it_935_ = lean_ctor_get(v_x_926_, 0);
if (lean_obj_tag(v_it_935_) == 0)
{
lean_object* v_currPos_936_; lean_object* v_searcher_937_; lean_object* v_out_938_; lean_object* v_currPos_939_; lean_object* v_searcher_940_; lean_object* v___x_941_; 
lean_inc_ref(v_it_935_);
lean_dec(v_h__2_928_);
v_currPos_936_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_currPos_936_);
v_searcher_937_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_searcher_937_);
lean_dec_ref_known(v_x_925_, 2);
v_out_938_ = lean_ctor_get(v_x_926_, 1);
lean_inc(v_out_938_);
lean_dec_ref_known(v_x_926_, 2);
v_currPos_939_ = lean_ctor_get(v_it_935_, 0);
lean_inc(v_currPos_939_);
v_searcher_940_ = lean_ctor_get(v_it_935_, 1);
lean_inc(v_searcher_940_);
lean_dec_ref_known(v_it_935_, 2);
v___x_941_ = lean_apply_5(v_h__1_927_, v_currPos_936_, v_searcher_937_, v_currPos_939_, v_searcher_940_, v_out_938_);
return v___x_941_;
}
else
{
lean_object* v_currPos_942_; lean_object* v_searcher_943_; lean_object* v_out_944_; lean_object* v___x_945_; 
lean_dec(v_h__1_927_);
v_currPos_942_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_currPos_942_);
v_searcher_943_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_searcher_943_);
lean_dec_ref_known(v_x_925_, 2);
v_out_944_ = lean_ctor_get(v_x_926_, 1);
lean_inc(v_out_944_);
lean_dec_ref_known(v_x_926_, 2);
v___x_945_ = lean_apply_3(v_h__2_928_, v_currPos_942_, v_searcher_943_, v_out_944_);
return v___x_945_;
}
}
case 1:
{
lean_object* v_it_946_; 
lean_dec(v_h__5_931_);
lean_dec(v_h__2_928_);
lean_dec(v_h__1_927_);
v_it_946_ = lean_ctor_get(v_x_926_, 0);
lean_inc(v_it_946_);
lean_dec_ref_known(v_x_926_, 1);
if (lean_obj_tag(v_it_946_) == 0)
{
lean_object* v_currPos_947_; lean_object* v_searcher_948_; lean_object* v_currPos_949_; lean_object* v_searcher_950_; lean_object* v___x_951_; 
lean_dec(v_h__4_930_);
v_currPos_947_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_currPos_947_);
v_searcher_948_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_searcher_948_);
lean_dec_ref_known(v_x_925_, 2);
v_currPos_949_ = lean_ctor_get(v_it_946_, 0);
lean_inc(v_currPos_949_);
v_searcher_950_ = lean_ctor_get(v_it_946_, 1);
lean_inc(v_searcher_950_);
lean_dec_ref_known(v_it_946_, 2);
v___x_951_ = lean_apply_4(v_h__3_929_, v_currPos_947_, v_searcher_948_, v_currPos_949_, v_searcher_950_);
return v___x_951_;
}
else
{
lean_object* v_currPos_952_; lean_object* v_searcher_953_; lean_object* v___x_954_; 
lean_dec(v_h__3_929_);
v_currPos_952_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_currPos_952_);
v_searcher_953_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_searcher_953_);
lean_dec_ref_known(v_x_925_, 2);
v___x_954_ = lean_apply_2(v_h__4_930_, v_currPos_952_, v_searcher_953_);
return v___x_954_;
}
}
default: 
{
lean_object* v_currPos_955_; lean_object* v_searcher_956_; lean_object* v___x_957_; 
lean_dec(v_h__4_930_);
lean_dec(v_h__3_929_);
lean_dec(v_h__2_928_);
lean_dec(v_h__1_927_);
v_currPos_955_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_currPos_955_);
v_searcher_956_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_searcher_956_);
lean_dec_ref_known(v_x_925_, 2);
v___x_957_ = lean_apply_2(v_h__5_931_, v_currPos_955_, v_searcher_956_);
return v___x_957_;
}
}
}
else
{
lean_dec(v_h__5_931_);
lean_dec(v_h__4_930_);
lean_dec(v_h__3_929_);
lean_dec(v_h__2_928_);
lean_dec(v_h__1_927_);
switch(lean_obj_tag(v_x_926_))
{
case 0:
{
lean_object* v_it_958_; lean_object* v_out_959_; lean_object* v___x_960_; 
lean_dec(v_h__8_934_);
lean_dec(v_h__7_933_);
v_it_958_ = lean_ctor_get(v_x_926_, 0);
lean_inc(v_it_958_);
v_out_959_ = lean_ctor_get(v_x_926_, 1);
lean_inc(v_out_959_);
lean_dec_ref_known(v_x_926_, 2);
v___x_960_ = lean_apply_2(v_h__6_932_, v_it_958_, v_out_959_);
return v___x_960_;
}
case 1:
{
lean_object* v_it_961_; lean_object* v___x_962_; 
lean_dec(v_h__8_934_);
lean_dec(v_h__6_932_);
v_it_961_ = lean_ctor_get(v_x_926_, 0);
lean_inc(v_it_961_);
lean_dec_ref_known(v_x_926_, 1);
v___x_962_ = lean_apply_1(v_h__7_933_, v_it_961_);
return v___x_962_;
}
default: 
{
lean_object* v___x_963_; lean_object* v___x_964_; 
lean_dec(v_h__7_933_);
lean_dec(v_h__6_932_);
v___x_963_ = lean_box(0);
v___x_964_ = lean_apply_1(v_h__8_934_, v___x_963_);
return v___x_964_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___boxed(lean_object* v_00_u03c1_965_, lean_object* v_00_u03c3_966_, lean_object* v_pat_967_, lean_object* v_inst_968_, lean_object* v_s_969_, lean_object* v_motive_970_, lean_object* v_x_971_, lean_object* v_x_972_, lean_object* v_h__1_973_, lean_object* v_h__2_974_, lean_object* v_h__3_975_, lean_object* v_h__4_976_, lean_object* v_h__5_977_, lean_object* v_h__6_978_, lean_object* v_h__7_979_, lean_object* v_h__8_980_){
_start:
{
lean_object* v_res_981_; 
v_res_981_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(v_00_u03c1_965_, v_00_u03c3_966_, v_pat_967_, v_inst_968_, v_s_969_, v_motive_970_, v_x_971_, v_x_972_, v_h__1_973_, v_h__2_974_, v_h__3_975_, v_h__4_976_, v_h__5_977_, v_h__6_978_, v_h__7_979_, v_h__8_980_);
lean_dec_ref(v_s_969_);
lean_dec(v_inst_968_);
lean_dec(v_pat_967_);
return v_res_981_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___redArg(lean_object* v_x_982_, lean_object* v_h__1_983_, lean_object* v_h__2_984_){
_start:
{
if (lean_obj_tag(v_x_982_) == 0)
{
lean_object* v_currPos_985_; lean_object* v_searcher_986_; lean_object* v___x_987_; 
lean_dec(v_h__2_984_);
v_currPos_985_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_currPos_985_);
v_searcher_986_ = lean_ctor_get(v_x_982_, 1);
lean_inc(v_searcher_986_);
lean_dec_ref_known(v_x_982_, 2);
v___x_987_ = lean_apply_2(v_h__1_983_, v_currPos_985_, v_searcher_986_);
return v___x_987_;
}
else
{
lean_object* v___x_988_; lean_object* v___x_989_; 
lean_dec(v_h__1_983_);
v___x_988_ = lean_box(0);
v___x_989_ = lean_apply_1(v_h__2_984_, v___x_988_);
return v___x_989_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_990_, lean_object* v_00_u03c3_991_, lean_object* v_pat_992_, lean_object* v_inst_993_, lean_object* v_s_994_, lean_object* v_motive_995_, lean_object* v_x_996_, lean_object* v_h__1_997_, lean_object* v_h__2_998_){
_start:
{
if (lean_obj_tag(v_x_996_) == 0)
{
lean_object* v_currPos_999_; lean_object* v_searcher_1000_; lean_object* v___x_1001_; 
lean_dec(v_h__2_998_);
v_currPos_999_ = lean_ctor_get(v_x_996_, 0);
lean_inc(v_currPos_999_);
v_searcher_1000_ = lean_ctor_get(v_x_996_, 1);
lean_inc(v_searcher_1000_);
lean_dec_ref_known(v_x_996_, 2);
v___x_1001_ = lean_apply_2(v_h__1_997_, v_currPos_999_, v_searcher_1000_);
return v___x_1001_;
}
else
{
lean_object* v___x_1002_; lean_object* v___x_1003_; 
lean_dec(v_h__1_997_);
v___x_1002_ = lean_box(0);
v___x_1003_ = lean_apply_1(v_h__2_998_, v___x_1002_);
return v___x_1003_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_1004_, lean_object* v_00_u03c3_1005_, lean_object* v_pat_1006_, lean_object* v_inst_1007_, lean_object* v_s_1008_, lean_object* v_motive_1009_, lean_object* v_x_1010_, lean_object* v_h__1_1011_, lean_object* v_h__2_1012_){
_start:
{
lean_object* v_res_1013_; 
v_res_1013_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(v_00_u03c1_1004_, v_00_u03c3_1005_, v_pat_1006_, v_inst_1007_, v_s_1008_, v_motive_1009_, v_x_1010_, v_h__1_1011_, v_h__2_1012_);
lean_dec_ref(v_s_1008_);
lean_dec(v_inst_1007_);
lean_dec(v_pat_1006_);
return v_res_1013_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_1015_; 
v___x_1015_ = lean_box(0);
return v___x_1015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_1016_){
_start:
{
lean_object* v_res_1017_; 
v_res_1017_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg();
return v_res_1017_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation(lean_object* v_00_u03c1_1018_, lean_object* v_00_u03c3_1019_, lean_object* v_inst_1020_, lean_object* v_pat_1021_, lean_object* v_inst_1022_, lean_object* v_s_1023_, lean_object* v_inst_1024_){
_start:
{
lean_object* v___x_1025_; 
v___x_1025_ = lean_box(0);
return v___x_1025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_1026_, lean_object* v_00_u03c3_1027_, lean_object* v_inst_1028_, lean_object* v_pat_1029_, lean_object* v_inst_1030_, lean_object* v_s_1031_, lean_object* v_inst_1032_){
_start:
{
lean_object* v_res_1033_; 
v_res_1033_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation(v_00_u03c1_1026_, v_00_u03c3_1027_, v_inst_1028_, v_pat_1029_, v_inst_1030_, v_s_1031_, v_inst_1032_);
lean_dec_ref(v_s_1031_);
lean_dec(v_inst_1030_);
lean_dec(v_pat_1029_);
lean_dec(v_inst_1028_);
return v_res_1033_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0(lean_object* v_toPure_1034_, lean_object* v_recur_1035_, lean_object* v_it_1036_, lean_object* v_____do__lift_1037_){
_start:
{
if (lean_obj_tag(v_____do__lift_1037_) == 0)
{
lean_object* v_a_1038_; lean_object* v___x_1039_; 
lean_dec(v_it_1036_);
lean_dec(v_recur_1035_);
v_a_1038_ = lean_ctor_get(v_____do__lift_1037_, 0);
lean_inc(v_a_1038_);
lean_dec_ref_known(v_____do__lift_1037_, 1);
v___x_1039_ = lean_apply_2(v_toPure_1034_, lean_box(0), v_a_1038_);
return v___x_1039_;
}
else
{
lean_object* v_a_1040_; lean_object* v___x_1041_; 
lean_dec(v_toPure_1034_);
v_a_1040_ = lean_ctor_get(v_____do__lift_1037_, 0);
lean_inc(v_a_1040_);
lean_dec_ref_known(v_____do__lift_1037_, 1);
v___x_1041_ = lean_apply_4(v_recur_1035_, v_it_1036_, v_a_1040_, lean_box(0), lean_box(0));
return v___x_1041_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1(lean_object* v_toPure_1042_, lean_object* v_recur_1043_, lean_object* v___y_1044_, lean_object* v_acc_1045_, lean_object* v_toBind_1046_, lean_object* v_s_1047_){
_start:
{
switch(lean_obj_tag(v_s_1047_))
{
case 0:
{
lean_object* v_it_1048_; lean_object* v_out_1049_; lean_object* v___f_1050_; lean_object* v___x_1051_; lean_object* v___x_1052_; 
v_it_1048_ = lean_ctor_get(v_s_1047_, 0);
lean_inc(v_it_1048_);
v_out_1049_ = lean_ctor_get(v_s_1047_, 1);
lean_inc(v_out_1049_);
lean_dec_ref_known(v_s_1047_, 2);
v___f_1050_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1050_, 0, v_toPure_1042_);
lean_closure_set(v___f_1050_, 1, v_recur_1043_);
lean_closure_set(v___f_1050_, 2, v_it_1048_);
v___x_1051_ = lean_apply_3(v___y_1044_, v_out_1049_, lean_box(0), v_acc_1045_);
v___x_1052_ = lean_apply_4(v_toBind_1046_, lean_box(0), lean_box(0), v___x_1051_, v___f_1050_);
return v___x_1052_;
}
case 1:
{
lean_object* v_it_1053_; lean_object* v___x_1054_; 
lean_dec(v_toBind_1046_);
lean_dec(v___y_1044_);
lean_dec(v_toPure_1042_);
v_it_1053_ = lean_ctor_get(v_s_1047_, 0);
lean_inc(v_it_1053_);
lean_dec_ref_known(v_s_1047_, 1);
v___x_1054_ = lean_apply_4(v_recur_1043_, v_it_1053_, v_acc_1045_, lean_box(0), lean_box(0));
return v___x_1054_;
}
default: 
{
lean_object* v___x_1055_; 
lean_dec(v_toBind_1046_);
lean_dec(v___y_1044_);
lean_dec(v_recur_1043_);
v___x_1055_ = lean_apply_2(v_toPure_1042_, lean_box(0), v_acc_1045_);
return v___x_1055_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2(lean_object* v_toPure_1056_, lean_object* v___y_1057_, lean_object* v_toBind_1058_, lean_object* v_inst_1059_, lean_object* v_s_1060_, lean_object* v_lift_1061_, lean_object* v_it_1062_, lean_object* v_acc_1063_, lean_object* v_hP_1064_, lean_object* v_recur_1065_){
_start:
{
lean_object* v___f_1066_; 
v___f_1066_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_1066_, 0, v_toPure_1056_);
lean_closure_set(v___f_1066_, 1, v_recur_1065_);
lean_closure_set(v___f_1066_, 2, v___y_1057_);
lean_closure_set(v___f_1066_, 3, v_acc_1063_);
lean_closure_set(v___f_1066_, 4, v_toBind_1058_);
if (lean_obj_tag(v_it_1062_) == 0)
{
lean_object* v_currPos_1067_; lean_object* v_searcher_1068_; lean_object* v___x_1070_; uint8_t v_isShared_1071_; uint8_t v_isSharedCheck_1125_; 
v_currPos_1067_ = lean_ctor_get(v_it_1062_, 0);
v_searcher_1068_ = lean_ctor_get(v_it_1062_, 1);
v_isSharedCheck_1125_ = !lean_is_exclusive(v_it_1062_);
if (v_isSharedCheck_1125_ == 0)
{
v___x_1070_ = v_it_1062_;
v_isShared_1071_ = v_isSharedCheck_1125_;
goto v_resetjp_1069_;
}
else
{
lean_inc(v_searcher_1068_);
lean_inc(v_currPos_1067_);
lean_dec(v_it_1062_);
v___x_1070_ = lean_box(0);
v_isShared_1071_ = v_isSharedCheck_1125_;
goto v_resetjp_1069_;
}
v_resetjp_1069_:
{
lean_object* v___x_1072_; 
lean_inc_ref(v_s_1060_);
v___x_1072_ = lean_apply_2(v_inst_1059_, v_s_1060_, v_searcher_1068_);
switch(lean_obj_tag(v___x_1072_))
{
case 0:
{
lean_object* v_out_1073_; 
v_out_1073_ = lean_ctor_get(v___x_1072_, 1);
lean_inc(v_out_1073_);
if (lean_obj_tag(v_out_1073_) == 0)
{
lean_object* v_it_1074_; lean_object* v___x_1076_; 
lean_dec_ref_known(v_out_1073_, 2);
lean_dec_ref(v_s_1060_);
v_it_1074_ = lean_ctor_get(v___x_1072_, 0);
lean_inc(v_it_1074_);
lean_dec_ref_known(v___x_1072_, 2);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v_it_1074_);
v___x_1076_ = v___x_1070_;
goto v_reusejp_1075_;
}
else
{
lean_object* v_reuseFailAlloc_1079_; 
v_reuseFailAlloc_1079_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1079_, 0, v_currPos_1067_);
lean_ctor_set(v_reuseFailAlloc_1079_, 1, v_it_1074_);
v___x_1076_ = v_reuseFailAlloc_1079_;
goto v_reusejp_1075_;
}
v_reusejp_1075_:
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
v___x_1077_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1077_, 0, v___x_1076_);
v___x_1078_ = lean_apply_4(v_lift_1061_, lean_box(0), lean_box(0), v___f_1066_, v___x_1077_);
return v___x_1078_;
}
}
else
{
lean_object* v_it_1080_; lean_object* v___x_1082_; uint8_t v_isShared_1083_; uint8_t v_isSharedCheck_1093_; 
v_it_1080_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1093_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1093_ == 0)
{
lean_object* v_unused_1094_; 
v_unused_1094_ = lean_ctor_get(v___x_1072_, 1);
lean_dec(v_unused_1094_);
v___x_1082_ = v___x_1072_;
v_isShared_1083_ = v_isSharedCheck_1093_;
goto v_resetjp_1081_;
}
else
{
lean_inc(v_it_1080_);
lean_dec(v___x_1072_);
v___x_1082_ = lean_box(0);
v_isShared_1083_ = v_isSharedCheck_1093_;
goto v_resetjp_1081_;
}
v_resetjp_1081_:
{
lean_object* v_endPos_1084_; lean_object* v_slice_1085_; lean_object* v_nextIt_1087_; 
v_endPos_1084_ = lean_ctor_get(v_out_1073_, 1);
lean_inc(v_endPos_1084_);
lean_dec_ref_known(v_out_1073_, 2);
v_slice_1085_ = l_String_Slice_slice_x21(v_s_1060_, v_currPos_1067_, v_endPos_1084_);
lean_dec(v_currPos_1067_);
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v_it_1080_);
lean_ctor_set(v___x_1070_, 0, v_endPos_1084_);
v_nextIt_1087_ = v___x_1070_;
goto v_reusejp_1086_;
}
else
{
lean_object* v_reuseFailAlloc_1092_; 
v_reuseFailAlloc_1092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1092_, 0, v_endPos_1084_);
lean_ctor_set(v_reuseFailAlloc_1092_, 1, v_it_1080_);
v_nextIt_1087_ = v_reuseFailAlloc_1092_;
goto v_reusejp_1086_;
}
v_reusejp_1086_:
{
lean_object* v___x_1089_; 
if (v_isShared_1083_ == 0)
{
lean_ctor_set(v___x_1082_, 1, v_slice_1085_);
lean_ctor_set(v___x_1082_, 0, v_nextIt_1087_);
v___x_1089_ = v___x_1082_;
goto v_reusejp_1088_;
}
else
{
lean_object* v_reuseFailAlloc_1091_; 
v_reuseFailAlloc_1091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1091_, 0, v_nextIt_1087_);
lean_ctor_set(v_reuseFailAlloc_1091_, 1, v_slice_1085_);
v___x_1089_ = v_reuseFailAlloc_1091_;
goto v_reusejp_1088_;
}
v_reusejp_1088_:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_apply_4(v_lift_1061_, lean_box(0), lean_box(0), v___f_1066_, v___x_1089_);
return v___x_1090_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1095_; lean_object* v___x_1097_; uint8_t v_isShared_1098_; uint8_t v_isSharedCheck_1106_; 
lean_dec_ref(v_s_1060_);
v_it_1095_ = lean_ctor_get(v___x_1072_, 0);
v_isSharedCheck_1106_ = !lean_is_exclusive(v___x_1072_);
if (v_isSharedCheck_1106_ == 0)
{
v___x_1097_ = v___x_1072_;
v_isShared_1098_ = v_isSharedCheck_1106_;
goto v_resetjp_1096_;
}
else
{
lean_inc(v_it_1095_);
lean_dec(v___x_1072_);
v___x_1097_ = lean_box(0);
v_isShared_1098_ = v_isSharedCheck_1106_;
goto v_resetjp_1096_;
}
v_resetjp_1096_:
{
lean_object* v___x_1100_; 
if (v_isShared_1071_ == 0)
{
lean_ctor_set(v___x_1070_, 1, v_it_1095_);
v___x_1100_ = v___x_1070_;
goto v_reusejp_1099_;
}
else
{
lean_object* v_reuseFailAlloc_1105_; 
v_reuseFailAlloc_1105_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1105_, 0, v_currPos_1067_);
lean_ctor_set(v_reuseFailAlloc_1105_, 1, v_it_1095_);
v___x_1100_ = v_reuseFailAlloc_1105_;
goto v_reusejp_1099_;
}
v_reusejp_1099_:
{
lean_object* v___x_1102_; 
if (v_isShared_1098_ == 0)
{
lean_ctor_set(v___x_1097_, 0, v___x_1100_);
v___x_1102_ = v___x_1097_;
goto v_reusejp_1101_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v___x_1100_);
v___x_1102_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1101_;
}
v_reusejp_1101_:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_apply_4(v_lift_1061_, lean_box(0), lean_box(0), v___f_1066_, v___x_1102_);
return v___x_1103_;
}
}
}
}
default: 
{
lean_object* v_str_1107_; lean_object* v_startInclusive_1108_; lean_object* v_endExclusive_1109_; lean_object* v___x_1111_; uint8_t v_isShared_1112_; uint8_t v_isSharedCheck_1124_; 
lean_del_object(v___x_1070_);
v_str_1107_ = lean_ctor_get(v_s_1060_, 0);
v_startInclusive_1108_ = lean_ctor_get(v_s_1060_, 1);
v_endExclusive_1109_ = lean_ctor_get(v_s_1060_, 2);
v_isSharedCheck_1124_ = !lean_is_exclusive(v_s_1060_);
if (v_isSharedCheck_1124_ == 0)
{
v___x_1111_ = v_s_1060_;
v_isShared_1112_ = v_isSharedCheck_1124_;
goto v_resetjp_1110_;
}
else
{
lean_inc(v_endExclusive_1109_);
lean_inc(v_startInclusive_1108_);
lean_inc(v_str_1107_);
lean_dec(v_s_1060_);
v___x_1111_ = lean_box(0);
v_isShared_1112_ = v_isSharedCheck_1124_;
goto v_resetjp_1110_;
}
v_resetjp_1110_:
{
lean_object* v___x_1113_; uint8_t v_decide_1114_; 
v___x_1113_ = lean_nat_sub(v_endExclusive_1109_, v_startInclusive_1108_);
v_decide_1114_ = lean_nat_dec_eq(v_currPos_1067_, v___x_1113_);
lean_dec(v___x_1113_);
if (v_decide_1114_ == 0)
{
lean_object* v___x_1115_; lean_object* v_slice_1117_; 
v___x_1115_ = lean_nat_add(v_startInclusive_1108_, v_currPos_1067_);
lean_dec(v_currPos_1067_);
lean_dec(v_startInclusive_1108_);
if (v_isShared_1112_ == 0)
{
lean_ctor_set(v___x_1111_, 1, v___x_1115_);
v_slice_1117_ = v___x_1111_;
goto v_reusejp_1116_;
}
else
{
lean_object* v_reuseFailAlloc_1121_; 
v_reuseFailAlloc_1121_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1121_, 0, v_str_1107_);
lean_ctor_set(v_reuseFailAlloc_1121_, 1, v___x_1115_);
lean_ctor_set(v_reuseFailAlloc_1121_, 2, v_endExclusive_1109_);
v_slice_1117_ = v_reuseFailAlloc_1121_;
goto v_reusejp_1116_;
}
v_reusejp_1116_:
{
lean_object* v___x_1118_; lean_object* v___x_1119_; lean_object* v___x_1120_; 
v___x_1118_ = lean_box(1);
v___x_1119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1119_, 0, v___x_1118_);
lean_ctor_set(v___x_1119_, 1, v_slice_1117_);
v___x_1120_ = lean_apply_4(v_lift_1061_, lean_box(0), lean_box(0), v___f_1066_, v___x_1119_);
return v___x_1120_;
}
}
else
{
lean_object* v___x_1122_; lean_object* v___x_1123_; 
lean_del_object(v___x_1111_);
lean_dec(v_endExclusive_1109_);
lean_dec(v_startInclusive_1108_);
lean_dec_ref(v_str_1107_);
lean_dec(v_currPos_1067_);
v___x_1122_ = lean_box(2);
v___x_1123_ = lean_apply_4(v_lift_1061_, lean_box(0), lean_box(0), v___f_1066_, v___x_1122_);
return v___x_1123_;
}
}
}
}
}
}
else
{
lean_object* v___x_1126_; lean_object* v___x_1127_; 
lean_dec_ref(v_s_1060_);
lean_dec(v_inst_1059_);
v___x_1126_ = lean_box(2);
v___x_1127_ = lean_apply_4(v_lift_1061_, lean_box(0), lean_box(0), v___f_1066_, v___x_1126_);
return v___x_1127_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3(lean_object* v_inst_1128_, lean_object* v_inst_1129_, lean_object* v_s_1130_, lean_object* v_lift_1131_, lean_object* v_00_u03b3_1132_, lean_object* v_Pl_1133_, lean_object* v_it_1134_, lean_object* v_init_1135_, lean_object* v___y_1136_){
_start:
{
lean_object* v_toApplicative_1137_; lean_object* v_toBind_1138_; lean_object* v_toPure_1139_; lean_object* v___f_1140_; lean_object* v___x_1141_; 
v_toApplicative_1137_ = lean_ctor_get(v_inst_1128_, 0);
lean_inc_ref(v_toApplicative_1137_);
v_toBind_1138_ = lean_ctor_get(v_inst_1128_, 1);
lean_inc(v_toBind_1138_);
lean_dec_ref(v_inst_1128_);
v_toPure_1139_ = lean_ctor_get(v_toApplicative_1137_, 1);
lean_inc(v_toPure_1139_);
lean_dec_ref(v_toApplicative_1137_);
v___f_1140_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_1140_, 0, v_toPure_1139_);
lean_closure_set(v___f_1140_, 1, v___y_1136_);
lean_closure_set(v___f_1140_, 2, v_toBind_1138_);
lean_closure_set(v___f_1140_, 3, v_inst_1129_);
lean_closure_set(v___f_1140_, 4, v_s_1130_);
lean_closure_set(v___f_1140_, 5, v_lift_1131_);
v___x_1141_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1140_, v_it_1134_, v_init_1135_, lean_box(0));
return v___x_1141_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg(lean_object* v_inst_1142_, lean_object* v_inst_1143_, lean_object* v_s_1144_){
_start:
{
lean_object* v___f_1145_; 
v___f_1145_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1145_, 0, v_inst_1143_);
lean_closure_set(v___f_1145_, 1, v_inst_1142_);
lean_closure_set(v___f_1145_, 2, v_s_1144_);
return v___f_1145_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(lean_object* v_00_u03c1_1146_, lean_object* v_00_u03c3_1147_, lean_object* v_inst_1148_, lean_object* v_pat_1149_, lean_object* v_inst_1150_, lean_object* v_n_1151_, lean_object* v_inst_1152_, lean_object* v_s_1153_){
_start:
{
lean_object* v___f_1154_; 
v___f_1154_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1154_, 0, v_inst_1152_);
lean_closure_set(v___f_1154_, 1, v_inst_1148_);
lean_closure_set(v___f_1154_, 2, v_s_1153_);
return v___f_1154_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___boxed(lean_object* v_00_u03c1_1155_, lean_object* v_00_u03c3_1156_, lean_object* v_inst_1157_, lean_object* v_pat_1158_, lean_object* v_inst_1159_, lean_object* v_n_1160_, lean_object* v_inst_1161_, lean_object* v_s_1162_){
_start:
{
lean_object* v_res_1163_; 
v_res_1163_ = l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(v_00_u03c1_1155_, v_00_u03c3_1156_, v_inst_1157_, v_pat_1158_, v_inst_1159_, v_n_1160_, v_inst_1161_, v_s_1162_);
lean_dec(v_inst_1159_);
lean_dec(v_pat_1158_);
return v_res_1163_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___redArg(lean_object* v_s_1164_, lean_object* v_inst_1165_){
_start:
{
lean_object* v___x_1166_; lean_object* v___x_1167_; lean_object* v___x_1168_; 
v___x_1166_ = lean_unsigned_to_nat(0u);
v___x_1167_ = lean_apply_1(v_inst_1165_, v_s_1164_);
v___x_1168_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1168_, 0, v___x_1166_);
lean_ctor_set(v___x_1168_, 1, v___x_1167_);
return v___x_1168_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive(lean_object* v_00_u03c1_1169_, lean_object* v_00_u03c3_1170_, lean_object* v_s_1171_, lean_object* v_pat_1172_, lean_object* v_inst_1173_){
_start:
{
lean_object* v___x_1174_; 
v___x_1174_ = l_String_Slice_splitInclusive___redArg(v_s_1171_, v_inst_1173_);
return v___x_1174_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___boxed(lean_object* v_00_u03c1_1175_, lean_object* v_00_u03c3_1176_, lean_object* v_s_1177_, lean_object* v_pat_1178_, lean_object* v_inst_1179_){
_start:
{
lean_object* v_res_1180_; 
v_res_1180_ = l_String_Slice_splitInclusive(v_00_u03c1_1175_, v_00_u03c3_1176_, v_s_1177_, v_pat_1178_, v_inst_1179_);
lean_dec(v_pat_1178_);
return v_res_1180_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___redArg(lean_object* v_s_1181_, lean_object* v_inst_1182_){
_start:
{
lean_object* v_skipPrefix_x3f_1183_; lean_object* v___x_1184_; 
v_skipPrefix_x3f_1183_ = lean_ctor_get(v_inst_1182_, 0);
lean_inc_ref(v_skipPrefix_x3f_1183_);
lean_dec_ref(v_inst_1182_);
v___x_1184_ = lean_apply_1(v_skipPrefix_x3f_1183_, v_s_1181_);
return v___x_1184_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f(lean_object* v_00_u03c1_1185_, lean_object* v_s_1186_, lean_object* v_pat_1187_, lean_object* v_inst_1188_){
_start:
{
lean_object* v_skipPrefix_x3f_1189_; lean_object* v___x_1190_; 
v_skipPrefix_x3f_1189_ = lean_ctor_get(v_inst_1188_, 0);
lean_inc_ref(v_skipPrefix_x3f_1189_);
lean_dec_ref(v_inst_1188_);
v___x_1190_ = lean_apply_1(v_skipPrefix_x3f_1189_, v_s_1186_);
return v___x_1190_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___boxed(lean_object* v_00_u03c1_1191_, lean_object* v_s_1192_, lean_object* v_pat_1193_, lean_object* v_inst_1194_){
_start:
{
lean_object* v_res_1195_; 
v_res_1195_ = l_String_Slice_skipPrefix_x3f(v_00_u03c1_1191_, v_s_1192_, v_pat_1193_, v_inst_1194_);
lean_dec(v_pat_1193_);
return v_res_1195_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg(lean_object* v_s_1196_, lean_object* v_pos_1197_, lean_object* v_inst_1198_){
_start:
{
lean_object* v_str_1199_; lean_object* v_startInclusive_1200_; lean_object* v_endExclusive_1201_; lean_object* v___x_1203_; uint8_t v_isShared_1204_; uint8_t v_isSharedCheck_1220_; 
v_str_1199_ = lean_ctor_get(v_s_1196_, 0);
v_startInclusive_1200_ = lean_ctor_get(v_s_1196_, 1);
v_endExclusive_1201_ = lean_ctor_get(v_s_1196_, 2);
v_isSharedCheck_1220_ = !lean_is_exclusive(v_s_1196_);
if (v_isSharedCheck_1220_ == 0)
{
v___x_1203_ = v_s_1196_;
v_isShared_1204_ = v_isSharedCheck_1220_;
goto v_resetjp_1202_;
}
else
{
lean_inc(v_endExclusive_1201_);
lean_inc(v_startInclusive_1200_);
lean_inc(v_str_1199_);
lean_dec(v_s_1196_);
v___x_1203_ = lean_box(0);
v_isShared_1204_ = v_isSharedCheck_1220_;
goto v_resetjp_1202_;
}
v_resetjp_1202_:
{
lean_object* v_skipPrefix_x3f_1205_; lean_object* v___x_1206_; lean_object* v___x_1208_; 
v_skipPrefix_x3f_1205_ = lean_ctor_get(v_inst_1198_, 0);
lean_inc_ref(v_skipPrefix_x3f_1205_);
lean_dec_ref(v_inst_1198_);
v___x_1206_ = lean_nat_add(v_startInclusive_1200_, v_pos_1197_);
lean_dec(v_startInclusive_1200_);
if (v_isShared_1204_ == 0)
{
lean_ctor_set(v___x_1203_, 1, v___x_1206_);
v___x_1208_ = v___x_1203_;
goto v_reusejp_1207_;
}
else
{
lean_object* v_reuseFailAlloc_1219_; 
v_reuseFailAlloc_1219_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1219_, 0, v_str_1199_);
lean_ctor_set(v_reuseFailAlloc_1219_, 1, v___x_1206_);
lean_ctor_set(v_reuseFailAlloc_1219_, 2, v_endExclusive_1201_);
v___x_1208_ = v_reuseFailAlloc_1219_;
goto v_reusejp_1207_;
}
v_reusejp_1207_:
{
lean_object* v___x_1209_; 
v___x_1209_ = lean_apply_1(v_skipPrefix_x3f_1205_, v___x_1208_);
if (lean_obj_tag(v___x_1209_) == 0)
{
return v___x_1209_;
}
else
{
lean_object* v_val_1210_; lean_object* v___x_1212_; uint8_t v_isShared_1213_; uint8_t v_isSharedCheck_1218_; 
v_val_1210_ = lean_ctor_get(v___x_1209_, 0);
v_isSharedCheck_1218_ = !lean_is_exclusive(v___x_1209_);
if (v_isSharedCheck_1218_ == 0)
{
v___x_1212_ = v___x_1209_;
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
else
{
lean_inc(v_val_1210_);
lean_dec(v___x_1209_);
v___x_1212_ = lean_box(0);
v_isShared_1213_ = v_isSharedCheck_1218_;
goto v_resetjp_1211_;
}
v_resetjp_1211_:
{
lean_object* v___x_1214_; lean_object* v___x_1216_; 
v___x_1214_ = lean_nat_add(v_pos_1197_, v_val_1210_);
lean_dec(v_val_1210_);
if (v_isShared_1213_ == 0)
{
lean_ctor_set(v___x_1212_, 0, v___x_1214_);
v___x_1216_ = v___x_1212_;
goto v_reusejp_1215_;
}
else
{
lean_object* v_reuseFailAlloc_1217_; 
v_reuseFailAlloc_1217_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1217_, 0, v___x_1214_);
v___x_1216_ = v_reuseFailAlloc_1217_;
goto v_reusejp_1215_;
}
v_reusejp_1215_:
{
return v___x_1216_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg___boxed(lean_object* v_s_1221_, lean_object* v_pos_1222_, lean_object* v_inst_1223_){
_start:
{
lean_object* v_res_1224_; 
v_res_1224_ = l_String_Slice_Pos_skip_x3f___redArg(v_s_1221_, v_pos_1222_, v_inst_1223_);
lean_dec(v_pos_1222_);
return v_res_1224_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f(lean_object* v_00_u03c1_1225_, lean_object* v_s_1226_, lean_object* v_pos_1227_, lean_object* v_pat_1228_, lean_object* v_inst_1229_){
_start:
{
lean_object* v_str_1230_; lean_object* v_startInclusive_1231_; lean_object* v_endExclusive_1232_; lean_object* v___x_1234_; uint8_t v_isShared_1235_; uint8_t v_isSharedCheck_1251_; 
v_str_1230_ = lean_ctor_get(v_s_1226_, 0);
v_startInclusive_1231_ = lean_ctor_get(v_s_1226_, 1);
v_endExclusive_1232_ = lean_ctor_get(v_s_1226_, 2);
v_isSharedCheck_1251_ = !lean_is_exclusive(v_s_1226_);
if (v_isSharedCheck_1251_ == 0)
{
v___x_1234_ = v_s_1226_;
v_isShared_1235_ = v_isSharedCheck_1251_;
goto v_resetjp_1233_;
}
else
{
lean_inc(v_endExclusive_1232_);
lean_inc(v_startInclusive_1231_);
lean_inc(v_str_1230_);
lean_dec(v_s_1226_);
v___x_1234_ = lean_box(0);
v_isShared_1235_ = v_isSharedCheck_1251_;
goto v_resetjp_1233_;
}
v_resetjp_1233_:
{
lean_object* v_skipPrefix_x3f_1236_; lean_object* v___x_1237_; lean_object* v___x_1239_; 
v_skipPrefix_x3f_1236_ = lean_ctor_get(v_inst_1229_, 0);
lean_inc_ref(v_skipPrefix_x3f_1236_);
lean_dec_ref(v_inst_1229_);
v___x_1237_ = lean_nat_add(v_startInclusive_1231_, v_pos_1227_);
lean_dec(v_startInclusive_1231_);
if (v_isShared_1235_ == 0)
{
lean_ctor_set(v___x_1234_, 1, v___x_1237_);
v___x_1239_ = v___x_1234_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1250_; 
v_reuseFailAlloc_1250_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1250_, 0, v_str_1230_);
lean_ctor_set(v_reuseFailAlloc_1250_, 1, v___x_1237_);
lean_ctor_set(v_reuseFailAlloc_1250_, 2, v_endExclusive_1232_);
v___x_1239_ = v_reuseFailAlloc_1250_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
lean_object* v___x_1240_; 
v___x_1240_ = lean_apply_1(v_skipPrefix_x3f_1236_, v___x_1239_);
if (lean_obj_tag(v___x_1240_) == 0)
{
return v___x_1240_;
}
else
{
lean_object* v_val_1241_; lean_object* v___x_1243_; uint8_t v_isShared_1244_; uint8_t v_isSharedCheck_1249_; 
v_val_1241_ = lean_ctor_get(v___x_1240_, 0);
v_isSharedCheck_1249_ = !lean_is_exclusive(v___x_1240_);
if (v_isSharedCheck_1249_ == 0)
{
v___x_1243_ = v___x_1240_;
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
else
{
lean_inc(v_val_1241_);
lean_dec(v___x_1240_);
v___x_1243_ = lean_box(0);
v_isShared_1244_ = v_isSharedCheck_1249_;
goto v_resetjp_1242_;
}
v_resetjp_1242_:
{
lean_object* v___x_1245_; lean_object* v___x_1247_; 
v___x_1245_ = lean_nat_add(v_pos_1227_, v_val_1241_);
lean_dec(v_val_1241_);
if (v_isShared_1244_ == 0)
{
lean_ctor_set(v___x_1243_, 0, v___x_1245_);
v___x_1247_ = v___x_1243_;
goto v_reusejp_1246_;
}
else
{
lean_object* v_reuseFailAlloc_1248_; 
v_reuseFailAlloc_1248_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1248_, 0, v___x_1245_);
v___x_1247_ = v_reuseFailAlloc_1248_;
goto v_reusejp_1246_;
}
v_reusejp_1246_:
{
return v___x_1247_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_1252_, lean_object* v_s_1253_, lean_object* v_pos_1254_, lean_object* v_pat_1255_, lean_object* v_inst_1256_){
_start:
{
lean_object* v_res_1257_; 
v_res_1257_ = l_String_Slice_Pos_skip_x3f(v_00_u03c1_1252_, v_s_1253_, v_pos_1254_, v_pat_1255_, v_inst_1256_);
lean_dec(v_pat_1255_);
lean_dec(v_pos_1254_);
return v_res_1257_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___redArg(lean_object* v_s_1258_, lean_object* v_inst_1259_){
_start:
{
lean_object* v_skipPrefix_x3f_1260_; lean_object* v___x_1261_; 
v_skipPrefix_x3f_1260_ = lean_ctor_get(v_inst_1259_, 0);
lean_inc_ref(v_skipPrefix_x3f_1260_);
lean_dec_ref(v_inst_1259_);
lean_inc_ref(v_s_1258_);
v___x_1261_ = lean_apply_1(v_skipPrefix_x3f_1260_, v_s_1258_);
if (lean_obj_tag(v___x_1261_) == 0)
{
lean_object* v___x_1262_; 
lean_dec_ref(v_s_1258_);
v___x_1262_ = lean_box(0);
return v___x_1262_;
}
else
{
lean_object* v_val_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1281_; 
v_val_1263_ = lean_ctor_get(v___x_1261_, 0);
v_isSharedCheck_1281_ = !lean_is_exclusive(v___x_1261_);
if (v_isSharedCheck_1281_ == 0)
{
v___x_1265_ = v___x_1261_;
v_isShared_1266_ = v_isSharedCheck_1281_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_val_1263_);
lean_dec(v___x_1261_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1281_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v_str_1267_; lean_object* v_startInclusive_1268_; lean_object* v_endExclusive_1269_; lean_object* v___x_1271_; uint8_t v_isShared_1272_; uint8_t v_isSharedCheck_1280_; 
v_str_1267_ = lean_ctor_get(v_s_1258_, 0);
v_startInclusive_1268_ = lean_ctor_get(v_s_1258_, 1);
v_endExclusive_1269_ = lean_ctor_get(v_s_1258_, 2);
v_isSharedCheck_1280_ = !lean_is_exclusive(v_s_1258_);
if (v_isSharedCheck_1280_ == 0)
{
v___x_1271_ = v_s_1258_;
v_isShared_1272_ = v_isSharedCheck_1280_;
goto v_resetjp_1270_;
}
else
{
lean_inc(v_endExclusive_1269_);
lean_inc(v_startInclusive_1268_);
lean_inc(v_str_1267_);
lean_dec(v_s_1258_);
v___x_1271_ = lean_box(0);
v_isShared_1272_ = v_isSharedCheck_1280_;
goto v_resetjp_1270_;
}
v_resetjp_1270_:
{
lean_object* v___x_1273_; lean_object* v___x_1275_; 
v___x_1273_ = lean_nat_add(v_startInclusive_1268_, v_val_1263_);
lean_dec(v_val_1263_);
lean_dec(v_startInclusive_1268_);
if (v_isShared_1272_ == 0)
{
lean_ctor_set(v___x_1271_, 1, v___x_1273_);
v___x_1275_ = v___x_1271_;
goto v_reusejp_1274_;
}
else
{
lean_object* v_reuseFailAlloc_1279_; 
v_reuseFailAlloc_1279_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1279_, 0, v_str_1267_);
lean_ctor_set(v_reuseFailAlloc_1279_, 1, v___x_1273_);
lean_ctor_set(v_reuseFailAlloc_1279_, 2, v_endExclusive_1269_);
v___x_1275_ = v_reuseFailAlloc_1279_;
goto v_reusejp_1274_;
}
v_reusejp_1274_:
{
lean_object* v___x_1277_; 
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1275_);
v___x_1277_ = v___x_1265_;
goto v_reusejp_1276_;
}
else
{
lean_object* v_reuseFailAlloc_1278_; 
v_reuseFailAlloc_1278_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1278_, 0, v___x_1275_);
v___x_1277_ = v_reuseFailAlloc_1278_;
goto v_reusejp_1276_;
}
v_reusejp_1276_:
{
return v___x_1277_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f(lean_object* v_00_u03c1_1282_, lean_object* v_s_1283_, lean_object* v_pat_1284_, lean_object* v_inst_1285_){
_start:
{
lean_object* v_skipPrefix_x3f_1286_; lean_object* v___x_1287_; 
v_skipPrefix_x3f_1286_ = lean_ctor_get(v_inst_1285_, 0);
lean_inc_ref(v_skipPrefix_x3f_1286_);
lean_dec_ref(v_inst_1285_);
lean_inc_ref(v_s_1283_);
v___x_1287_ = lean_apply_1(v_skipPrefix_x3f_1286_, v_s_1283_);
if (lean_obj_tag(v___x_1287_) == 0)
{
lean_object* v___x_1288_; 
lean_dec_ref(v_s_1283_);
v___x_1288_ = lean_box(0);
return v___x_1288_;
}
else
{
lean_object* v_val_1289_; lean_object* v___x_1291_; uint8_t v_isShared_1292_; uint8_t v_isSharedCheck_1307_; 
v_val_1289_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1307_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1307_ == 0)
{
v___x_1291_ = v___x_1287_;
v_isShared_1292_ = v_isSharedCheck_1307_;
goto v_resetjp_1290_;
}
else
{
lean_inc(v_val_1289_);
lean_dec(v___x_1287_);
v___x_1291_ = lean_box(0);
v_isShared_1292_ = v_isSharedCheck_1307_;
goto v_resetjp_1290_;
}
v_resetjp_1290_:
{
lean_object* v_str_1293_; lean_object* v_startInclusive_1294_; lean_object* v_endExclusive_1295_; lean_object* v___x_1297_; uint8_t v_isShared_1298_; uint8_t v_isSharedCheck_1306_; 
v_str_1293_ = lean_ctor_get(v_s_1283_, 0);
v_startInclusive_1294_ = lean_ctor_get(v_s_1283_, 1);
v_endExclusive_1295_ = lean_ctor_get(v_s_1283_, 2);
v_isSharedCheck_1306_ = !lean_is_exclusive(v_s_1283_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1297_ = v_s_1283_;
v_isShared_1298_ = v_isSharedCheck_1306_;
goto v_resetjp_1296_;
}
else
{
lean_inc(v_endExclusive_1295_);
lean_inc(v_startInclusive_1294_);
lean_inc(v_str_1293_);
lean_dec(v_s_1283_);
v___x_1297_ = lean_box(0);
v_isShared_1298_ = v_isSharedCheck_1306_;
goto v_resetjp_1296_;
}
v_resetjp_1296_:
{
lean_object* v___x_1299_; lean_object* v___x_1301_; 
v___x_1299_ = lean_nat_add(v_startInclusive_1294_, v_val_1289_);
lean_dec(v_val_1289_);
lean_dec(v_startInclusive_1294_);
if (v_isShared_1298_ == 0)
{
lean_ctor_set(v___x_1297_, 1, v___x_1299_);
v___x_1301_ = v___x_1297_;
goto v_reusejp_1300_;
}
else
{
lean_object* v_reuseFailAlloc_1305_; 
v_reuseFailAlloc_1305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1305_, 0, v_str_1293_);
lean_ctor_set(v_reuseFailAlloc_1305_, 1, v___x_1299_);
lean_ctor_set(v_reuseFailAlloc_1305_, 2, v_endExclusive_1295_);
v___x_1301_ = v_reuseFailAlloc_1305_;
goto v_reusejp_1300_;
}
v_reusejp_1300_:
{
lean_object* v___x_1303_; 
if (v_isShared_1292_ == 0)
{
lean_ctor_set(v___x_1291_, 0, v___x_1301_);
v___x_1303_ = v___x_1291_;
goto v_reusejp_1302_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v___x_1301_);
v___x_1303_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1302_;
}
v_reusejp_1302_:
{
return v___x_1303_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_1308_, lean_object* v_s_1309_, lean_object* v_pat_1310_, lean_object* v_inst_1311_){
_start:
{
lean_object* v_res_1312_; 
v_res_1312_ = l_String_Slice_dropPrefix_x3f(v_00_u03c1_1308_, v_s_1309_, v_pat_1310_, v_inst_1311_);
lean_dec(v_pat_1310_);
return v_res_1312_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___redArg(lean_object* v_s_1313_, lean_object* v_inst_1314_){
_start:
{
lean_object* v_skipPrefix_x3f_1315_; lean_object* v___x_1316_; 
v_skipPrefix_x3f_1315_ = lean_ctor_get(v_inst_1314_, 0);
lean_inc_ref(v_skipPrefix_x3f_1315_);
lean_dec_ref(v_inst_1314_);
lean_inc_ref(v_s_1313_);
v___x_1316_ = lean_apply_1(v_skipPrefix_x3f_1315_, v_s_1313_);
if (lean_obj_tag(v___x_1316_) == 0)
{
return v_s_1313_;
}
else
{
lean_object* v_val_1317_; lean_object* v_str_1318_; lean_object* v_startInclusive_1319_; lean_object* v_endExclusive_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1328_; 
v_val_1317_ = lean_ctor_get(v___x_1316_, 0);
lean_inc(v_val_1317_);
lean_dec_ref_known(v___x_1316_, 1);
v_str_1318_ = lean_ctor_get(v_s_1313_, 0);
v_startInclusive_1319_ = lean_ctor_get(v_s_1313_, 1);
v_endExclusive_1320_ = lean_ctor_get(v_s_1313_, 2);
v_isSharedCheck_1328_ = !lean_is_exclusive(v_s_1313_);
if (v_isSharedCheck_1328_ == 0)
{
v___x_1322_ = v_s_1313_;
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_endExclusive_1320_);
lean_inc(v_startInclusive_1319_);
lean_inc(v_str_1318_);
lean_dec(v_s_1313_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1328_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = lean_nat_add(v_startInclusive_1319_, v_val_1317_);
lean_dec(v_val_1317_);
lean_dec(v_startInclusive_1319_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v___x_1324_);
v___x_1326_ = v___x_1322_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1327_; 
v_reuseFailAlloc_1327_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1327_, 0, v_str_1318_);
lean_ctor_set(v_reuseFailAlloc_1327_, 1, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1327_, 2, v_endExclusive_1320_);
v___x_1326_ = v_reuseFailAlloc_1327_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
return v___x_1326_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix(lean_object* v_00_u03c1_1329_, lean_object* v_s_1330_, lean_object* v_pat_1331_, lean_object* v_inst_1332_){
_start:
{
lean_object* v___x_1333_; 
v___x_1333_ = l_String_Slice_dropPrefix___redArg(v_s_1330_, v_inst_1332_);
return v___x_1333_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___boxed(lean_object* v_00_u03c1_1334_, lean_object* v_s_1335_, lean_object* v_pat_1336_, lean_object* v_inst_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_String_Slice_dropPrefix(v_00_u03c1_1334_, v_s_1335_, v_pat_1336_, v_inst_1337_);
lean_dec(v_pat_1336_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__0(lean_object* v_x_1339_, lean_object* v_x_1340_, lean_object* v_f_1341_, lean_object* v_c_1342_){
_start:
{
lean_object* v___x_1343_; 
v___x_1343_ = lean_apply_1(v_f_1341_, v_c_1342_);
return v___x_1343_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1(lean_object* v_s_1344_, lean_object* v_inst_1345_, lean_object* v_replacement_1346_, lean_object* v_x1_1347_, lean_object* v_x2_1348_, lean_object* v_x3_1349_){
_start:
{
if (lean_obj_tag(v_x1_1347_) == 0)
{
lean_object* v_startPos_1350_; lean_object* v_endPos_1351_; lean_object* v___x_1352_; lean_object* v_str_1353_; lean_object* v_startInclusive_1354_; lean_object* v_endExclusive_1355_; lean_object* v___x_1356_; lean_object* v___x_1357_; lean_object* v___x_1358_; 
lean_dec(v_replacement_1346_);
lean_dec_ref(v_inst_1345_);
v_startPos_1350_ = lean_ctor_get(v_x1_1347_, 0);
v_endPos_1351_ = lean_ctor_get(v_x1_1347_, 1);
v___x_1352_ = l_String_Slice_slice_x21(v_s_1344_, v_startPos_1350_, v_endPos_1351_);
v_str_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc_ref(v_str_1353_);
v_startInclusive_1354_ = lean_ctor_get(v___x_1352_, 1);
lean_inc(v_startInclusive_1354_);
v_endExclusive_1355_ = lean_ctor_get(v___x_1352_, 2);
lean_inc(v_endExclusive_1355_);
lean_dec_ref(v___x_1352_);
v___x_1356_ = lean_string_utf8_extract_fast(v_str_1353_, v_startInclusive_1354_, v_endExclusive_1355_);
lean_dec(v_endExclusive_1355_);
lean_dec(v_startInclusive_1354_);
lean_dec_ref(v_str_1353_);
v___x_1357_ = lean_string_append(v_x3_1349_, v___x_1356_);
lean_dec_ref(v___x_1356_);
v___x_1358_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1358_, 0, v___x_1357_);
return v___x_1358_;
}
else
{
lean_object* v___x_1359_; lean_object* v_str_1360_; lean_object* v_startInclusive_1361_; lean_object* v_endExclusive_1362_; lean_object* v___x_1363_; lean_object* v___x_1364_; lean_object* v___x_1365_; 
lean_dec_ref(v_s_1344_);
v___x_1359_ = lean_apply_1(v_inst_1345_, v_replacement_1346_);
v_str_1360_ = lean_ctor_get(v___x_1359_, 0);
lean_inc_ref(v_str_1360_);
v_startInclusive_1361_ = lean_ctor_get(v___x_1359_, 1);
lean_inc(v_startInclusive_1361_);
v_endExclusive_1362_ = lean_ctor_get(v___x_1359_, 2);
lean_inc(v_endExclusive_1362_);
lean_dec_ref(v___x_1359_);
v___x_1363_ = lean_string_utf8_extract_fast(v_str_1360_, v_startInclusive_1361_, v_endExclusive_1362_);
lean_dec(v_endExclusive_1362_);
lean_dec(v_startInclusive_1361_);
lean_dec_ref(v_str_1360_);
v___x_1364_ = lean_string_append(v_x3_1349_, v___x_1363_);
lean_dec_ref(v___x_1363_);
v___x_1365_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1365_, 0, v___x_1364_);
return v___x_1365_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1___boxed(lean_object* v_s_1366_, lean_object* v_inst_1367_, lean_object* v_replacement_1368_, lean_object* v_x1_1369_, lean_object* v_x2_1370_, lean_object* v_x3_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_String_Slice_replace___redArg___lam__1(v_s_1366_, v_inst_1367_, v_replacement_1368_, v_x1_1369_, v_x2_1370_, v_x3_1371_);
lean_dec_ref(v_x1_1369_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg(lean_object* v_inst_1375_, lean_object* v_inst_1376_, lean_object* v_s_1377_, lean_object* v_inst_1378_, lean_object* v_replacement_1379_){
_start:
{
lean_object* v___f_1380_; lean_object* v___f_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; lean_object* v___x_1384_; 
v___f_1380_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1377_, 2);
v___f_1381_ = lean_alloc_closure((void*)(l_String_Slice_replace___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1381_, 0, v_s_1377_);
lean_closure_set(v___f_1381_, 1, v_inst_1376_);
lean_closure_set(v___f_1381_, 2, v_replacement_1379_);
v___x_1382_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
v___x_1383_ = lean_apply_1(v_inst_1378_, v_s_1377_);
v___x_1384_ = lean_apply_7(v_inst_1375_, v_s_1377_, v___f_1380_, lean_box(0), lean_box(0), v___x_1383_, v___x_1382_, v___f_1381_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace(lean_object* v_00_u03c1_1385_, lean_object* v_00_u03c3_1386_, lean_object* v_inst_1387_, lean_object* v_inst_1388_, lean_object* v_00_u03b1_1389_, lean_object* v_inst_1390_, lean_object* v_s_1391_, lean_object* v_pattern_1392_, lean_object* v_inst_1393_, lean_object* v_replacement_1394_){
_start:
{
lean_object* v___x_1395_; 
v___x_1395_ = l_String_Slice_replace___redArg(v_inst_1388_, v_inst_1390_, v_s_1391_, v_inst_1393_, v_replacement_1394_);
return v___x_1395_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___boxed(lean_object* v_00_u03c1_1396_, lean_object* v_00_u03c3_1397_, lean_object* v_inst_1398_, lean_object* v_inst_1399_, lean_object* v_00_u03b1_1400_, lean_object* v_inst_1401_, lean_object* v_s_1402_, lean_object* v_pattern_1403_, lean_object* v_inst_1404_, lean_object* v_replacement_1405_){
_start:
{
lean_object* v_res_1406_; 
v_res_1406_ = l_String_Slice_replace(v_00_u03c1_1396_, v_00_u03c3_1397_, v_inst_1398_, v_inst_1399_, v_00_u03b1_1400_, v_inst_1401_, v_s_1402_, v_pattern_1403_, v_inst_1404_, v_replacement_1405_);
lean_dec(v_pattern_1403_);
lean_dec(v_inst_1398_);
return v_res_1406_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object* v_s_1407_, lean_object* v_pos_1408_, lean_object* v_inst_1409_){
_start:
{
lean_object* v_str_1410_; lean_object* v_startInclusive_1411_; lean_object* v_endExclusive_1412_; lean_object* v_skipPrefix_x3f_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
v_str_1410_ = lean_ctor_get(v_s_1407_, 0);
v_startInclusive_1411_ = lean_ctor_get(v_s_1407_, 1);
v_endExclusive_1412_ = lean_ctor_get(v_s_1407_, 2);
v_skipPrefix_x3f_1413_ = lean_ctor_get(v_inst_1409_, 0);
v___x_1414_ = lean_nat_add(v_startInclusive_1411_, v_pos_1408_);
lean_inc(v_endExclusive_1412_);
lean_inc_ref(v_str_1410_);
v___x_1415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1415_, 0, v_str_1410_);
lean_ctor_set(v___x_1415_, 1, v___x_1414_);
lean_ctor_set(v___x_1415_, 2, v_endExclusive_1412_);
lean_inc_ref(v_skipPrefix_x3f_1413_);
v___x_1416_ = lean_apply_1(v_skipPrefix_x3f_1413_, v___x_1415_);
if (lean_obj_tag(v___x_1416_) == 0)
{
lean_dec_ref(v_inst_1409_);
return v_pos_1408_;
}
else
{
lean_object* v_val_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; lean_object* v___x_1420_; uint8_t v___x_1421_; 
v_val_1417_ = lean_ctor_get(v___x_1416_, 0);
lean_inc(v_val_1417_);
lean_dec_ref_known(v___x_1416_, 1);
v___x_1418_ = lean_nat_add(v_pos_1408_, v_val_1417_);
lean_dec(v_val_1417_);
v___x_1419_ = lean_unsigned_to_nat(1u);
v___x_1420_ = lean_nat_add(v_pos_1408_, v___x_1419_);
v___x_1421_ = lean_nat_dec_le(v___x_1420_, v___x_1418_);
lean_dec(v___x_1420_);
if (v___x_1421_ == 0)
{
lean_dec(v___x_1418_);
lean_dec_ref(v_inst_1409_);
return v_pos_1408_;
}
else
{
lean_dec(v_pos_1408_);
v_pos_1408_ = v___x_1418_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg___boxed(lean_object* v_s_1423_, lean_object* v_pos_1424_, lean_object* v_inst_1425_){
_start:
{
lean_object* v_res_1426_; 
v_res_1426_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1423_, v_pos_1424_, v_inst_1425_);
lean_dec_ref(v_s_1423_);
return v_res_1426_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile(lean_object* v_00_u03c1_1427_, lean_object* v_s_1428_, lean_object* v_pos_1429_, lean_object* v_pat_1430_, lean_object* v_inst_1431_){
_start:
{
lean_object* v___x_1432_; 
v___x_1432_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1428_, v_pos_1429_, v_inst_1431_);
return v___x_1432_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___boxed(lean_object* v_00_u03c1_1433_, lean_object* v_s_1434_, lean_object* v_pos_1435_, lean_object* v_pat_1436_, lean_object* v_inst_1437_){
_start:
{
lean_object* v_res_1438_; 
v_res_1438_ = l_String_Slice_Pos_skipWhile(v_00_u03c1_1433_, v_s_1434_, v_pos_1435_, v_pat_1436_, v_inst_1437_);
lean_dec(v_pat_1436_);
lean_dec_ref(v_s_1434_);
return v_res_1438_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object* v_x_1439_, lean_object* v_h__1_1440_, lean_object* v_h__2_1441_){
_start:
{
if (lean_obj_tag(v_x_1439_) == 0)
{
lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_dec(v_h__1_1440_);
v___x_1442_ = lean_box(0);
v___x_1443_ = lean_apply_1(v_h__2_1441_, v___x_1442_);
return v___x_1443_;
}
else
{
lean_object* v_val_1444_; lean_object* v___x_1445_; 
lean_dec(v_h__2_1441_);
v_val_1444_ = lean_ctor_get(v_x_1439_, 0);
lean_inc(v_val_1444_);
lean_dec_ref_known(v_x_1439_, 1);
v___x_1445_ = lean_apply_1(v_h__1_1440_, v_val_1444_);
return v___x_1445_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object* v_s_1446_, lean_object* v_motive_1447_, lean_object* v_x_1448_, lean_object* v_h__1_1449_, lean_object* v_h__2_1450_){
_start:
{
if (lean_obj_tag(v_x_1448_) == 0)
{
lean_object* v___x_1451_; lean_object* v___x_1452_; 
lean_dec(v_h__1_1449_);
v___x_1451_ = lean_box(0);
v___x_1452_ = lean_apply_1(v_h__2_1450_, v___x_1451_);
return v___x_1452_;
}
else
{
lean_object* v_val_1453_; lean_object* v___x_1454_; 
lean_dec(v_h__2_1450_);
v_val_1453_ = lean_ctor_get(v_x_1448_, 0);
lean_inc(v_val_1453_);
lean_dec_ref_known(v_x_1448_, 1);
v___x_1454_ = lean_apply_1(v_h__1_1449_, v_val_1453_);
return v___x_1454_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object* v_s_1455_, lean_object* v_motive_1456_, lean_object* v_x_1457_, lean_object* v_h__1_1458_, lean_object* v_h__2_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_1455_, v_motive_1456_, v_x_1457_, v_h__1_1458_, v_h__2_1459_);
lean_dec_ref(v_s_1455_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg(lean_object* v_s_1461_, lean_object* v_inst_1462_){
_start:
{
lean_object* v___x_1463_; lean_object* v___x_1464_; 
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1461_, v___x_1463_, v_inst_1462_);
return v___x_1464_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg___boxed(lean_object* v_s_1465_, lean_object* v_inst_1466_){
_start:
{
lean_object* v_res_1467_; 
v_res_1467_ = l_String_Slice_skipPrefixWhile___redArg(v_s_1465_, v_inst_1466_);
lean_dec_ref(v_s_1465_);
return v_res_1467_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile(lean_object* v_00_u03c1_1468_, lean_object* v_s_1469_, lean_object* v_pat_1470_, lean_object* v_inst_1471_){
_start:
{
lean_object* v___x_1472_; lean_object* v___x_1473_; 
v___x_1472_ = lean_unsigned_to_nat(0u);
v___x_1473_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1469_, v___x_1472_, v_inst_1471_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___boxed(lean_object* v_00_u03c1_1474_, lean_object* v_s_1475_, lean_object* v_pat_1476_, lean_object* v_inst_1477_){
_start:
{
lean_object* v_res_1478_; 
v_res_1478_ = l_String_Slice_skipPrefixWhile(v_00_u03c1_1474_, v_s_1475_, v_pat_1476_, v_inst_1477_);
lean_dec(v_pat_1476_);
lean_dec_ref(v_s_1475_);
return v_res_1478_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg(lean_object* v_s_1479_, lean_object* v_inst_1480_){
_start:
{
lean_object* v_str_1481_; lean_object* v_startInclusive_1482_; lean_object* v_endExclusive_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; lean_object* v___x_1487_; uint8_t v_isShared_1488_; uint8_t v_isSharedCheck_1493_; 
v_str_1481_ = lean_ctor_get(v_s_1479_, 0);
lean_inc_ref(v_str_1481_);
v_startInclusive_1482_ = lean_ctor_get(v_s_1479_, 1);
lean_inc(v_startInclusive_1482_);
v_endExclusive_1483_ = lean_ctor_get(v_s_1479_, 2);
lean_inc(v_endExclusive_1483_);
v___x_1484_ = lean_unsigned_to_nat(0u);
v___x_1485_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1479_, v___x_1484_, v_inst_1480_);
v_isSharedCheck_1493_ = !lean_is_exclusive(v_s_1479_);
if (v_isSharedCheck_1493_ == 0)
{
lean_object* v_unused_1494_; lean_object* v_unused_1495_; lean_object* v_unused_1496_; 
v_unused_1494_ = lean_ctor_get(v_s_1479_, 2);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_s_1479_, 1);
lean_dec(v_unused_1495_);
v_unused_1496_ = lean_ctor_get(v_s_1479_, 0);
lean_dec(v_unused_1496_);
v___x_1487_ = v_s_1479_;
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
else
{
lean_dec(v_s_1479_);
v___x_1487_ = lean_box(0);
v_isShared_1488_ = v_isSharedCheck_1493_;
goto v_resetjp_1486_;
}
v_resetjp_1486_:
{
lean_object* v___x_1489_; lean_object* v___x_1491_; 
v___x_1489_ = lean_nat_add(v_startInclusive_1482_, v___x_1485_);
lean_dec(v___x_1485_);
lean_dec(v_startInclusive_1482_);
if (v_isShared_1488_ == 0)
{
lean_ctor_set(v___x_1487_, 1, v___x_1489_);
v___x_1491_ = v___x_1487_;
goto v_reusejp_1490_;
}
else
{
lean_object* v_reuseFailAlloc_1492_; 
v_reuseFailAlloc_1492_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1492_, 0, v_str_1481_);
lean_ctor_set(v_reuseFailAlloc_1492_, 1, v___x_1489_);
lean_ctor_set(v_reuseFailAlloc_1492_, 2, v_endExclusive_1483_);
v___x_1491_ = v_reuseFailAlloc_1492_;
goto v_reusejp_1490_;
}
v_reusejp_1490_:
{
return v___x_1491_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile(lean_object* v_00_u03c1_1497_, lean_object* v_s_1498_, lean_object* v_pat_1499_, lean_object* v_inst_1500_){
_start:
{
lean_object* v_str_1501_; lean_object* v_startInclusive_1502_; lean_object* v_endExclusive_1503_; lean_object* v___x_1504_; lean_object* v___x_1505_; lean_object* v___x_1507_; uint8_t v_isShared_1508_; uint8_t v_isSharedCheck_1513_; 
v_str_1501_ = lean_ctor_get(v_s_1498_, 0);
lean_inc_ref(v_str_1501_);
v_startInclusive_1502_ = lean_ctor_get(v_s_1498_, 1);
lean_inc(v_startInclusive_1502_);
v_endExclusive_1503_ = lean_ctor_get(v_s_1498_, 2);
lean_inc(v_endExclusive_1503_);
v___x_1504_ = lean_unsigned_to_nat(0u);
v___x_1505_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1498_, v___x_1504_, v_inst_1500_);
v_isSharedCheck_1513_ = !lean_is_exclusive(v_s_1498_);
if (v_isSharedCheck_1513_ == 0)
{
lean_object* v_unused_1514_; lean_object* v_unused_1515_; lean_object* v_unused_1516_; 
v_unused_1514_ = lean_ctor_get(v_s_1498_, 2);
lean_dec(v_unused_1514_);
v_unused_1515_ = lean_ctor_get(v_s_1498_, 1);
lean_dec(v_unused_1515_);
v_unused_1516_ = lean_ctor_get(v_s_1498_, 0);
lean_dec(v_unused_1516_);
v___x_1507_ = v_s_1498_;
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
else
{
lean_dec(v_s_1498_);
v___x_1507_ = lean_box(0);
v_isShared_1508_ = v_isSharedCheck_1513_;
goto v_resetjp_1506_;
}
v_resetjp_1506_:
{
lean_object* v___x_1509_; lean_object* v___x_1511_; 
v___x_1509_ = lean_nat_add(v_startInclusive_1502_, v___x_1505_);
lean_dec(v___x_1505_);
lean_dec(v_startInclusive_1502_);
if (v_isShared_1508_ == 0)
{
lean_ctor_set(v___x_1507_, 1, v___x_1509_);
v___x_1511_ = v___x_1507_;
goto v_reusejp_1510_;
}
else
{
lean_object* v_reuseFailAlloc_1512_; 
v_reuseFailAlloc_1512_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1512_, 0, v_str_1501_);
lean_ctor_set(v_reuseFailAlloc_1512_, 1, v___x_1509_);
lean_ctor_set(v_reuseFailAlloc_1512_, 2, v_endExclusive_1503_);
v___x_1511_ = v_reuseFailAlloc_1512_;
goto v_reusejp_1510_;
}
v_reusejp_1510_:
{
return v___x_1511_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___boxed(lean_object* v_00_u03c1_1517_, lean_object* v_s_1518_, lean_object* v_pat_1519_, lean_object* v_inst_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_String_Slice_dropWhile(v_00_u03c1_1517_, v_s_1518_, v_pat_1519_, v_inst_1520_);
lean_dec(v_pat_1519_);
return v_res_1521_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiStart___closed__1(void){
_start:
{
lean_object* v___x_1523_; lean_object* v___x_1524_; 
v___x_1523_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_1524_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1523_);
return v___x_1524_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart(lean_object* v_s_1525_){
_start:
{
lean_object* v___x_1526_; lean_object* v_str_1527_; lean_object* v_startInclusive_1528_; lean_object* v_endExclusive_1529_; lean_object* v___x_1530_; lean_object* v___x_1531_; lean_object* v___x_1533_; uint8_t v_isShared_1534_; uint8_t v_isSharedCheck_1539_; 
v___x_1526_ = lean_obj_once(&l_String_Slice_trimAsciiStart___closed__1, &l_String_Slice_trimAsciiStart___closed__1_once, _init_l_String_Slice_trimAsciiStart___closed__1);
v_str_1527_ = lean_ctor_get(v_s_1525_, 0);
lean_inc_ref(v_str_1527_);
v_startInclusive_1528_ = lean_ctor_get(v_s_1525_, 1);
lean_inc(v_startInclusive_1528_);
v_endExclusive_1529_ = lean_ctor_get(v_s_1525_, 2);
lean_inc(v_endExclusive_1529_);
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1525_, v___x_1530_, v___x_1526_);
v_isSharedCheck_1539_ = !lean_is_exclusive(v_s_1525_);
if (v_isSharedCheck_1539_ == 0)
{
lean_object* v_unused_1540_; lean_object* v_unused_1541_; lean_object* v_unused_1542_; 
v_unused_1540_ = lean_ctor_get(v_s_1525_, 2);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v_s_1525_, 1);
lean_dec(v_unused_1541_);
v_unused_1542_ = lean_ctor_get(v_s_1525_, 0);
lean_dec(v_unused_1542_);
v___x_1533_ = v_s_1525_;
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
else
{
lean_dec(v_s_1525_);
v___x_1533_ = lean_box(0);
v_isShared_1534_ = v_isSharedCheck_1539_;
goto v_resetjp_1532_;
}
v_resetjp_1532_:
{
lean_object* v___x_1535_; lean_object* v___x_1537_; 
v___x_1535_ = lean_nat_add(v_startInclusive_1528_, v___x_1531_);
lean_dec(v___x_1531_);
lean_dec(v_startInclusive_1528_);
if (v_isShared_1534_ == 0)
{
lean_ctor_set(v___x_1533_, 1, v___x_1535_);
v___x_1537_ = v___x_1533_;
goto v_reusejp_1536_;
}
else
{
lean_object* v_reuseFailAlloc_1538_; 
v_reuseFailAlloc_1538_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1538_, 0, v_str_1527_);
lean_ctor_set(v_reuseFailAlloc_1538_, 1, v___x_1535_);
lean_ctor_set(v_reuseFailAlloc_1538_, 2, v_endExclusive_1529_);
v___x_1537_ = v_reuseFailAlloc_1538_;
goto v_reusejp_1536_;
}
v_reusejp_1536_:
{
return v___x_1537_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___redArg(lean_object* v_s_1543_, lean_object* v_inst_1544_){
_start:
{
lean_object* v_str_1545_; lean_object* v_startInclusive_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1556_; 
v_str_1545_ = lean_ctor_get(v_s_1543_, 0);
lean_inc_ref(v_str_1545_);
v_startInclusive_1546_ = lean_ctor_get(v_s_1543_, 1);
lean_inc(v_startInclusive_1546_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1543_, v___x_1547_, v_inst_1544_);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_s_1543_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; lean_object* v_unused_1558_; lean_object* v_unused_1559_; 
v_unused_1557_ = lean_ctor_get(v_s_1543_, 2);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v_s_1543_, 1);
lean_dec(v_unused_1558_);
v_unused_1559_ = lean_ctor_get(v_s_1543_, 0);
lean_dec(v_unused_1559_);
v___x_1550_ = v_s_1543_;
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v_s_1543_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = lean_nat_add(v_startInclusive_1546_, v___x_1548_);
lean_dec(v___x_1548_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 2, v___x_1552_);
v___x_1554_ = v___x_1550_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_str_1545_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v_startInclusive_1546_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v___x_1552_);
v___x_1554_ = v_reuseFailAlloc_1555_;
goto v_reusejp_1553_;
}
v_reusejp_1553_:
{
return v___x_1554_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile(lean_object* v_00_u03c1_1560_, lean_object* v_s_1561_, lean_object* v_pat_1562_, lean_object* v_inst_1563_){
_start:
{
lean_object* v_str_1564_; lean_object* v_startInclusive_1565_; lean_object* v___x_1566_; lean_object* v___x_1567_; lean_object* v___x_1569_; uint8_t v_isShared_1570_; uint8_t v_isSharedCheck_1575_; 
v_str_1564_ = lean_ctor_get(v_s_1561_, 0);
lean_inc_ref(v_str_1564_);
v_startInclusive_1565_ = lean_ctor_get(v_s_1561_, 1);
lean_inc(v_startInclusive_1565_);
v___x_1566_ = lean_unsigned_to_nat(0u);
v___x_1567_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1561_, v___x_1566_, v_inst_1563_);
v_isSharedCheck_1575_ = !lean_is_exclusive(v_s_1561_);
if (v_isSharedCheck_1575_ == 0)
{
lean_object* v_unused_1576_; lean_object* v_unused_1577_; lean_object* v_unused_1578_; 
v_unused_1576_ = lean_ctor_get(v_s_1561_, 2);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_s_1561_, 1);
lean_dec(v_unused_1577_);
v_unused_1578_ = lean_ctor_get(v_s_1561_, 0);
lean_dec(v_unused_1578_);
v___x_1569_ = v_s_1561_;
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
else
{
lean_dec(v_s_1561_);
v___x_1569_ = lean_box(0);
v_isShared_1570_ = v_isSharedCheck_1575_;
goto v_resetjp_1568_;
}
v_resetjp_1568_:
{
lean_object* v___x_1571_; lean_object* v___x_1573_; 
v___x_1571_ = lean_nat_add(v_startInclusive_1565_, v___x_1567_);
lean_dec(v___x_1567_);
if (v_isShared_1570_ == 0)
{
lean_ctor_set(v___x_1569_, 2, v___x_1571_);
v___x_1573_ = v___x_1569_;
goto v_reusejp_1572_;
}
else
{
lean_object* v_reuseFailAlloc_1574_; 
v_reuseFailAlloc_1574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1574_, 0, v_str_1564_);
lean_ctor_set(v_reuseFailAlloc_1574_, 1, v_startInclusive_1565_);
lean_ctor_set(v_reuseFailAlloc_1574_, 2, v___x_1571_);
v___x_1573_ = v_reuseFailAlloc_1574_;
goto v_reusejp_1572_;
}
v_reusejp_1572_:
{
return v___x_1573_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___boxed(lean_object* v_00_u03c1_1579_, lean_object* v_s_1580_, lean_object* v_pat_1581_, lean_object* v_inst_1582_){
_start:
{
lean_object* v_res_1583_; 
v_res_1583_ = l_String_Slice_takeWhile(v_00_u03c1_1579_, v_s_1580_, v_pat_1581_, v_inst_1582_);
lean_dec(v_pat_1581_);
return v_res_1583_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1(lean_object* v___x_1584_, lean_object* v_x1_1585_, lean_object* v_x2_1586_, lean_object* v_x3_1587_){
_start:
{
if (lean_obj_tag(v_x1_1585_) == 0)
{
lean_object* v___x_1588_; 
v___x_1588_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1588_, 0, v___x_1584_);
return v___x_1588_;
}
else
{
lean_object* v_startPos_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; 
lean_dec(v___x_1584_);
v_startPos_1589_ = lean_ctor_get(v_x1_1585_, 0);
lean_inc(v_startPos_1589_);
v___x_1590_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1590_, 0, v_startPos_1589_);
v___x_1591_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1591_, 0, v___x_1590_);
return v___x_1591_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1___boxed(lean_object* v___x_1592_, lean_object* v_x1_1593_, lean_object* v_x2_1594_, lean_object* v_x3_1595_){
_start:
{
lean_object* v_res_1596_; 
v_res_1596_ = l_String_Slice_find_x3f___redArg___lam__1(v___x_1592_, v_x1_1593_, v_x2_1594_, v_x3_1595_);
lean_dec(v_x3_1595_);
lean_dec_ref(v_x1_1593_);
return v_res_1596_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg(lean_object* v_inst_1599_, lean_object* v_s_1600_, lean_object* v_inst_1601_){
_start:
{
lean_object* v___f_1602_; lean_object* v_searcher_1603_; lean_object* v___x_1604_; lean_object* v___f_1605_; lean_object* v___x_1606_; 
v___f_1602_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1600_);
v_searcher_1603_ = lean_apply_1(v_inst_1601_, v_s_1600_);
v___x_1604_ = lean_box(0);
v___f_1605_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1606_ = lean_apply_7(v_inst_1599_, v_s_1600_, v___f_1602_, lean_box(0), lean_box(0), v_searcher_1603_, v___x_1604_, v___f_1605_);
return v___x_1606_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f(lean_object* v_00_u03c1_1607_, lean_object* v_00_u03c3_1608_, lean_object* v_inst_1609_, lean_object* v_inst_1610_, lean_object* v_s_1611_, lean_object* v_pat_1612_, lean_object* v_inst_1613_){
_start:
{
lean_object* v___f_1614_; lean_object* v_searcher_1615_; lean_object* v___x_1616_; lean_object* v___f_1617_; lean_object* v___x_1618_; 
v___f_1614_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1611_);
v_searcher_1615_ = lean_apply_1(v_inst_1613_, v_s_1611_);
v___x_1616_ = lean_box(0);
v___f_1617_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1618_ = lean_apply_7(v_inst_1610_, v_s_1611_, v___f_1614_, lean_box(0), lean_box(0), v_searcher_1615_, v___x_1616_, v___f_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___boxed(lean_object* v_00_u03c1_1619_, lean_object* v_00_u03c3_1620_, lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_s_1623_, lean_object* v_pat_1624_, lean_object* v_inst_1625_){
_start:
{
lean_object* v_res_1626_; 
v_res_1626_ = l_String_Slice_find_x3f(v_00_u03c1_1619_, v_00_u03c3_1620_, v_inst_1621_, v_inst_1622_, v_s_1623_, v_pat_1624_, v_inst_1625_);
lean_dec(v_pat_1624_);
lean_dec(v_inst_1621_);
return v_res_1626_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___redArg(lean_object* v_inst_1627_, lean_object* v_s_1628_, lean_object* v_inst_1629_){
_start:
{
lean_object* v___f_1630_; lean_object* v_searcher_1631_; lean_object* v___x_1632_; lean_object* v___f_1633_; lean_object* v___x_1634_; 
v___f_1630_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1628_, 2);
v_searcher_1631_ = lean_apply_1(v_inst_1629_, v_s_1628_);
v___x_1632_ = lean_box(0);
v___f_1633_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1634_ = lean_apply_7(v_inst_1627_, v_s_1628_, v___f_1630_, lean_box(0), lean_box(0), v_searcher_1631_, v___x_1632_, v___f_1633_);
if (lean_obj_tag(v___x_1634_) == 0)
{
lean_object* v_startInclusive_1635_; lean_object* v_endExclusive_1636_; lean_object* v___x_1637_; 
v_startInclusive_1635_ = lean_ctor_get(v_s_1628_, 1);
lean_inc(v_startInclusive_1635_);
v_endExclusive_1636_ = lean_ctor_get(v_s_1628_, 2);
lean_inc(v_endExclusive_1636_);
lean_dec_ref(v_s_1628_);
v___x_1637_ = lean_nat_sub(v_endExclusive_1636_, v_startInclusive_1635_);
lean_dec(v_startInclusive_1635_);
lean_dec(v_endExclusive_1636_);
return v___x_1637_;
}
else
{
lean_object* v_val_1638_; 
lean_dec_ref(v_s_1628_);
v_val_1638_ = lean_ctor_get(v___x_1634_, 0);
lean_inc(v_val_1638_);
lean_dec_ref_known(v___x_1634_, 1);
return v_val_1638_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find(lean_object* v_00_u03c1_1639_, lean_object* v_00_u03c3_1640_, lean_object* v_inst_1641_, lean_object* v_inst_1642_, lean_object* v_s_1643_, lean_object* v_pat_1644_, lean_object* v_inst_1645_){
_start:
{
lean_object* v___f_1646_; lean_object* v_searcher_1647_; lean_object* v___x_1648_; lean_object* v___f_1649_; lean_object* v___x_1650_; 
v___f_1646_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1643_, 2);
v_searcher_1647_ = lean_apply_1(v_inst_1645_, v_s_1643_);
v___x_1648_ = lean_box(0);
v___f_1649_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1650_ = lean_apply_7(v_inst_1642_, v_s_1643_, v___f_1646_, lean_box(0), lean_box(0), v_searcher_1647_, v___x_1648_, v___f_1649_);
if (lean_obj_tag(v___x_1650_) == 0)
{
lean_object* v_startInclusive_1651_; lean_object* v_endExclusive_1652_; lean_object* v___x_1653_; 
v_startInclusive_1651_ = lean_ctor_get(v_s_1643_, 1);
lean_inc(v_startInclusive_1651_);
v_endExclusive_1652_ = lean_ctor_get(v_s_1643_, 2);
lean_inc(v_endExclusive_1652_);
lean_dec_ref(v_s_1643_);
v___x_1653_ = lean_nat_sub(v_endExclusive_1652_, v_startInclusive_1651_);
lean_dec(v_startInclusive_1651_);
lean_dec(v_endExclusive_1652_);
return v___x_1653_;
}
else
{
lean_object* v_val_1654_; 
lean_dec_ref(v_s_1643_);
v_val_1654_ = lean_ctor_get(v___x_1650_, 0);
lean_inc(v_val_1654_);
lean_dec_ref_known(v___x_1650_, 1);
return v_val_1654_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___boxed(lean_object* v_00_u03c1_1655_, lean_object* v_00_u03c3_1656_, lean_object* v_inst_1657_, lean_object* v_inst_1658_, lean_object* v_s_1659_, lean_object* v_pat_1660_, lean_object* v_inst_1661_){
_start:
{
lean_object* v_res_1662_; 
v_res_1662_ = l_String_Slice_find(v_00_u03c1_1655_, v_00_u03c3_1656_, v_inst_1657_, v_inst_1658_, v_s_1659_, v_pat_1660_, v_inst_1661_);
lean_dec(v_pat_1660_);
lean_dec(v_inst_1657_);
return v_res_1662_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1(uint8_t v___x_1666_, lean_object* v_x1_1667_, lean_object* v_x2_1668_, uint8_t v_x3_1669_){
_start:
{
if (lean_obj_tag(v_x1_1667_) == 1)
{
lean_object* v___x_1670_; 
v___x_1670_ = ((lean_object*)(l_String_Slice_contains___redArg___lam__1___closed__0));
return v___x_1670_;
}
else
{
lean_object* v___x_1671_; lean_object* v___x_1672_; 
v___x_1671_ = lean_box(v___x_1666_);
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1671_);
return v___x_1672_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1___boxed(lean_object* v___x_1673_, lean_object* v_x1_1674_, lean_object* v_x2_1675_, lean_object* v_x3_1676_){
_start:
{
uint8_t v___x_82__boxed_1677_; uint8_t v_x3_85__boxed_1678_; lean_object* v_res_1679_; 
v___x_82__boxed_1677_ = lean_unbox(v___x_1673_);
v_x3_85__boxed_1678_ = lean_unbox(v_x3_1676_);
v_res_1679_ = l_String_Slice_contains___redArg___lam__1(v___x_82__boxed_1677_, v_x1_1674_, v_x2_1675_, v_x3_85__boxed_1678_);
lean_dec_ref(v_x1_1674_);
return v_res_1679_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___redArg(lean_object* v_inst_1683_, lean_object* v_s_1684_, lean_object* v_inst_1685_){
_start:
{
lean_object* v___f_1686_; lean_object* v_searcher_1687_; uint8_t v___x_1688_; lean_object* v___f_1689_; lean_object* v___x_1690_; lean_object* v___x_1691_; uint8_t v___x_1692_; 
v___f_1686_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1684_);
v_searcher_1687_ = lean_apply_1(v_inst_1685_, v_s_1684_);
v___x_1688_ = 0;
v___f_1689_ = ((lean_object*)(l_String_Slice_contains___redArg___closed__0));
v___x_1690_ = lean_box(v___x_1688_);
v___x_1691_ = lean_apply_7(v_inst_1683_, v_s_1684_, v___f_1686_, lean_box(0), lean_box(0), v_searcher_1687_, v___x_1690_, v___f_1689_);
v___x_1692_ = lean_unbox(v___x_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___boxed(lean_object* v_inst_1693_, lean_object* v_s_1694_, lean_object* v_inst_1695_){
_start:
{
uint8_t v_res_1696_; lean_object* v_r_1697_; 
v_res_1696_ = l_String_Slice_contains___redArg(v_inst_1693_, v_s_1694_, v_inst_1695_);
v_r_1697_ = lean_box(v_res_1696_);
return v_r_1697_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains(lean_object* v_00_u03c1_1698_, lean_object* v_00_u03c3_1699_, lean_object* v_inst_1700_, lean_object* v_inst_1701_, lean_object* v_s_1702_, lean_object* v_pat_1703_, lean_object* v_inst_1704_){
_start:
{
uint8_t v___x_1705_; 
v___x_1705_ = l_String_Slice_contains___redArg(v_inst_1701_, v_s_1702_, v_inst_1704_);
return v___x_1705_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___boxed(lean_object* v_00_u03c1_1706_, lean_object* v_00_u03c3_1707_, lean_object* v_inst_1708_, lean_object* v_inst_1709_, lean_object* v_s_1710_, lean_object* v_pat_1711_, lean_object* v_inst_1712_){
_start:
{
uint8_t v_res_1713_; lean_object* v_r_1714_; 
v_res_1713_ = l_String_Slice_contains(v_00_u03c1_1706_, v_00_u03c3_1707_, v_inst_1708_, v_inst_1709_, v_s_1710_, v_pat_1711_, v_inst_1712_);
lean_dec(v_pat_1711_);
lean_dec(v_inst_1708_);
v_r_1714_ = lean_box(v_res_1713_);
return v_r_1714_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any___redArg(lean_object* v_inst_1715_, lean_object* v_s_1716_, lean_object* v_inst_1717_){
_start:
{
uint8_t v___x_1718_; 
v___x_1718_ = l_String_Slice_contains___redArg(v_inst_1715_, v_s_1716_, v_inst_1717_);
return v___x_1718_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___redArg___boxed(lean_object* v_inst_1719_, lean_object* v_s_1720_, lean_object* v_inst_1721_){
_start:
{
uint8_t v_res_1722_; lean_object* v_r_1723_; 
v_res_1722_ = l_String_Slice_any___redArg(v_inst_1719_, v_s_1720_, v_inst_1721_);
v_r_1723_ = lean_box(v_res_1722_);
return v_r_1723_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any(lean_object* v_00_u03c1_1724_, lean_object* v_00_u03c3_1725_, lean_object* v_inst_1726_, lean_object* v_inst_1727_, lean_object* v_s_1728_, lean_object* v_pat_1729_, lean_object* v_inst_1730_){
_start:
{
uint8_t v___x_1731_; 
v___x_1731_ = l_String_Slice_contains___redArg(v_inst_1727_, v_s_1728_, v_inst_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___boxed(lean_object* v_00_u03c1_1732_, lean_object* v_00_u03c3_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_s_1736_, lean_object* v_pat_1737_, lean_object* v_inst_1738_){
_start:
{
uint8_t v_res_1739_; lean_object* v_r_1740_; 
v_res_1739_ = l_String_Slice_any(v_00_u03c1_1732_, v_00_u03c3_1733_, v_inst_1734_, v_inst_1735_, v_s_1736_, v_pat_1737_, v_inst_1738_);
lean_dec(v_pat_1737_);
lean_dec(v_inst_1734_);
v_r_1740_ = lean_box(v_res_1739_);
return v_r_1740_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all___redArg(lean_object* v_s_1741_, lean_object* v_inst_1742_){
_start:
{
lean_object* v_startInclusive_1743_; lean_object* v_endExclusive_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v_decide_1748_; 
v_startInclusive_1743_ = lean_ctor_get(v_s_1741_, 1);
v_endExclusive_1744_ = lean_ctor_get(v_s_1741_, 2);
v___x_1745_ = lean_unsigned_to_nat(0u);
v___x_1746_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1741_, v___x_1745_, v_inst_1742_);
v___x_1747_ = lean_nat_sub(v_endExclusive_1744_, v_startInclusive_1743_);
v_decide_1748_ = lean_nat_dec_eq(v___x_1746_, v___x_1747_);
lean_dec(v___x_1747_);
lean_dec(v___x_1746_);
return v_decide_1748_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___redArg___boxed(lean_object* v_s_1749_, lean_object* v_inst_1750_){
_start:
{
uint8_t v_res_1751_; lean_object* v_r_1752_; 
v_res_1751_ = l_String_Slice_all___redArg(v_s_1749_, v_inst_1750_);
lean_dec_ref(v_s_1749_);
v_r_1752_ = lean_box(v_res_1751_);
return v_r_1752_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all(lean_object* v_00_u03c1_1753_, lean_object* v_s_1754_, lean_object* v_pat_1755_, lean_object* v_inst_1756_){
_start:
{
lean_object* v_startInclusive_1757_; lean_object* v_endExclusive_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; uint8_t v_decide_1762_; 
v_startInclusive_1757_ = lean_ctor_get(v_s_1754_, 1);
v_endExclusive_1758_ = lean_ctor_get(v_s_1754_, 2);
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1754_, v___x_1759_, v_inst_1756_);
v___x_1761_ = lean_nat_sub(v_endExclusive_1758_, v_startInclusive_1757_);
v_decide_1762_ = lean_nat_dec_eq(v___x_1760_, v___x_1761_);
lean_dec(v___x_1761_);
lean_dec(v___x_1760_);
return v_decide_1762_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___boxed(lean_object* v_00_u03c1_1763_, lean_object* v_s_1764_, lean_object* v_pat_1765_, lean_object* v_inst_1766_){
_start:
{
uint8_t v_res_1767_; lean_object* v_r_1768_; 
v_res_1767_ = l_String_Slice_all(v_00_u03c1_1763_, v_s_1764_, v_pat_1765_, v_inst_1766_);
lean_dec(v_pat_1765_);
lean_dec_ref(v_s_1764_);
v_r_1768_ = lean_box(v_res_1767_);
return v_r_1768_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith___redArg(lean_object* v_s_1769_, lean_object* v_inst_1770_){
_start:
{
lean_object* v_endsWith_1771_; lean_object* v___x_1772_; uint8_t v___x_1773_; 
v_endsWith_1771_ = lean_ctor_get(v_inst_1770_, 2);
lean_inc_ref(v_endsWith_1771_);
lean_dec_ref(v_inst_1770_);
v___x_1772_ = lean_apply_1(v_endsWith_1771_, v_s_1769_);
v___x_1773_ = lean_unbox(v___x_1772_);
return v___x_1773_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___redArg___boxed(lean_object* v_s_1774_, lean_object* v_inst_1775_){
_start:
{
uint8_t v_res_1776_; lean_object* v_r_1777_; 
v_res_1776_ = l_String_Slice_endsWith___redArg(v_s_1774_, v_inst_1775_);
v_r_1777_ = lean_box(v_res_1776_);
return v_r_1777_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith(lean_object* v_00_u03c1_1778_, lean_object* v_s_1779_, lean_object* v_pat_1780_, lean_object* v_inst_1781_){
_start:
{
lean_object* v_endsWith_1782_; lean_object* v___x_1783_; uint8_t v___x_1784_; 
v_endsWith_1782_ = lean_ctor_get(v_inst_1781_, 2);
lean_inc_ref(v_endsWith_1782_);
lean_dec_ref(v_inst_1781_);
v___x_1783_ = lean_apply_1(v_endsWith_1782_, v_s_1779_);
v___x_1784_ = lean_unbox(v___x_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___boxed(lean_object* v_00_u03c1_1785_, lean_object* v_s_1786_, lean_object* v_pat_1787_, lean_object* v_inst_1788_){
_start:
{
uint8_t v_res_1789_; lean_object* v_r_1790_; 
v_res_1789_ = l_String_Slice_endsWith(v_00_u03c1_1785_, v_s_1786_, v_pat_1787_, v_inst_1788_);
lean_dec(v_pat_1787_);
v_r_1790_ = lean_box(v_res_1789_);
return v_r_1790_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg(lean_object* v_x_1791_){
_start:
{
lean_object* v___x_1792_; 
v___x_1792_ = lean_obj_tag_nat(v_x_1791_);
return v___x_1792_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg___boxed(lean_object* v_x_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg(v_x_1793_);
lean_dec(v_x_1793_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl(lean_object* v_00_u03c3_1795_, lean_object* v_00_u03c1_1796_, lean_object* v_pat_1797_, lean_object* v_s_1798_, lean_object* v_inst_1799_, lean_object* v_x_1800_){
_start:
{
lean_object* v___x_1801_; 
v___x_1801_ = lean_obj_tag_nat(v_x_1800_);
return v___x_1801_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___boxed(lean_object* v_00_u03c3_1802_, lean_object* v_00_u03c1_1803_, lean_object* v_pat_1804_, lean_object* v_s_1805_, lean_object* v_inst_1806_, lean_object* v_x_1807_){
_start:
{
lean_object* v_res_1808_; 
v_res_1808_ = l_String_Slice_RevSplitIterator_ctorIdx___impl(v_00_u03c3_1802_, v_00_u03c1_1803_, v_pat_1804_, v_s_1805_, v_inst_1806_, v_x_1807_);
lean_dec(v_x_1807_);
lean_dec(v_inst_1806_);
lean_dec_ref(v_s_1805_);
lean_dec(v_pat_1804_);
return v_res_1808_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___redArg(lean_object* v_t_1809_, lean_object* v_k_1810_){
_start:
{
if (lean_obj_tag(v_t_1809_) == 0)
{
lean_object* v_currPos_1811_; lean_object* v_searcher_1812_; lean_object* v___x_1813_; 
v_currPos_1811_ = lean_ctor_get(v_t_1809_, 0);
lean_inc(v_currPos_1811_);
v_searcher_1812_ = lean_ctor_get(v_t_1809_, 1);
lean_inc(v_searcher_1812_);
lean_dec_ref_known(v_t_1809_, 2);
v___x_1813_ = lean_apply_2(v_k_1810_, v_currPos_1811_, v_searcher_1812_);
return v___x_1813_;
}
else
{
return v_k_1810_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim(lean_object* v_00_u03c3_1814_, lean_object* v_00_u03c1_1815_, lean_object* v_pat_1816_, lean_object* v_s_1817_, lean_object* v_inst_1818_, lean_object* v_motive_1819_, lean_object* v_ctorIdx_1820_, lean_object* v_t_1821_, lean_object* v_h_1822_, lean_object* v_k_1823_){
_start:
{
lean_object* v___x_1824_; 
v___x_1824_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1821_, v_k_1823_);
return v___x_1824_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_1825_, lean_object* v_00_u03c1_1826_, lean_object* v_pat_1827_, lean_object* v_s_1828_, lean_object* v_inst_1829_, lean_object* v_motive_1830_, lean_object* v_ctorIdx_1831_, lean_object* v_t_1832_, lean_object* v_h_1833_, lean_object* v_k_1834_){
_start:
{
lean_object* v_res_1835_; 
v_res_1835_ = l_String_Slice_RevSplitIterator_ctorElim(v_00_u03c3_1825_, v_00_u03c1_1826_, v_pat_1827_, v_s_1828_, v_inst_1829_, v_motive_1830_, v_ctorIdx_1831_, v_t_1832_, v_h_1833_, v_k_1834_);
lean_dec(v_ctorIdx_1831_);
lean_dec(v_inst_1829_);
lean_dec_ref(v_s_1828_);
lean_dec(v_pat_1827_);
return v_res_1835_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___redArg(lean_object* v_t_1836_, lean_object* v_operating_1837_){
_start:
{
lean_object* v___x_1838_; 
v___x_1838_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1836_, v_operating_1837_);
return v___x_1838_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim(lean_object* v_00_u03c3_1839_, lean_object* v_00_u03c1_1840_, lean_object* v_pat_1841_, lean_object* v_s_1842_, lean_object* v_inst_1843_, lean_object* v_motive_1844_, lean_object* v_t_1845_, lean_object* v_h_1846_, lean_object* v_operating_1847_){
_start:
{
lean_object* v___x_1848_; 
v___x_1848_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1845_, v_operating_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_1849_, lean_object* v_00_u03c1_1850_, lean_object* v_pat_1851_, lean_object* v_s_1852_, lean_object* v_inst_1853_, lean_object* v_motive_1854_, lean_object* v_t_1855_, lean_object* v_h_1856_, lean_object* v_operating_1857_){
_start:
{
lean_object* v_res_1858_; 
v_res_1858_ = l_String_Slice_RevSplitIterator_operating_elim(v_00_u03c3_1849_, v_00_u03c1_1850_, v_pat_1851_, v_s_1852_, v_inst_1853_, v_motive_1854_, v_t_1855_, v_h_1856_, v_operating_1857_);
lean_dec(v_inst_1853_);
lean_dec_ref(v_s_1852_);
lean_dec(v_pat_1851_);
return v_res_1858_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___redArg(lean_object* v_t_1859_, lean_object* v_atEnd_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1859_, v_atEnd_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim(lean_object* v_00_u03c3_1862_, lean_object* v_00_u03c1_1863_, lean_object* v_pat_1864_, lean_object* v_s_1865_, lean_object* v_inst_1866_, lean_object* v_motive_1867_, lean_object* v_t_1868_, lean_object* v_h_1869_, lean_object* v_atEnd_1870_){
_start:
{
lean_object* v___x_1871_; 
v___x_1871_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1868_, v_atEnd_1870_);
return v___x_1871_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_1872_, lean_object* v_00_u03c1_1873_, lean_object* v_pat_1874_, lean_object* v_s_1875_, lean_object* v_inst_1876_, lean_object* v_motive_1877_, lean_object* v_t_1878_, lean_object* v_h_1879_, lean_object* v_atEnd_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_String_Slice_RevSplitIterator_atEnd_elim(v_00_u03c3_1872_, v_00_u03c1_1873_, v_pat_1874_, v_s_1875_, v_inst_1876_, v_motive_1877_, v_t_1878_, v_h_1879_, v_atEnd_1880_);
lean_dec(v_inst_1876_);
lean_dec_ref(v_s_1875_);
lean_dec(v_pat_1874_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg(){
_start:
{
lean_object* v___x_1883_; 
v___x_1883_ = lean_box(1);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg___boxed(lean_object* v___dummy_1884_){
_start:
{
lean_object* v_res_1885_; 
v_res_1885_ = l_String_Slice_instInhabitedRevSplitIterator_default___redArg();
return v_res_1885_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default(lean_object* v_00_u03c3_1886_, lean_object* v_00_u03c1_1887_, lean_object* v_pat_1888_, lean_object* v_s_1889_, lean_object* v_inst_1890_){
_start:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_box(1);
return v___x_1891_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___boxed(lean_object* v_00_u03c3_1892_, lean_object* v_00_u03c1_1893_, lean_object* v_pat_1894_, lean_object* v_s_1895_, lean_object* v_inst_1896_){
_start:
{
lean_object* v_res_1897_; 
v_res_1897_ = l_String_Slice_instInhabitedRevSplitIterator_default(v_00_u03c3_1892_, v_00_u03c1_1893_, v_pat_1894_, v_s_1895_, v_inst_1896_);
lean_dec(v_inst_1896_);
lean_dec_ref(v_s_1895_);
lean_dec(v_pat_1894_);
return v_res_1897_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg(){
_start:
{
lean_object* v___x_1899_; 
v___x_1899_ = lean_box(1);
return v___x_1899_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg___boxed(lean_object* v___dummy_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l_String_Slice_instInhabitedRevSplitIterator___redArg();
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator(lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = lean_box(1);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___boxed(lean_object* v_a_1908_, lean_object* v_a_1909_, lean_object* v_a_1910_, lean_object* v_a_1911_, lean_object* v_a_1912_){
_start:
{
lean_object* v_res_1913_; 
v_res_1913_ = l_String_Slice_instInhabitedRevSplitIterator(v_a_1908_, v_a_1909_, v_a_1910_, v_a_1911_, v_a_1912_);
lean_dec(v_a_1912_);
lean_dec_ref(v_a_1911_);
lean_dec(v_a_1910_);
return v_res_1913_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0(lean_object* v_inst_1914_, lean_object* v_s_1915_, lean_object* v_inst_1916_, lean_object* v_x_1917_){
_start:
{
if (lean_obj_tag(v_x_1917_) == 0)
{
lean_object* v_currPos_1918_; lean_object* v_searcher_1919_; lean_object* v___x_1921_; uint8_t v_isShared_1922_; uint8_t v_isSharedCheck_1977_; 
v_currPos_1918_ = lean_ctor_get(v_x_1917_, 0);
v_searcher_1919_ = lean_ctor_get(v_x_1917_, 1);
v_isSharedCheck_1977_ = !lean_is_exclusive(v_x_1917_);
if (v_isSharedCheck_1977_ == 0)
{
v___x_1921_ = v_x_1917_;
v_isShared_1922_ = v_isSharedCheck_1977_;
goto v_resetjp_1920_;
}
else
{
lean_inc(v_searcher_1919_);
lean_inc(v_currPos_1918_);
lean_dec(v_x_1917_);
v___x_1921_ = lean_box(0);
v_isShared_1922_ = v_isSharedCheck_1977_;
goto v_resetjp_1920_;
}
v_resetjp_1920_:
{
lean_object* v___x_1923_; 
lean_inc_ref(v_s_1915_);
v___x_1923_ = lean_apply_2(v_inst_1914_, v_s_1915_, v_searcher_1919_);
switch(lean_obj_tag(v___x_1923_))
{
case 0:
{
lean_object* v_out_1924_; 
v_out_1924_ = lean_ctor_get(v___x_1923_, 1);
lean_inc(v_out_1924_);
if (lean_obj_tag(v_out_1924_) == 0)
{
lean_object* v_it_1925_; lean_object* v___x_1927_; 
lean_dec_ref_known(v_out_1924_, 2);
lean_dec_ref(v_s_1915_);
v_it_1925_ = lean_ctor_get(v___x_1923_, 0);
lean_inc(v_it_1925_);
lean_dec_ref_known(v___x_1923_, 2);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v_it_1925_);
v___x_1927_ = v___x_1921_;
goto v_reusejp_1926_;
}
else
{
lean_object* v_reuseFailAlloc_1930_; 
v_reuseFailAlloc_1930_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1930_, 0, v_currPos_1918_);
lean_ctor_set(v_reuseFailAlloc_1930_, 1, v_it_1925_);
v___x_1927_ = v_reuseFailAlloc_1930_;
goto v_reusejp_1926_;
}
v_reusejp_1926_:
{
lean_object* v___x_1928_; lean_object* v___x_1929_; 
v___x_1928_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1928_, 0, v___x_1927_);
v___x_1929_ = lean_apply_2(v_inst_1916_, lean_box(0), v___x_1928_);
return v___x_1929_;
}
}
else
{
lean_object* v_it_1931_; lean_object* v___x_1933_; uint8_t v_isShared_1934_; uint8_t v_isSharedCheck_1945_; 
v_it_1931_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1945_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1945_ == 0)
{
lean_object* v_unused_1946_; 
v_unused_1946_ = lean_ctor_get(v___x_1923_, 1);
lean_dec(v_unused_1946_);
v___x_1933_ = v___x_1923_;
v_isShared_1934_ = v_isSharedCheck_1945_;
goto v_resetjp_1932_;
}
else
{
lean_inc(v_it_1931_);
lean_dec(v___x_1923_);
v___x_1933_ = lean_box(0);
v_isShared_1934_ = v_isSharedCheck_1945_;
goto v_resetjp_1932_;
}
v_resetjp_1932_:
{
lean_object* v_startPos_1935_; lean_object* v_endPos_1936_; lean_object* v_slice_1937_; lean_object* v_nextIt_1939_; 
v_startPos_1935_ = lean_ctor_get(v_out_1924_, 0);
lean_inc(v_startPos_1935_);
v_endPos_1936_ = lean_ctor_get(v_out_1924_, 1);
lean_inc(v_endPos_1936_);
lean_dec_ref_known(v_out_1924_, 2);
v_slice_1937_ = l_String_Slice_slice_x21(v_s_1915_, v_endPos_1936_, v_currPos_1918_);
lean_dec(v_currPos_1918_);
lean_dec(v_endPos_1936_);
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v_it_1931_);
lean_ctor_set(v___x_1921_, 0, v_startPos_1935_);
v_nextIt_1939_ = v___x_1921_;
goto v_reusejp_1938_;
}
else
{
lean_object* v_reuseFailAlloc_1944_; 
v_reuseFailAlloc_1944_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1944_, 0, v_startPos_1935_);
lean_ctor_set(v_reuseFailAlloc_1944_, 1, v_it_1931_);
v_nextIt_1939_ = v_reuseFailAlloc_1944_;
goto v_reusejp_1938_;
}
v_reusejp_1938_:
{
lean_object* v___x_1941_; 
if (v_isShared_1934_ == 0)
{
lean_ctor_set(v___x_1933_, 1, v_slice_1937_);
lean_ctor_set(v___x_1933_, 0, v_nextIt_1939_);
v___x_1941_ = v___x_1933_;
goto v_reusejp_1940_;
}
else
{
lean_object* v_reuseFailAlloc_1943_; 
v_reuseFailAlloc_1943_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1943_, 0, v_nextIt_1939_);
lean_ctor_set(v_reuseFailAlloc_1943_, 1, v_slice_1937_);
v___x_1941_ = v_reuseFailAlloc_1943_;
goto v_reusejp_1940_;
}
v_reusejp_1940_:
{
lean_object* v___x_1942_; 
v___x_1942_ = lean_apply_2(v_inst_1916_, lean_box(0), v___x_1941_);
return v___x_1942_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1947_; lean_object* v___x_1949_; uint8_t v_isShared_1950_; uint8_t v_isSharedCheck_1958_; 
lean_dec_ref(v_s_1915_);
v_it_1947_ = lean_ctor_get(v___x_1923_, 0);
v_isSharedCheck_1958_ = !lean_is_exclusive(v___x_1923_);
if (v_isSharedCheck_1958_ == 0)
{
v___x_1949_ = v___x_1923_;
v_isShared_1950_ = v_isSharedCheck_1958_;
goto v_resetjp_1948_;
}
else
{
lean_inc(v_it_1947_);
lean_dec(v___x_1923_);
v___x_1949_ = lean_box(0);
v_isShared_1950_ = v_isSharedCheck_1958_;
goto v_resetjp_1948_;
}
v_resetjp_1948_:
{
lean_object* v___x_1952_; 
if (v_isShared_1922_ == 0)
{
lean_ctor_set(v___x_1921_, 1, v_it_1947_);
v___x_1952_ = v___x_1921_;
goto v_reusejp_1951_;
}
else
{
lean_object* v_reuseFailAlloc_1957_; 
v_reuseFailAlloc_1957_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1957_, 0, v_currPos_1918_);
lean_ctor_set(v_reuseFailAlloc_1957_, 1, v_it_1947_);
v___x_1952_ = v_reuseFailAlloc_1957_;
goto v_reusejp_1951_;
}
v_reusejp_1951_:
{
lean_object* v___x_1954_; 
if (v_isShared_1950_ == 0)
{
lean_ctor_set(v___x_1949_, 0, v___x_1952_);
v___x_1954_ = v___x_1949_;
goto v_reusejp_1953_;
}
else
{
lean_object* v_reuseFailAlloc_1956_; 
v_reuseFailAlloc_1956_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1956_, 0, v___x_1952_);
v___x_1954_ = v_reuseFailAlloc_1956_;
goto v_reusejp_1953_;
}
v_reusejp_1953_:
{
lean_object* v___x_1955_; 
v___x_1955_ = lean_apply_2(v_inst_1916_, lean_box(0), v___x_1954_);
return v___x_1955_;
}
}
}
}
default: 
{
lean_object* v___x_1959_; uint8_t v_decide_1960_; 
lean_del_object(v___x_1921_);
v___x_1959_ = lean_unsigned_to_nat(0u);
v_decide_1960_ = lean_nat_dec_eq(v_currPos_1918_, v___x_1959_);
if (v_decide_1960_ == 0)
{
lean_object* v_str_1961_; lean_object* v_startInclusive_1962_; lean_object* v___x_1964_; uint8_t v_isShared_1965_; uint8_t v_isSharedCheck_1973_; 
v_str_1961_ = lean_ctor_get(v_s_1915_, 0);
v_startInclusive_1962_ = lean_ctor_get(v_s_1915_, 1);
v_isSharedCheck_1973_ = !lean_is_exclusive(v_s_1915_);
if (v_isSharedCheck_1973_ == 0)
{
lean_object* v_unused_1974_; 
v_unused_1974_ = lean_ctor_get(v_s_1915_, 2);
lean_dec(v_unused_1974_);
v___x_1964_ = v_s_1915_;
v_isShared_1965_ = v_isSharedCheck_1973_;
goto v_resetjp_1963_;
}
else
{
lean_inc(v_startInclusive_1962_);
lean_inc(v_str_1961_);
lean_dec(v_s_1915_);
v___x_1964_ = lean_box(0);
v_isShared_1965_ = v_isSharedCheck_1973_;
goto v_resetjp_1963_;
}
v_resetjp_1963_:
{
lean_object* v___x_1966_; lean_object* v_slice_1968_; 
v___x_1966_ = lean_nat_add(v_startInclusive_1962_, v_currPos_1918_);
lean_dec(v_currPos_1918_);
if (v_isShared_1965_ == 0)
{
lean_ctor_set(v___x_1964_, 2, v___x_1966_);
v_slice_1968_ = v___x_1964_;
goto v_reusejp_1967_;
}
else
{
lean_object* v_reuseFailAlloc_1972_; 
v_reuseFailAlloc_1972_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1972_, 0, v_str_1961_);
lean_ctor_set(v_reuseFailAlloc_1972_, 1, v_startInclusive_1962_);
lean_ctor_set(v_reuseFailAlloc_1972_, 2, v___x_1966_);
v_slice_1968_ = v_reuseFailAlloc_1972_;
goto v_reusejp_1967_;
}
v_reusejp_1967_:
{
lean_object* v___x_1969_; lean_object* v___x_1970_; lean_object* v___x_1971_; 
v___x_1969_ = lean_box(1);
v___x_1970_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1970_, 0, v___x_1969_);
lean_ctor_set(v___x_1970_, 1, v_slice_1968_);
v___x_1971_ = lean_apply_2(v_inst_1916_, lean_box(0), v___x_1970_);
return v___x_1971_;
}
}
}
else
{
lean_object* v___x_1975_; lean_object* v___x_1976_; 
lean_dec(v_currPos_1918_);
lean_dec_ref(v_s_1915_);
v___x_1975_ = lean_box(2);
v___x_1976_ = lean_apply_2(v_inst_1916_, lean_box(0), v___x_1975_);
return v___x_1976_;
}
}
}
}
}
else
{
lean_object* v___x_1978_; lean_object* v___x_1979_; 
lean_dec_ref(v_s_1915_);
lean_dec(v_inst_1914_);
v___x_1978_ = lean_box(2);
v___x_1979_ = lean_apply_2(v_inst_1916_, lean_box(0), v___x_1978_);
return v___x_1979_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg(lean_object* v_inst_1980_, lean_object* v_s_1981_, lean_object* v_inst_1982_){
_start:
{
lean_object* v___f_1983_; 
v___f_1983_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1983_, 0, v_inst_1980_);
lean_closure_set(v___f_1983_, 1, v_s_1981_);
lean_closure_set(v___f_1983_, 2, v_inst_1982_);
return v___f_1983_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure(lean_object* v_00_u03c1_1984_, lean_object* v_00_u03c1_1985_, lean_object* v_00_u03c3_1986_, lean_object* v_inst_1987_, lean_object* v_inst_1988_, lean_object* v_m_1989_, lean_object* v_s_1990_, lean_object* v_inst_1991_){
_start:
{
lean_object* v___f_1992_; 
v___f_1992_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1992_, 0, v_inst_1987_);
lean_closure_set(v___f_1992_, 1, v_s_1990_);
lean_closure_set(v___f_1992_, 2, v_inst_1991_);
return v___f_1992_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___boxed(lean_object* v_00_u03c1_1993_, lean_object* v_00_u03c1_1994_, lean_object* v_00_u03c3_1995_, lean_object* v_inst_1996_, lean_object* v_inst_1997_, lean_object* v_m_1998_, lean_object* v_s_1999_, lean_object* v_inst_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l_String_Slice_RevSplitIterator_instIteratorOfPure(v_00_u03c1_1993_, v_00_u03c1_1994_, v_00_u03c3_1995_, v_inst_1996_, v_inst_1997_, v_m_1998_, v_s_1999_, v_inst_2000_);
lean_dec(v_inst_1997_);
lean_dec(v_00_u03c1_1994_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___redArg(lean_object* v_x_2002_){
_start:
{
if (lean_obj_tag(v_x_2002_) == 0)
{
lean_object* v_searcher_2003_; lean_object* v___x_2004_; 
v_searcher_2003_ = lean_ctor_get(v_x_2002_, 1);
lean_inc(v_searcher_2003_);
v___x_2004_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2004_, 0, v_searcher_2003_);
return v___x_2004_;
}
else
{
lean_object* v___x_2005_; 
v___x_2005_ = lean_box(0);
return v___x_2005_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___redArg___boxed(lean_object* v_x_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2006_);
lean_dec(v_x_2006_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption(lean_object* v_00_u03c1_2008_, lean_object* v_00_u03c1_2009_, lean_object* v_00_u03c3_2010_, lean_object* v_inst_2011_, lean_object* v_s_2012_, lean_object* v_x_2013_){
_start:
{
lean_object* v___x_2014_; 
v___x_2014_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2013_);
return v___x_2014_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___boxed(lean_object* v_00_u03c1_2015_, lean_object* v_00_u03c1_2016_, lean_object* v_00_u03c3_2017_, lean_object* v_inst_2018_, lean_object* v_s_2019_, lean_object* v_x_2020_){
_start:
{
lean_object* v_res_2021_; 
v_res_2021_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption(v_00_u03c1_2015_, v_00_u03c1_2016_, v_00_u03c3_2017_, v_inst_2018_, v_s_2019_, v_x_2020_);
lean_dec(v_x_2020_);
lean_dec_ref(v_s_2019_);
lean_dec(v_inst_2018_);
lean_dec(v_00_u03c1_2016_);
return v_res_2021_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(lean_object* v_x_2022_, lean_object* v_h__1_2023_, lean_object* v_h__2_2024_){
_start:
{
if (lean_obj_tag(v_x_2022_) == 0)
{
lean_object* v_currPos_2025_; lean_object* v_searcher_2026_; lean_object* v___x_2027_; 
lean_dec(v_h__2_2024_);
v_currPos_2025_ = lean_ctor_get(v_x_2022_, 0);
lean_inc(v_currPos_2025_);
v_searcher_2026_ = lean_ctor_get(v_x_2022_, 1);
lean_inc(v_searcher_2026_);
lean_dec_ref_known(v_x_2022_, 2);
v___x_2027_ = lean_apply_2(v_h__1_2023_, v_currPos_2025_, v_searcher_2026_);
return v___x_2027_;
}
else
{
lean_object* v___x_2028_; lean_object* v___x_2029_; 
lean_dec(v_h__1_2023_);
v___x_2028_ = lean_box(0);
v___x_2029_ = lean_apply_1(v_h__2_2024_, v___x_2028_);
return v___x_2029_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(lean_object* v_00_u03c1_2030_, lean_object* v_00_u03c1_2031_, lean_object* v_00_u03c3_2032_, lean_object* v_inst_2033_, lean_object* v_m_2034_, lean_object* v_s_2035_, lean_object* v_motive_2036_, lean_object* v_x_2037_, lean_object* v_h__1_2038_, lean_object* v_h__2_2039_){
_start:
{
if (lean_obj_tag(v_x_2037_) == 0)
{
lean_object* v_currPos_2040_; lean_object* v_searcher_2041_; lean_object* v___x_2042_; 
lean_dec(v_h__2_2039_);
v_currPos_2040_ = lean_ctor_get(v_x_2037_, 0);
lean_inc(v_currPos_2040_);
v_searcher_2041_ = lean_ctor_get(v_x_2037_, 1);
lean_inc(v_searcher_2041_);
lean_dec_ref_known(v_x_2037_, 2);
v___x_2042_ = lean_apply_2(v_h__1_2038_, v_currPos_2040_, v_searcher_2041_);
return v___x_2042_;
}
else
{
lean_object* v___x_2043_; lean_object* v___x_2044_; 
lean_dec(v_h__1_2038_);
v___x_2043_ = lean_box(0);
v___x_2044_ = lean_apply_1(v_h__2_2039_, v___x_2043_);
return v___x_2044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___boxed(lean_object* v_00_u03c1_2045_, lean_object* v_00_u03c1_2046_, lean_object* v_00_u03c3_2047_, lean_object* v_inst_2048_, lean_object* v_m_2049_, lean_object* v_s_2050_, lean_object* v_motive_2051_, lean_object* v_x_2052_, lean_object* v_h__1_2053_, lean_object* v_h__2_2054_){
_start:
{
lean_object* v_res_2055_; 
v_res_2055_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(v_00_u03c1_2045_, v_00_u03c1_2046_, v_00_u03c3_2047_, v_inst_2048_, v_m_2049_, v_s_2050_, v_motive_2051_, v_x_2052_, v_h__1_2053_, v_h__2_2054_);
lean_dec_ref(v_s_2050_);
lean_dec(v_inst_2048_);
lean_dec(v_00_u03c1_2046_);
return v_res_2055_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(lean_object* v_x_2056_, lean_object* v_x_2057_, lean_object* v_h__1_2058_, lean_object* v_h__2_2059_, lean_object* v_h__3_2060_, lean_object* v_h__4_2061_, lean_object* v_h__5_2062_, lean_object* v_h__6_2063_, lean_object* v_h__7_2064_, lean_object* v_h__8_2065_){
_start:
{
if (lean_obj_tag(v_x_2056_) == 0)
{
lean_dec(v_h__8_2065_);
lean_dec(v_h__7_2064_);
lean_dec(v_h__6_2063_);
switch(lean_obj_tag(v_x_2057_))
{
case 0:
{
lean_object* v_it_2066_; 
lean_dec(v_h__5_2062_);
lean_dec(v_h__4_2061_);
lean_dec(v_h__3_2060_);
v_it_2066_ = lean_ctor_get(v_x_2057_, 0);
if (lean_obj_tag(v_it_2066_) == 0)
{
lean_object* v_currPos_2067_; lean_object* v_searcher_2068_; lean_object* v_out_2069_; lean_object* v_currPos_2070_; lean_object* v_searcher_2071_; lean_object* v___x_2072_; 
lean_inc_ref(v_it_2066_);
lean_dec(v_h__2_2059_);
v_currPos_2067_ = lean_ctor_get(v_x_2056_, 0);
lean_inc(v_currPos_2067_);
v_searcher_2068_ = lean_ctor_get(v_x_2056_, 1);
lean_inc(v_searcher_2068_);
lean_dec_ref_known(v_x_2056_, 2);
v_out_2069_ = lean_ctor_get(v_x_2057_, 1);
lean_inc(v_out_2069_);
lean_dec_ref_known(v_x_2057_, 2);
v_currPos_2070_ = lean_ctor_get(v_it_2066_, 0);
lean_inc(v_currPos_2070_);
v_searcher_2071_ = lean_ctor_get(v_it_2066_, 1);
lean_inc(v_searcher_2071_);
lean_dec_ref_known(v_it_2066_, 2);
v___x_2072_ = lean_apply_5(v_h__1_2058_, v_currPos_2067_, v_searcher_2068_, v_currPos_2070_, v_searcher_2071_, v_out_2069_);
return v___x_2072_;
}
else
{
lean_object* v_currPos_2073_; lean_object* v_searcher_2074_; lean_object* v_out_2075_; lean_object* v___x_2076_; 
lean_dec(v_h__1_2058_);
v_currPos_2073_ = lean_ctor_get(v_x_2056_, 0);
lean_inc(v_currPos_2073_);
v_searcher_2074_ = lean_ctor_get(v_x_2056_, 1);
lean_inc(v_searcher_2074_);
lean_dec_ref_known(v_x_2056_, 2);
v_out_2075_ = lean_ctor_get(v_x_2057_, 1);
lean_inc(v_out_2075_);
lean_dec_ref_known(v_x_2057_, 2);
v___x_2076_ = lean_apply_3(v_h__2_2059_, v_currPos_2073_, v_searcher_2074_, v_out_2075_);
return v___x_2076_;
}
}
case 1:
{
lean_object* v_it_2077_; 
lean_dec(v_h__5_2062_);
lean_dec(v_h__2_2059_);
lean_dec(v_h__1_2058_);
v_it_2077_ = lean_ctor_get(v_x_2057_, 0);
lean_inc(v_it_2077_);
lean_dec_ref_known(v_x_2057_, 1);
if (lean_obj_tag(v_it_2077_) == 0)
{
lean_object* v_currPos_2078_; lean_object* v_searcher_2079_; lean_object* v_currPos_2080_; lean_object* v_searcher_2081_; lean_object* v___x_2082_; 
lean_dec(v_h__4_2061_);
v_currPos_2078_ = lean_ctor_get(v_x_2056_, 0);
lean_inc(v_currPos_2078_);
v_searcher_2079_ = lean_ctor_get(v_x_2056_, 1);
lean_inc(v_searcher_2079_);
lean_dec_ref_known(v_x_2056_, 2);
v_currPos_2080_ = lean_ctor_get(v_it_2077_, 0);
lean_inc(v_currPos_2080_);
v_searcher_2081_ = lean_ctor_get(v_it_2077_, 1);
lean_inc(v_searcher_2081_);
lean_dec_ref_known(v_it_2077_, 2);
v___x_2082_ = lean_apply_4(v_h__3_2060_, v_currPos_2078_, v_searcher_2079_, v_currPos_2080_, v_searcher_2081_);
return v___x_2082_;
}
else
{
lean_object* v_currPos_2083_; lean_object* v_searcher_2084_; lean_object* v___x_2085_; 
lean_dec(v_h__3_2060_);
v_currPos_2083_ = lean_ctor_get(v_x_2056_, 0);
lean_inc(v_currPos_2083_);
v_searcher_2084_ = lean_ctor_get(v_x_2056_, 1);
lean_inc(v_searcher_2084_);
lean_dec_ref_known(v_x_2056_, 2);
v___x_2085_ = lean_apply_2(v_h__4_2061_, v_currPos_2083_, v_searcher_2084_);
return v___x_2085_;
}
}
default: 
{
lean_object* v_currPos_2086_; lean_object* v_searcher_2087_; lean_object* v___x_2088_; 
lean_dec(v_h__4_2061_);
lean_dec(v_h__3_2060_);
lean_dec(v_h__2_2059_);
lean_dec(v_h__1_2058_);
v_currPos_2086_ = lean_ctor_get(v_x_2056_, 0);
lean_inc(v_currPos_2086_);
v_searcher_2087_ = lean_ctor_get(v_x_2056_, 1);
lean_inc(v_searcher_2087_);
lean_dec_ref_known(v_x_2056_, 2);
v___x_2088_ = lean_apply_2(v_h__5_2062_, v_currPos_2086_, v_searcher_2087_);
return v___x_2088_;
}
}
}
else
{
lean_dec(v_h__5_2062_);
lean_dec(v_h__4_2061_);
lean_dec(v_h__3_2060_);
lean_dec(v_h__2_2059_);
lean_dec(v_h__1_2058_);
switch(lean_obj_tag(v_x_2057_))
{
case 0:
{
lean_object* v_it_2089_; lean_object* v_out_2090_; lean_object* v___x_2091_; 
lean_dec(v_h__8_2065_);
lean_dec(v_h__7_2064_);
v_it_2089_ = lean_ctor_get(v_x_2057_, 0);
lean_inc(v_it_2089_);
v_out_2090_ = lean_ctor_get(v_x_2057_, 1);
lean_inc(v_out_2090_);
lean_dec_ref_known(v_x_2057_, 2);
v___x_2091_ = lean_apply_2(v_h__6_2063_, v_it_2089_, v_out_2090_);
return v___x_2091_;
}
case 1:
{
lean_object* v_it_2092_; lean_object* v___x_2093_; 
lean_dec(v_h__8_2065_);
lean_dec(v_h__6_2063_);
v_it_2092_ = lean_ctor_get(v_x_2057_, 0);
lean_inc(v_it_2092_);
lean_dec_ref_known(v_x_2057_, 1);
v___x_2093_ = lean_apply_1(v_h__7_2064_, v_it_2092_);
return v___x_2093_;
}
default: 
{
lean_object* v___x_2094_; lean_object* v___x_2095_; 
lean_dec(v_h__7_2064_);
lean_dec(v_h__6_2063_);
v___x_2094_ = lean_box(0);
v___x_2095_ = lean_apply_1(v_h__8_2065_, v___x_2094_);
return v___x_2095_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(lean_object* v_00_u03c1_2096_, lean_object* v_00_u03c1_2097_, lean_object* v_00_u03c3_2098_, lean_object* v_inst_2099_, lean_object* v_m_2100_, lean_object* v_s_2101_, lean_object* v_motive_2102_, lean_object* v_x_2103_, lean_object* v_x_2104_, lean_object* v_h__1_2105_, lean_object* v_h__2_2106_, lean_object* v_h__3_2107_, lean_object* v_h__4_2108_, lean_object* v_h__5_2109_, lean_object* v_h__6_2110_, lean_object* v_h__7_2111_, lean_object* v_h__8_2112_){
_start:
{
if (lean_obj_tag(v_x_2103_) == 0)
{
lean_dec(v_h__8_2112_);
lean_dec(v_h__7_2111_);
lean_dec(v_h__6_2110_);
switch(lean_obj_tag(v_x_2104_))
{
case 0:
{
lean_object* v_it_2113_; 
lean_dec(v_h__5_2109_);
lean_dec(v_h__4_2108_);
lean_dec(v_h__3_2107_);
v_it_2113_ = lean_ctor_get(v_x_2104_, 0);
if (lean_obj_tag(v_it_2113_) == 0)
{
lean_object* v_currPos_2114_; lean_object* v_searcher_2115_; lean_object* v_out_2116_; lean_object* v_currPos_2117_; lean_object* v_searcher_2118_; lean_object* v___x_2119_; 
lean_inc_ref(v_it_2113_);
lean_dec(v_h__2_2106_);
v_currPos_2114_ = lean_ctor_get(v_x_2103_, 0);
lean_inc(v_currPos_2114_);
v_searcher_2115_ = lean_ctor_get(v_x_2103_, 1);
lean_inc(v_searcher_2115_);
lean_dec_ref_known(v_x_2103_, 2);
v_out_2116_ = lean_ctor_get(v_x_2104_, 1);
lean_inc(v_out_2116_);
lean_dec_ref_known(v_x_2104_, 2);
v_currPos_2117_ = lean_ctor_get(v_it_2113_, 0);
lean_inc(v_currPos_2117_);
v_searcher_2118_ = lean_ctor_get(v_it_2113_, 1);
lean_inc(v_searcher_2118_);
lean_dec_ref_known(v_it_2113_, 2);
v___x_2119_ = lean_apply_5(v_h__1_2105_, v_currPos_2114_, v_searcher_2115_, v_currPos_2117_, v_searcher_2118_, v_out_2116_);
return v___x_2119_;
}
else
{
lean_object* v_currPos_2120_; lean_object* v_searcher_2121_; lean_object* v_out_2122_; lean_object* v___x_2123_; 
lean_dec(v_h__1_2105_);
v_currPos_2120_ = lean_ctor_get(v_x_2103_, 0);
lean_inc(v_currPos_2120_);
v_searcher_2121_ = lean_ctor_get(v_x_2103_, 1);
lean_inc(v_searcher_2121_);
lean_dec_ref_known(v_x_2103_, 2);
v_out_2122_ = lean_ctor_get(v_x_2104_, 1);
lean_inc(v_out_2122_);
lean_dec_ref_known(v_x_2104_, 2);
v___x_2123_ = lean_apply_3(v_h__2_2106_, v_currPos_2120_, v_searcher_2121_, v_out_2122_);
return v___x_2123_;
}
}
case 1:
{
lean_object* v_it_2124_; 
lean_dec(v_h__5_2109_);
lean_dec(v_h__2_2106_);
lean_dec(v_h__1_2105_);
v_it_2124_ = lean_ctor_get(v_x_2104_, 0);
lean_inc(v_it_2124_);
lean_dec_ref_known(v_x_2104_, 1);
if (lean_obj_tag(v_it_2124_) == 0)
{
lean_object* v_currPos_2125_; lean_object* v_searcher_2126_; lean_object* v_currPos_2127_; lean_object* v_searcher_2128_; lean_object* v___x_2129_; 
lean_dec(v_h__4_2108_);
v_currPos_2125_ = lean_ctor_get(v_x_2103_, 0);
lean_inc(v_currPos_2125_);
v_searcher_2126_ = lean_ctor_get(v_x_2103_, 1);
lean_inc(v_searcher_2126_);
lean_dec_ref_known(v_x_2103_, 2);
v_currPos_2127_ = lean_ctor_get(v_it_2124_, 0);
lean_inc(v_currPos_2127_);
v_searcher_2128_ = lean_ctor_get(v_it_2124_, 1);
lean_inc(v_searcher_2128_);
lean_dec_ref_known(v_it_2124_, 2);
v___x_2129_ = lean_apply_4(v_h__3_2107_, v_currPos_2125_, v_searcher_2126_, v_currPos_2127_, v_searcher_2128_);
return v___x_2129_;
}
else
{
lean_object* v_currPos_2130_; lean_object* v_searcher_2131_; lean_object* v___x_2132_; 
lean_dec(v_h__3_2107_);
v_currPos_2130_ = lean_ctor_get(v_x_2103_, 0);
lean_inc(v_currPos_2130_);
v_searcher_2131_ = lean_ctor_get(v_x_2103_, 1);
lean_inc(v_searcher_2131_);
lean_dec_ref_known(v_x_2103_, 2);
v___x_2132_ = lean_apply_2(v_h__4_2108_, v_currPos_2130_, v_searcher_2131_);
return v___x_2132_;
}
}
default: 
{
lean_object* v_currPos_2133_; lean_object* v_searcher_2134_; lean_object* v___x_2135_; 
lean_dec(v_h__4_2108_);
lean_dec(v_h__3_2107_);
lean_dec(v_h__2_2106_);
lean_dec(v_h__1_2105_);
v_currPos_2133_ = lean_ctor_get(v_x_2103_, 0);
lean_inc(v_currPos_2133_);
v_searcher_2134_ = lean_ctor_get(v_x_2103_, 1);
lean_inc(v_searcher_2134_);
lean_dec_ref_known(v_x_2103_, 2);
v___x_2135_ = lean_apply_2(v_h__5_2109_, v_currPos_2133_, v_searcher_2134_);
return v___x_2135_;
}
}
}
else
{
lean_dec(v_h__5_2109_);
lean_dec(v_h__4_2108_);
lean_dec(v_h__3_2107_);
lean_dec(v_h__2_2106_);
lean_dec(v_h__1_2105_);
switch(lean_obj_tag(v_x_2104_))
{
case 0:
{
lean_object* v_it_2136_; lean_object* v_out_2137_; lean_object* v___x_2138_; 
lean_dec(v_h__8_2112_);
lean_dec(v_h__7_2111_);
v_it_2136_ = lean_ctor_get(v_x_2104_, 0);
lean_inc(v_it_2136_);
v_out_2137_ = lean_ctor_get(v_x_2104_, 1);
lean_inc(v_out_2137_);
lean_dec_ref_known(v_x_2104_, 2);
v___x_2138_ = lean_apply_2(v_h__6_2110_, v_it_2136_, v_out_2137_);
return v___x_2138_;
}
case 1:
{
lean_object* v_it_2139_; lean_object* v___x_2140_; 
lean_dec(v_h__8_2112_);
lean_dec(v_h__6_2110_);
v_it_2139_ = lean_ctor_get(v_x_2104_, 0);
lean_inc(v_it_2139_);
lean_dec_ref_known(v_x_2104_, 1);
v___x_2140_ = lean_apply_1(v_h__7_2111_, v_it_2139_);
return v___x_2140_;
}
default: 
{
lean_object* v___x_2141_; lean_object* v___x_2142_; 
lean_dec(v_h__7_2111_);
lean_dec(v_h__6_2110_);
v___x_2141_ = lean_box(0);
v___x_2142_ = lean_apply_1(v_h__8_2112_, v___x_2141_);
return v___x_2142_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___boxed(lean_object** _args){
lean_object* v_00_u03c1_2143_ = _args[0];
lean_object* v_00_u03c1_2144_ = _args[1];
lean_object* v_00_u03c3_2145_ = _args[2];
lean_object* v_inst_2146_ = _args[3];
lean_object* v_m_2147_ = _args[4];
lean_object* v_s_2148_ = _args[5];
lean_object* v_motive_2149_ = _args[6];
lean_object* v_x_2150_ = _args[7];
lean_object* v_x_2151_ = _args[8];
lean_object* v_h__1_2152_ = _args[9];
lean_object* v_h__2_2153_ = _args[10];
lean_object* v_h__3_2154_ = _args[11];
lean_object* v_h__4_2155_ = _args[12];
lean_object* v_h__5_2156_ = _args[13];
lean_object* v_h__6_2157_ = _args[14];
lean_object* v_h__7_2158_ = _args[15];
lean_object* v_h__8_2159_ = _args[16];
_start:
{
lean_object* v_res_2160_; 
v_res_2160_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(v_00_u03c1_2143_, v_00_u03c1_2144_, v_00_u03c3_2145_, v_inst_2146_, v_m_2147_, v_s_2148_, v_motive_2149_, v_x_2150_, v_x_2151_, v_h__1_2152_, v_h__2_2153_, v_h__3_2154_, v_h__4_2155_, v_h__5_2156_, v_h__6_2157_, v_h__7_2158_, v_h__8_2159_);
lean_dec_ref(v_s_2148_);
lean_dec(v_inst_2146_);
lean_dec(v_00_u03c1_2144_);
return v_res_2160_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___redArg(lean_object* v_x_2161_, lean_object* v_h__1_2162_, lean_object* v_h__2_2163_){
_start:
{
if (lean_obj_tag(v_x_2161_) == 0)
{
lean_object* v_currPos_2164_; lean_object* v_searcher_2165_; lean_object* v___x_2166_; 
lean_dec(v_h__2_2163_);
v_currPos_2164_ = lean_ctor_get(v_x_2161_, 0);
lean_inc(v_currPos_2164_);
v_searcher_2165_ = lean_ctor_get(v_x_2161_, 1);
lean_inc(v_searcher_2165_);
lean_dec_ref_known(v_x_2161_, 2);
v___x_2166_ = lean_apply_2(v_h__1_2162_, v_currPos_2164_, v_searcher_2165_);
return v___x_2166_;
}
else
{
lean_object* v___x_2167_; lean_object* v___x_2168_; 
lean_dec(v_h__1_2162_);
v___x_2167_ = lean_box(0);
v___x_2168_ = lean_apply_1(v_h__2_2163_, v___x_2167_);
return v___x_2168_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_2169_, lean_object* v_00_u03c1_2170_, lean_object* v_00_u03c3_2171_, lean_object* v_inst_2172_, lean_object* v_s_2173_, lean_object* v_motive_2174_, lean_object* v_x_2175_, lean_object* v_h__1_2176_, lean_object* v_h__2_2177_){
_start:
{
if (lean_obj_tag(v_x_2175_) == 0)
{
lean_object* v_currPos_2178_; lean_object* v_searcher_2179_; lean_object* v___x_2180_; 
lean_dec(v_h__2_2177_);
v_currPos_2178_ = lean_ctor_get(v_x_2175_, 0);
lean_inc(v_currPos_2178_);
v_searcher_2179_ = lean_ctor_get(v_x_2175_, 1);
lean_inc(v_searcher_2179_);
lean_dec_ref_known(v_x_2175_, 2);
v___x_2180_ = lean_apply_2(v_h__1_2176_, v_currPos_2178_, v_searcher_2179_);
return v___x_2180_;
}
else
{
lean_object* v___x_2181_; lean_object* v___x_2182_; 
lean_dec(v_h__1_2176_);
v___x_2181_ = lean_box(0);
v___x_2182_ = lean_apply_1(v_h__2_2177_, v___x_2181_);
return v___x_2182_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_2183_, lean_object* v_00_u03c1_2184_, lean_object* v_00_u03c3_2185_, lean_object* v_inst_2186_, lean_object* v_s_2187_, lean_object* v_motive_2188_, lean_object* v_x_2189_, lean_object* v_h__1_2190_, lean_object* v_h__2_2191_){
_start:
{
lean_object* v_res_2192_; 
v_res_2192_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(v_00_u03c1_2183_, v_00_u03c1_2184_, v_00_u03c3_2185_, v_inst_2186_, v_s_2187_, v_motive_2188_, v_x_2189_, v_h__1_2190_, v_h__2_2191_);
lean_dec_ref(v_s_2187_);
lean_dec(v_inst_2186_);
lean_dec(v_00_u03c1_2184_);
return v_res_2192_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_2194_; 
v___x_2194_ = lean_box(0);
return v___x_2194_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_2195_){
_start:
{
lean_object* v_res_2196_; 
v_res_2196_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation___redArg();
return v_res_2196_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation(lean_object* v_00_u03c1_2197_, lean_object* v_00_u03c1_2198_, lean_object* v_00_u03c3_2199_, lean_object* v_inst_2200_, lean_object* v_inst_2201_, lean_object* v_s_2202_, lean_object* v_inst_2203_){
_start:
{
lean_object* v___x_2204_; 
v___x_2204_ = lean_box(0);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_2205_, lean_object* v_00_u03c1_2206_, lean_object* v_00_u03c3_2207_, lean_object* v_inst_2208_, lean_object* v_inst_2209_, lean_object* v_s_2210_, lean_object* v_inst_2211_){
_start:
{
lean_object* v_res_2212_; 
v_res_2212_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation(v_00_u03c1_2205_, v_00_u03c1_2206_, v_00_u03c3_2207_, v_inst_2208_, v_inst_2209_, v_s_2210_, v_inst_2211_);
lean_dec_ref(v_s_2210_);
lean_dec(v_inst_2209_);
lean_dec(v_inst_2208_);
lean_dec(v_00_u03c1_2206_);
return v_res_2212_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object* v_toPure_2213_, lean_object* v_recur_2214_, lean_object* v_it_2215_, lean_object* v_____do__lift_2216_){
_start:
{
if (lean_obj_tag(v_____do__lift_2216_) == 0)
{
lean_object* v_a_2217_; lean_object* v___x_2218_; 
lean_dec(v_it_2215_);
lean_dec(v_recur_2214_);
v_a_2217_ = lean_ctor_get(v_____do__lift_2216_, 0);
lean_inc(v_a_2217_);
lean_dec_ref_known(v_____do__lift_2216_, 1);
v___x_2218_ = lean_apply_2(v_toPure_2213_, lean_box(0), v_a_2217_);
return v___x_2218_;
}
else
{
lean_object* v_a_2219_; lean_object* v___x_2220_; 
lean_dec(v_toPure_2213_);
v_a_2219_ = lean_ctor_get(v_____do__lift_2216_, 0);
lean_inc(v_a_2219_);
lean_dec_ref_known(v_____do__lift_2216_, 1);
v___x_2220_ = lean_apply_4(v_recur_2214_, v_it_2215_, v_a_2219_, lean_box(0), lean_box(0));
return v___x_2220_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object* v_toPure_2221_, lean_object* v_recur_2222_, lean_object* v___y_2223_, lean_object* v_acc_2224_, lean_object* v_toBind_2225_, lean_object* v_s_2226_){
_start:
{
switch(lean_obj_tag(v_s_2226_))
{
case 0:
{
lean_object* v_it_2227_; lean_object* v_out_2228_; lean_object* v___f_2229_; lean_object* v___x_2230_; lean_object* v___x_2231_; 
v_it_2227_ = lean_ctor_get(v_s_2226_, 0);
lean_inc(v_it_2227_);
v_out_2228_ = lean_ctor_get(v_s_2226_, 1);
lean_inc(v_out_2228_);
lean_dec_ref_known(v_s_2226_, 2);
v___f_2229_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2229_, 0, v_toPure_2221_);
lean_closure_set(v___f_2229_, 1, v_recur_2222_);
lean_closure_set(v___f_2229_, 2, v_it_2227_);
v___x_2230_ = lean_apply_3(v___y_2223_, v_out_2228_, lean_box(0), v_acc_2224_);
v___x_2231_ = lean_apply_4(v_toBind_2225_, lean_box(0), lean_box(0), v___x_2230_, v___f_2229_);
return v___x_2231_;
}
case 1:
{
lean_object* v_it_2232_; lean_object* v___x_2233_; 
lean_dec(v_toBind_2225_);
lean_dec(v___y_2223_);
lean_dec(v_toPure_2221_);
v_it_2232_ = lean_ctor_get(v_s_2226_, 0);
lean_inc(v_it_2232_);
lean_dec_ref_known(v_s_2226_, 1);
v___x_2233_ = lean_apply_4(v_recur_2222_, v_it_2232_, v_acc_2224_, lean_box(0), lean_box(0));
return v___x_2233_;
}
default: 
{
lean_object* v___x_2234_; 
lean_dec(v_toBind_2225_);
lean_dec(v___y_2223_);
lean_dec(v_recur_2222_);
v___x_2234_ = lean_apply_2(v_toPure_2221_, lean_box(0), v_acc_2224_);
return v___x_2234_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object* v_toPure_2235_, lean_object* v___y_2236_, lean_object* v_toBind_2237_, lean_object* v_inst_2238_, lean_object* v_s_2239_, lean_object* v_toPure_2240_, lean_object* v_lift_2241_, lean_object* v_it_2242_, lean_object* v_acc_2243_, lean_object* v_hP_2244_, lean_object* v_recur_2245_){
_start:
{
lean_object* v___f_2246_; 
v___f_2246_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2246_, 0, v_toPure_2235_);
lean_closure_set(v___f_2246_, 1, v_recur_2245_);
lean_closure_set(v___f_2246_, 2, v___y_2236_);
lean_closure_set(v___f_2246_, 3, v_acc_2243_);
lean_closure_set(v___f_2246_, 4, v_toBind_2237_);
if (lean_obj_tag(v_it_2242_) == 0)
{
lean_object* v_currPos_2247_; lean_object* v_searcher_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2311_; 
v_currPos_2247_ = lean_ctor_get(v_it_2242_, 0);
v_searcher_2248_ = lean_ctor_get(v_it_2242_, 1);
v_isSharedCheck_2311_ = !lean_is_exclusive(v_it_2242_);
if (v_isSharedCheck_2311_ == 0)
{
v___x_2250_ = v_it_2242_;
v_isShared_2251_ = v_isSharedCheck_2311_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_searcher_2248_);
lean_inc(v_currPos_2247_);
lean_dec(v_it_2242_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2311_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v___x_2252_; 
lean_inc_ref(v_s_2239_);
v___x_2252_ = lean_apply_2(v_inst_2238_, v_s_2239_, v_searcher_2248_);
switch(lean_obj_tag(v___x_2252_))
{
case 0:
{
lean_object* v_out_2253_; 
v_out_2253_ = lean_ctor_get(v___x_2252_, 1);
lean_inc(v_out_2253_);
if (lean_obj_tag(v_out_2253_) == 0)
{
lean_object* v_it_2254_; lean_object* v___x_2256_; 
lean_dec_ref_known(v_out_2253_, 2);
lean_dec_ref(v_s_2239_);
v_it_2254_ = lean_ctor_get(v___x_2252_, 0);
lean_inc(v_it_2254_);
lean_dec_ref_known(v___x_2252_, 2);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v_it_2254_);
v___x_2256_ = v___x_2250_;
goto v_reusejp_2255_;
}
else
{
lean_object* v_reuseFailAlloc_2260_; 
v_reuseFailAlloc_2260_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2260_, 0, v_currPos_2247_);
lean_ctor_set(v_reuseFailAlloc_2260_, 1, v_it_2254_);
v___x_2256_ = v_reuseFailAlloc_2260_;
goto v_reusejp_2255_;
}
v_reusejp_2255_:
{
lean_object* v___x_2257_; lean_object* v___x_2258_; lean_object* v___x_2259_; 
v___x_2257_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2257_, 0, v___x_2256_);
v___x_2258_ = lean_apply_2(v_toPure_2240_, lean_box(0), v___x_2257_);
v___x_2259_ = lean_apply_4(v_lift_2241_, lean_box(0), lean_box(0), v___f_2246_, v___x_2258_);
return v___x_2259_;
}
}
else
{
lean_object* v_it_2261_; lean_object* v___x_2263_; uint8_t v_isShared_2264_; uint8_t v_isSharedCheck_2276_; 
v_it_2261_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2276_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2276_ == 0)
{
lean_object* v_unused_2277_; 
v_unused_2277_ = lean_ctor_get(v___x_2252_, 1);
lean_dec(v_unused_2277_);
v___x_2263_ = v___x_2252_;
v_isShared_2264_ = v_isSharedCheck_2276_;
goto v_resetjp_2262_;
}
else
{
lean_inc(v_it_2261_);
lean_dec(v___x_2252_);
v___x_2263_ = lean_box(0);
v_isShared_2264_ = v_isSharedCheck_2276_;
goto v_resetjp_2262_;
}
v_resetjp_2262_:
{
lean_object* v_startPos_2265_; lean_object* v_endPos_2266_; lean_object* v_slice_2267_; lean_object* v_nextIt_2269_; 
v_startPos_2265_ = lean_ctor_get(v_out_2253_, 0);
lean_inc(v_startPos_2265_);
v_endPos_2266_ = lean_ctor_get(v_out_2253_, 1);
lean_inc(v_endPos_2266_);
lean_dec_ref_known(v_out_2253_, 2);
v_slice_2267_ = l_String_Slice_slice_x21(v_s_2239_, v_endPos_2266_, v_currPos_2247_);
lean_dec(v_currPos_2247_);
lean_dec(v_endPos_2266_);
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v_it_2261_);
lean_ctor_set(v___x_2250_, 0, v_startPos_2265_);
v_nextIt_2269_ = v___x_2250_;
goto v_reusejp_2268_;
}
else
{
lean_object* v_reuseFailAlloc_2275_; 
v_reuseFailAlloc_2275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2275_, 0, v_startPos_2265_);
lean_ctor_set(v_reuseFailAlloc_2275_, 1, v_it_2261_);
v_nextIt_2269_ = v_reuseFailAlloc_2275_;
goto v_reusejp_2268_;
}
v_reusejp_2268_:
{
lean_object* v___x_2271_; 
if (v_isShared_2264_ == 0)
{
lean_ctor_set(v___x_2263_, 1, v_slice_2267_);
lean_ctor_set(v___x_2263_, 0, v_nextIt_2269_);
v___x_2271_ = v___x_2263_;
goto v_reusejp_2270_;
}
else
{
lean_object* v_reuseFailAlloc_2274_; 
v_reuseFailAlloc_2274_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2274_, 0, v_nextIt_2269_);
lean_ctor_set(v_reuseFailAlloc_2274_, 1, v_slice_2267_);
v___x_2271_ = v_reuseFailAlloc_2274_;
goto v_reusejp_2270_;
}
v_reusejp_2270_:
{
lean_object* v___x_2272_; lean_object* v___x_2273_; 
v___x_2272_ = lean_apply_2(v_toPure_2240_, lean_box(0), v___x_2271_);
v___x_2273_ = lean_apply_4(v_lift_2241_, lean_box(0), lean_box(0), v___f_2246_, v___x_2272_);
return v___x_2273_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2290_; 
lean_dec_ref(v_s_2239_);
v_it_2278_ = lean_ctor_get(v___x_2252_, 0);
v_isSharedCheck_2290_ = !lean_is_exclusive(v___x_2252_);
if (v_isSharedCheck_2290_ == 0)
{
v___x_2280_ = v___x_2252_;
v_isShared_2281_ = v_isSharedCheck_2290_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_it_2278_);
lean_dec(v___x_2252_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2290_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2283_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 1, v_it_2278_);
v___x_2283_ = v___x_2250_;
goto v_reusejp_2282_;
}
else
{
lean_object* v_reuseFailAlloc_2289_; 
v_reuseFailAlloc_2289_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2289_, 0, v_currPos_2247_);
lean_ctor_set(v_reuseFailAlloc_2289_, 1, v_it_2278_);
v___x_2283_ = v_reuseFailAlloc_2289_;
goto v_reusejp_2282_;
}
v_reusejp_2282_:
{
lean_object* v___x_2285_; 
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 0, v___x_2283_);
v___x_2285_ = v___x_2280_;
goto v_reusejp_2284_;
}
else
{
lean_object* v_reuseFailAlloc_2288_; 
v_reuseFailAlloc_2288_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2288_, 0, v___x_2283_);
v___x_2285_ = v_reuseFailAlloc_2288_;
goto v_reusejp_2284_;
}
v_reusejp_2284_:
{
lean_object* v___x_2286_; lean_object* v___x_2287_; 
v___x_2286_ = lean_apply_2(v_toPure_2240_, lean_box(0), v___x_2285_);
v___x_2287_ = lean_apply_4(v_lift_2241_, lean_box(0), lean_box(0), v___f_2246_, v___x_2286_);
return v___x_2287_;
}
}
}
}
default: 
{
lean_object* v___x_2291_; uint8_t v_decide_2292_; 
lean_del_object(v___x_2250_);
v___x_2291_ = lean_unsigned_to_nat(0u);
v_decide_2292_ = lean_nat_dec_eq(v_currPos_2247_, v___x_2291_);
if (v_decide_2292_ == 0)
{
lean_object* v_str_2293_; lean_object* v_startInclusive_2294_; lean_object* v___x_2296_; uint8_t v_isShared_2297_; uint8_t v_isSharedCheck_2306_; 
v_str_2293_ = lean_ctor_get(v_s_2239_, 0);
v_startInclusive_2294_ = lean_ctor_get(v_s_2239_, 1);
v_isSharedCheck_2306_ = !lean_is_exclusive(v_s_2239_);
if (v_isSharedCheck_2306_ == 0)
{
lean_object* v_unused_2307_; 
v_unused_2307_ = lean_ctor_get(v_s_2239_, 2);
lean_dec(v_unused_2307_);
v___x_2296_ = v_s_2239_;
v_isShared_2297_ = v_isSharedCheck_2306_;
goto v_resetjp_2295_;
}
else
{
lean_inc(v_startInclusive_2294_);
lean_inc(v_str_2293_);
lean_dec(v_s_2239_);
v___x_2296_ = lean_box(0);
v_isShared_2297_ = v_isSharedCheck_2306_;
goto v_resetjp_2295_;
}
v_resetjp_2295_:
{
lean_object* v___x_2298_; lean_object* v_slice_2300_; 
v___x_2298_ = lean_nat_add(v_startInclusive_2294_, v_currPos_2247_);
lean_dec(v_currPos_2247_);
if (v_isShared_2297_ == 0)
{
lean_ctor_set(v___x_2296_, 2, v___x_2298_);
v_slice_2300_ = v___x_2296_;
goto v_reusejp_2299_;
}
else
{
lean_object* v_reuseFailAlloc_2305_; 
v_reuseFailAlloc_2305_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2305_, 0, v_str_2293_);
lean_ctor_set(v_reuseFailAlloc_2305_, 1, v_startInclusive_2294_);
lean_ctor_set(v_reuseFailAlloc_2305_, 2, v___x_2298_);
v_slice_2300_ = v_reuseFailAlloc_2305_;
goto v_reusejp_2299_;
}
v_reusejp_2299_:
{
lean_object* v___x_2301_; lean_object* v___x_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; 
v___x_2301_ = lean_box(1);
v___x_2302_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2302_, 0, v___x_2301_);
lean_ctor_set(v___x_2302_, 1, v_slice_2300_);
v___x_2303_ = lean_apply_2(v_toPure_2240_, lean_box(0), v___x_2302_);
v___x_2304_ = lean_apply_4(v_lift_2241_, lean_box(0), lean_box(0), v___f_2246_, v___x_2303_);
return v___x_2304_;
}
}
}
else
{
lean_object* v___x_2308_; lean_object* v___x_2309_; lean_object* v___x_2310_; 
lean_dec(v_currPos_2247_);
lean_dec_ref(v_s_2239_);
v___x_2308_ = lean_box(2);
v___x_2309_ = lean_apply_2(v_toPure_2240_, lean_box(0), v___x_2308_);
v___x_2310_ = lean_apply_4(v_lift_2241_, lean_box(0), lean_box(0), v___f_2246_, v___x_2309_);
return v___x_2310_;
}
}
}
}
}
else
{
lean_object* v___x_2312_; lean_object* v___x_2313_; lean_object* v___x_2314_; 
lean_dec_ref(v_s_2239_);
lean_dec(v_inst_2238_);
v___x_2312_ = lean_box(2);
v___x_2313_ = lean_apply_2(v_toPure_2240_, lean_box(0), v___x_2312_);
v___x_2314_ = lean_apply_4(v_lift_2241_, lean_box(0), lean_box(0), v___f_2246_, v___x_2313_);
return v___x_2314_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object* v_inst_2315_, lean_object* v_inst_2316_, lean_object* v_s_2317_, lean_object* v_toPure_2318_, lean_object* v_lift_2319_, lean_object* v_00_u03b3_2320_, lean_object* v_Pl_2321_, lean_object* v_it_2322_, lean_object* v_init_2323_, lean_object* v___y_2324_){
_start:
{
lean_object* v_toApplicative_2325_; lean_object* v_toBind_2326_; lean_object* v_toPure_2327_; lean_object* v___f_2328_; lean_object* v___x_2329_; 
v_toApplicative_2325_ = lean_ctor_get(v_inst_2315_, 0);
lean_inc_ref(v_toApplicative_2325_);
v_toBind_2326_ = lean_ctor_get(v_inst_2315_, 1);
lean_inc(v_toBind_2326_);
lean_dec_ref(v_inst_2315_);
v_toPure_2327_ = lean_ctor_get(v_toApplicative_2325_, 1);
lean_inc(v_toPure_2327_);
lean_dec_ref(v_toApplicative_2325_);
v___f_2328_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2), 11, 7);
lean_closure_set(v___f_2328_, 0, v_toPure_2327_);
lean_closure_set(v___f_2328_, 1, v___y_2324_);
lean_closure_set(v___f_2328_, 2, v_toBind_2326_);
lean_closure_set(v___f_2328_, 3, v_inst_2316_);
lean_closure_set(v___f_2328_, 4, v_s_2317_);
lean_closure_set(v___f_2328_, 5, v_toPure_2318_);
lean_closure_set(v___f_2328_, 6, v_lift_2319_);
v___x_2329_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2328_, v_it_2322_, v_init_2323_, lean_box(0));
return v___x_2329_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(lean_object* v_inst_2330_, lean_object* v_s_2331_, lean_object* v_inst_2332_, lean_object* v_inst_2333_){
_start:
{
lean_object* v_toApplicative_2334_; lean_object* v_toPure_2335_; lean_object* v___f_2336_; 
v_toApplicative_2334_ = lean_ctor_get(v_inst_2332_, 0);
lean_inc_ref(v_toApplicative_2334_);
lean_dec_ref(v_inst_2332_);
v_toPure_2335_ = lean_ctor_get(v_toApplicative_2334_, 1);
lean_inc(v_toPure_2335_);
lean_dec_ref(v_toApplicative_2334_);
v___f_2336_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3), 10, 4);
lean_closure_set(v___f_2336_, 0, v_inst_2333_);
lean_closure_set(v___f_2336_, 1, v_inst_2330_);
lean_closure_set(v___f_2336_, 2, v_s_2331_);
lean_closure_set(v___f_2336_, 3, v_toPure_2335_);
return v___f_2336_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(lean_object* v_00_u03c1_2337_, lean_object* v_00_u03c1_2338_, lean_object* v_00_u03c3_2339_, lean_object* v_inst_2340_, lean_object* v_inst_2341_, lean_object* v_m_2342_, lean_object* v_n_2343_, lean_object* v_s_2344_, lean_object* v_inst_2345_, lean_object* v_inst_2346_){
_start:
{
lean_object* v___x_2347_; 
v___x_2347_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(v_inst_2340_, v_s_2344_, v_inst_2345_, v_inst_2346_);
return v___x_2347_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___boxed(lean_object* v_00_u03c1_2348_, lean_object* v_00_u03c1_2349_, lean_object* v_00_u03c3_2350_, lean_object* v_inst_2351_, lean_object* v_inst_2352_, lean_object* v_m_2353_, lean_object* v_n_2354_, lean_object* v_s_2355_, lean_object* v_inst_2356_, lean_object* v_inst_2357_){
_start:
{
lean_object* v_res_2358_; 
v_res_2358_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(v_00_u03c1_2348_, v_00_u03c1_2349_, v_00_u03c3_2350_, v_inst_2351_, v_inst_2352_, v_m_2353_, v_n_2354_, v_s_2355_, v_inst_2356_, v_inst_2357_);
lean_dec(v_inst_2352_);
lean_dec(v_00_u03c1_2349_);
return v_res_2358_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___redArg(lean_object* v_s_2359_, lean_object* v_inst_2360_){
_start:
{
lean_object* v_startInclusive_2361_; lean_object* v_endExclusive_2362_; lean_object* v___x_2363_; lean_object* v___x_2364_; lean_object* v___x_2365_; 
v_startInclusive_2361_ = lean_ctor_get(v_s_2359_, 1);
v_endExclusive_2362_ = lean_ctor_get(v_s_2359_, 2);
v___x_2363_ = lean_nat_sub(v_endExclusive_2362_, v_startInclusive_2361_);
v___x_2364_ = lean_apply_1(v_inst_2360_, v_s_2359_);
v___x_2365_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2365_, 0, v___x_2363_);
lean_ctor_set(v___x_2365_, 1, v___x_2364_);
return v___x_2365_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit(lean_object* v_00_u03c3_2366_, lean_object* v_00_u03c1_2367_, lean_object* v_s_2368_, lean_object* v_pat_2369_, lean_object* v_inst_2370_){
_start:
{
lean_object* v___x_2371_; 
v___x_2371_ = l_String_Slice_revSplit___redArg(v_s_2368_, v_inst_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___boxed(lean_object* v_00_u03c3_2372_, lean_object* v_00_u03c1_2373_, lean_object* v_s_2374_, lean_object* v_pat_2375_, lean_object* v_inst_2376_){
_start:
{
lean_object* v_res_2377_; 
v_res_2377_ = l_String_Slice_revSplit(v_00_u03c3_2372_, v_00_u03c1_2373_, v_s_2374_, v_pat_2375_, v_inst_2376_);
lean_dec(v_pat_2375_);
return v_res_2377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___redArg(lean_object* v_s_2378_, lean_object* v_inst_2379_){
_start:
{
lean_object* v_skipSuffix_x3f_2380_; lean_object* v___x_2381_; 
v_skipSuffix_x3f_2380_ = lean_ctor_get(v_inst_2379_, 0);
lean_inc_ref(v_skipSuffix_x3f_2380_);
lean_dec_ref(v_inst_2379_);
v___x_2381_ = lean_apply_1(v_skipSuffix_x3f_2380_, v_s_2378_);
return v___x_2381_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f(lean_object* v_00_u03c1_2382_, lean_object* v_s_2383_, lean_object* v_pat_2384_, lean_object* v_inst_2385_){
_start:
{
lean_object* v_skipSuffix_x3f_2386_; lean_object* v___x_2387_; 
v_skipSuffix_x3f_2386_ = lean_ctor_get(v_inst_2385_, 0);
lean_inc_ref(v_skipSuffix_x3f_2386_);
lean_dec_ref(v_inst_2385_);
v___x_2387_ = lean_apply_1(v_skipSuffix_x3f_2386_, v_s_2383_);
return v___x_2387_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___boxed(lean_object* v_00_u03c1_2388_, lean_object* v_s_2389_, lean_object* v_pat_2390_, lean_object* v_inst_2391_){
_start:
{
lean_object* v_res_2392_; 
v_res_2392_ = l_String_Slice_skipSuffix_x3f(v_00_u03c1_2388_, v_s_2389_, v_pat_2390_, v_inst_2391_);
lean_dec(v_pat_2390_);
return v_res_2392_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg(lean_object* v_s_2393_, lean_object* v_pos_2394_, lean_object* v_inst_2395_){
_start:
{
lean_object* v_str_2396_; lean_object* v_startInclusive_2397_; lean_object* v___x_2399_; uint8_t v_isShared_2400_; uint8_t v_isSharedCheck_2415_; 
v_str_2396_ = lean_ctor_get(v_s_2393_, 0);
v_startInclusive_2397_ = lean_ctor_get(v_s_2393_, 1);
v_isSharedCheck_2415_ = !lean_is_exclusive(v_s_2393_);
if (v_isSharedCheck_2415_ == 0)
{
lean_object* v_unused_2416_; 
v_unused_2416_ = lean_ctor_get(v_s_2393_, 2);
lean_dec(v_unused_2416_);
v___x_2399_ = v_s_2393_;
v_isShared_2400_ = v_isSharedCheck_2415_;
goto v_resetjp_2398_;
}
else
{
lean_inc(v_startInclusive_2397_);
lean_inc(v_str_2396_);
lean_dec(v_s_2393_);
v___x_2399_ = lean_box(0);
v_isShared_2400_ = v_isSharedCheck_2415_;
goto v_resetjp_2398_;
}
v_resetjp_2398_:
{
lean_object* v_skipSuffix_x3f_2401_; lean_object* v___x_2402_; lean_object* v___x_2404_; 
v_skipSuffix_x3f_2401_ = lean_ctor_get(v_inst_2395_, 0);
lean_inc_ref(v_skipSuffix_x3f_2401_);
lean_dec_ref(v_inst_2395_);
v___x_2402_ = lean_nat_add(v_startInclusive_2397_, v_pos_2394_);
if (v_isShared_2400_ == 0)
{
lean_ctor_set(v___x_2399_, 2, v___x_2402_);
v___x_2404_ = v___x_2399_;
goto v_reusejp_2403_;
}
else
{
lean_object* v_reuseFailAlloc_2414_; 
v_reuseFailAlloc_2414_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2414_, 0, v_str_2396_);
lean_ctor_set(v_reuseFailAlloc_2414_, 1, v_startInclusive_2397_);
lean_ctor_set(v_reuseFailAlloc_2414_, 2, v___x_2402_);
v___x_2404_ = v_reuseFailAlloc_2414_;
goto v_reusejp_2403_;
}
v_reusejp_2403_:
{
lean_object* v___x_2405_; 
v___x_2405_ = lean_apply_1(v_skipSuffix_x3f_2401_, v___x_2404_);
if (lean_obj_tag(v___x_2405_) == 0)
{
return v___x_2405_;
}
else
{
lean_object* v_val_2406_; lean_object* v___x_2408_; uint8_t v_isShared_2409_; uint8_t v_isSharedCheck_2413_; 
v_val_2406_ = lean_ctor_get(v___x_2405_, 0);
v_isSharedCheck_2413_ = !lean_is_exclusive(v___x_2405_);
if (v_isSharedCheck_2413_ == 0)
{
v___x_2408_ = v___x_2405_;
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
else
{
lean_inc(v_val_2406_);
lean_dec(v___x_2405_);
v___x_2408_ = lean_box(0);
v_isShared_2409_ = v_isSharedCheck_2413_;
goto v_resetjp_2407_;
}
v_resetjp_2407_:
{
lean_object* v___x_2411_; 
if (v_isShared_2409_ == 0)
{
v___x_2411_ = v___x_2408_;
goto v_reusejp_2410_;
}
else
{
lean_object* v_reuseFailAlloc_2412_; 
v_reuseFailAlloc_2412_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2412_, 0, v_val_2406_);
v___x_2411_ = v_reuseFailAlloc_2412_;
goto v_reusejp_2410_;
}
v_reusejp_2410_:
{
return v___x_2411_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg___boxed(lean_object* v_s_2417_, lean_object* v_pos_2418_, lean_object* v_inst_2419_){
_start:
{
lean_object* v_res_2420_; 
v_res_2420_ = l_String_Slice_Pos_revSkip_x3f___redArg(v_s_2417_, v_pos_2418_, v_inst_2419_);
lean_dec(v_pos_2418_);
return v_res_2420_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f(lean_object* v_00_u03c1_2421_, lean_object* v_s_2422_, lean_object* v_pos_2423_, lean_object* v_pat_2424_, lean_object* v_inst_2425_){
_start:
{
lean_object* v_str_2426_; lean_object* v_startInclusive_2427_; lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2445_; 
v_str_2426_ = lean_ctor_get(v_s_2422_, 0);
v_startInclusive_2427_ = lean_ctor_get(v_s_2422_, 1);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_s_2422_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; 
v_unused_2446_ = lean_ctor_get(v_s_2422_, 2);
lean_dec(v_unused_2446_);
v___x_2429_ = v_s_2422_;
v_isShared_2430_ = v_isSharedCheck_2445_;
goto v_resetjp_2428_;
}
else
{
lean_inc(v_startInclusive_2427_);
lean_inc(v_str_2426_);
lean_dec(v_s_2422_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2445_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v_skipSuffix_x3f_2431_; lean_object* v___x_2432_; lean_object* v___x_2434_; 
v_skipSuffix_x3f_2431_ = lean_ctor_get(v_inst_2425_, 0);
lean_inc_ref(v_skipSuffix_x3f_2431_);
lean_dec_ref(v_inst_2425_);
v___x_2432_ = lean_nat_add(v_startInclusive_2427_, v_pos_2423_);
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 2, v___x_2432_);
v___x_2434_ = v___x_2429_;
goto v_reusejp_2433_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_str_2426_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v_startInclusive_2427_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v___x_2432_);
v___x_2434_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2433_;
}
v_reusejp_2433_:
{
lean_object* v___x_2435_; 
v___x_2435_ = lean_apply_1(v_skipSuffix_x3f_2431_, v___x_2434_);
if (lean_obj_tag(v___x_2435_) == 0)
{
return v___x_2435_;
}
else
{
lean_object* v_val_2436_; lean_object* v___x_2438_; uint8_t v_isShared_2439_; uint8_t v_isSharedCheck_2443_; 
v_val_2436_ = lean_ctor_get(v___x_2435_, 0);
v_isSharedCheck_2443_ = !lean_is_exclusive(v___x_2435_);
if (v_isSharedCheck_2443_ == 0)
{
v___x_2438_ = v___x_2435_;
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
else
{
lean_inc(v_val_2436_);
lean_dec(v___x_2435_);
v___x_2438_ = lean_box(0);
v_isShared_2439_ = v_isSharedCheck_2443_;
goto v_resetjp_2437_;
}
v_resetjp_2437_:
{
lean_object* v___x_2441_; 
if (v_isShared_2439_ == 0)
{
v___x_2441_ = v___x_2438_;
goto v_reusejp_2440_;
}
else
{
lean_object* v_reuseFailAlloc_2442_; 
v_reuseFailAlloc_2442_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2442_, 0, v_val_2436_);
v___x_2441_ = v_reuseFailAlloc_2442_;
goto v_reusejp_2440_;
}
v_reusejp_2440_:
{
return v___x_2441_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_2447_, lean_object* v_s_2448_, lean_object* v_pos_2449_, lean_object* v_pat_2450_, lean_object* v_inst_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_String_Slice_Pos_revSkip_x3f(v_00_u03c1_2447_, v_s_2448_, v_pos_2449_, v_pat_2450_, v_inst_2451_);
lean_dec(v_pat_2450_);
lean_dec(v_pos_2449_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___redArg(lean_object* v_s_2453_, lean_object* v_inst_2454_){
_start:
{
lean_object* v_skipSuffix_x3f_2455_; lean_object* v___x_2456_; 
v_skipSuffix_x3f_2455_ = lean_ctor_get(v_inst_2454_, 0);
lean_inc_ref(v_skipSuffix_x3f_2455_);
lean_dec_ref(v_inst_2454_);
lean_inc_ref(v_s_2453_);
v___x_2456_ = lean_apply_1(v_skipSuffix_x3f_2455_, v_s_2453_);
if (lean_obj_tag(v___x_2456_) == 0)
{
lean_object* v___x_2457_; 
lean_dec_ref(v_s_2453_);
v___x_2457_ = lean_box(0);
return v___x_2457_;
}
else
{
lean_object* v_val_2458_; lean_object* v___x_2460_; uint8_t v_isShared_2461_; uint8_t v_isSharedCheck_2476_; 
v_val_2458_ = lean_ctor_get(v___x_2456_, 0);
v_isSharedCheck_2476_ = !lean_is_exclusive(v___x_2456_);
if (v_isSharedCheck_2476_ == 0)
{
v___x_2460_ = v___x_2456_;
v_isShared_2461_ = v_isSharedCheck_2476_;
goto v_resetjp_2459_;
}
else
{
lean_inc(v_val_2458_);
lean_dec(v___x_2456_);
v___x_2460_ = lean_box(0);
v_isShared_2461_ = v_isSharedCheck_2476_;
goto v_resetjp_2459_;
}
v_resetjp_2459_:
{
lean_object* v_str_2462_; lean_object* v_startInclusive_2463_; lean_object* v___x_2465_; uint8_t v_isShared_2466_; uint8_t v_isSharedCheck_2474_; 
v_str_2462_ = lean_ctor_get(v_s_2453_, 0);
v_startInclusive_2463_ = lean_ctor_get(v_s_2453_, 1);
v_isSharedCheck_2474_ = !lean_is_exclusive(v_s_2453_);
if (v_isSharedCheck_2474_ == 0)
{
lean_object* v_unused_2475_; 
v_unused_2475_ = lean_ctor_get(v_s_2453_, 2);
lean_dec(v_unused_2475_);
v___x_2465_ = v_s_2453_;
v_isShared_2466_ = v_isSharedCheck_2474_;
goto v_resetjp_2464_;
}
else
{
lean_inc(v_startInclusive_2463_);
lean_inc(v_str_2462_);
lean_dec(v_s_2453_);
v___x_2465_ = lean_box(0);
v_isShared_2466_ = v_isSharedCheck_2474_;
goto v_resetjp_2464_;
}
v_resetjp_2464_:
{
lean_object* v___x_2467_; lean_object* v___x_2469_; 
v___x_2467_ = lean_nat_add(v_startInclusive_2463_, v_val_2458_);
lean_dec(v_val_2458_);
if (v_isShared_2466_ == 0)
{
lean_ctor_set(v___x_2465_, 2, v___x_2467_);
v___x_2469_ = v___x_2465_;
goto v_reusejp_2468_;
}
else
{
lean_object* v_reuseFailAlloc_2473_; 
v_reuseFailAlloc_2473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2473_, 0, v_str_2462_);
lean_ctor_set(v_reuseFailAlloc_2473_, 1, v_startInclusive_2463_);
lean_ctor_set(v_reuseFailAlloc_2473_, 2, v___x_2467_);
v___x_2469_ = v_reuseFailAlloc_2473_;
goto v_reusejp_2468_;
}
v_reusejp_2468_:
{
lean_object* v___x_2471_; 
if (v_isShared_2461_ == 0)
{
lean_ctor_set(v___x_2460_, 0, v___x_2469_);
v___x_2471_ = v___x_2460_;
goto v_reusejp_2470_;
}
else
{
lean_object* v_reuseFailAlloc_2472_; 
v_reuseFailAlloc_2472_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2472_, 0, v___x_2469_);
v___x_2471_ = v_reuseFailAlloc_2472_;
goto v_reusejp_2470_;
}
v_reusejp_2470_:
{
return v___x_2471_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f(lean_object* v_00_u03c1_2477_, lean_object* v_s_2478_, lean_object* v_pat_2479_, lean_object* v_inst_2480_){
_start:
{
lean_object* v_skipSuffix_x3f_2481_; lean_object* v___x_2482_; 
v_skipSuffix_x3f_2481_ = lean_ctor_get(v_inst_2480_, 0);
lean_inc_ref(v_skipSuffix_x3f_2481_);
lean_dec_ref(v_inst_2480_);
lean_inc_ref(v_s_2478_);
v___x_2482_ = lean_apply_1(v_skipSuffix_x3f_2481_, v_s_2478_);
if (lean_obj_tag(v___x_2482_) == 0)
{
lean_object* v___x_2483_; 
lean_dec_ref(v_s_2478_);
v___x_2483_ = lean_box(0);
return v___x_2483_;
}
else
{
lean_object* v_val_2484_; lean_object* v___x_2486_; uint8_t v_isShared_2487_; uint8_t v_isSharedCheck_2502_; 
v_val_2484_ = lean_ctor_get(v___x_2482_, 0);
v_isSharedCheck_2502_ = !lean_is_exclusive(v___x_2482_);
if (v_isSharedCheck_2502_ == 0)
{
v___x_2486_ = v___x_2482_;
v_isShared_2487_ = v_isSharedCheck_2502_;
goto v_resetjp_2485_;
}
else
{
lean_inc(v_val_2484_);
lean_dec(v___x_2482_);
v___x_2486_ = lean_box(0);
v_isShared_2487_ = v_isSharedCheck_2502_;
goto v_resetjp_2485_;
}
v_resetjp_2485_:
{
lean_object* v_str_2488_; lean_object* v_startInclusive_2489_; lean_object* v___x_2491_; uint8_t v_isShared_2492_; uint8_t v_isSharedCheck_2500_; 
v_str_2488_ = lean_ctor_get(v_s_2478_, 0);
v_startInclusive_2489_ = lean_ctor_get(v_s_2478_, 1);
v_isSharedCheck_2500_ = !lean_is_exclusive(v_s_2478_);
if (v_isSharedCheck_2500_ == 0)
{
lean_object* v_unused_2501_; 
v_unused_2501_ = lean_ctor_get(v_s_2478_, 2);
lean_dec(v_unused_2501_);
v___x_2491_ = v_s_2478_;
v_isShared_2492_ = v_isSharedCheck_2500_;
goto v_resetjp_2490_;
}
else
{
lean_inc(v_startInclusive_2489_);
lean_inc(v_str_2488_);
lean_dec(v_s_2478_);
v___x_2491_ = lean_box(0);
v_isShared_2492_ = v_isSharedCheck_2500_;
goto v_resetjp_2490_;
}
v_resetjp_2490_:
{
lean_object* v___x_2493_; lean_object* v___x_2495_; 
v___x_2493_ = lean_nat_add(v_startInclusive_2489_, v_val_2484_);
lean_dec(v_val_2484_);
if (v_isShared_2492_ == 0)
{
lean_ctor_set(v___x_2491_, 2, v___x_2493_);
v___x_2495_ = v___x_2491_;
goto v_reusejp_2494_;
}
else
{
lean_object* v_reuseFailAlloc_2499_; 
v_reuseFailAlloc_2499_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2499_, 0, v_str_2488_);
lean_ctor_set(v_reuseFailAlloc_2499_, 1, v_startInclusive_2489_);
lean_ctor_set(v_reuseFailAlloc_2499_, 2, v___x_2493_);
v___x_2495_ = v_reuseFailAlloc_2499_;
goto v_reusejp_2494_;
}
v_reusejp_2494_:
{
lean_object* v___x_2497_; 
if (v_isShared_2487_ == 0)
{
lean_ctor_set(v___x_2486_, 0, v___x_2495_);
v___x_2497_ = v___x_2486_;
goto v_reusejp_2496_;
}
else
{
lean_object* v_reuseFailAlloc_2498_; 
v_reuseFailAlloc_2498_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2498_, 0, v___x_2495_);
v___x_2497_ = v_reuseFailAlloc_2498_;
goto v_reusejp_2496_;
}
v_reusejp_2496_:
{
return v___x_2497_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_2503_, lean_object* v_s_2504_, lean_object* v_pat_2505_, lean_object* v_inst_2506_){
_start:
{
lean_object* v_res_2507_; 
v_res_2507_ = l_String_Slice_dropSuffix_x3f(v_00_u03c1_2503_, v_s_2504_, v_pat_2505_, v_inst_2506_);
lean_dec(v_pat_2505_);
return v_res_2507_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___redArg(lean_object* v_s_2508_, lean_object* v_inst_2509_){
_start:
{
lean_object* v_skipSuffix_x3f_2510_; lean_object* v___x_2511_; 
v_skipSuffix_x3f_2510_ = lean_ctor_get(v_inst_2509_, 0);
lean_inc_ref(v_skipSuffix_x3f_2510_);
lean_dec_ref(v_inst_2509_);
lean_inc_ref(v_s_2508_);
v___x_2511_ = lean_apply_1(v_skipSuffix_x3f_2510_, v_s_2508_);
if (lean_obj_tag(v___x_2511_) == 0)
{
return v_s_2508_;
}
else
{
lean_object* v_val_2512_; lean_object* v_str_2513_; lean_object* v_startInclusive_2514_; lean_object* v___x_2516_; uint8_t v_isShared_2517_; uint8_t v_isSharedCheck_2522_; 
v_val_2512_ = lean_ctor_get(v___x_2511_, 0);
lean_inc(v_val_2512_);
lean_dec_ref_known(v___x_2511_, 1);
v_str_2513_ = lean_ctor_get(v_s_2508_, 0);
v_startInclusive_2514_ = lean_ctor_get(v_s_2508_, 1);
v_isSharedCheck_2522_ = !lean_is_exclusive(v_s_2508_);
if (v_isSharedCheck_2522_ == 0)
{
lean_object* v_unused_2523_; 
v_unused_2523_ = lean_ctor_get(v_s_2508_, 2);
lean_dec(v_unused_2523_);
v___x_2516_ = v_s_2508_;
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
else
{
lean_inc(v_startInclusive_2514_);
lean_inc(v_str_2513_);
lean_dec(v_s_2508_);
v___x_2516_ = lean_box(0);
v_isShared_2517_ = v_isSharedCheck_2522_;
goto v_resetjp_2515_;
}
v_resetjp_2515_:
{
lean_object* v___x_2518_; lean_object* v___x_2520_; 
v___x_2518_ = lean_nat_add(v_startInclusive_2514_, v_val_2512_);
lean_dec(v_val_2512_);
if (v_isShared_2517_ == 0)
{
lean_ctor_set(v___x_2516_, 2, v___x_2518_);
v___x_2520_ = v___x_2516_;
goto v_reusejp_2519_;
}
else
{
lean_object* v_reuseFailAlloc_2521_; 
v_reuseFailAlloc_2521_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2521_, 0, v_str_2513_);
lean_ctor_set(v_reuseFailAlloc_2521_, 1, v_startInclusive_2514_);
lean_ctor_set(v_reuseFailAlloc_2521_, 2, v___x_2518_);
v___x_2520_ = v_reuseFailAlloc_2521_;
goto v_reusejp_2519_;
}
v_reusejp_2519_:
{
return v___x_2520_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix(lean_object* v_00_u03c1_2524_, lean_object* v_s_2525_, lean_object* v_pat_2526_, lean_object* v_inst_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_String_Slice_dropSuffix___redArg(v_s_2525_, v_inst_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___boxed(lean_object* v_00_u03c1_2529_, lean_object* v_s_2530_, lean_object* v_pat_2531_, lean_object* v_inst_2532_){
_start:
{
lean_object* v_res_2533_; 
v_res_2533_ = l_String_Slice_dropSuffix(v_00_u03c1_2529_, v_s_2530_, v_pat_2531_, v_inst_2532_);
lean_dec(v_pat_2531_);
return v_res_2533_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object* v_s_2534_, lean_object* v_pos_2535_, lean_object* v_inst_2536_){
_start:
{
lean_object* v_str_2537_; lean_object* v_startInclusive_2538_; lean_object* v_skipSuffix_x3f_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; 
v_str_2537_ = lean_ctor_get(v_s_2534_, 0);
v_startInclusive_2538_ = lean_ctor_get(v_s_2534_, 1);
v_skipSuffix_x3f_2539_ = lean_ctor_get(v_inst_2536_, 0);
v___x_2540_ = lean_nat_add(v_startInclusive_2538_, v_pos_2535_);
lean_inc(v_startInclusive_2538_);
lean_inc_ref(v_str_2537_);
v___x_2541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2541_, 0, v_str_2537_);
lean_ctor_set(v___x_2541_, 1, v_startInclusive_2538_);
lean_ctor_set(v___x_2541_, 2, v___x_2540_);
lean_inc_ref(v_skipSuffix_x3f_2539_);
v___x_2542_ = lean_apply_1(v_skipSuffix_x3f_2539_, v___x_2541_);
if (lean_obj_tag(v___x_2542_) == 0)
{
lean_dec_ref(v_inst_2536_);
return v_pos_2535_;
}
else
{
lean_object* v_val_2543_; lean_object* v___x_2544_; lean_object* v___x_2545_; uint8_t v___x_2546_; 
v_val_2543_ = lean_ctor_get(v___x_2542_, 0);
lean_inc(v_val_2543_);
lean_dec_ref_known(v___x_2542_, 1);
v___x_2544_ = lean_unsigned_to_nat(1u);
v___x_2545_ = lean_nat_add(v_val_2543_, v___x_2544_);
v___x_2546_ = lean_nat_dec_le(v___x_2545_, v_pos_2535_);
lean_dec(v___x_2545_);
if (v___x_2546_ == 0)
{
lean_dec(v_val_2543_);
lean_dec_ref(v_inst_2536_);
return v_pos_2535_;
}
else
{
lean_dec(v_pos_2535_);
v_pos_2535_ = v_val_2543_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg___boxed(lean_object* v_s_2548_, lean_object* v_pos_2549_, lean_object* v_inst_2550_){
_start:
{
lean_object* v_res_2551_; 
v_res_2551_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2548_, v_pos_2549_, v_inst_2550_);
lean_dec_ref(v_s_2548_);
return v_res_2551_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile(lean_object* v_00_u03c1_2552_, lean_object* v_s_2553_, lean_object* v_pos_2554_, lean_object* v_pat_2555_, lean_object* v_inst_2556_){
_start:
{
lean_object* v___x_2557_; 
v___x_2557_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2553_, v_pos_2554_, v_inst_2556_);
return v___x_2557_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_2558_, lean_object* v_s_2559_, lean_object* v_pos_2560_, lean_object* v_pat_2561_, lean_object* v_inst_2562_){
_start:
{
lean_object* v_res_2563_; 
v_res_2563_ = l_String_Slice_Pos_revSkipWhile(v_00_u03c1_2558_, v_s_2559_, v_pos_2560_, v_pat_2561_, v_inst_2562_);
lean_dec(v_pat_2561_);
lean_dec_ref(v_s_2559_);
return v_res_2563_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg(lean_object* v_s_2564_, lean_object* v_inst_2565_){
_start:
{
lean_object* v_startInclusive_2566_; lean_object* v_endExclusive_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; 
v_startInclusive_2566_ = lean_ctor_get(v_s_2564_, 1);
v_endExclusive_2567_ = lean_ctor_get(v_s_2564_, 2);
v___x_2568_ = lean_nat_sub(v_endExclusive_2567_, v_startInclusive_2566_);
v___x_2569_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2564_, v___x_2568_, v_inst_2565_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg___boxed(lean_object* v_s_2570_, lean_object* v_inst_2571_){
_start:
{
lean_object* v_res_2572_; 
v_res_2572_ = l_String_Slice_skipSuffixWhile___redArg(v_s_2570_, v_inst_2571_);
lean_dec_ref(v_s_2570_);
return v_res_2572_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile(lean_object* v_00_u03c1_2573_, lean_object* v_s_2574_, lean_object* v_pat_2575_, lean_object* v_inst_2576_){
_start:
{
lean_object* v_startInclusive_2577_; lean_object* v_endExclusive_2578_; lean_object* v___x_2579_; lean_object* v___x_2580_; 
v_startInclusive_2577_ = lean_ctor_get(v_s_2574_, 1);
v_endExclusive_2578_ = lean_ctor_get(v_s_2574_, 2);
v___x_2579_ = lean_nat_sub(v_endExclusive_2578_, v_startInclusive_2577_);
v___x_2580_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2574_, v___x_2579_, v_inst_2576_);
return v___x_2580_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___boxed(lean_object* v_00_u03c1_2581_, lean_object* v_s_2582_, lean_object* v_pat_2583_, lean_object* v_inst_2584_){
_start:
{
lean_object* v_res_2585_; 
v_res_2585_ = l_String_Slice_skipSuffixWhile(v_00_u03c1_2581_, v_s_2582_, v_pat_2583_, v_inst_2584_);
lean_dec(v_pat_2583_);
lean_dec_ref(v_s_2582_);
return v_res_2585_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_revAll___redArg(lean_object* v_s_2586_, lean_object* v_inst_2587_){
_start:
{
lean_object* v_startInclusive_2588_; lean_object* v_endExclusive_2589_; lean_object* v___x_2590_; lean_object* v___x_2591_; lean_object* v___x_2592_; uint8_t v_decide_2593_; 
v_startInclusive_2588_ = lean_ctor_get(v_s_2586_, 1);
v_endExclusive_2589_ = lean_ctor_get(v_s_2586_, 2);
v___x_2590_ = lean_nat_sub(v_endExclusive_2589_, v_startInclusive_2588_);
v___x_2591_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2586_, v___x_2590_, v_inst_2587_);
v___x_2592_ = lean_unsigned_to_nat(0u);
v_decide_2593_ = lean_nat_dec_eq(v___x_2591_, v___x_2592_);
lean_dec(v___x_2591_);
return v_decide_2593_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___redArg___boxed(lean_object* v_s_2594_, lean_object* v_inst_2595_){
_start:
{
uint8_t v_res_2596_; lean_object* v_r_2597_; 
v_res_2596_ = l_String_Slice_revAll___redArg(v_s_2594_, v_inst_2595_);
lean_dec_ref(v_s_2594_);
v_r_2597_ = lean_box(v_res_2596_);
return v_r_2597_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_revAll(lean_object* v_00_u03c1_2598_, lean_object* v_s_2599_, lean_object* v_pat_2600_, lean_object* v_inst_2601_){
_start:
{
lean_object* v_startInclusive_2602_; lean_object* v_endExclusive_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2606_; uint8_t v_decide_2607_; 
v_startInclusive_2602_ = lean_ctor_get(v_s_2599_, 1);
v_endExclusive_2603_ = lean_ctor_get(v_s_2599_, 2);
v___x_2604_ = lean_nat_sub(v_endExclusive_2603_, v_startInclusive_2602_);
v___x_2605_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2599_, v___x_2604_, v_inst_2601_);
v___x_2606_ = lean_unsigned_to_nat(0u);
v_decide_2607_ = lean_nat_dec_eq(v___x_2605_, v___x_2606_);
lean_dec(v___x_2605_);
return v_decide_2607_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___boxed(lean_object* v_00_u03c1_2608_, lean_object* v_s_2609_, lean_object* v_pat_2610_, lean_object* v_inst_2611_){
_start:
{
uint8_t v_res_2612_; lean_object* v_r_2613_; 
v_res_2612_ = l_String_Slice_revAll(v_00_u03c1_2608_, v_s_2609_, v_pat_2610_, v_inst_2611_);
lean_dec(v_pat_2610_);
lean_dec_ref(v_s_2609_);
v_r_2613_ = lean_box(v_res_2612_);
return v_r_2613_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object* v_s_2614_, lean_object* v_inst_2615_){
_start:
{
lean_object* v_str_2616_; lean_object* v_startInclusive_2617_; lean_object* v_endExclusive_2618_; lean_object* v___x_2619_; lean_object* v___x_2620_; lean_object* v___x_2622_; uint8_t v_isShared_2623_; uint8_t v_isSharedCheck_2628_; 
v_str_2616_ = lean_ctor_get(v_s_2614_, 0);
lean_inc_ref(v_str_2616_);
v_startInclusive_2617_ = lean_ctor_get(v_s_2614_, 1);
lean_inc(v_startInclusive_2617_);
v_endExclusive_2618_ = lean_ctor_get(v_s_2614_, 2);
v___x_2619_ = lean_nat_sub(v_endExclusive_2618_, v_startInclusive_2617_);
v___x_2620_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2614_, v___x_2619_, v_inst_2615_);
v_isSharedCheck_2628_ = !lean_is_exclusive(v_s_2614_);
if (v_isSharedCheck_2628_ == 0)
{
lean_object* v_unused_2629_; lean_object* v_unused_2630_; lean_object* v_unused_2631_; 
v_unused_2629_ = lean_ctor_get(v_s_2614_, 2);
lean_dec(v_unused_2629_);
v_unused_2630_ = lean_ctor_get(v_s_2614_, 1);
lean_dec(v_unused_2630_);
v_unused_2631_ = lean_ctor_get(v_s_2614_, 0);
lean_dec(v_unused_2631_);
v___x_2622_ = v_s_2614_;
v_isShared_2623_ = v_isSharedCheck_2628_;
goto v_resetjp_2621_;
}
else
{
lean_dec(v_s_2614_);
v___x_2622_ = lean_box(0);
v_isShared_2623_ = v_isSharedCheck_2628_;
goto v_resetjp_2621_;
}
v_resetjp_2621_:
{
lean_object* v___x_2624_; lean_object* v___x_2626_; 
v___x_2624_ = lean_nat_add(v_startInclusive_2617_, v___x_2620_);
lean_dec(v___x_2620_);
if (v_isShared_2623_ == 0)
{
lean_ctor_set(v___x_2622_, 2, v___x_2624_);
v___x_2626_ = v___x_2622_;
goto v_reusejp_2625_;
}
else
{
lean_object* v_reuseFailAlloc_2627_; 
v_reuseFailAlloc_2627_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2627_, 0, v_str_2616_);
lean_ctor_set(v_reuseFailAlloc_2627_, 1, v_startInclusive_2617_);
lean_ctor_set(v_reuseFailAlloc_2627_, 2, v___x_2624_);
v___x_2626_ = v_reuseFailAlloc_2627_;
goto v_reusejp_2625_;
}
v_reusejp_2625_:
{
return v___x_2626_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object* v_00_u03c1_2632_, lean_object* v_s_2633_, lean_object* v_pat_2634_, lean_object* v_inst_2635_){
_start:
{
lean_object* v_str_2636_; lean_object* v_startInclusive_2637_; lean_object* v_endExclusive_2638_; lean_object* v___x_2639_; lean_object* v___x_2640_; lean_object* v___x_2642_; uint8_t v_isShared_2643_; uint8_t v_isSharedCheck_2648_; 
v_str_2636_ = lean_ctor_get(v_s_2633_, 0);
lean_inc_ref(v_str_2636_);
v_startInclusive_2637_ = lean_ctor_get(v_s_2633_, 1);
lean_inc(v_startInclusive_2637_);
v_endExclusive_2638_ = lean_ctor_get(v_s_2633_, 2);
v___x_2639_ = lean_nat_sub(v_endExclusive_2638_, v_startInclusive_2637_);
v___x_2640_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2633_, v___x_2639_, v_inst_2635_);
v_isSharedCheck_2648_ = !lean_is_exclusive(v_s_2633_);
if (v_isSharedCheck_2648_ == 0)
{
lean_object* v_unused_2649_; lean_object* v_unused_2650_; lean_object* v_unused_2651_; 
v_unused_2649_ = lean_ctor_get(v_s_2633_, 2);
lean_dec(v_unused_2649_);
v_unused_2650_ = lean_ctor_get(v_s_2633_, 1);
lean_dec(v_unused_2650_);
v_unused_2651_ = lean_ctor_get(v_s_2633_, 0);
lean_dec(v_unused_2651_);
v___x_2642_ = v_s_2633_;
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
else
{
lean_dec(v_s_2633_);
v___x_2642_ = lean_box(0);
v_isShared_2643_ = v_isSharedCheck_2648_;
goto v_resetjp_2641_;
}
v_resetjp_2641_:
{
lean_object* v___x_2644_; lean_object* v___x_2646_; 
v___x_2644_ = lean_nat_add(v_startInclusive_2637_, v___x_2640_);
lean_dec(v___x_2640_);
if (v_isShared_2643_ == 0)
{
lean_ctor_set(v___x_2642_, 2, v___x_2644_);
v___x_2646_ = v___x_2642_;
goto v_reusejp_2645_;
}
else
{
lean_object* v_reuseFailAlloc_2647_; 
v_reuseFailAlloc_2647_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2647_, 0, v_str_2636_);
lean_ctor_set(v_reuseFailAlloc_2647_, 1, v_startInclusive_2637_);
lean_ctor_set(v_reuseFailAlloc_2647_, 2, v___x_2644_);
v___x_2646_ = v_reuseFailAlloc_2647_;
goto v_reusejp_2645_;
}
v_reusejp_2645_:
{
return v___x_2646_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object* v_00_u03c1_2652_, lean_object* v_s_2653_, lean_object* v_pat_2654_, lean_object* v_inst_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_String_Slice_dropEndWhile(v_00_u03c1_2652_, v_s_2653_, v_pat_2654_, v_inst_2655_);
lean_dec(v_pat_2654_);
return v_res_2656_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiEnd___closed__0(void){
_start:
{
lean_object* v___x_2657_; lean_object* v___x_2658_; 
v___x_2657_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_2658_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_2657_);
return v___x_2658_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object* v_s_2659_){
_start:
{
lean_object* v___x_2660_; lean_object* v_str_2661_; lean_object* v_startInclusive_2662_; lean_object* v_endExclusive_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2667_; uint8_t v_isShared_2668_; uint8_t v_isSharedCheck_2673_; 
v___x_2660_ = lean_obj_once(&l_String_Slice_trimAsciiEnd___closed__0, &l_String_Slice_trimAsciiEnd___closed__0_once, _init_l_String_Slice_trimAsciiEnd___closed__0);
v_str_2661_ = lean_ctor_get(v_s_2659_, 0);
lean_inc_ref(v_str_2661_);
v_startInclusive_2662_ = lean_ctor_get(v_s_2659_, 1);
lean_inc(v_startInclusive_2662_);
v_endExclusive_2663_ = lean_ctor_get(v_s_2659_, 2);
v___x_2664_ = lean_nat_sub(v_endExclusive_2663_, v_startInclusive_2662_);
v___x_2665_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2659_, v___x_2664_, v___x_2660_);
v_isSharedCheck_2673_ = !lean_is_exclusive(v_s_2659_);
if (v_isSharedCheck_2673_ == 0)
{
lean_object* v_unused_2674_; lean_object* v_unused_2675_; lean_object* v_unused_2676_; 
v_unused_2674_ = lean_ctor_get(v_s_2659_, 2);
lean_dec(v_unused_2674_);
v_unused_2675_ = lean_ctor_get(v_s_2659_, 1);
lean_dec(v_unused_2675_);
v_unused_2676_ = lean_ctor_get(v_s_2659_, 0);
lean_dec(v_unused_2676_);
v___x_2667_ = v_s_2659_;
v_isShared_2668_ = v_isSharedCheck_2673_;
goto v_resetjp_2666_;
}
else
{
lean_dec(v_s_2659_);
v___x_2667_ = lean_box(0);
v_isShared_2668_ = v_isSharedCheck_2673_;
goto v_resetjp_2666_;
}
v_resetjp_2666_:
{
lean_object* v___x_2669_; lean_object* v___x_2671_; 
v___x_2669_ = lean_nat_add(v_startInclusive_2662_, v___x_2665_);
lean_dec(v___x_2665_);
if (v_isShared_2668_ == 0)
{
lean_ctor_set(v___x_2667_, 2, v___x_2669_);
v___x_2671_ = v___x_2667_;
goto v_reusejp_2670_;
}
else
{
lean_object* v_reuseFailAlloc_2672_; 
v_reuseFailAlloc_2672_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2672_, 0, v_str_2661_);
lean_ctor_set(v_reuseFailAlloc_2672_, 1, v_startInclusive_2662_);
lean_ctor_set(v_reuseFailAlloc_2672_, 2, v___x_2669_);
v___x_2671_ = v_reuseFailAlloc_2672_;
goto v_reusejp_2670_;
}
v_reusejp_2670_:
{
return v___x_2671_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___redArg(lean_object* v_s_2677_, lean_object* v_inst_2678_){
_start:
{
lean_object* v_str_2679_; lean_object* v_startInclusive_2680_; lean_object* v_endExclusive_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; lean_object* v___x_2685_; uint8_t v_isShared_2686_; uint8_t v_isSharedCheck_2691_; 
v_str_2679_ = lean_ctor_get(v_s_2677_, 0);
lean_inc_ref(v_str_2679_);
v_startInclusive_2680_ = lean_ctor_get(v_s_2677_, 1);
lean_inc(v_startInclusive_2680_);
v_endExclusive_2681_ = lean_ctor_get(v_s_2677_, 2);
lean_inc(v_endExclusive_2681_);
v___x_2682_ = lean_nat_sub(v_endExclusive_2681_, v_startInclusive_2680_);
v___x_2683_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2677_, v___x_2682_, v_inst_2678_);
v_isSharedCheck_2691_ = !lean_is_exclusive(v_s_2677_);
if (v_isSharedCheck_2691_ == 0)
{
lean_object* v_unused_2692_; lean_object* v_unused_2693_; lean_object* v_unused_2694_; 
v_unused_2692_ = lean_ctor_get(v_s_2677_, 2);
lean_dec(v_unused_2692_);
v_unused_2693_ = lean_ctor_get(v_s_2677_, 1);
lean_dec(v_unused_2693_);
v_unused_2694_ = lean_ctor_get(v_s_2677_, 0);
lean_dec(v_unused_2694_);
v___x_2685_ = v_s_2677_;
v_isShared_2686_ = v_isSharedCheck_2691_;
goto v_resetjp_2684_;
}
else
{
lean_dec(v_s_2677_);
v___x_2685_ = lean_box(0);
v_isShared_2686_ = v_isSharedCheck_2691_;
goto v_resetjp_2684_;
}
v_resetjp_2684_:
{
lean_object* v___x_2687_; lean_object* v___x_2689_; 
v___x_2687_ = lean_nat_add(v_startInclusive_2680_, v___x_2683_);
lean_dec(v___x_2683_);
lean_dec(v_startInclusive_2680_);
if (v_isShared_2686_ == 0)
{
lean_ctor_set(v___x_2685_, 1, v___x_2687_);
v___x_2689_ = v___x_2685_;
goto v_reusejp_2688_;
}
else
{
lean_object* v_reuseFailAlloc_2690_; 
v_reuseFailAlloc_2690_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2690_, 0, v_str_2679_);
lean_ctor_set(v_reuseFailAlloc_2690_, 1, v___x_2687_);
lean_ctor_set(v_reuseFailAlloc_2690_, 2, v_endExclusive_2681_);
v___x_2689_ = v_reuseFailAlloc_2690_;
goto v_reusejp_2688_;
}
v_reusejp_2688_:
{
return v___x_2689_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile(lean_object* v_00_u03c1_2695_, lean_object* v_s_2696_, lean_object* v_pat_2697_, lean_object* v_inst_2698_){
_start:
{
lean_object* v_str_2699_; lean_object* v_startInclusive_2700_; lean_object* v_endExclusive_2701_; lean_object* v___x_2702_; lean_object* v___x_2703_; lean_object* v___x_2705_; uint8_t v_isShared_2706_; uint8_t v_isSharedCheck_2711_; 
v_str_2699_ = lean_ctor_get(v_s_2696_, 0);
lean_inc_ref(v_str_2699_);
v_startInclusive_2700_ = lean_ctor_get(v_s_2696_, 1);
lean_inc(v_startInclusive_2700_);
v_endExclusive_2701_ = lean_ctor_get(v_s_2696_, 2);
lean_inc(v_endExclusive_2701_);
v___x_2702_ = lean_nat_sub(v_endExclusive_2701_, v_startInclusive_2700_);
v___x_2703_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2696_, v___x_2702_, v_inst_2698_);
v_isSharedCheck_2711_ = !lean_is_exclusive(v_s_2696_);
if (v_isSharedCheck_2711_ == 0)
{
lean_object* v_unused_2712_; lean_object* v_unused_2713_; lean_object* v_unused_2714_; 
v_unused_2712_ = lean_ctor_get(v_s_2696_, 2);
lean_dec(v_unused_2712_);
v_unused_2713_ = lean_ctor_get(v_s_2696_, 1);
lean_dec(v_unused_2713_);
v_unused_2714_ = lean_ctor_get(v_s_2696_, 0);
lean_dec(v_unused_2714_);
v___x_2705_ = v_s_2696_;
v_isShared_2706_ = v_isSharedCheck_2711_;
goto v_resetjp_2704_;
}
else
{
lean_dec(v_s_2696_);
v___x_2705_ = lean_box(0);
v_isShared_2706_ = v_isSharedCheck_2711_;
goto v_resetjp_2704_;
}
v_resetjp_2704_:
{
lean_object* v___x_2707_; lean_object* v___x_2709_; 
v___x_2707_ = lean_nat_add(v_startInclusive_2700_, v___x_2703_);
lean_dec(v___x_2703_);
lean_dec(v_startInclusive_2700_);
if (v_isShared_2706_ == 0)
{
lean_ctor_set(v___x_2705_, 1, v___x_2707_);
v___x_2709_ = v___x_2705_;
goto v_reusejp_2708_;
}
else
{
lean_object* v_reuseFailAlloc_2710_; 
v_reuseFailAlloc_2710_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2710_, 0, v_str_2699_);
lean_ctor_set(v_reuseFailAlloc_2710_, 1, v___x_2707_);
lean_ctor_set(v_reuseFailAlloc_2710_, 2, v_endExclusive_2701_);
v___x_2709_ = v_reuseFailAlloc_2710_;
goto v_reusejp_2708_;
}
v_reusejp_2708_:
{
return v___x_2709_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___boxed(lean_object* v_00_u03c1_2715_, lean_object* v_s_2716_, lean_object* v_pat_2717_, lean_object* v_inst_2718_){
_start:
{
lean_object* v_res_2719_; 
v_res_2719_ = l_String_Slice_takeEndWhile(v_00_u03c1_2715_, v_s_2716_, v_pat_2717_, v_inst_2718_);
lean_dec(v_pat_2717_);
return v_res_2719_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___redArg(lean_object* v_inst_2720_, lean_object* v_s_2721_, lean_object* v_inst_2722_){
_start:
{
lean_object* v___f_2723_; lean_object* v_searcher_2724_; lean_object* v___x_2725_; lean_object* v___f_2726_; lean_object* v___x_2727_; 
v___f_2723_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_2721_);
v_searcher_2724_ = lean_apply_1(v_inst_2722_, v_s_2721_);
v___x_2725_ = lean_box(0);
v___f_2726_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_2727_ = lean_apply_7(v_inst_2720_, v_s_2721_, v___f_2723_, lean_box(0), lean_box(0), v_searcher_2724_, v___x_2725_, v___f_2726_);
return v___x_2727_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f(lean_object* v_00_u03c3_2728_, lean_object* v_inst_2729_, lean_object* v_inst_2730_, lean_object* v_00_u03c1_2731_, lean_object* v_s_2732_, lean_object* v_pat_2733_, lean_object* v_inst_2734_){
_start:
{
lean_object* v___x_2735_; 
v___x_2735_ = l_String_Slice_revFind_x3f___redArg(v_inst_2730_, v_s_2732_, v_inst_2734_);
return v___x_2735_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___boxed(lean_object* v_00_u03c3_2736_, lean_object* v_inst_2737_, lean_object* v_inst_2738_, lean_object* v_00_u03c1_2739_, lean_object* v_s_2740_, lean_object* v_pat_2741_, lean_object* v_inst_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_String_Slice_revFind_x3f(v_00_u03c3_2736_, v_inst_2737_, v_inst_2738_, v_00_u03c1_2739_, v_s_2740_, v_pat_2741_, v_inst_2742_);
lean_dec(v_pat_2741_);
lean_dec(v_inst_2737_);
return v_res_2743_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(lean_object* v_s_2744_, lean_object* v_pos_2745_){
_start:
{
lean_object* v_str_2746_; lean_object* v_startInclusive_2747_; lean_object* v_endExclusive_2748_; lean_object* v___x_2749_; lean_object* v___x_2758_; lean_object* v___x_2759_; uint8_t v_decide_2760_; 
v_str_2746_ = lean_ctor_get(v_s_2744_, 0);
v_startInclusive_2747_ = lean_ctor_get(v_s_2744_, 1);
v_endExclusive_2748_ = lean_ctor_get(v_s_2744_, 2);
v___x_2749_ = lean_nat_add(v_startInclusive_2747_, v_pos_2745_);
v___x_2758_ = lean_unsigned_to_nat(0u);
v___x_2759_ = lean_nat_sub(v_endExclusive_2748_, v___x_2749_);
v_decide_2760_ = lean_nat_dec_eq(v___x_2758_, v___x_2759_);
lean_dec(v___x_2759_);
if (v_decide_2760_ == 0)
{
uint32_t v___x_2761_; uint32_t v___x_2762_; uint8_t v___x_2763_; 
v___x_2761_ = lean_string_utf8_get_fast(v_str_2746_, v___x_2749_);
v___x_2762_ = 32;
v___x_2763_ = lean_uint32_dec_eq(v___x_2761_, v___x_2762_);
if (v___x_2763_ == 0)
{
uint32_t v___x_2764_; uint8_t v___x_2765_; 
v___x_2764_ = 9;
v___x_2765_ = lean_uint32_dec_eq(v___x_2761_, v___x_2764_);
if (v___x_2765_ == 0)
{
uint32_t v___x_2766_; uint8_t v___x_2767_; 
v___x_2766_ = 13;
v___x_2767_ = lean_uint32_dec_eq(v___x_2761_, v___x_2766_);
if (v___x_2767_ == 0)
{
uint32_t v___x_2768_; uint8_t v___x_2769_; 
v___x_2768_ = 10;
v___x_2769_ = lean_uint32_dec_eq(v___x_2761_, v___x_2768_);
if (v___x_2769_ == 0)
{
lean_dec(v___x_2749_);
return v_pos_2745_;
}
else
{
goto v___jp_2750_;
}
}
else
{
goto v___jp_2750_;
}
}
else
{
goto v___jp_2750_;
}
}
else
{
goto v___jp_2750_;
}
}
else
{
lean_dec(v___x_2749_);
return v_pos_2745_;
}
v___jp_2750_:
{
lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2753_; lean_object* v___x_2754_; lean_object* v___x_2755_; uint8_t v___x_2756_; 
v___x_2751_ = lean_string_utf8_next_fast(v_str_2746_, v___x_2749_);
v___x_2752_ = lean_nat_sub(v___x_2751_, v___x_2749_);
lean_dec(v___x_2749_);
v___x_2753_ = lean_nat_add(v_pos_2745_, v___x_2752_);
lean_dec(v___x_2752_);
v___x_2754_ = lean_unsigned_to_nat(1u);
v___x_2755_ = lean_nat_add(v_pos_2745_, v___x_2754_);
v___x_2756_ = lean_nat_dec_le(v___x_2755_, v___x_2753_);
lean_dec(v___x_2755_);
if (v___x_2756_ == 0)
{
lean_dec(v___x_2753_);
return v_pos_2745_;
}
else
{
lean_dec(v_pos_2745_);
v_pos_2745_ = v___x_2753_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0___boxed(lean_object* v_s_2770_, lean_object* v_pos_2771_){
_start:
{
lean_object* v_res_2772_; 
v_res_2772_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2770_, v_pos_2771_);
lean_dec_ref(v_s_2770_);
return v_res_2772_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(lean_object* v_s_2773_, lean_object* v_pos_2774_){
_start:
{
lean_object* v_str_2775_; lean_object* v_startInclusive_2776_; lean_object* v___x_2777_; lean_object* v___x_2778_; lean_object* v___x_2779_; uint8_t v_decide_2780_; 
v_str_2775_ = lean_ctor_get(v_s_2773_, 0);
v_startInclusive_2776_ = lean_ctor_get(v_s_2773_, 1);
v___x_2777_ = lean_nat_add(v_startInclusive_2776_, v_pos_2774_);
v___x_2778_ = lean_nat_sub(v___x_2777_, v_startInclusive_2776_);
v___x_2779_ = lean_unsigned_to_nat(0u);
v_decide_2780_ = lean_nat_dec_eq(v___x_2778_, v___x_2779_);
if (v_decide_2780_ == 0)
{
lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2783_; lean_object* v___x_2784_; lean_object* v___x_2789_; uint32_t v___x_2790_; uint32_t v___x_2791_; uint8_t v___x_2792_; 
lean_inc(v_startInclusive_2776_);
lean_inc_ref(v_str_2775_);
v___x_2781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2781_, 0, v_str_2775_);
lean_ctor_set(v___x_2781_, 1, v_startInclusive_2776_);
lean_ctor_set(v___x_2781_, 2, v___x_2777_);
v___x_2782_ = lean_unsigned_to_nat(1u);
v___x_2783_ = lean_nat_sub(v___x_2778_, v___x_2782_);
lean_dec(v___x_2778_);
v___x_2784_ = l_String_Slice_posLE(v___x_2781_, v___x_2783_);
lean_dec_ref_known(v___x_2781_, 3);
v___x_2789_ = lean_nat_add(v_startInclusive_2776_, v___x_2784_);
v___x_2790_ = lean_string_utf8_get_fast(v_str_2775_, v___x_2789_);
lean_dec(v___x_2789_);
v___x_2791_ = 32;
v___x_2792_ = lean_uint32_dec_eq(v___x_2790_, v___x_2791_);
if (v___x_2792_ == 0)
{
uint32_t v___x_2793_; uint8_t v___x_2794_; 
v___x_2793_ = 9;
v___x_2794_ = lean_uint32_dec_eq(v___x_2790_, v___x_2793_);
if (v___x_2794_ == 0)
{
uint32_t v___x_2795_; uint8_t v___x_2796_; 
v___x_2795_ = 13;
v___x_2796_ = lean_uint32_dec_eq(v___x_2790_, v___x_2795_);
if (v___x_2796_ == 0)
{
uint32_t v___x_2797_; uint8_t v___x_2798_; 
v___x_2797_ = 10;
v___x_2798_ = lean_uint32_dec_eq(v___x_2790_, v___x_2797_);
if (v___x_2798_ == 0)
{
lean_dec(v___x_2784_);
return v_pos_2774_;
}
else
{
goto v___jp_2785_;
}
}
else
{
goto v___jp_2785_;
}
}
else
{
goto v___jp_2785_;
}
}
else
{
goto v___jp_2785_;
}
v___jp_2785_:
{
lean_object* v___x_2786_; uint8_t v___x_2787_; 
v___x_2786_ = lean_nat_add(v___x_2784_, v___x_2782_);
v___x_2787_ = lean_nat_dec_le(v___x_2786_, v_pos_2774_);
lean_dec(v___x_2786_);
if (v___x_2787_ == 0)
{
lean_dec(v___x_2784_);
return v_pos_2774_;
}
else
{
lean_dec(v_pos_2774_);
v_pos_2774_ = v___x_2784_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2778_);
lean_dec(v___x_2777_);
return v_pos_2774_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1___boxed(lean_object* v_s_2799_, lean_object* v_pos_2800_){
_start:
{
lean_object* v_res_2801_; 
v_res_2801_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v_s_2799_, v_pos_2800_);
lean_dec_ref(v_s_2799_);
return v_res_2801_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAscii(lean_object* v_s_2802_){
_start:
{
lean_object* v_str_2803_; lean_object* v_startInclusive_2804_; lean_object* v_endExclusive_2805_; lean_object* v___x_2806_; lean_object* v___x_2807_; lean_object* v___x_2809_; uint8_t v_isShared_2810_; uint8_t v_isSharedCheck_2819_; 
v_str_2803_ = lean_ctor_get(v_s_2802_, 0);
lean_inc_ref(v_str_2803_);
v_startInclusive_2804_ = lean_ctor_get(v_s_2802_, 1);
lean_inc(v_startInclusive_2804_);
v_endExclusive_2805_ = lean_ctor_get(v_s_2802_, 2);
lean_inc(v_endExclusive_2805_);
v___x_2806_ = lean_unsigned_to_nat(0u);
v___x_2807_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2802_, v___x_2806_);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_s_2802_);
if (v_isSharedCheck_2819_ == 0)
{
lean_object* v_unused_2820_; lean_object* v_unused_2821_; lean_object* v_unused_2822_; 
v_unused_2820_ = lean_ctor_get(v_s_2802_, 2);
lean_dec(v_unused_2820_);
v_unused_2821_ = lean_ctor_get(v_s_2802_, 1);
lean_dec(v_unused_2821_);
v_unused_2822_ = lean_ctor_get(v_s_2802_, 0);
lean_dec(v_unused_2822_);
v___x_2809_ = v_s_2802_;
v_isShared_2810_ = v_isSharedCheck_2819_;
goto v_resetjp_2808_;
}
else
{
lean_dec(v_s_2802_);
v___x_2809_ = lean_box(0);
v_isShared_2810_ = v_isSharedCheck_2819_;
goto v_resetjp_2808_;
}
v_resetjp_2808_:
{
lean_object* v___x_2811_; lean_object* v___x_2813_; 
v___x_2811_ = lean_nat_add(v_startInclusive_2804_, v___x_2807_);
lean_dec(v___x_2807_);
lean_dec(v_startInclusive_2804_);
lean_inc(v_endExclusive_2805_);
lean_inc(v___x_2811_);
lean_inc_ref(v_str_2803_);
if (v_isShared_2810_ == 0)
{
lean_ctor_set(v___x_2809_, 1, v___x_2811_);
v___x_2813_ = v___x_2809_;
goto v_reusejp_2812_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_str_2803_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2811_);
lean_ctor_set(v_reuseFailAlloc_2818_, 2, v_endExclusive_2805_);
v___x_2813_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2812_;
}
v_reusejp_2812_:
{
lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2816_; lean_object* v___x_2817_; 
v___x_2814_ = lean_nat_sub(v_endExclusive_2805_, v___x_2811_);
lean_dec(v_endExclusive_2805_);
v___x_2815_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v___x_2813_, v___x_2814_);
lean_dec_ref(v___x_2813_);
v___x_2816_ = lean_nat_add(v___x_2811_, v___x_2815_);
lean_dec(v___x_2815_);
v___x_2817_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2817_, 0, v_str_2803_);
lean_ctor_set(v___x_2817_, 1, v___x_2811_);
lean_ctor_set(v___x_2817_, 2, v___x_2816_);
return v___x_2817_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines_lineMap(lean_object* v_s_2823_){
_start:
{
lean_object* v_str_2824_; lean_object* v_startInclusive_2825_; lean_object* v_endExclusive_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; uint8_t v_decide_2829_; 
v_str_2824_ = lean_ctor_get(v_s_2823_, 0);
v_startInclusive_2825_ = lean_ctor_get(v_s_2823_, 1);
v_endExclusive_2826_ = lean_ctor_get(v_s_2823_, 2);
v___x_2827_ = lean_nat_sub(v_endExclusive_2826_, v_startInclusive_2825_);
v___x_2828_ = lean_unsigned_to_nat(0u);
v_decide_2829_ = lean_nat_dec_eq(v___x_2827_, v___x_2828_);
if (v_decide_2829_ == 0)
{
uint32_t v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint32_t v___x_2835_; uint8_t v___x_2836_; 
v___x_2830_ = 10;
v___x_2831_ = lean_unsigned_to_nat(1u);
v___x_2832_ = lean_nat_sub(v___x_2827_, v___x_2831_);
lean_dec(v___x_2827_);
v___x_2833_ = l_String_Slice_posLE(v_s_2823_, v___x_2832_);
v___x_2834_ = lean_nat_add(v_startInclusive_2825_, v___x_2833_);
lean_dec(v___x_2833_);
v___x_2835_ = lean_string_utf8_get_fast(v_str_2824_, v___x_2834_);
v___x_2836_ = lean_uint32_dec_eq(v___x_2835_, v___x_2830_);
if (v___x_2836_ == 0)
{
lean_dec(v___x_2834_);
return v_s_2823_;
}
else
{
lean_object* v___x_2838_; uint8_t v_isShared_2839_; uint8_t v_isSharedCheck_2852_; 
lean_inc(v_startInclusive_2825_);
lean_inc_ref(v_str_2824_);
v_isSharedCheck_2852_ = !lean_is_exclusive(v_s_2823_);
if (v_isSharedCheck_2852_ == 0)
{
lean_object* v_unused_2853_; lean_object* v_unused_2854_; lean_object* v_unused_2855_; 
v_unused_2853_ = lean_ctor_get(v_s_2823_, 2);
lean_dec(v_unused_2853_);
v_unused_2854_ = lean_ctor_get(v_s_2823_, 1);
lean_dec(v_unused_2854_);
v_unused_2855_ = lean_ctor_get(v_s_2823_, 0);
lean_dec(v_unused_2855_);
v___x_2838_ = v_s_2823_;
v_isShared_2839_ = v_isSharedCheck_2852_;
goto v_resetjp_2837_;
}
else
{
lean_dec(v_s_2823_);
v___x_2838_ = lean_box(0);
v_isShared_2839_ = v_isSharedCheck_2852_;
goto v_resetjp_2837_;
}
v_resetjp_2837_:
{
lean_object* v___x_2841_; 
lean_inc(v___x_2834_);
lean_inc(v_startInclusive_2825_);
lean_inc_ref(v_str_2824_);
if (v_isShared_2839_ == 0)
{
lean_ctor_set(v___x_2838_, 2, v___x_2834_);
v___x_2841_ = v___x_2838_;
goto v_reusejp_2840_;
}
else
{
lean_object* v_reuseFailAlloc_2851_; 
v_reuseFailAlloc_2851_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2851_, 0, v_str_2824_);
lean_ctor_set(v_reuseFailAlloc_2851_, 1, v_startInclusive_2825_);
lean_ctor_set(v_reuseFailAlloc_2851_, 2, v___x_2834_);
v___x_2841_ = v_reuseFailAlloc_2851_;
goto v_reusejp_2840_;
}
v_reusejp_2840_:
{
lean_object* v___x_2842_; uint8_t v_decide_2843_; 
v___x_2842_ = lean_nat_sub(v___x_2834_, v_startInclusive_2825_);
lean_dec(v___x_2834_);
v_decide_2843_ = lean_nat_dec_eq(v___x_2842_, v___x_2828_);
if (v_decide_2843_ == 0)
{
uint32_t v___x_2844_; lean_object* v___x_2845_; lean_object* v___x_2846_; lean_object* v___x_2847_; uint32_t v___x_2848_; uint8_t v___x_2849_; 
v___x_2844_ = 13;
v___x_2845_ = lean_nat_sub(v___x_2842_, v___x_2831_);
lean_dec(v___x_2842_);
v___x_2846_ = l_String_Slice_posLE(v___x_2841_, v___x_2845_);
v___x_2847_ = lean_nat_add(v_startInclusive_2825_, v___x_2846_);
lean_dec(v___x_2846_);
v___x_2848_ = lean_string_utf8_get_fast(v_str_2824_, v___x_2847_);
v___x_2849_ = lean_uint32_dec_eq(v___x_2848_, v___x_2844_);
if (v___x_2849_ == 0)
{
lean_dec(v___x_2847_);
lean_dec(v_startInclusive_2825_);
lean_dec_ref(v_str_2824_);
return v___x_2841_;
}
else
{
lean_object* v___x_2850_; 
lean_dec_ref(v___x_2841_);
v___x_2850_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2850_, 0, v_str_2824_);
lean_ctor_set(v___x_2850_, 1, v_startInclusive_2825_);
lean_ctor_set(v___x_2850_, 2, v___x_2847_);
return v___x_2850_;
}
}
else
{
lean_dec(v___x_2842_);
lean_dec(v_startInclusive_2825_);
lean_dec_ref(v_str_2824_);
return v___x_2841_;
}
}
}
}
}
else
{
lean_dec(v___x_2827_);
return v_s_2823_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg(){
_start:
{
lean_object* v___x_2859_; 
v___x_2859_ = ((lean_object*)(l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___closed__0));
return v___x_2859_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___boxed(lean_object* v___dummy_2860_){
_start:
{
lean_object* v_res_2861_; 
v_res_2861_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
return v_res_2861_;
}
}
static lean_object* _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2862_; 
v___x_2862_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
return v___x_2862_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(lean_object* v_s_2863_){
_start:
{
lean_object* v___x_2864_; 
v___x_2864_ = lean_obj_once(&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0, &l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_once, _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0);
return v___x_2864_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(lean_object* v_s_2865_){
_start:
{
lean_object* v_res_2866_; 
v_res_2866_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_2865_);
lean_dec_ref(v_s_2865_);
return v_res_2866_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines(lean_object* v_s_2867_){
_start:
{
lean_object* v___x_2868_; 
v___x_2868_ = lean_obj_once(&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0, &l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_once, _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0);
return v___x_2868_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines___boxed(lean_object* v_s_2869_){
_start:
{
lean_object* v_res_2870_; 
v_res_2870_ = l_String_Slice_lines(v_s_2869_);
lean_dec_ref(v_s_2869_);
return v_res_2870_;
}
}
lean_object* runtime_initialize_Init_Data_String_Slice_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_ToSlice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Slice_Pattern(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
res = runtime_initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_ToSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Slice_Pattern(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Slice_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Pattern(uint8_t builtin);
lean_object* initialize_Init_Data_String_ToSlice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iter_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Slice_Pattern(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Slice_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_ToSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Collect(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Consumers_Loop(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Option_Lemmas(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Termination(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Slice_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Slice_Pattern(builtin);
}
#ifdef __cplusplus
}
#endif
