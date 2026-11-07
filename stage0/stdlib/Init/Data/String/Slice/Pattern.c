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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_424_; 
v___x_424_ = lean_box(0);
return v___x_424_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_425_){
_start:
{
lean_object* v_res_426_; 
v_res_426_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation___redArg();
return v_res_426_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation(lean_object* v_00_u03c1_427_, lean_object* v_00_u03c3_428_, lean_object* v_inst_429_, lean_object* v_pat_430_, lean_object* v_inst_431_, lean_object* v_s_432_, lean_object* v_inst_433_){
_start:
{
lean_object* v___x_434_; 
v___x_434_ = lean_box(0);
return v___x_434_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_435_, lean_object* v_00_u03c3_436_, lean_object* v_inst_437_, lean_object* v_pat_438_, lean_object* v_inst_439_, lean_object* v_s_440_, lean_object* v_inst_441_){
_start:
{
lean_object* v_res_442_; 
v_res_442_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitIterator_finitenessRelation(v_00_u03c1_435_, v_00_u03c3_436_, v_inst_437_, v_pat_438_, v_inst_439_, v_s_440_, v_inst_441_);
lean_dec_ref(v_s_440_);
lean_dec(v_inst_439_);
lean_dec(v_pat_438_);
lean_dec(v_inst_437_);
return v_res_442_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0(lean_object* v_toPure_443_, lean_object* v_recur_444_, lean_object* v_it_445_, lean_object* v_____do__lift_446_){
_start:
{
if (lean_obj_tag(v_____do__lift_446_) == 0)
{
lean_object* v_a_447_; lean_object* v___x_448_; 
lean_dec(v_it_445_);
lean_dec(v_recur_444_);
v_a_447_ = lean_ctor_get(v_____do__lift_446_, 0);
lean_inc(v_a_447_);
lean_dec_ref_known(v_____do__lift_446_, 1);
v___x_448_ = lean_apply_2(v_toPure_443_, lean_box(0), v_a_447_);
return v___x_448_;
}
else
{
lean_object* v_a_449_; lean_object* v___x_450_; 
lean_dec(v_toPure_443_);
v_a_449_ = lean_ctor_get(v_____do__lift_446_, 0);
lean_inc(v_a_449_);
lean_dec_ref_known(v_____do__lift_446_, 1);
v___x_450_ = lean_apply_4(v_recur_444_, v_it_445_, v_a_449_, lean_box(0), lean_box(0));
return v___x_450_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1(lean_object* v_toPure_451_, lean_object* v_recur_452_, lean_object* v___y_453_, lean_object* v_acc_454_, lean_object* v_toBind_455_, lean_object* v_s_456_){
_start:
{
switch(lean_obj_tag(v_s_456_))
{
case 0:
{
lean_object* v_it_457_; lean_object* v_out_458_; lean_object* v___f_459_; lean_object* v___x_460_; lean_object* v___x_461_; 
v_it_457_ = lean_ctor_get(v_s_456_, 0);
lean_inc(v_it_457_);
v_out_458_ = lean_ctor_get(v_s_456_, 1);
lean_inc(v_out_458_);
lean_dec_ref_known(v_s_456_, 2);
v___f_459_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_459_, 0, v_toPure_451_);
lean_closure_set(v___f_459_, 1, v_recur_452_);
lean_closure_set(v___f_459_, 2, v_it_457_);
v___x_460_ = lean_apply_3(v___y_453_, v_out_458_, lean_box(0), v_acc_454_);
v___x_461_ = lean_apply_4(v_toBind_455_, lean_box(0), lean_box(0), v___x_460_, v___f_459_);
return v___x_461_;
}
case 1:
{
lean_object* v_it_462_; lean_object* v___x_463_; 
lean_dec(v_toBind_455_);
lean_dec(v___y_453_);
lean_dec(v_toPure_451_);
v_it_462_ = lean_ctor_get(v_s_456_, 0);
lean_inc(v_it_462_);
lean_dec_ref_known(v_s_456_, 1);
v___x_463_ = lean_apply_4(v_recur_452_, v_it_462_, v_acc_454_, lean_box(0), lean_box(0));
return v___x_463_;
}
default: 
{
lean_object* v___x_464_; 
lean_dec(v_toBind_455_);
lean_dec(v___y_453_);
lean_dec(v_recur_452_);
v___x_464_ = lean_apply_2(v_toPure_451_, lean_box(0), v_acc_454_);
return v___x_464_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2(lean_object* v_toPure_465_, lean_object* v___y_466_, lean_object* v_toBind_467_, lean_object* v_inst_468_, lean_object* v_s_469_, lean_object* v_lift_470_, lean_object* v_it_471_, lean_object* v_acc_472_, lean_object* v_hP_473_, lean_object* v_recur_474_){
_start:
{
lean_object* v___f_475_; 
v___f_475_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_475_, 0, v_toPure_465_);
lean_closure_set(v___f_475_, 1, v_recur_474_);
lean_closure_set(v___f_475_, 2, v___y_466_);
lean_closure_set(v___f_475_, 3, v_acc_472_);
lean_closure_set(v___f_475_, 4, v_toBind_467_);
if (lean_obj_tag(v_it_471_) == 0)
{
lean_object* v_currPos_476_; lean_object* v_searcher_477_; lean_object* v___x_479_; uint8_t v_isShared_480_; uint8_t v_isSharedCheck_524_; 
v_currPos_476_ = lean_ctor_get(v_it_471_, 0);
v_searcher_477_ = lean_ctor_get(v_it_471_, 1);
v_isSharedCheck_524_ = !lean_is_exclusive(v_it_471_);
if (v_isSharedCheck_524_ == 0)
{
v___x_479_ = v_it_471_;
v_isShared_480_ = v_isSharedCheck_524_;
goto v_resetjp_478_;
}
else
{
lean_inc(v_searcher_477_);
lean_inc(v_currPos_476_);
lean_dec(v_it_471_);
v___x_479_ = lean_box(0);
v_isShared_480_ = v_isSharedCheck_524_;
goto v_resetjp_478_;
}
v_resetjp_478_:
{
lean_object* v___x_481_; 
lean_inc_ref(v_s_469_);
v___x_481_ = lean_apply_2(v_inst_468_, v_s_469_, v_searcher_477_);
switch(lean_obj_tag(v___x_481_))
{
case 0:
{
lean_object* v_out_482_; 
v_out_482_ = lean_ctor_get(v___x_481_, 1);
lean_inc(v_out_482_);
if (lean_obj_tag(v_out_482_) == 0)
{
lean_object* v_it_483_; lean_object* v___x_485_; 
lean_dec_ref_known(v_out_482_, 2);
lean_dec_ref(v_s_469_);
v_it_483_ = lean_ctor_get(v___x_481_, 0);
lean_inc(v_it_483_);
lean_dec_ref_known(v___x_481_, 2);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v_it_483_);
v___x_485_ = v___x_479_;
goto v_reusejp_484_;
}
else
{
lean_object* v_reuseFailAlloc_488_; 
v_reuseFailAlloc_488_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_488_, 0, v_currPos_476_);
lean_ctor_set(v_reuseFailAlloc_488_, 1, v_it_483_);
v___x_485_ = v_reuseFailAlloc_488_;
goto v_reusejp_484_;
}
v_reusejp_484_:
{
lean_object* v___x_486_; lean_object* v___x_487_; 
v___x_486_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_486_, 0, v___x_485_);
v___x_487_ = lean_apply_4(v_lift_470_, lean_box(0), lean_box(0), v___f_475_, v___x_486_);
return v___x_487_;
}
}
else
{
lean_object* v_it_489_; lean_object* v___x_491_; uint8_t v_isShared_492_; uint8_t v_isSharedCheck_503_; 
v_it_489_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_503_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_503_ == 0)
{
lean_object* v_unused_504_; 
v_unused_504_ = lean_ctor_get(v___x_481_, 1);
lean_dec(v_unused_504_);
v___x_491_ = v___x_481_;
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
else
{
lean_inc(v_it_489_);
lean_dec(v___x_481_);
v___x_491_ = lean_box(0);
v_isShared_492_ = v_isSharedCheck_503_;
goto v_resetjp_490_;
}
v_resetjp_490_:
{
lean_object* v_startPos_493_; lean_object* v_endPos_494_; lean_object* v_slice_495_; lean_object* v_nextIt_497_; 
v_startPos_493_ = lean_ctor_get(v_out_482_, 0);
lean_inc(v_startPos_493_);
v_endPos_494_ = lean_ctor_get(v_out_482_, 1);
lean_inc(v_endPos_494_);
lean_dec_ref_known(v_out_482_, 2);
v_slice_495_ = l_String_Slice_subslice_x21(v_s_469_, v_currPos_476_, v_startPos_493_);
lean_dec_ref(v_s_469_);
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v_it_489_);
lean_ctor_set(v___x_479_, 0, v_endPos_494_);
v_nextIt_497_ = v___x_479_;
goto v_reusejp_496_;
}
else
{
lean_object* v_reuseFailAlloc_502_; 
v_reuseFailAlloc_502_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_502_, 0, v_endPos_494_);
lean_ctor_set(v_reuseFailAlloc_502_, 1, v_it_489_);
v_nextIt_497_ = v_reuseFailAlloc_502_;
goto v_reusejp_496_;
}
v_reusejp_496_:
{
lean_object* v___x_499_; 
if (v_isShared_492_ == 0)
{
lean_ctor_set(v___x_491_, 1, v_slice_495_);
lean_ctor_set(v___x_491_, 0, v_nextIt_497_);
v___x_499_ = v___x_491_;
goto v_reusejp_498_;
}
else
{
lean_object* v_reuseFailAlloc_501_; 
v_reuseFailAlloc_501_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_501_, 0, v_nextIt_497_);
lean_ctor_set(v_reuseFailAlloc_501_, 1, v_slice_495_);
v___x_499_ = v_reuseFailAlloc_501_;
goto v_reusejp_498_;
}
v_reusejp_498_:
{
lean_object* v___x_500_; 
v___x_500_ = lean_apply_4(v_lift_470_, lean_box(0), lean_box(0), v___f_475_, v___x_499_);
return v___x_500_;
}
}
}
}
}
case 1:
{
lean_object* v_it_505_; lean_object* v___x_507_; uint8_t v_isShared_508_; uint8_t v_isSharedCheck_516_; 
lean_dec_ref(v_s_469_);
v_it_505_ = lean_ctor_get(v___x_481_, 0);
v_isSharedCheck_516_ = !lean_is_exclusive(v___x_481_);
if (v_isSharedCheck_516_ == 0)
{
v___x_507_ = v___x_481_;
v_isShared_508_ = v_isSharedCheck_516_;
goto v_resetjp_506_;
}
else
{
lean_inc(v_it_505_);
lean_dec(v___x_481_);
v___x_507_ = lean_box(0);
v_isShared_508_ = v_isSharedCheck_516_;
goto v_resetjp_506_;
}
v_resetjp_506_:
{
lean_object* v___x_510_; 
if (v_isShared_480_ == 0)
{
lean_ctor_set(v___x_479_, 1, v_it_505_);
v___x_510_ = v___x_479_;
goto v_reusejp_509_;
}
else
{
lean_object* v_reuseFailAlloc_515_; 
v_reuseFailAlloc_515_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_515_, 0, v_currPos_476_);
lean_ctor_set(v_reuseFailAlloc_515_, 1, v_it_505_);
v___x_510_ = v_reuseFailAlloc_515_;
goto v_reusejp_509_;
}
v_reusejp_509_:
{
lean_object* v___x_512_; 
if (v_isShared_508_ == 0)
{
lean_ctor_set(v___x_507_, 0, v___x_510_);
v___x_512_ = v___x_507_;
goto v_reusejp_511_;
}
else
{
lean_object* v_reuseFailAlloc_514_; 
v_reuseFailAlloc_514_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_514_, 0, v___x_510_);
v___x_512_ = v_reuseFailAlloc_514_;
goto v_reusejp_511_;
}
v_reusejp_511_:
{
lean_object* v___x_513_; 
v___x_513_ = lean_apply_4(v_lift_470_, lean_box(0), lean_box(0), v___f_475_, v___x_512_);
return v___x_513_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_517_; lean_object* v_endExclusive_518_; lean_object* v___x_519_; lean_object* v_slice_520_; lean_object* v___x_521_; lean_object* v___x_522_; lean_object* v___x_523_; 
lean_del_object(v___x_479_);
v_startInclusive_517_ = lean_ctor_get(v_s_469_, 1);
lean_inc(v_startInclusive_517_);
v_endExclusive_518_ = lean_ctor_get(v_s_469_, 2);
lean_inc(v_endExclusive_518_);
lean_dec_ref(v_s_469_);
v___x_519_ = lean_nat_sub(v_endExclusive_518_, v_startInclusive_517_);
lean_dec(v_startInclusive_517_);
lean_dec(v_endExclusive_518_);
v_slice_520_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_520_, 0, v_currPos_476_);
lean_ctor_set(v_slice_520_, 1, v___x_519_);
v___x_521_ = lean_box(1);
v___x_522_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_522_, 0, v___x_521_);
lean_ctor_set(v___x_522_, 1, v_slice_520_);
v___x_523_ = lean_apply_4(v_lift_470_, lean_box(0), lean_box(0), v___f_475_, v___x_522_);
return v___x_523_;
}
}
}
}
else
{
lean_object* v___x_525_; lean_object* v___x_526_; 
lean_dec_ref(v_s_469_);
lean_dec(v_inst_468_);
v___x_525_ = lean_box(2);
v___x_526_ = lean_apply_4(v_lift_470_, lean_box(0), lean_box(0), v___f_475_, v___x_525_);
return v___x_526_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3(lean_object* v_inst_527_, lean_object* v_inst_528_, lean_object* v_s_529_, lean_object* v_lift_530_, lean_object* v_00_u03b3_531_, lean_object* v_Pl_532_, lean_object* v_it_533_, lean_object* v_init_534_, lean_object* v___y_535_){
_start:
{
lean_object* v_toApplicative_536_; lean_object* v_toBind_537_; lean_object* v_toPure_538_; lean_object* v___f_539_; lean_object* v___x_540_; 
v_toApplicative_536_ = lean_ctor_get(v_inst_527_, 0);
lean_inc_ref(v_toApplicative_536_);
v_toBind_537_ = lean_ctor_get(v_inst_527_, 1);
lean_inc(v_toBind_537_);
lean_dec_ref(v_inst_527_);
v_toPure_538_ = lean_ctor_get(v_toApplicative_536_, 1);
lean_inc(v_toPure_538_);
lean_dec_ref(v_toApplicative_536_);
v___f_539_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_539_, 0, v_toPure_538_);
lean_closure_set(v___f_539_, 1, v___y_535_);
lean_closure_set(v___f_539_, 2, v_toBind_537_);
lean_closure_set(v___f_539_, 3, v_inst_528_);
lean_closure_set(v___f_539_, 4, v_s_529_);
lean_closure_set(v___f_539_, 5, v_lift_530_);
v___x_540_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_539_, v_it_533_, v_init_534_, lean_box(0));
return v___x_540_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg(lean_object* v_inst_541_, lean_object* v_s_542_, lean_object* v_inst_543_){
_start:
{
lean_object* v___f_544_; 
v___f_544_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_544_, 0, v_inst_543_);
lean_closure_set(v___f_544_, 1, v_inst_541_);
lean_closure_set(v___f_544_, 2, v_s_542_);
return v___f_544_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(lean_object* v_00_u03c1_545_, lean_object* v_00_u03c3_546_, lean_object* v_inst_547_, lean_object* v_pat_548_, lean_object* v_inst_549_, lean_object* v_n_550_, lean_object* v_s_551_, lean_object* v_inst_552_){
_start:
{
lean_object* v___f_553_; 
v___f_553_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_553_, 0, v_inst_552_);
lean_closure_set(v___f_553_, 1, v_inst_547_);
lean_closure_set(v___f_553_, 2, v_s_551_);
return v___f_553_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___boxed(lean_object* v_00_u03c1_554_, lean_object* v_00_u03c3_555_, lean_object* v_inst_556_, lean_object* v_pat_557_, lean_object* v_inst_558_, lean_object* v_n_559_, lean_object* v_s_560_, lean_object* v_inst_561_){
_start:
{
lean_object* v_res_562_; 
v_res_562_ = l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(v_00_u03c1_554_, v_00_u03c3_555_, v_inst_556_, v_pat_557_, v_inst_558_, v_n_559_, v_s_560_, v_inst_561_);
lean_dec(v_inst_558_);
lean_dec(v_pat_557_);
return v_res_562_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___redArg(lean_object* v_s_563_, lean_object* v_inst_564_){
_start:
{
lean_object* v___x_565_; lean_object* v___x_566_; lean_object* v___x_567_; 
v___x_565_ = lean_unsigned_to_nat(0u);
v___x_566_ = lean_apply_1(v_inst_564_, v_s_563_);
v___x_567_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_567_, 0, v___x_565_);
lean_ctor_set(v___x_567_, 1, v___x_566_);
return v___x_567_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice(lean_object* v_00_u03c1_568_, lean_object* v_00_u03c3_569_, lean_object* v_s_570_, lean_object* v_pat_571_, lean_object* v_inst_572_){
_start:
{
lean_object* v___x_573_; 
v___x_573_ = l_String_Slice_splitToSubslice___redArg(v_s_570_, v_inst_572_);
return v___x_573_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___boxed(lean_object* v_00_u03c1_574_, lean_object* v_00_u03c3_575_, lean_object* v_s_576_, lean_object* v_pat_577_, lean_object* v_inst_578_){
_start:
{
lean_object* v_res_579_; 
v_res_579_ = l_String_Slice_splitToSubslice(v_00_u03c1_574_, v_00_u03c3_575_, v_s_576_, v_pat_577_, v_inst_578_);
lean_dec(v_pat_577_);
return v_res_579_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___redArg(lean_object* v_s_580_, lean_object* v_inst_581_){
_start:
{
lean_object* v___x_582_; 
v___x_582_ = l_String_Slice_splitToSubslice___redArg(v_s_580_, v_inst_581_);
return v___x_582_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split(lean_object* v_00_u03c1_583_, lean_object* v_00_u03c3_584_, lean_object* v_inst_585_, lean_object* v_s_586_, lean_object* v_pat_587_, lean_object* v_inst_588_){
_start:
{
lean_object* v___x_589_; 
v___x_589_ = l_String_Slice_splitToSubslice___redArg(v_s_586_, v_inst_588_);
return v___x_589_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___boxed(lean_object* v_00_u03c1_590_, lean_object* v_00_u03c3_591_, lean_object* v_inst_592_, lean_object* v_s_593_, lean_object* v_pat_594_, lean_object* v_inst_595_){
_start:
{
lean_object* v_res_596_; 
v_res_596_ = l_String_Slice_split(v_00_u03c1_590_, v_00_u03c3_591_, v_inst_592_, v_s_593_, v_pat_594_, v_inst_595_);
lean_dec(v_pat_594_);
lean_dec(v_inst_592_);
return v_res_596_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg(lean_object* v_x_597_){
_start:
{
lean_object* v___x_598_; 
v___x_598_ = lean_obj_tag_nat(v_x_597_);
return v___x_598_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg___boxed(lean_object* v_x_599_){
_start:
{
lean_object* v_res_600_; 
v_res_600_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg(v_x_599_);
lean_dec(v_x_599_);
return v_res_600_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl(lean_object* v_00_u03c3_601_, lean_object* v_00_u03c1_602_, lean_object* v_pat_603_, lean_object* v_s_604_, lean_object* v_inst_605_, lean_object* v_x_606_){
_start:
{
lean_object* v___x_607_; 
v___x_607_ = lean_obj_tag_nat(v_x_606_);
return v___x_607_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___boxed(lean_object* v_00_u03c3_608_, lean_object* v_00_u03c1_609_, lean_object* v_pat_610_, lean_object* v_s_611_, lean_object* v_inst_612_, lean_object* v_x_613_){
_start:
{
lean_object* v_res_614_; 
v_res_614_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___impl(v_00_u03c3_608_, v_00_u03c1_609_, v_pat_610_, v_s_611_, v_inst_612_, v_x_613_);
lean_dec(v_x_613_);
lean_dec(v_inst_612_);
lean_dec_ref(v_s_611_);
lean_dec(v_pat_610_);
return v_res_614_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(lean_object* v_t_615_, lean_object* v_k_616_){
_start:
{
if (lean_obj_tag(v_t_615_) == 0)
{
lean_object* v_currPos_617_; lean_object* v_searcher_618_; lean_object* v___x_619_; 
v_currPos_617_ = lean_ctor_get(v_t_615_, 0);
lean_inc(v_currPos_617_);
v_searcher_618_ = lean_ctor_get(v_t_615_, 1);
lean_inc(v_searcher_618_);
lean_dec_ref_known(v_t_615_, 2);
v___x_619_ = lean_apply_2(v_k_616_, v_currPos_617_, v_searcher_618_);
return v___x_619_;
}
else
{
return v_k_616_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim(lean_object* v_00_u03c3_620_, lean_object* v_00_u03c1_621_, lean_object* v_pat_622_, lean_object* v_s_623_, lean_object* v_inst_624_, lean_object* v_motive_625_, lean_object* v_ctorIdx_626_, lean_object* v_t_627_, lean_object* v_h_628_, lean_object* v_k_629_){
_start:
{
lean_object* v___x_630_; 
v___x_630_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_627_, v_k_629_);
return v___x_630_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___boxed(lean_object* v_00_u03c3_631_, lean_object* v_00_u03c1_632_, lean_object* v_pat_633_, lean_object* v_s_634_, lean_object* v_inst_635_, lean_object* v_motive_636_, lean_object* v_ctorIdx_637_, lean_object* v_t_638_, lean_object* v_h_639_, lean_object* v_k_640_){
_start:
{
lean_object* v_res_641_; 
v_res_641_ = l_String_Slice_SplitInclusiveIterator_ctorElim(v_00_u03c3_631_, v_00_u03c1_632_, v_pat_633_, v_s_634_, v_inst_635_, v_motive_636_, v_ctorIdx_637_, v_t_638_, v_h_639_, v_k_640_);
lean_dec(v_ctorIdx_637_);
lean_dec(v_inst_635_);
lean_dec_ref(v_s_634_);
lean_dec(v_pat_633_);
return v_res_641_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___redArg(lean_object* v_t_642_, lean_object* v_operating_643_){
_start:
{
lean_object* v___x_644_; 
v___x_644_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_642_, v_operating_643_);
return v___x_644_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim(lean_object* v_00_u03c3_645_, lean_object* v_00_u03c1_646_, lean_object* v_pat_647_, lean_object* v_s_648_, lean_object* v_inst_649_, lean_object* v_motive_650_, lean_object* v_t_651_, lean_object* v_h_652_, lean_object* v_operating_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_651_, v_operating_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___boxed(lean_object* v_00_u03c3_655_, lean_object* v_00_u03c1_656_, lean_object* v_pat_657_, lean_object* v_s_658_, lean_object* v_inst_659_, lean_object* v_motive_660_, lean_object* v_t_661_, lean_object* v_h_662_, lean_object* v_operating_663_){
_start:
{
lean_object* v_res_664_; 
v_res_664_ = l_String_Slice_SplitInclusiveIterator_operating_elim(v_00_u03c3_655_, v_00_u03c1_656_, v_pat_657_, v_s_658_, v_inst_659_, v_motive_660_, v_t_661_, v_h_662_, v_operating_663_);
lean_dec(v_inst_659_);
lean_dec_ref(v_s_658_);
lean_dec(v_pat_657_);
return v_res_664_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___redArg(lean_object* v_t_665_, lean_object* v_atEnd_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_665_, v_atEnd_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim(lean_object* v_00_u03c3_668_, lean_object* v_00_u03c1_669_, lean_object* v_pat_670_, lean_object* v_s_671_, lean_object* v_inst_672_, lean_object* v_motive_673_, lean_object* v_t_674_, lean_object* v_h_675_, lean_object* v_atEnd_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_674_, v_atEnd_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_678_, lean_object* v_00_u03c1_679_, lean_object* v_pat_680_, lean_object* v_s_681_, lean_object* v_inst_682_, lean_object* v_motive_683_, lean_object* v_t_684_, lean_object* v_h_685_, lean_object* v_atEnd_686_){
_start:
{
lean_object* v_res_687_; 
v_res_687_ = l_String_Slice_SplitInclusiveIterator_atEnd_elim(v_00_u03c3_678_, v_00_u03c1_679_, v_pat_680_, v_s_681_, v_inst_682_, v_motive_683_, v_t_684_, v_h_685_, v_atEnd_686_);
lean_dec(v_inst_682_);
lean_dec_ref(v_s_681_);
lean_dec(v_pat_680_);
return v_res_687_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg(){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = lean_box(1);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg___boxed(lean_object* v___dummy_690_){
_start:
{
lean_object* v_res_691_; 
v_res_691_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg();
return v_res_691_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default(lean_object* v_00_u03c3_692_, lean_object* v_00_u03c1_693_, lean_object* v_pat_694_, lean_object* v_s_695_, lean_object* v_inst_696_){
_start:
{
lean_object* v___x_697_; 
v___x_697_ = lean_box(1);
return v___x_697_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___boxed(lean_object* v_00_u03c3_698_, lean_object* v_00_u03c1_699_, lean_object* v_pat_700_, lean_object* v_s_701_, lean_object* v_inst_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default(v_00_u03c3_698_, v_00_u03c1_699_, v_pat_700_, v_s_701_, v_inst_702_);
lean_dec(v_inst_702_);
lean_dec_ref(v_s_701_);
lean_dec(v_pat_700_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg(){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = lean_box(1);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg___boxed(lean_object* v___dummy_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_String_Slice_instInhabitedSplitInclusiveIterator___redArg();
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator(lean_object* v_a_708_, lean_object* v_a_709_, lean_object* v_a_710_, lean_object* v_a_711_, lean_object* v_a_712_){
_start:
{
lean_object* v___x_713_; 
v___x_713_ = lean_box(1);
return v___x_713_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___boxed(lean_object* v_a_714_, lean_object* v_a_715_, lean_object* v_a_716_, lean_object* v_a_717_, lean_object* v_a_718_){
_start:
{
lean_object* v_res_719_; 
v_res_719_ = l_String_Slice_instInhabitedSplitInclusiveIterator(v_a_714_, v_a_715_, v_a_716_, v_a_717_, v_a_718_);
lean_dec(v_a_718_);
lean_dec_ref(v_a_717_);
lean_dec(v_a_716_);
return v_res_719_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0(lean_object* v_inst_720_, lean_object* v_s_721_, lean_object* v_x_722_){
_start:
{
if (lean_obj_tag(v_x_722_) == 0)
{
lean_object* v_currPos_723_; lean_object* v_searcher_724_; lean_object* v___x_726_; uint8_t v_isShared_727_; uint8_t v_isSharedCheck_776_; 
v_currPos_723_ = lean_ctor_get(v_x_722_, 0);
v_searcher_724_ = lean_ctor_get(v_x_722_, 1);
v_isSharedCheck_776_ = !lean_is_exclusive(v_x_722_);
if (v_isSharedCheck_776_ == 0)
{
v___x_726_ = v_x_722_;
v_isShared_727_ = v_isSharedCheck_776_;
goto v_resetjp_725_;
}
else
{
lean_inc(v_searcher_724_);
lean_inc(v_currPos_723_);
lean_dec(v_x_722_);
v___x_726_ = lean_box(0);
v_isShared_727_ = v_isSharedCheck_776_;
goto v_resetjp_725_;
}
v_resetjp_725_:
{
lean_object* v___x_728_; 
lean_inc_ref(v_s_721_);
v___x_728_ = lean_apply_2(v_inst_720_, v_s_721_, v_searcher_724_);
switch(lean_obj_tag(v___x_728_))
{
case 0:
{
lean_object* v_out_729_; 
v_out_729_ = lean_ctor_get(v___x_728_, 1);
lean_inc(v_out_729_);
if (lean_obj_tag(v_out_729_) == 0)
{
lean_object* v_it_730_; lean_object* v___x_732_; 
lean_dec_ref_known(v_out_729_, 2);
lean_dec_ref(v_s_721_);
v_it_730_ = lean_ctor_get(v___x_728_, 0);
lean_inc(v_it_730_);
lean_dec_ref_known(v___x_728_, 2);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v_it_730_);
v___x_732_ = v___x_726_;
goto v_reusejp_731_;
}
else
{
lean_object* v_reuseFailAlloc_734_; 
v_reuseFailAlloc_734_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_734_, 0, v_currPos_723_);
lean_ctor_set(v_reuseFailAlloc_734_, 1, v_it_730_);
v___x_732_ = v_reuseFailAlloc_734_;
goto v_reusejp_731_;
}
v_reusejp_731_:
{
lean_object* v___x_733_; 
v___x_733_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_733_, 0, v___x_732_);
return v___x_733_;
}
}
else
{
lean_object* v_it_735_; lean_object* v___x_737_; uint8_t v_isShared_738_; uint8_t v_isSharedCheck_747_; 
v_it_735_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_747_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_747_ == 0)
{
lean_object* v_unused_748_; 
v_unused_748_ = lean_ctor_get(v___x_728_, 1);
lean_dec(v_unused_748_);
v___x_737_ = v___x_728_;
v_isShared_738_ = v_isSharedCheck_747_;
goto v_resetjp_736_;
}
else
{
lean_inc(v_it_735_);
lean_dec(v___x_728_);
v___x_737_ = lean_box(0);
v_isShared_738_ = v_isSharedCheck_747_;
goto v_resetjp_736_;
}
v_resetjp_736_:
{
lean_object* v_endPos_739_; lean_object* v_slice_740_; lean_object* v_nextIt_742_; 
v_endPos_739_ = lean_ctor_get(v_out_729_, 1);
lean_inc(v_endPos_739_);
lean_dec_ref_known(v_out_729_, 2);
v_slice_740_ = l_String_Slice_slice_x21(v_s_721_, v_currPos_723_, v_endPos_739_);
lean_dec(v_currPos_723_);
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v_it_735_);
lean_ctor_set(v___x_726_, 0, v_endPos_739_);
v_nextIt_742_ = v___x_726_;
goto v_reusejp_741_;
}
else
{
lean_object* v_reuseFailAlloc_746_; 
v_reuseFailAlloc_746_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_746_, 0, v_endPos_739_);
lean_ctor_set(v_reuseFailAlloc_746_, 1, v_it_735_);
v_nextIt_742_ = v_reuseFailAlloc_746_;
goto v_reusejp_741_;
}
v_reusejp_741_:
{
lean_object* v___x_744_; 
if (v_isShared_738_ == 0)
{
lean_ctor_set(v___x_737_, 1, v_slice_740_);
lean_ctor_set(v___x_737_, 0, v_nextIt_742_);
v___x_744_ = v___x_737_;
goto v_reusejp_743_;
}
else
{
lean_object* v_reuseFailAlloc_745_; 
v_reuseFailAlloc_745_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_745_, 0, v_nextIt_742_);
lean_ctor_set(v_reuseFailAlloc_745_, 1, v_slice_740_);
v___x_744_ = v_reuseFailAlloc_745_;
goto v_reusejp_743_;
}
v_reusejp_743_:
{
return v___x_744_;
}
}
}
}
}
case 1:
{
lean_object* v_it_749_; lean_object* v___x_751_; uint8_t v_isShared_752_; uint8_t v_isSharedCheck_759_; 
lean_dec_ref(v_s_721_);
v_it_749_ = lean_ctor_get(v___x_728_, 0);
v_isSharedCheck_759_ = !lean_is_exclusive(v___x_728_);
if (v_isSharedCheck_759_ == 0)
{
v___x_751_ = v___x_728_;
v_isShared_752_ = v_isSharedCheck_759_;
goto v_resetjp_750_;
}
else
{
lean_inc(v_it_749_);
lean_dec(v___x_728_);
v___x_751_ = lean_box(0);
v_isShared_752_ = v_isSharedCheck_759_;
goto v_resetjp_750_;
}
v_resetjp_750_:
{
lean_object* v___x_754_; 
if (v_isShared_727_ == 0)
{
lean_ctor_set(v___x_726_, 1, v_it_749_);
v___x_754_ = v___x_726_;
goto v_reusejp_753_;
}
else
{
lean_object* v_reuseFailAlloc_758_; 
v_reuseFailAlloc_758_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_758_, 0, v_currPos_723_);
lean_ctor_set(v_reuseFailAlloc_758_, 1, v_it_749_);
v___x_754_ = v_reuseFailAlloc_758_;
goto v_reusejp_753_;
}
v_reusejp_753_:
{
lean_object* v___x_756_; 
if (v_isShared_752_ == 0)
{
lean_ctor_set(v___x_751_, 0, v___x_754_);
v___x_756_ = v___x_751_;
goto v_reusejp_755_;
}
else
{
lean_object* v_reuseFailAlloc_757_; 
v_reuseFailAlloc_757_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_757_, 0, v___x_754_);
v___x_756_ = v_reuseFailAlloc_757_;
goto v_reusejp_755_;
}
v_reusejp_755_:
{
return v___x_756_;
}
}
}
}
default: 
{
lean_object* v_str_760_; lean_object* v_startInclusive_761_; lean_object* v_endExclusive_762_; lean_object* v___x_764_; uint8_t v_isShared_765_; uint8_t v_isSharedCheck_775_; 
lean_del_object(v___x_726_);
v_str_760_ = lean_ctor_get(v_s_721_, 0);
v_startInclusive_761_ = lean_ctor_get(v_s_721_, 1);
v_endExclusive_762_ = lean_ctor_get(v_s_721_, 2);
v_isSharedCheck_775_ = !lean_is_exclusive(v_s_721_);
if (v_isSharedCheck_775_ == 0)
{
v___x_764_ = v_s_721_;
v_isShared_765_ = v_isSharedCheck_775_;
goto v_resetjp_763_;
}
else
{
lean_inc(v_endExclusive_762_);
lean_inc(v_startInclusive_761_);
lean_inc(v_str_760_);
lean_dec(v_s_721_);
v___x_764_ = lean_box(0);
v_isShared_765_ = v_isSharedCheck_775_;
goto v_resetjp_763_;
}
v_resetjp_763_:
{
lean_object* v___x_766_; uint8_t v_decide_767_; 
v___x_766_ = lean_nat_sub(v_endExclusive_762_, v_startInclusive_761_);
v_decide_767_ = lean_nat_dec_eq(v_currPos_723_, v___x_766_);
lean_dec(v___x_766_);
if (v_decide_767_ == 0)
{
lean_object* v___x_768_; lean_object* v_slice_770_; 
v___x_768_ = lean_nat_add(v_startInclusive_761_, v_currPos_723_);
lean_dec(v_currPos_723_);
lean_dec(v_startInclusive_761_);
if (v_isShared_765_ == 0)
{
lean_ctor_set(v___x_764_, 1, v___x_768_);
v_slice_770_ = v___x_764_;
goto v_reusejp_769_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_str_760_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v___x_768_);
lean_ctor_set(v_reuseFailAlloc_773_, 2, v_endExclusive_762_);
v_slice_770_ = v_reuseFailAlloc_773_;
goto v_reusejp_769_;
}
v_reusejp_769_:
{
lean_object* v___x_771_; lean_object* v___x_772_; 
v___x_771_ = lean_box(1);
v___x_772_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
lean_ctor_set(v___x_772_, 1, v_slice_770_);
return v___x_772_;
}
}
else
{
lean_object* v___x_774_; 
lean_del_object(v___x_764_);
lean_dec(v_endExclusive_762_);
lean_dec(v_startInclusive_761_);
lean_dec_ref(v_str_760_);
lean_dec(v_currPos_723_);
v___x_774_ = lean_box(2);
return v___x_774_;
}
}
}
}
}
}
else
{
lean_object* v___x_777_; 
lean_dec_ref(v_s_721_);
lean_dec(v_inst_720_);
v___x_777_ = lean_box(2);
return v___x_777_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg(lean_object* v_inst_778_, lean_object* v_s_779_){
_start:
{
lean_object* v___f_780_; 
v___f_780_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_780_, 0, v_inst_778_);
lean_closure_set(v___f_780_, 1, v_s_779_);
return v___f_780_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId(lean_object* v_00_u03c1_781_, lean_object* v_00_u03c3_782_, lean_object* v_inst_783_, lean_object* v_pat_784_, lean_object* v_inst_785_, lean_object* v_s_786_){
_start:
{
lean_object* v___f_787_; 
v___f_787_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_787_, 0, v_inst_783_);
lean_closure_set(v___f_787_, 1, v_s_786_);
return v___f_787_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___boxed(lean_object* v_00_u03c1_788_, lean_object* v_00_u03c3_789_, lean_object* v_inst_790_, lean_object* v_pat_791_, lean_object* v_inst_792_, lean_object* v_s_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_String_Slice_SplitInclusiveIterator_instIteratorId(v_00_u03c1_788_, v_00_u03c3_789_, v_inst_790_, v_pat_791_, v_inst_792_, v_s_793_);
lean_dec(v_inst_792_);
lean_dec(v_pat_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___redArg(lean_object* v_x_795_){
_start:
{
if (lean_obj_tag(v_x_795_) == 0)
{
lean_object* v_searcher_796_; lean_object* v___x_797_; 
v_searcher_796_ = lean_ctor_get(v_x_795_, 1);
lean_inc(v_searcher_796_);
v___x_797_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_797_, 0, v_searcher_796_);
return v___x_797_;
}
else
{
lean_object* v___x_798_; 
v___x_798_ = lean_box(0);
return v___x_798_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___redArg___boxed(lean_object* v_x_799_){
_start:
{
lean_object* v_res_800_; 
v_res_800_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_799_);
lean_dec(v_x_799_);
return v_res_800_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption(lean_object* v_00_u03c1_801_, lean_object* v_00_u03c3_802_, lean_object* v_pat_803_, lean_object* v_inst_804_, lean_object* v_s_805_, lean_object* v_x_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_806_);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption___boxed(lean_object* v_00_u03c1_808_, lean_object* v_00_u03c3_809_, lean_object* v_pat_810_, lean_object* v_inst_811_, lean_object* v_s_812_, lean_object* v_x_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_toOption(v_00_u03c1_808_, v_00_u03c3_809_, v_pat_810_, v_inst_811_, v_s_812_, v_x_813_);
lean_dec(v_x_813_);
lean_dec_ref(v_s_812_);
lean_dec(v_inst_811_);
lean_dec(v_pat_810_);
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___redArg(lean_object* v_x_815_, lean_object* v_h__1_816_, lean_object* v_h__2_817_){
_start:
{
if (lean_obj_tag(v_x_815_) == 0)
{
lean_object* v_currPos_818_; lean_object* v_searcher_819_; lean_object* v___x_820_; 
lean_dec(v_h__2_817_);
v_currPos_818_ = lean_ctor_get(v_x_815_, 0);
lean_inc(v_currPos_818_);
v_searcher_819_ = lean_ctor_get(v_x_815_, 1);
lean_inc(v_searcher_819_);
lean_dec_ref_known(v_x_815_, 2);
v___x_820_ = lean_apply_2(v_h__1_816_, v_currPos_818_, v_searcher_819_);
return v___x_820_;
}
else
{
lean_object* v___x_821_; lean_object* v___x_822_; 
lean_dec(v_h__1_816_);
v___x_821_ = lean_box(0);
v___x_822_ = lean_apply_1(v_h__2_817_, v___x_821_);
return v___x_822_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(lean_object* v_00_u03c1_823_, lean_object* v_00_u03c3_824_, lean_object* v_pat_825_, lean_object* v_inst_826_, lean_object* v_s_827_, lean_object* v_motive_828_, lean_object* v_x_829_, lean_object* v_h__1_830_, lean_object* v_h__2_831_){
_start:
{
if (lean_obj_tag(v_x_829_) == 0)
{
lean_object* v_currPos_832_; lean_object* v_searcher_833_; lean_object* v___x_834_; 
lean_dec(v_h__2_831_);
v_currPos_832_ = lean_ctor_get(v_x_829_, 0);
lean_inc(v_currPos_832_);
v_searcher_833_ = lean_ctor_get(v_x_829_, 1);
lean_inc(v_searcher_833_);
lean_dec_ref_known(v_x_829_, 2);
v___x_834_ = lean_apply_2(v_h__1_830_, v_currPos_832_, v_searcher_833_);
return v___x_834_;
}
else
{
lean_object* v___x_835_; lean_object* v___x_836_; 
lean_dec(v_h__1_830_);
v___x_835_ = lean_box(0);
v___x_836_ = lean_apply_1(v_h__2_831_, v___x_835_);
return v___x_836_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___boxed(lean_object* v_00_u03c1_837_, lean_object* v_00_u03c3_838_, lean_object* v_pat_839_, lean_object* v_inst_840_, lean_object* v_s_841_, lean_object* v_motive_842_, lean_object* v_x_843_, lean_object* v_h__1_844_, lean_object* v_h__2_845_){
_start:
{
lean_object* v_res_846_; 
v_res_846_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(v_00_u03c1_837_, v_00_u03c3_838_, v_pat_839_, v_inst_840_, v_s_841_, v_motive_842_, v_x_843_, v_h__1_844_, v_h__2_845_);
lean_dec_ref(v_s_841_);
lean_dec(v_inst_840_);
lean_dec(v_pat_839_);
return v_res_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___redArg(lean_object* v_x_847_, lean_object* v_x_848_, lean_object* v_h__1_849_, lean_object* v_h__2_850_, lean_object* v_h__3_851_, lean_object* v_h__4_852_, lean_object* v_h__5_853_, lean_object* v_h__6_854_, lean_object* v_h__7_855_, lean_object* v_h__8_856_){
_start:
{
if (lean_obj_tag(v_x_847_) == 0)
{
lean_dec(v_h__8_856_);
lean_dec(v_h__7_855_);
lean_dec(v_h__6_854_);
switch(lean_obj_tag(v_x_848_))
{
case 0:
{
lean_object* v_it_857_; 
lean_dec(v_h__5_853_);
lean_dec(v_h__4_852_);
lean_dec(v_h__3_851_);
v_it_857_ = lean_ctor_get(v_x_848_, 0);
if (lean_obj_tag(v_it_857_) == 0)
{
lean_object* v_currPos_858_; lean_object* v_searcher_859_; lean_object* v_out_860_; lean_object* v_currPos_861_; lean_object* v_searcher_862_; lean_object* v___x_863_; 
lean_inc_ref(v_it_857_);
lean_dec(v_h__2_850_);
v_currPos_858_ = lean_ctor_get(v_x_847_, 0);
lean_inc(v_currPos_858_);
v_searcher_859_ = lean_ctor_get(v_x_847_, 1);
lean_inc(v_searcher_859_);
lean_dec_ref_known(v_x_847_, 2);
v_out_860_ = lean_ctor_get(v_x_848_, 1);
lean_inc(v_out_860_);
lean_dec_ref_known(v_x_848_, 2);
v_currPos_861_ = lean_ctor_get(v_it_857_, 0);
lean_inc(v_currPos_861_);
v_searcher_862_ = lean_ctor_get(v_it_857_, 1);
lean_inc(v_searcher_862_);
lean_dec_ref_known(v_it_857_, 2);
v___x_863_ = lean_apply_5(v_h__1_849_, v_currPos_858_, v_searcher_859_, v_currPos_861_, v_searcher_862_, v_out_860_);
return v___x_863_;
}
else
{
lean_object* v_currPos_864_; lean_object* v_searcher_865_; lean_object* v_out_866_; lean_object* v___x_867_; 
lean_dec(v_h__1_849_);
v_currPos_864_ = lean_ctor_get(v_x_847_, 0);
lean_inc(v_currPos_864_);
v_searcher_865_ = lean_ctor_get(v_x_847_, 1);
lean_inc(v_searcher_865_);
lean_dec_ref_known(v_x_847_, 2);
v_out_866_ = lean_ctor_get(v_x_848_, 1);
lean_inc(v_out_866_);
lean_dec_ref_known(v_x_848_, 2);
v___x_867_ = lean_apply_3(v_h__2_850_, v_currPos_864_, v_searcher_865_, v_out_866_);
return v___x_867_;
}
}
case 1:
{
lean_object* v_it_868_; 
lean_dec(v_h__5_853_);
lean_dec(v_h__2_850_);
lean_dec(v_h__1_849_);
v_it_868_ = lean_ctor_get(v_x_848_, 0);
lean_inc(v_it_868_);
lean_dec_ref_known(v_x_848_, 1);
if (lean_obj_tag(v_it_868_) == 0)
{
lean_object* v_currPos_869_; lean_object* v_searcher_870_; lean_object* v_currPos_871_; lean_object* v_searcher_872_; lean_object* v___x_873_; 
lean_dec(v_h__4_852_);
v_currPos_869_ = lean_ctor_get(v_x_847_, 0);
lean_inc(v_currPos_869_);
v_searcher_870_ = lean_ctor_get(v_x_847_, 1);
lean_inc(v_searcher_870_);
lean_dec_ref_known(v_x_847_, 2);
v_currPos_871_ = lean_ctor_get(v_it_868_, 0);
lean_inc(v_currPos_871_);
v_searcher_872_ = lean_ctor_get(v_it_868_, 1);
lean_inc(v_searcher_872_);
lean_dec_ref_known(v_it_868_, 2);
v___x_873_ = lean_apply_4(v_h__3_851_, v_currPos_869_, v_searcher_870_, v_currPos_871_, v_searcher_872_);
return v___x_873_;
}
else
{
lean_object* v_currPos_874_; lean_object* v_searcher_875_; lean_object* v___x_876_; 
lean_dec(v_h__3_851_);
v_currPos_874_ = lean_ctor_get(v_x_847_, 0);
lean_inc(v_currPos_874_);
v_searcher_875_ = lean_ctor_get(v_x_847_, 1);
lean_inc(v_searcher_875_);
lean_dec_ref_known(v_x_847_, 2);
v___x_876_ = lean_apply_2(v_h__4_852_, v_currPos_874_, v_searcher_875_);
return v___x_876_;
}
}
default: 
{
lean_object* v_currPos_877_; lean_object* v_searcher_878_; lean_object* v___x_879_; 
lean_dec(v_h__4_852_);
lean_dec(v_h__3_851_);
lean_dec(v_h__2_850_);
lean_dec(v_h__1_849_);
v_currPos_877_ = lean_ctor_get(v_x_847_, 0);
lean_inc(v_currPos_877_);
v_searcher_878_ = lean_ctor_get(v_x_847_, 1);
lean_inc(v_searcher_878_);
lean_dec_ref_known(v_x_847_, 2);
v___x_879_ = lean_apply_2(v_h__5_853_, v_currPos_877_, v_searcher_878_);
return v___x_879_;
}
}
}
else
{
lean_dec(v_h__5_853_);
lean_dec(v_h__4_852_);
lean_dec(v_h__3_851_);
lean_dec(v_h__2_850_);
lean_dec(v_h__1_849_);
switch(lean_obj_tag(v_x_848_))
{
case 0:
{
lean_object* v_it_880_; lean_object* v_out_881_; lean_object* v___x_882_; 
lean_dec(v_h__8_856_);
lean_dec(v_h__7_855_);
v_it_880_ = lean_ctor_get(v_x_848_, 0);
lean_inc(v_it_880_);
v_out_881_ = lean_ctor_get(v_x_848_, 1);
lean_inc(v_out_881_);
lean_dec_ref_known(v_x_848_, 2);
v___x_882_ = lean_apply_2(v_h__6_854_, v_it_880_, v_out_881_);
return v___x_882_;
}
case 1:
{
lean_object* v_it_883_; lean_object* v___x_884_; 
lean_dec(v_h__8_856_);
lean_dec(v_h__6_854_);
v_it_883_ = lean_ctor_get(v_x_848_, 0);
lean_inc(v_it_883_);
lean_dec_ref_known(v_x_848_, 1);
v___x_884_ = lean_apply_1(v_h__7_855_, v_it_883_);
return v___x_884_;
}
default: 
{
lean_object* v___x_885_; lean_object* v___x_886_; 
lean_dec(v_h__7_855_);
lean_dec(v_h__6_854_);
v___x_885_ = lean_box(0);
v___x_886_ = lean_apply_1(v_h__8_856_, v___x_885_);
return v___x_886_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(lean_object* v_00_u03c1_887_, lean_object* v_00_u03c3_888_, lean_object* v_pat_889_, lean_object* v_inst_890_, lean_object* v_s_891_, lean_object* v_motive_892_, lean_object* v_x_893_, lean_object* v_x_894_, lean_object* v_h__1_895_, lean_object* v_h__2_896_, lean_object* v_h__3_897_, lean_object* v_h__4_898_, lean_object* v_h__5_899_, lean_object* v_h__6_900_, lean_object* v_h__7_901_, lean_object* v_h__8_902_){
_start:
{
if (lean_obj_tag(v_x_893_) == 0)
{
lean_dec(v_h__8_902_);
lean_dec(v_h__7_901_);
lean_dec(v_h__6_900_);
switch(lean_obj_tag(v_x_894_))
{
case 0:
{
lean_object* v_it_903_; 
lean_dec(v_h__5_899_);
lean_dec(v_h__4_898_);
lean_dec(v_h__3_897_);
v_it_903_ = lean_ctor_get(v_x_894_, 0);
if (lean_obj_tag(v_it_903_) == 0)
{
lean_object* v_currPos_904_; lean_object* v_searcher_905_; lean_object* v_out_906_; lean_object* v_currPos_907_; lean_object* v_searcher_908_; lean_object* v___x_909_; 
lean_inc_ref(v_it_903_);
lean_dec(v_h__2_896_);
v_currPos_904_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_currPos_904_);
v_searcher_905_ = lean_ctor_get(v_x_893_, 1);
lean_inc(v_searcher_905_);
lean_dec_ref_known(v_x_893_, 2);
v_out_906_ = lean_ctor_get(v_x_894_, 1);
lean_inc(v_out_906_);
lean_dec_ref_known(v_x_894_, 2);
v_currPos_907_ = lean_ctor_get(v_it_903_, 0);
lean_inc(v_currPos_907_);
v_searcher_908_ = lean_ctor_get(v_it_903_, 1);
lean_inc(v_searcher_908_);
lean_dec_ref_known(v_it_903_, 2);
v___x_909_ = lean_apply_5(v_h__1_895_, v_currPos_904_, v_searcher_905_, v_currPos_907_, v_searcher_908_, v_out_906_);
return v___x_909_;
}
else
{
lean_object* v_currPos_910_; lean_object* v_searcher_911_; lean_object* v_out_912_; lean_object* v___x_913_; 
lean_dec(v_h__1_895_);
v_currPos_910_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_currPos_910_);
v_searcher_911_ = lean_ctor_get(v_x_893_, 1);
lean_inc(v_searcher_911_);
lean_dec_ref_known(v_x_893_, 2);
v_out_912_ = lean_ctor_get(v_x_894_, 1);
lean_inc(v_out_912_);
lean_dec_ref_known(v_x_894_, 2);
v___x_913_ = lean_apply_3(v_h__2_896_, v_currPos_910_, v_searcher_911_, v_out_912_);
return v___x_913_;
}
}
case 1:
{
lean_object* v_it_914_; 
lean_dec(v_h__5_899_);
lean_dec(v_h__2_896_);
lean_dec(v_h__1_895_);
v_it_914_ = lean_ctor_get(v_x_894_, 0);
lean_inc(v_it_914_);
lean_dec_ref_known(v_x_894_, 1);
if (lean_obj_tag(v_it_914_) == 0)
{
lean_object* v_currPos_915_; lean_object* v_searcher_916_; lean_object* v_currPos_917_; lean_object* v_searcher_918_; lean_object* v___x_919_; 
lean_dec(v_h__4_898_);
v_currPos_915_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_currPos_915_);
v_searcher_916_ = lean_ctor_get(v_x_893_, 1);
lean_inc(v_searcher_916_);
lean_dec_ref_known(v_x_893_, 2);
v_currPos_917_ = lean_ctor_get(v_it_914_, 0);
lean_inc(v_currPos_917_);
v_searcher_918_ = lean_ctor_get(v_it_914_, 1);
lean_inc(v_searcher_918_);
lean_dec_ref_known(v_it_914_, 2);
v___x_919_ = lean_apply_4(v_h__3_897_, v_currPos_915_, v_searcher_916_, v_currPos_917_, v_searcher_918_);
return v___x_919_;
}
else
{
lean_object* v_currPos_920_; lean_object* v_searcher_921_; lean_object* v___x_922_; 
lean_dec(v_h__3_897_);
v_currPos_920_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_currPos_920_);
v_searcher_921_ = lean_ctor_get(v_x_893_, 1);
lean_inc(v_searcher_921_);
lean_dec_ref_known(v_x_893_, 2);
v___x_922_ = lean_apply_2(v_h__4_898_, v_currPos_920_, v_searcher_921_);
return v___x_922_;
}
}
default: 
{
lean_object* v_currPos_923_; lean_object* v_searcher_924_; lean_object* v___x_925_; 
lean_dec(v_h__4_898_);
lean_dec(v_h__3_897_);
lean_dec(v_h__2_896_);
lean_dec(v_h__1_895_);
v_currPos_923_ = lean_ctor_get(v_x_893_, 0);
lean_inc(v_currPos_923_);
v_searcher_924_ = lean_ctor_get(v_x_893_, 1);
lean_inc(v_searcher_924_);
lean_dec_ref_known(v_x_893_, 2);
v___x_925_ = lean_apply_2(v_h__5_899_, v_currPos_923_, v_searcher_924_);
return v___x_925_;
}
}
}
else
{
lean_dec(v_h__5_899_);
lean_dec(v_h__4_898_);
lean_dec(v_h__3_897_);
lean_dec(v_h__2_896_);
lean_dec(v_h__1_895_);
switch(lean_obj_tag(v_x_894_))
{
case 0:
{
lean_object* v_it_926_; lean_object* v_out_927_; lean_object* v___x_928_; 
lean_dec(v_h__8_902_);
lean_dec(v_h__7_901_);
v_it_926_ = lean_ctor_get(v_x_894_, 0);
lean_inc(v_it_926_);
v_out_927_ = lean_ctor_get(v_x_894_, 1);
lean_inc(v_out_927_);
lean_dec_ref_known(v_x_894_, 2);
v___x_928_ = lean_apply_2(v_h__6_900_, v_it_926_, v_out_927_);
return v___x_928_;
}
case 1:
{
lean_object* v_it_929_; lean_object* v___x_930_; 
lean_dec(v_h__8_902_);
lean_dec(v_h__6_900_);
v_it_929_ = lean_ctor_get(v_x_894_, 0);
lean_inc(v_it_929_);
lean_dec_ref_known(v_x_894_, 1);
v___x_930_ = lean_apply_1(v_h__7_901_, v_it_929_);
return v___x_930_;
}
default: 
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_h__7_901_);
lean_dec(v_h__6_900_);
v___x_931_ = lean_box(0);
v___x_932_ = lean_apply_1(v_h__8_902_, v___x_931_);
return v___x_932_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___boxed(lean_object* v_00_u03c1_933_, lean_object* v_00_u03c3_934_, lean_object* v_pat_935_, lean_object* v_inst_936_, lean_object* v_s_937_, lean_object* v_motive_938_, lean_object* v_x_939_, lean_object* v_x_940_, lean_object* v_h__1_941_, lean_object* v_h__2_942_, lean_object* v_h__3_943_, lean_object* v_h__4_944_, lean_object* v_h__5_945_, lean_object* v_h__6_946_, lean_object* v_h__7_947_, lean_object* v_h__8_948_){
_start:
{
lean_object* v_res_949_; 
v_res_949_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(v_00_u03c1_933_, v_00_u03c3_934_, v_pat_935_, v_inst_936_, v_s_937_, v_motive_938_, v_x_939_, v_x_940_, v_h__1_941_, v_h__2_942_, v_h__3_943_, v_h__4_944_, v_h__5_945_, v_h__6_946_, v_h__7_947_, v_h__8_948_);
lean_dec_ref(v_s_937_);
lean_dec(v_inst_936_);
lean_dec(v_pat_935_);
return v_res_949_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_951_; 
v___x_951_ = lean_box(0);
return v___x_951_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg();
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation(lean_object* v_00_u03c1_954_, lean_object* v_00_u03c3_955_, lean_object* v_inst_956_, lean_object* v_pat_957_, lean_object* v_inst_958_, lean_object* v_s_959_, lean_object* v_inst_960_){
_start:
{
lean_object* v___x_961_; 
v___x_961_ = lean_box(0);
return v___x_961_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_962_, lean_object* v_00_u03c3_963_, lean_object* v_inst_964_, lean_object* v_pat_965_, lean_object* v_inst_966_, lean_object* v_s_967_, lean_object* v_inst_968_){
_start:
{
lean_object* v_res_969_; 
v_res_969_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_SplitInclusiveIterator_finitenessRelation(v_00_u03c1_962_, v_00_u03c3_963_, v_inst_964_, v_pat_965_, v_inst_966_, v_s_967_, v_inst_968_);
lean_dec_ref(v_s_967_);
lean_dec(v_inst_966_);
lean_dec(v_pat_965_);
lean_dec(v_inst_964_);
return v_res_969_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0(lean_object* v_toPure_970_, lean_object* v_recur_971_, lean_object* v_it_972_, lean_object* v_____do__lift_973_){
_start:
{
if (lean_obj_tag(v_____do__lift_973_) == 0)
{
lean_object* v_a_974_; lean_object* v___x_975_; 
lean_dec(v_it_972_);
lean_dec(v_recur_971_);
v_a_974_ = lean_ctor_get(v_____do__lift_973_, 0);
lean_inc(v_a_974_);
lean_dec_ref_known(v_____do__lift_973_, 1);
v___x_975_ = lean_apply_2(v_toPure_970_, lean_box(0), v_a_974_);
return v___x_975_;
}
else
{
lean_object* v_a_976_; lean_object* v___x_977_; 
lean_dec(v_toPure_970_);
v_a_976_ = lean_ctor_get(v_____do__lift_973_, 0);
lean_inc(v_a_976_);
lean_dec_ref_known(v_____do__lift_973_, 1);
v___x_977_ = lean_apply_4(v_recur_971_, v_it_972_, v_a_976_, lean_box(0), lean_box(0));
return v___x_977_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1(lean_object* v_toPure_978_, lean_object* v_recur_979_, lean_object* v___y_980_, lean_object* v_acc_981_, lean_object* v_toBind_982_, lean_object* v_s_983_){
_start:
{
switch(lean_obj_tag(v_s_983_))
{
case 0:
{
lean_object* v_it_984_; lean_object* v_out_985_; lean_object* v___f_986_; lean_object* v___x_987_; lean_object* v___x_988_; 
v_it_984_ = lean_ctor_get(v_s_983_, 0);
lean_inc(v_it_984_);
v_out_985_ = lean_ctor_get(v_s_983_, 1);
lean_inc(v_out_985_);
lean_dec_ref_known(v_s_983_, 2);
v___f_986_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_986_, 0, v_toPure_978_);
lean_closure_set(v___f_986_, 1, v_recur_979_);
lean_closure_set(v___f_986_, 2, v_it_984_);
v___x_987_ = lean_apply_3(v___y_980_, v_out_985_, lean_box(0), v_acc_981_);
v___x_988_ = lean_apply_4(v_toBind_982_, lean_box(0), lean_box(0), v___x_987_, v___f_986_);
return v___x_988_;
}
case 1:
{
lean_object* v_it_989_; lean_object* v___x_990_; 
lean_dec(v_toBind_982_);
lean_dec(v___y_980_);
lean_dec(v_toPure_978_);
v_it_989_ = lean_ctor_get(v_s_983_, 0);
lean_inc(v_it_989_);
lean_dec_ref_known(v_s_983_, 1);
v___x_990_ = lean_apply_4(v_recur_979_, v_it_989_, v_acc_981_, lean_box(0), lean_box(0));
return v___x_990_;
}
default: 
{
lean_object* v___x_991_; 
lean_dec(v_toBind_982_);
lean_dec(v___y_980_);
lean_dec(v_recur_979_);
v___x_991_ = lean_apply_2(v_toPure_978_, lean_box(0), v_acc_981_);
return v___x_991_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2(lean_object* v_toPure_992_, lean_object* v___y_993_, lean_object* v_toBind_994_, lean_object* v_inst_995_, lean_object* v_s_996_, lean_object* v_lift_997_, lean_object* v_it_998_, lean_object* v_acc_999_, lean_object* v_hP_1000_, lean_object* v_recur_1001_){
_start:
{
lean_object* v___f_1002_; 
v___f_1002_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_1002_, 0, v_toPure_992_);
lean_closure_set(v___f_1002_, 1, v_recur_1001_);
lean_closure_set(v___f_1002_, 2, v___y_993_);
lean_closure_set(v___f_1002_, 3, v_acc_999_);
lean_closure_set(v___f_1002_, 4, v_toBind_994_);
if (lean_obj_tag(v_it_998_) == 0)
{
lean_object* v_currPos_1003_; lean_object* v_searcher_1004_; lean_object* v___x_1006_; uint8_t v_isShared_1007_; uint8_t v_isSharedCheck_1061_; 
v_currPos_1003_ = lean_ctor_get(v_it_998_, 0);
v_searcher_1004_ = lean_ctor_get(v_it_998_, 1);
v_isSharedCheck_1061_ = !lean_is_exclusive(v_it_998_);
if (v_isSharedCheck_1061_ == 0)
{
v___x_1006_ = v_it_998_;
v_isShared_1007_ = v_isSharedCheck_1061_;
goto v_resetjp_1005_;
}
else
{
lean_inc(v_searcher_1004_);
lean_inc(v_currPos_1003_);
lean_dec(v_it_998_);
v___x_1006_ = lean_box(0);
v_isShared_1007_ = v_isSharedCheck_1061_;
goto v_resetjp_1005_;
}
v_resetjp_1005_:
{
lean_object* v___x_1008_; 
lean_inc_ref(v_s_996_);
v___x_1008_ = lean_apply_2(v_inst_995_, v_s_996_, v_searcher_1004_);
switch(lean_obj_tag(v___x_1008_))
{
case 0:
{
lean_object* v_out_1009_; 
v_out_1009_ = lean_ctor_get(v___x_1008_, 1);
lean_inc(v_out_1009_);
if (lean_obj_tag(v_out_1009_) == 0)
{
lean_object* v_it_1010_; lean_object* v___x_1012_; 
lean_dec_ref_known(v_out_1009_, 2);
lean_dec_ref(v_s_996_);
v_it_1010_ = lean_ctor_get(v___x_1008_, 0);
lean_inc(v_it_1010_);
lean_dec_ref_known(v___x_1008_, 2);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v_it_1010_);
v___x_1012_ = v___x_1006_;
goto v_reusejp_1011_;
}
else
{
lean_object* v_reuseFailAlloc_1015_; 
v_reuseFailAlloc_1015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1015_, 0, v_currPos_1003_);
lean_ctor_set(v_reuseFailAlloc_1015_, 1, v_it_1010_);
v___x_1012_ = v_reuseFailAlloc_1015_;
goto v_reusejp_1011_;
}
v_reusejp_1011_:
{
lean_object* v___x_1013_; lean_object* v___x_1014_; 
v___x_1013_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1013_, 0, v___x_1012_);
v___x_1014_ = lean_apply_4(v_lift_997_, lean_box(0), lean_box(0), v___f_1002_, v___x_1013_);
return v___x_1014_;
}
}
else
{
lean_object* v_it_1016_; lean_object* v___x_1018_; uint8_t v_isShared_1019_; uint8_t v_isSharedCheck_1029_; 
v_it_1016_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1029_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1029_ == 0)
{
lean_object* v_unused_1030_; 
v_unused_1030_ = lean_ctor_get(v___x_1008_, 1);
lean_dec(v_unused_1030_);
v___x_1018_ = v___x_1008_;
v_isShared_1019_ = v_isSharedCheck_1029_;
goto v_resetjp_1017_;
}
else
{
lean_inc(v_it_1016_);
lean_dec(v___x_1008_);
v___x_1018_ = lean_box(0);
v_isShared_1019_ = v_isSharedCheck_1029_;
goto v_resetjp_1017_;
}
v_resetjp_1017_:
{
lean_object* v_endPos_1020_; lean_object* v_slice_1021_; lean_object* v_nextIt_1023_; 
v_endPos_1020_ = lean_ctor_get(v_out_1009_, 1);
lean_inc(v_endPos_1020_);
lean_dec_ref_known(v_out_1009_, 2);
v_slice_1021_ = l_String_Slice_slice_x21(v_s_996_, v_currPos_1003_, v_endPos_1020_);
lean_dec(v_currPos_1003_);
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v_it_1016_);
lean_ctor_set(v___x_1006_, 0, v_endPos_1020_);
v_nextIt_1023_ = v___x_1006_;
goto v_reusejp_1022_;
}
else
{
lean_object* v_reuseFailAlloc_1028_; 
v_reuseFailAlloc_1028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1028_, 0, v_endPos_1020_);
lean_ctor_set(v_reuseFailAlloc_1028_, 1, v_it_1016_);
v_nextIt_1023_ = v_reuseFailAlloc_1028_;
goto v_reusejp_1022_;
}
v_reusejp_1022_:
{
lean_object* v___x_1025_; 
if (v_isShared_1019_ == 0)
{
lean_ctor_set(v___x_1018_, 1, v_slice_1021_);
lean_ctor_set(v___x_1018_, 0, v_nextIt_1023_);
v___x_1025_ = v___x_1018_;
goto v_reusejp_1024_;
}
else
{
lean_object* v_reuseFailAlloc_1027_; 
v_reuseFailAlloc_1027_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1027_, 0, v_nextIt_1023_);
lean_ctor_set(v_reuseFailAlloc_1027_, 1, v_slice_1021_);
v___x_1025_ = v_reuseFailAlloc_1027_;
goto v_reusejp_1024_;
}
v_reusejp_1024_:
{
lean_object* v___x_1026_; 
v___x_1026_ = lean_apply_4(v_lift_997_, lean_box(0), lean_box(0), v___f_1002_, v___x_1025_);
return v___x_1026_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1031_; lean_object* v___x_1033_; uint8_t v_isShared_1034_; uint8_t v_isSharedCheck_1042_; 
lean_dec_ref(v_s_996_);
v_it_1031_ = lean_ctor_get(v___x_1008_, 0);
v_isSharedCheck_1042_ = !lean_is_exclusive(v___x_1008_);
if (v_isSharedCheck_1042_ == 0)
{
v___x_1033_ = v___x_1008_;
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
else
{
lean_inc(v_it_1031_);
lean_dec(v___x_1008_);
v___x_1033_ = lean_box(0);
v_isShared_1034_ = v_isSharedCheck_1042_;
goto v_resetjp_1032_;
}
v_resetjp_1032_:
{
lean_object* v___x_1036_; 
if (v_isShared_1007_ == 0)
{
lean_ctor_set(v___x_1006_, 1, v_it_1031_);
v___x_1036_ = v___x_1006_;
goto v_reusejp_1035_;
}
else
{
lean_object* v_reuseFailAlloc_1041_; 
v_reuseFailAlloc_1041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1041_, 0, v_currPos_1003_);
lean_ctor_set(v_reuseFailAlloc_1041_, 1, v_it_1031_);
v___x_1036_ = v_reuseFailAlloc_1041_;
goto v_reusejp_1035_;
}
v_reusejp_1035_:
{
lean_object* v___x_1038_; 
if (v_isShared_1034_ == 0)
{
lean_ctor_set(v___x_1033_, 0, v___x_1036_);
v___x_1038_ = v___x_1033_;
goto v_reusejp_1037_;
}
else
{
lean_object* v_reuseFailAlloc_1040_; 
v_reuseFailAlloc_1040_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1040_, 0, v___x_1036_);
v___x_1038_ = v_reuseFailAlloc_1040_;
goto v_reusejp_1037_;
}
v_reusejp_1037_:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_apply_4(v_lift_997_, lean_box(0), lean_box(0), v___f_1002_, v___x_1038_);
return v___x_1039_;
}
}
}
}
default: 
{
lean_object* v_str_1043_; lean_object* v_startInclusive_1044_; lean_object* v_endExclusive_1045_; lean_object* v___x_1047_; uint8_t v_isShared_1048_; uint8_t v_isSharedCheck_1060_; 
lean_del_object(v___x_1006_);
v_str_1043_ = lean_ctor_get(v_s_996_, 0);
v_startInclusive_1044_ = lean_ctor_get(v_s_996_, 1);
v_endExclusive_1045_ = lean_ctor_get(v_s_996_, 2);
v_isSharedCheck_1060_ = !lean_is_exclusive(v_s_996_);
if (v_isSharedCheck_1060_ == 0)
{
v___x_1047_ = v_s_996_;
v_isShared_1048_ = v_isSharedCheck_1060_;
goto v_resetjp_1046_;
}
else
{
lean_inc(v_endExclusive_1045_);
lean_inc(v_startInclusive_1044_);
lean_inc(v_str_1043_);
lean_dec(v_s_996_);
v___x_1047_ = lean_box(0);
v_isShared_1048_ = v_isSharedCheck_1060_;
goto v_resetjp_1046_;
}
v_resetjp_1046_:
{
lean_object* v___x_1049_; uint8_t v_decide_1050_; 
v___x_1049_ = lean_nat_sub(v_endExclusive_1045_, v_startInclusive_1044_);
v_decide_1050_ = lean_nat_dec_eq(v_currPos_1003_, v___x_1049_);
lean_dec(v___x_1049_);
if (v_decide_1050_ == 0)
{
lean_object* v___x_1051_; lean_object* v_slice_1053_; 
v___x_1051_ = lean_nat_add(v_startInclusive_1044_, v_currPos_1003_);
lean_dec(v_currPos_1003_);
lean_dec(v_startInclusive_1044_);
if (v_isShared_1048_ == 0)
{
lean_ctor_set(v___x_1047_, 1, v___x_1051_);
v_slice_1053_ = v___x_1047_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_str_1043_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v___x_1051_);
lean_ctor_set(v_reuseFailAlloc_1057_, 2, v_endExclusive_1045_);
v_slice_1053_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1054_; lean_object* v___x_1055_; lean_object* v___x_1056_; 
v___x_1054_ = lean_box(1);
v___x_1055_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1055_, 0, v___x_1054_);
lean_ctor_set(v___x_1055_, 1, v_slice_1053_);
v___x_1056_ = lean_apply_4(v_lift_997_, lean_box(0), lean_box(0), v___f_1002_, v___x_1055_);
return v___x_1056_;
}
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_del_object(v___x_1047_);
lean_dec(v_endExclusive_1045_);
lean_dec(v_startInclusive_1044_);
lean_dec_ref(v_str_1043_);
lean_dec(v_currPos_1003_);
v___x_1058_ = lean_box(2);
v___x_1059_ = lean_apply_4(v_lift_997_, lean_box(0), lean_box(0), v___f_1002_, v___x_1058_);
return v___x_1059_;
}
}
}
}
}
}
else
{
lean_object* v___x_1062_; lean_object* v___x_1063_; 
lean_dec_ref(v_s_996_);
lean_dec(v_inst_995_);
v___x_1062_ = lean_box(2);
v___x_1063_ = lean_apply_4(v_lift_997_, lean_box(0), lean_box(0), v___f_1002_, v___x_1062_);
return v___x_1063_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3(lean_object* v_inst_1064_, lean_object* v_inst_1065_, lean_object* v_s_1066_, lean_object* v_lift_1067_, lean_object* v_00_u03b3_1068_, lean_object* v_Pl_1069_, lean_object* v_it_1070_, lean_object* v_init_1071_, lean_object* v___y_1072_){
_start:
{
lean_object* v_toApplicative_1073_; lean_object* v_toBind_1074_; lean_object* v_toPure_1075_; lean_object* v___f_1076_; lean_object* v___x_1077_; 
v_toApplicative_1073_ = lean_ctor_get(v_inst_1064_, 0);
lean_inc_ref(v_toApplicative_1073_);
v_toBind_1074_ = lean_ctor_get(v_inst_1064_, 1);
lean_inc(v_toBind_1074_);
lean_dec_ref(v_inst_1064_);
v_toPure_1075_ = lean_ctor_get(v_toApplicative_1073_, 1);
lean_inc(v_toPure_1075_);
lean_dec_ref(v_toApplicative_1073_);
v___f_1076_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_1076_, 0, v_toPure_1075_);
lean_closure_set(v___f_1076_, 1, v___y_1072_);
lean_closure_set(v___f_1076_, 2, v_toBind_1074_);
lean_closure_set(v___f_1076_, 3, v_inst_1065_);
lean_closure_set(v___f_1076_, 4, v_s_1066_);
lean_closure_set(v___f_1076_, 5, v_lift_1067_);
v___x_1077_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1076_, v_it_1070_, v_init_1071_, lean_box(0));
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg(lean_object* v_inst_1078_, lean_object* v_inst_1079_, lean_object* v_s_1080_){
_start:
{
lean_object* v___f_1081_; 
v___f_1081_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1081_, 0, v_inst_1079_);
lean_closure_set(v___f_1081_, 1, v_inst_1078_);
lean_closure_set(v___f_1081_, 2, v_s_1080_);
return v___f_1081_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(lean_object* v_00_u03c1_1082_, lean_object* v_00_u03c3_1083_, lean_object* v_inst_1084_, lean_object* v_pat_1085_, lean_object* v_inst_1086_, lean_object* v_n_1087_, lean_object* v_inst_1088_, lean_object* v_s_1089_){
_start:
{
lean_object* v___f_1090_; 
v___f_1090_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1090_, 0, v_inst_1088_);
lean_closure_set(v___f_1090_, 1, v_inst_1084_);
lean_closure_set(v___f_1090_, 2, v_s_1089_);
return v___f_1090_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___boxed(lean_object* v_00_u03c1_1091_, lean_object* v_00_u03c3_1092_, lean_object* v_inst_1093_, lean_object* v_pat_1094_, lean_object* v_inst_1095_, lean_object* v_n_1096_, lean_object* v_inst_1097_, lean_object* v_s_1098_){
_start:
{
lean_object* v_res_1099_; 
v_res_1099_ = l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(v_00_u03c1_1091_, v_00_u03c3_1092_, v_inst_1093_, v_pat_1094_, v_inst_1095_, v_n_1096_, v_inst_1097_, v_s_1098_);
lean_dec(v_inst_1095_);
lean_dec(v_pat_1094_);
return v_res_1099_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___redArg(lean_object* v_s_1100_, lean_object* v_inst_1101_){
_start:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v___x_1102_ = lean_unsigned_to_nat(0u);
v___x_1103_ = lean_apply_1(v_inst_1101_, v_s_1100_);
v___x_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1104_, 0, v___x_1102_);
lean_ctor_set(v___x_1104_, 1, v___x_1103_);
return v___x_1104_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive(lean_object* v_00_u03c1_1105_, lean_object* v_00_u03c3_1106_, lean_object* v_s_1107_, lean_object* v_pat_1108_, lean_object* v_inst_1109_){
_start:
{
lean_object* v___x_1110_; 
v___x_1110_ = l_String_Slice_splitInclusive___redArg(v_s_1107_, v_inst_1109_);
return v___x_1110_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___boxed(lean_object* v_00_u03c1_1111_, lean_object* v_00_u03c3_1112_, lean_object* v_s_1113_, lean_object* v_pat_1114_, lean_object* v_inst_1115_){
_start:
{
lean_object* v_res_1116_; 
v_res_1116_ = l_String_Slice_splitInclusive(v_00_u03c1_1111_, v_00_u03c3_1112_, v_s_1113_, v_pat_1114_, v_inst_1115_);
lean_dec(v_pat_1114_);
return v_res_1116_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___redArg(lean_object* v_s_1117_, lean_object* v_inst_1118_){
_start:
{
lean_object* v_skipPrefix_x3f_1119_; lean_object* v___x_1120_; 
v_skipPrefix_x3f_1119_ = lean_ctor_get(v_inst_1118_, 0);
lean_inc_ref(v_skipPrefix_x3f_1119_);
lean_dec_ref(v_inst_1118_);
v___x_1120_ = lean_apply_1(v_skipPrefix_x3f_1119_, v_s_1117_);
return v___x_1120_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f(lean_object* v_00_u03c1_1121_, lean_object* v_s_1122_, lean_object* v_pat_1123_, lean_object* v_inst_1124_){
_start:
{
lean_object* v_skipPrefix_x3f_1125_; lean_object* v___x_1126_; 
v_skipPrefix_x3f_1125_ = lean_ctor_get(v_inst_1124_, 0);
lean_inc_ref(v_skipPrefix_x3f_1125_);
lean_dec_ref(v_inst_1124_);
v___x_1126_ = lean_apply_1(v_skipPrefix_x3f_1125_, v_s_1122_);
return v___x_1126_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___boxed(lean_object* v_00_u03c1_1127_, lean_object* v_s_1128_, lean_object* v_pat_1129_, lean_object* v_inst_1130_){
_start:
{
lean_object* v_res_1131_; 
v_res_1131_ = l_String_Slice_skipPrefix_x3f(v_00_u03c1_1127_, v_s_1128_, v_pat_1129_, v_inst_1130_);
lean_dec(v_pat_1129_);
return v_res_1131_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg(lean_object* v_s_1132_, lean_object* v_pos_1133_, lean_object* v_inst_1134_){
_start:
{
lean_object* v_str_1135_; lean_object* v_startInclusive_1136_; lean_object* v_endExclusive_1137_; lean_object* v___x_1139_; uint8_t v_isShared_1140_; uint8_t v_isSharedCheck_1156_; 
v_str_1135_ = lean_ctor_get(v_s_1132_, 0);
v_startInclusive_1136_ = lean_ctor_get(v_s_1132_, 1);
v_endExclusive_1137_ = lean_ctor_get(v_s_1132_, 2);
v_isSharedCheck_1156_ = !lean_is_exclusive(v_s_1132_);
if (v_isSharedCheck_1156_ == 0)
{
v___x_1139_ = v_s_1132_;
v_isShared_1140_ = v_isSharedCheck_1156_;
goto v_resetjp_1138_;
}
else
{
lean_inc(v_endExclusive_1137_);
lean_inc(v_startInclusive_1136_);
lean_inc(v_str_1135_);
lean_dec(v_s_1132_);
v___x_1139_ = lean_box(0);
v_isShared_1140_ = v_isSharedCheck_1156_;
goto v_resetjp_1138_;
}
v_resetjp_1138_:
{
lean_object* v_skipPrefix_x3f_1141_; lean_object* v___x_1142_; lean_object* v___x_1144_; 
v_skipPrefix_x3f_1141_ = lean_ctor_get(v_inst_1134_, 0);
lean_inc_ref(v_skipPrefix_x3f_1141_);
lean_dec_ref(v_inst_1134_);
v___x_1142_ = lean_nat_add(v_startInclusive_1136_, v_pos_1133_);
lean_dec(v_startInclusive_1136_);
if (v_isShared_1140_ == 0)
{
lean_ctor_set(v___x_1139_, 1, v___x_1142_);
v___x_1144_ = v___x_1139_;
goto v_reusejp_1143_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v_str_1135_);
lean_ctor_set(v_reuseFailAlloc_1155_, 1, v___x_1142_);
lean_ctor_set(v_reuseFailAlloc_1155_, 2, v_endExclusive_1137_);
v___x_1144_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1143_;
}
v_reusejp_1143_:
{
lean_object* v___x_1145_; 
v___x_1145_ = lean_apply_1(v_skipPrefix_x3f_1141_, v___x_1144_);
if (lean_obj_tag(v___x_1145_) == 0)
{
return v___x_1145_;
}
else
{
lean_object* v_val_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1154_; 
v_val_1146_ = lean_ctor_get(v___x_1145_, 0);
v_isSharedCheck_1154_ = !lean_is_exclusive(v___x_1145_);
if (v_isSharedCheck_1154_ == 0)
{
v___x_1148_ = v___x_1145_;
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_val_1146_);
lean_dec(v___x_1145_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1154_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; lean_object* v___x_1152_; 
v___x_1150_ = lean_nat_add(v_pos_1133_, v_val_1146_);
lean_dec(v_val_1146_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1150_);
v___x_1152_ = v___x_1148_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1153_; 
v_reuseFailAlloc_1153_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1153_, 0, v___x_1150_);
v___x_1152_ = v_reuseFailAlloc_1153_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
return v___x_1152_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg___boxed(lean_object* v_s_1157_, lean_object* v_pos_1158_, lean_object* v_inst_1159_){
_start:
{
lean_object* v_res_1160_; 
v_res_1160_ = l_String_Slice_Pos_skip_x3f___redArg(v_s_1157_, v_pos_1158_, v_inst_1159_);
lean_dec(v_pos_1158_);
return v_res_1160_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f(lean_object* v_00_u03c1_1161_, lean_object* v_s_1162_, lean_object* v_pos_1163_, lean_object* v_pat_1164_, lean_object* v_inst_1165_){
_start:
{
lean_object* v_str_1166_; lean_object* v_startInclusive_1167_; lean_object* v_endExclusive_1168_; lean_object* v___x_1170_; uint8_t v_isShared_1171_; uint8_t v_isSharedCheck_1187_; 
v_str_1166_ = lean_ctor_get(v_s_1162_, 0);
v_startInclusive_1167_ = lean_ctor_get(v_s_1162_, 1);
v_endExclusive_1168_ = lean_ctor_get(v_s_1162_, 2);
v_isSharedCheck_1187_ = !lean_is_exclusive(v_s_1162_);
if (v_isSharedCheck_1187_ == 0)
{
v___x_1170_ = v_s_1162_;
v_isShared_1171_ = v_isSharedCheck_1187_;
goto v_resetjp_1169_;
}
else
{
lean_inc(v_endExclusive_1168_);
lean_inc(v_startInclusive_1167_);
lean_inc(v_str_1166_);
lean_dec(v_s_1162_);
v___x_1170_ = lean_box(0);
v_isShared_1171_ = v_isSharedCheck_1187_;
goto v_resetjp_1169_;
}
v_resetjp_1169_:
{
lean_object* v_skipPrefix_x3f_1172_; lean_object* v___x_1173_; lean_object* v___x_1175_; 
v_skipPrefix_x3f_1172_ = lean_ctor_get(v_inst_1165_, 0);
lean_inc_ref(v_skipPrefix_x3f_1172_);
lean_dec_ref(v_inst_1165_);
v___x_1173_ = lean_nat_add(v_startInclusive_1167_, v_pos_1163_);
lean_dec(v_startInclusive_1167_);
if (v_isShared_1171_ == 0)
{
lean_ctor_set(v___x_1170_, 1, v___x_1173_);
v___x_1175_ = v___x_1170_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1186_; 
v_reuseFailAlloc_1186_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1186_, 0, v_str_1166_);
lean_ctor_set(v_reuseFailAlloc_1186_, 1, v___x_1173_);
lean_ctor_set(v_reuseFailAlloc_1186_, 2, v_endExclusive_1168_);
v___x_1175_ = v_reuseFailAlloc_1186_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1176_; 
v___x_1176_ = lean_apply_1(v_skipPrefix_x3f_1172_, v___x_1175_);
if (lean_obj_tag(v___x_1176_) == 0)
{
return v___x_1176_;
}
else
{
lean_object* v_val_1177_; lean_object* v___x_1179_; uint8_t v_isShared_1180_; uint8_t v_isSharedCheck_1185_; 
v_val_1177_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1185_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1185_ == 0)
{
v___x_1179_ = v___x_1176_;
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
else
{
lean_inc(v_val_1177_);
lean_dec(v___x_1176_);
v___x_1179_ = lean_box(0);
v_isShared_1180_ = v_isSharedCheck_1185_;
goto v_resetjp_1178_;
}
v_resetjp_1178_:
{
lean_object* v___x_1181_; lean_object* v___x_1183_; 
v___x_1181_ = lean_nat_add(v_pos_1163_, v_val_1177_);
lean_dec(v_val_1177_);
if (v_isShared_1180_ == 0)
{
lean_ctor_set(v___x_1179_, 0, v___x_1181_);
v___x_1183_ = v___x_1179_;
goto v_reusejp_1182_;
}
else
{
lean_object* v_reuseFailAlloc_1184_; 
v_reuseFailAlloc_1184_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1184_, 0, v___x_1181_);
v___x_1183_ = v_reuseFailAlloc_1184_;
goto v_reusejp_1182_;
}
v_reusejp_1182_:
{
return v___x_1183_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_1188_, lean_object* v_s_1189_, lean_object* v_pos_1190_, lean_object* v_pat_1191_, lean_object* v_inst_1192_){
_start:
{
lean_object* v_res_1193_; 
v_res_1193_ = l_String_Slice_Pos_skip_x3f(v_00_u03c1_1188_, v_s_1189_, v_pos_1190_, v_pat_1191_, v_inst_1192_);
lean_dec(v_pat_1191_);
lean_dec(v_pos_1190_);
return v_res_1193_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___redArg(lean_object* v_s_1194_, lean_object* v_inst_1195_){
_start:
{
lean_object* v_skipPrefix_x3f_1196_; lean_object* v___x_1197_; 
v_skipPrefix_x3f_1196_ = lean_ctor_get(v_inst_1195_, 0);
lean_inc_ref(v_skipPrefix_x3f_1196_);
lean_dec_ref(v_inst_1195_);
lean_inc_ref(v_s_1194_);
v___x_1197_ = lean_apply_1(v_skipPrefix_x3f_1196_, v_s_1194_);
if (lean_obj_tag(v___x_1197_) == 0)
{
lean_object* v___x_1198_; 
lean_dec_ref(v_s_1194_);
v___x_1198_ = lean_box(0);
return v___x_1198_;
}
else
{
lean_object* v_val_1199_; lean_object* v___x_1201_; uint8_t v_isShared_1202_; uint8_t v_isSharedCheck_1217_; 
v_val_1199_ = lean_ctor_get(v___x_1197_, 0);
v_isSharedCheck_1217_ = !lean_is_exclusive(v___x_1197_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1201_ = v___x_1197_;
v_isShared_1202_ = v_isSharedCheck_1217_;
goto v_resetjp_1200_;
}
else
{
lean_inc(v_val_1199_);
lean_dec(v___x_1197_);
v___x_1201_ = lean_box(0);
v_isShared_1202_ = v_isSharedCheck_1217_;
goto v_resetjp_1200_;
}
v_resetjp_1200_:
{
lean_object* v_str_1203_; lean_object* v_startInclusive_1204_; lean_object* v_endExclusive_1205_; lean_object* v___x_1207_; uint8_t v_isShared_1208_; uint8_t v_isSharedCheck_1216_; 
v_str_1203_ = lean_ctor_get(v_s_1194_, 0);
v_startInclusive_1204_ = lean_ctor_get(v_s_1194_, 1);
v_endExclusive_1205_ = lean_ctor_get(v_s_1194_, 2);
v_isSharedCheck_1216_ = !lean_is_exclusive(v_s_1194_);
if (v_isSharedCheck_1216_ == 0)
{
v___x_1207_ = v_s_1194_;
v_isShared_1208_ = v_isSharedCheck_1216_;
goto v_resetjp_1206_;
}
else
{
lean_inc(v_endExclusive_1205_);
lean_inc(v_startInclusive_1204_);
lean_inc(v_str_1203_);
lean_dec(v_s_1194_);
v___x_1207_ = lean_box(0);
v_isShared_1208_ = v_isSharedCheck_1216_;
goto v_resetjp_1206_;
}
v_resetjp_1206_:
{
lean_object* v___x_1209_; lean_object* v___x_1211_; 
v___x_1209_ = lean_nat_add(v_startInclusive_1204_, v_val_1199_);
lean_dec(v_val_1199_);
lean_dec(v_startInclusive_1204_);
if (v_isShared_1208_ == 0)
{
lean_ctor_set(v___x_1207_, 1, v___x_1209_);
v___x_1211_ = v___x_1207_;
goto v_reusejp_1210_;
}
else
{
lean_object* v_reuseFailAlloc_1215_; 
v_reuseFailAlloc_1215_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1215_, 0, v_str_1203_);
lean_ctor_set(v_reuseFailAlloc_1215_, 1, v___x_1209_);
lean_ctor_set(v_reuseFailAlloc_1215_, 2, v_endExclusive_1205_);
v___x_1211_ = v_reuseFailAlloc_1215_;
goto v_reusejp_1210_;
}
v_reusejp_1210_:
{
lean_object* v___x_1213_; 
if (v_isShared_1202_ == 0)
{
lean_ctor_set(v___x_1201_, 0, v___x_1211_);
v___x_1213_ = v___x_1201_;
goto v_reusejp_1212_;
}
else
{
lean_object* v_reuseFailAlloc_1214_; 
v_reuseFailAlloc_1214_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1214_, 0, v___x_1211_);
v___x_1213_ = v_reuseFailAlloc_1214_;
goto v_reusejp_1212_;
}
v_reusejp_1212_:
{
return v___x_1213_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f(lean_object* v_00_u03c1_1218_, lean_object* v_s_1219_, lean_object* v_pat_1220_, lean_object* v_inst_1221_){
_start:
{
lean_object* v_skipPrefix_x3f_1222_; lean_object* v___x_1223_; 
v_skipPrefix_x3f_1222_ = lean_ctor_get(v_inst_1221_, 0);
lean_inc_ref(v_skipPrefix_x3f_1222_);
lean_dec_ref(v_inst_1221_);
lean_inc_ref(v_s_1219_);
v___x_1223_ = lean_apply_1(v_skipPrefix_x3f_1222_, v_s_1219_);
if (lean_obj_tag(v___x_1223_) == 0)
{
lean_object* v___x_1224_; 
lean_dec_ref(v_s_1219_);
v___x_1224_ = lean_box(0);
return v___x_1224_;
}
else
{
lean_object* v_val_1225_; lean_object* v___x_1227_; uint8_t v_isShared_1228_; uint8_t v_isSharedCheck_1243_; 
v_val_1225_ = lean_ctor_get(v___x_1223_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1223_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1227_ = v___x_1223_;
v_isShared_1228_ = v_isSharedCheck_1243_;
goto v_resetjp_1226_;
}
else
{
lean_inc(v_val_1225_);
lean_dec(v___x_1223_);
v___x_1227_ = lean_box(0);
v_isShared_1228_ = v_isSharedCheck_1243_;
goto v_resetjp_1226_;
}
v_resetjp_1226_:
{
lean_object* v_str_1229_; lean_object* v_startInclusive_1230_; lean_object* v_endExclusive_1231_; lean_object* v___x_1233_; uint8_t v_isShared_1234_; uint8_t v_isSharedCheck_1242_; 
v_str_1229_ = lean_ctor_get(v_s_1219_, 0);
v_startInclusive_1230_ = lean_ctor_get(v_s_1219_, 1);
v_endExclusive_1231_ = lean_ctor_get(v_s_1219_, 2);
v_isSharedCheck_1242_ = !lean_is_exclusive(v_s_1219_);
if (v_isSharedCheck_1242_ == 0)
{
v___x_1233_ = v_s_1219_;
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
else
{
lean_inc(v_endExclusive_1231_);
lean_inc(v_startInclusive_1230_);
lean_inc(v_str_1229_);
lean_dec(v_s_1219_);
v___x_1233_ = lean_box(0);
v_isShared_1234_ = v_isSharedCheck_1242_;
goto v_resetjp_1232_;
}
v_resetjp_1232_:
{
lean_object* v___x_1235_; lean_object* v___x_1237_; 
v___x_1235_ = lean_nat_add(v_startInclusive_1230_, v_val_1225_);
lean_dec(v_val_1225_);
lean_dec(v_startInclusive_1230_);
if (v_isShared_1234_ == 0)
{
lean_ctor_set(v___x_1233_, 1, v___x_1235_);
v___x_1237_ = v___x_1233_;
goto v_reusejp_1236_;
}
else
{
lean_object* v_reuseFailAlloc_1241_; 
v_reuseFailAlloc_1241_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1241_, 0, v_str_1229_);
lean_ctor_set(v_reuseFailAlloc_1241_, 1, v___x_1235_);
lean_ctor_set(v_reuseFailAlloc_1241_, 2, v_endExclusive_1231_);
v___x_1237_ = v_reuseFailAlloc_1241_;
goto v_reusejp_1236_;
}
v_reusejp_1236_:
{
lean_object* v___x_1239_; 
if (v_isShared_1228_ == 0)
{
lean_ctor_set(v___x_1227_, 0, v___x_1237_);
v___x_1239_ = v___x_1227_;
goto v_reusejp_1238_;
}
else
{
lean_object* v_reuseFailAlloc_1240_; 
v_reuseFailAlloc_1240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1240_, 0, v___x_1237_);
v___x_1239_ = v_reuseFailAlloc_1240_;
goto v_reusejp_1238_;
}
v_reusejp_1238_:
{
return v___x_1239_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_1244_, lean_object* v_s_1245_, lean_object* v_pat_1246_, lean_object* v_inst_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_String_Slice_dropPrefix_x3f(v_00_u03c1_1244_, v_s_1245_, v_pat_1246_, v_inst_1247_);
lean_dec(v_pat_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___redArg(lean_object* v_s_1249_, lean_object* v_inst_1250_){
_start:
{
lean_object* v_skipPrefix_x3f_1251_; lean_object* v___x_1252_; 
v_skipPrefix_x3f_1251_ = lean_ctor_get(v_inst_1250_, 0);
lean_inc_ref(v_skipPrefix_x3f_1251_);
lean_dec_ref(v_inst_1250_);
lean_inc_ref(v_s_1249_);
v___x_1252_ = lean_apply_1(v_skipPrefix_x3f_1251_, v_s_1249_);
if (lean_obj_tag(v___x_1252_) == 0)
{
return v_s_1249_;
}
else
{
lean_object* v_val_1253_; lean_object* v_str_1254_; lean_object* v_startInclusive_1255_; lean_object* v_endExclusive_1256_; lean_object* v___x_1258_; uint8_t v_isShared_1259_; uint8_t v_isSharedCheck_1264_; 
v_val_1253_ = lean_ctor_get(v___x_1252_, 0);
lean_inc(v_val_1253_);
lean_dec_ref_known(v___x_1252_, 1);
v_str_1254_ = lean_ctor_get(v_s_1249_, 0);
v_startInclusive_1255_ = lean_ctor_get(v_s_1249_, 1);
v_endExclusive_1256_ = lean_ctor_get(v_s_1249_, 2);
v_isSharedCheck_1264_ = !lean_is_exclusive(v_s_1249_);
if (v_isSharedCheck_1264_ == 0)
{
v___x_1258_ = v_s_1249_;
v_isShared_1259_ = v_isSharedCheck_1264_;
goto v_resetjp_1257_;
}
else
{
lean_inc(v_endExclusive_1256_);
lean_inc(v_startInclusive_1255_);
lean_inc(v_str_1254_);
lean_dec(v_s_1249_);
v___x_1258_ = lean_box(0);
v_isShared_1259_ = v_isSharedCheck_1264_;
goto v_resetjp_1257_;
}
v_resetjp_1257_:
{
lean_object* v___x_1260_; lean_object* v___x_1262_; 
v___x_1260_ = lean_nat_add(v_startInclusive_1255_, v_val_1253_);
lean_dec(v_val_1253_);
lean_dec(v_startInclusive_1255_);
if (v_isShared_1259_ == 0)
{
lean_ctor_set(v___x_1258_, 1, v___x_1260_);
v___x_1262_ = v___x_1258_;
goto v_reusejp_1261_;
}
else
{
lean_object* v_reuseFailAlloc_1263_; 
v_reuseFailAlloc_1263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1263_, 0, v_str_1254_);
lean_ctor_set(v_reuseFailAlloc_1263_, 1, v___x_1260_);
lean_ctor_set(v_reuseFailAlloc_1263_, 2, v_endExclusive_1256_);
v___x_1262_ = v_reuseFailAlloc_1263_;
goto v_reusejp_1261_;
}
v_reusejp_1261_:
{
return v___x_1262_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix(lean_object* v_00_u03c1_1265_, lean_object* v_s_1266_, lean_object* v_pat_1267_, lean_object* v_inst_1268_){
_start:
{
lean_object* v___x_1269_; 
v___x_1269_ = l_String_Slice_dropPrefix___redArg(v_s_1266_, v_inst_1268_);
return v___x_1269_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___boxed(lean_object* v_00_u03c1_1270_, lean_object* v_s_1271_, lean_object* v_pat_1272_, lean_object* v_inst_1273_){
_start:
{
lean_object* v_res_1274_; 
v_res_1274_ = l_String_Slice_dropPrefix(v_00_u03c1_1270_, v_s_1271_, v_pat_1272_, v_inst_1273_);
lean_dec(v_pat_1272_);
return v_res_1274_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__0(lean_object* v_x_1275_, lean_object* v_x_1276_, lean_object* v_f_1277_, lean_object* v_c_1278_){
_start:
{
lean_object* v___x_1279_; 
v___x_1279_ = lean_apply_1(v_f_1277_, v_c_1278_);
return v___x_1279_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1(lean_object* v_s_1280_, lean_object* v_inst_1281_, lean_object* v_replacement_1282_, lean_object* v_x1_1283_, lean_object* v_x2_1284_, lean_object* v_x3_1285_){
_start:
{
if (lean_obj_tag(v_x1_1283_) == 0)
{
lean_object* v_startPos_1286_; lean_object* v_endPos_1287_; lean_object* v___x_1288_; lean_object* v_str_1289_; lean_object* v_startInclusive_1290_; lean_object* v_endExclusive_1291_; lean_object* v___x_1292_; lean_object* v___x_1293_; lean_object* v___x_1294_; 
lean_dec(v_replacement_1282_);
lean_dec_ref(v_inst_1281_);
v_startPos_1286_ = lean_ctor_get(v_x1_1283_, 0);
v_endPos_1287_ = lean_ctor_get(v_x1_1283_, 1);
v___x_1288_ = l_String_Slice_slice_x21(v_s_1280_, v_startPos_1286_, v_endPos_1287_);
v_str_1289_ = lean_ctor_get(v___x_1288_, 0);
lean_inc_ref(v_str_1289_);
v_startInclusive_1290_ = lean_ctor_get(v___x_1288_, 1);
lean_inc(v_startInclusive_1290_);
v_endExclusive_1291_ = lean_ctor_get(v___x_1288_, 2);
lean_inc(v_endExclusive_1291_);
lean_dec_ref(v___x_1288_);
v___x_1292_ = lean_string_utf8_extract_fast(v_str_1289_, v_startInclusive_1290_, v_endExclusive_1291_);
lean_dec(v_endExclusive_1291_);
lean_dec(v_startInclusive_1290_);
lean_dec_ref(v_str_1289_);
v___x_1293_ = lean_string_append(v_x3_1285_, v___x_1292_);
lean_dec_ref(v___x_1292_);
v___x_1294_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1294_, 0, v___x_1293_);
return v___x_1294_;
}
else
{
lean_object* v___x_1295_; lean_object* v_str_1296_; lean_object* v_startInclusive_1297_; lean_object* v_endExclusive_1298_; lean_object* v___x_1299_; lean_object* v___x_1300_; lean_object* v___x_1301_; 
lean_dec_ref(v_s_1280_);
v___x_1295_ = lean_apply_1(v_inst_1281_, v_replacement_1282_);
v_str_1296_ = lean_ctor_get(v___x_1295_, 0);
lean_inc_ref(v_str_1296_);
v_startInclusive_1297_ = lean_ctor_get(v___x_1295_, 1);
lean_inc(v_startInclusive_1297_);
v_endExclusive_1298_ = lean_ctor_get(v___x_1295_, 2);
lean_inc(v_endExclusive_1298_);
lean_dec_ref(v___x_1295_);
v___x_1299_ = lean_string_utf8_extract_fast(v_str_1296_, v_startInclusive_1297_, v_endExclusive_1298_);
lean_dec(v_endExclusive_1298_);
lean_dec(v_startInclusive_1297_);
lean_dec_ref(v_str_1296_);
v___x_1300_ = lean_string_append(v_x3_1285_, v___x_1299_);
lean_dec_ref(v___x_1299_);
v___x_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1301_, 0, v___x_1300_);
return v___x_1301_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1___boxed(lean_object* v_s_1302_, lean_object* v_inst_1303_, lean_object* v_replacement_1304_, lean_object* v_x1_1305_, lean_object* v_x2_1306_, lean_object* v_x3_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_String_Slice_replace___redArg___lam__1(v_s_1302_, v_inst_1303_, v_replacement_1304_, v_x1_1305_, v_x2_1306_, v_x3_1307_);
lean_dec_ref(v_x1_1305_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg(lean_object* v_inst_1311_, lean_object* v_inst_1312_, lean_object* v_s_1313_, lean_object* v_inst_1314_, lean_object* v_replacement_1315_){
_start:
{
lean_object* v___f_1316_; lean_object* v___f_1317_; lean_object* v___x_1318_; lean_object* v___x_1319_; lean_object* v___x_1320_; 
v___f_1316_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1313_, 2);
v___f_1317_ = lean_alloc_closure((void*)(l_String_Slice_replace___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1317_, 0, v_s_1313_);
lean_closure_set(v___f_1317_, 1, v_inst_1312_);
lean_closure_set(v___f_1317_, 2, v_replacement_1315_);
v___x_1318_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
v___x_1319_ = lean_apply_1(v_inst_1314_, v_s_1313_);
v___x_1320_ = lean_apply_7(v_inst_1311_, v_s_1313_, v___f_1316_, lean_box(0), lean_box(0), v___x_1319_, v___x_1318_, v___f_1317_);
return v___x_1320_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace(lean_object* v_00_u03c1_1321_, lean_object* v_00_u03c3_1322_, lean_object* v_inst_1323_, lean_object* v_inst_1324_, lean_object* v_00_u03b1_1325_, lean_object* v_inst_1326_, lean_object* v_s_1327_, lean_object* v_pattern_1328_, lean_object* v_inst_1329_, lean_object* v_replacement_1330_){
_start:
{
lean_object* v___x_1331_; 
v___x_1331_ = l_String_Slice_replace___redArg(v_inst_1324_, v_inst_1326_, v_s_1327_, v_inst_1329_, v_replacement_1330_);
return v___x_1331_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___boxed(lean_object* v_00_u03c1_1332_, lean_object* v_00_u03c3_1333_, lean_object* v_inst_1334_, lean_object* v_inst_1335_, lean_object* v_00_u03b1_1336_, lean_object* v_inst_1337_, lean_object* v_s_1338_, lean_object* v_pattern_1339_, lean_object* v_inst_1340_, lean_object* v_replacement_1341_){
_start:
{
lean_object* v_res_1342_; 
v_res_1342_ = l_String_Slice_replace(v_00_u03c1_1332_, v_00_u03c3_1333_, v_inst_1334_, v_inst_1335_, v_00_u03b1_1336_, v_inst_1337_, v_s_1338_, v_pattern_1339_, v_inst_1340_, v_replacement_1341_);
lean_dec(v_pattern_1339_);
lean_dec(v_inst_1334_);
return v_res_1342_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object* v_s_1343_, lean_object* v_pos_1344_, lean_object* v_inst_1345_){
_start:
{
lean_object* v_str_1346_; lean_object* v_startInclusive_1347_; lean_object* v_endExclusive_1348_; lean_object* v_skipPrefix_x3f_1349_; lean_object* v___x_1350_; lean_object* v___x_1351_; lean_object* v___x_1352_; 
v_str_1346_ = lean_ctor_get(v_s_1343_, 0);
v_startInclusive_1347_ = lean_ctor_get(v_s_1343_, 1);
v_endExclusive_1348_ = lean_ctor_get(v_s_1343_, 2);
v_skipPrefix_x3f_1349_ = lean_ctor_get(v_inst_1345_, 0);
v___x_1350_ = lean_nat_add(v_startInclusive_1347_, v_pos_1344_);
lean_inc(v_endExclusive_1348_);
lean_inc_ref(v_str_1346_);
v___x_1351_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1351_, 0, v_str_1346_);
lean_ctor_set(v___x_1351_, 1, v___x_1350_);
lean_ctor_set(v___x_1351_, 2, v_endExclusive_1348_);
lean_inc_ref(v_skipPrefix_x3f_1349_);
v___x_1352_ = lean_apply_1(v_skipPrefix_x3f_1349_, v___x_1351_);
if (lean_obj_tag(v___x_1352_) == 0)
{
lean_dec_ref(v_inst_1345_);
return v_pos_1344_;
}
else
{
lean_object* v_val_1353_; lean_object* v___x_1354_; lean_object* v___x_1355_; lean_object* v___x_1356_; uint8_t v___x_1357_; 
v_val_1353_ = lean_ctor_get(v___x_1352_, 0);
lean_inc(v_val_1353_);
lean_dec_ref_known(v___x_1352_, 1);
v___x_1354_ = lean_nat_add(v_pos_1344_, v_val_1353_);
lean_dec(v_val_1353_);
v___x_1355_ = lean_unsigned_to_nat(1u);
v___x_1356_ = lean_nat_add(v_pos_1344_, v___x_1355_);
v___x_1357_ = lean_nat_dec_le(v___x_1356_, v___x_1354_);
lean_dec(v___x_1356_);
if (v___x_1357_ == 0)
{
lean_dec(v___x_1354_);
lean_dec_ref(v_inst_1345_);
return v_pos_1344_;
}
else
{
lean_dec(v_pos_1344_);
v_pos_1344_ = v___x_1354_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg___boxed(lean_object* v_s_1359_, lean_object* v_pos_1360_, lean_object* v_inst_1361_){
_start:
{
lean_object* v_res_1362_; 
v_res_1362_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1359_, v_pos_1360_, v_inst_1361_);
lean_dec_ref(v_s_1359_);
return v_res_1362_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile(lean_object* v_00_u03c1_1363_, lean_object* v_s_1364_, lean_object* v_pos_1365_, lean_object* v_pat_1366_, lean_object* v_inst_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1364_, v_pos_1365_, v_inst_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___boxed(lean_object* v_00_u03c1_1369_, lean_object* v_s_1370_, lean_object* v_pos_1371_, lean_object* v_pat_1372_, lean_object* v_inst_1373_){
_start:
{
lean_object* v_res_1374_; 
v_res_1374_ = l_String_Slice_Pos_skipWhile(v_00_u03c1_1369_, v_s_1370_, v_pos_1371_, v_pat_1372_, v_inst_1373_);
lean_dec(v_pat_1372_);
lean_dec_ref(v_s_1370_);
return v_res_1374_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object* v_x_1375_, lean_object* v_h__1_1376_, lean_object* v_h__2_1377_){
_start:
{
if (lean_obj_tag(v_x_1375_) == 0)
{
lean_object* v___x_1378_; lean_object* v___x_1379_; 
lean_dec(v_h__1_1376_);
v___x_1378_ = lean_box(0);
v___x_1379_ = lean_apply_1(v_h__2_1377_, v___x_1378_);
return v___x_1379_;
}
else
{
lean_object* v_val_1380_; lean_object* v___x_1381_; 
lean_dec(v_h__2_1377_);
v_val_1380_ = lean_ctor_get(v_x_1375_, 0);
lean_inc(v_val_1380_);
lean_dec_ref_known(v_x_1375_, 1);
v___x_1381_ = lean_apply_1(v_h__1_1376_, v_val_1380_);
return v___x_1381_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object* v_s_1382_, lean_object* v_motive_1383_, lean_object* v_x_1384_, lean_object* v_h__1_1385_, lean_object* v_h__2_1386_){
_start:
{
if (lean_obj_tag(v_x_1384_) == 0)
{
lean_object* v___x_1387_; lean_object* v___x_1388_; 
lean_dec(v_h__1_1385_);
v___x_1387_ = lean_box(0);
v___x_1388_ = lean_apply_1(v_h__2_1386_, v___x_1387_);
return v___x_1388_;
}
else
{
lean_object* v_val_1389_; lean_object* v___x_1390_; 
lean_dec(v_h__2_1386_);
v_val_1389_ = lean_ctor_get(v_x_1384_, 0);
lean_inc(v_val_1389_);
lean_dec_ref_known(v_x_1384_, 1);
v___x_1390_ = lean_apply_1(v_h__1_1385_, v_val_1389_);
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object* v_s_1391_, lean_object* v_motive_1392_, lean_object* v_x_1393_, lean_object* v_h__1_1394_, lean_object* v_h__2_1395_){
_start:
{
lean_object* v_res_1396_; 
v_res_1396_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_1391_, v_motive_1392_, v_x_1393_, v_h__1_1394_, v_h__2_1395_);
lean_dec_ref(v_s_1391_);
return v_res_1396_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg(lean_object* v_s_1397_, lean_object* v_inst_1398_){
_start:
{
lean_object* v___x_1399_; lean_object* v___x_1400_; 
v___x_1399_ = lean_unsigned_to_nat(0u);
v___x_1400_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1397_, v___x_1399_, v_inst_1398_);
return v___x_1400_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg___boxed(lean_object* v_s_1401_, lean_object* v_inst_1402_){
_start:
{
lean_object* v_res_1403_; 
v_res_1403_ = l_String_Slice_skipPrefixWhile___redArg(v_s_1401_, v_inst_1402_);
lean_dec_ref(v_s_1401_);
return v_res_1403_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile(lean_object* v_00_u03c1_1404_, lean_object* v_s_1405_, lean_object* v_pat_1406_, lean_object* v_inst_1407_){
_start:
{
lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___x_1408_ = lean_unsigned_to_nat(0u);
v___x_1409_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1405_, v___x_1408_, v_inst_1407_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___boxed(lean_object* v_00_u03c1_1410_, lean_object* v_s_1411_, lean_object* v_pat_1412_, lean_object* v_inst_1413_){
_start:
{
lean_object* v_res_1414_; 
v_res_1414_ = l_String_Slice_skipPrefixWhile(v_00_u03c1_1410_, v_s_1411_, v_pat_1412_, v_inst_1413_);
lean_dec(v_pat_1412_);
lean_dec_ref(v_s_1411_);
return v_res_1414_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg(lean_object* v_s_1415_, lean_object* v_inst_1416_){
_start:
{
lean_object* v_str_1417_; lean_object* v_startInclusive_1418_; lean_object* v_endExclusive_1419_; lean_object* v___x_1420_; lean_object* v___x_1421_; lean_object* v___x_1423_; uint8_t v_isShared_1424_; uint8_t v_isSharedCheck_1429_; 
v_str_1417_ = lean_ctor_get(v_s_1415_, 0);
lean_inc_ref(v_str_1417_);
v_startInclusive_1418_ = lean_ctor_get(v_s_1415_, 1);
lean_inc(v_startInclusive_1418_);
v_endExclusive_1419_ = lean_ctor_get(v_s_1415_, 2);
lean_inc(v_endExclusive_1419_);
v___x_1420_ = lean_unsigned_to_nat(0u);
v___x_1421_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1415_, v___x_1420_, v_inst_1416_);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_s_1415_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; lean_object* v_unused_1431_; lean_object* v_unused_1432_; 
v_unused_1430_ = lean_ctor_get(v_s_1415_, 2);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_s_1415_, 1);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_s_1415_, 0);
lean_dec(v_unused_1432_);
v___x_1423_ = v_s_1415_;
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
else
{
lean_dec(v_s_1415_);
v___x_1423_ = lean_box(0);
v_isShared_1424_ = v_isSharedCheck_1429_;
goto v_resetjp_1422_;
}
v_resetjp_1422_:
{
lean_object* v___x_1425_; lean_object* v___x_1427_; 
v___x_1425_ = lean_nat_add(v_startInclusive_1418_, v___x_1421_);
lean_dec(v___x_1421_);
lean_dec(v_startInclusive_1418_);
if (v_isShared_1424_ == 0)
{
lean_ctor_set(v___x_1423_, 1, v___x_1425_);
v___x_1427_ = v___x_1423_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_str_1417_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v___x_1425_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v_endExclusive_1419_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile(lean_object* v_00_u03c1_1433_, lean_object* v_s_1434_, lean_object* v_pat_1435_, lean_object* v_inst_1436_){
_start:
{
lean_object* v_str_1437_; lean_object* v_startInclusive_1438_; lean_object* v_endExclusive_1439_; lean_object* v___x_1440_; lean_object* v___x_1441_; lean_object* v___x_1443_; uint8_t v_isShared_1444_; uint8_t v_isSharedCheck_1449_; 
v_str_1437_ = lean_ctor_get(v_s_1434_, 0);
lean_inc_ref(v_str_1437_);
v_startInclusive_1438_ = lean_ctor_get(v_s_1434_, 1);
lean_inc(v_startInclusive_1438_);
v_endExclusive_1439_ = lean_ctor_get(v_s_1434_, 2);
lean_inc(v_endExclusive_1439_);
v___x_1440_ = lean_unsigned_to_nat(0u);
v___x_1441_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1434_, v___x_1440_, v_inst_1436_);
v_isSharedCheck_1449_ = !lean_is_exclusive(v_s_1434_);
if (v_isSharedCheck_1449_ == 0)
{
lean_object* v_unused_1450_; lean_object* v_unused_1451_; lean_object* v_unused_1452_; 
v_unused_1450_ = lean_ctor_get(v_s_1434_, 2);
lean_dec(v_unused_1450_);
v_unused_1451_ = lean_ctor_get(v_s_1434_, 1);
lean_dec(v_unused_1451_);
v_unused_1452_ = lean_ctor_get(v_s_1434_, 0);
lean_dec(v_unused_1452_);
v___x_1443_ = v_s_1434_;
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
else
{
lean_dec(v_s_1434_);
v___x_1443_ = lean_box(0);
v_isShared_1444_ = v_isSharedCheck_1449_;
goto v_resetjp_1442_;
}
v_resetjp_1442_:
{
lean_object* v___x_1445_; lean_object* v___x_1447_; 
v___x_1445_ = lean_nat_add(v_startInclusive_1438_, v___x_1441_);
lean_dec(v___x_1441_);
lean_dec(v_startInclusive_1438_);
if (v_isShared_1444_ == 0)
{
lean_ctor_set(v___x_1443_, 1, v___x_1445_);
v___x_1447_ = v___x_1443_;
goto v_reusejp_1446_;
}
else
{
lean_object* v_reuseFailAlloc_1448_; 
v_reuseFailAlloc_1448_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1448_, 0, v_str_1437_);
lean_ctor_set(v_reuseFailAlloc_1448_, 1, v___x_1445_);
lean_ctor_set(v_reuseFailAlloc_1448_, 2, v_endExclusive_1439_);
v___x_1447_ = v_reuseFailAlloc_1448_;
goto v_reusejp_1446_;
}
v_reusejp_1446_:
{
return v___x_1447_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___boxed(lean_object* v_00_u03c1_1453_, lean_object* v_s_1454_, lean_object* v_pat_1455_, lean_object* v_inst_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_String_Slice_dropWhile(v_00_u03c1_1453_, v_s_1454_, v_pat_1455_, v_inst_1456_);
lean_dec(v_pat_1455_);
return v_res_1457_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiStart___closed__1(void){
_start:
{
lean_object* v___x_1459_; lean_object* v___x_1460_; 
v___x_1459_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_1460_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1459_);
return v___x_1460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart(lean_object* v_s_1461_){
_start:
{
lean_object* v___x_1462_; lean_object* v_str_1463_; lean_object* v_startInclusive_1464_; lean_object* v_endExclusive_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1475_; 
v___x_1462_ = lean_obj_once(&l_String_Slice_trimAsciiStart___closed__1, &l_String_Slice_trimAsciiStart___closed__1_once, _init_l_String_Slice_trimAsciiStart___closed__1);
v_str_1463_ = lean_ctor_get(v_s_1461_, 0);
lean_inc_ref(v_str_1463_);
v_startInclusive_1464_ = lean_ctor_get(v_s_1461_, 1);
lean_inc(v_startInclusive_1464_);
v_endExclusive_1465_ = lean_ctor_get(v_s_1461_, 2);
lean_inc(v_endExclusive_1465_);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1461_, v___x_1466_, v___x_1462_);
v_isSharedCheck_1475_ = !lean_is_exclusive(v_s_1461_);
if (v_isSharedCheck_1475_ == 0)
{
lean_object* v_unused_1476_; lean_object* v_unused_1477_; lean_object* v_unused_1478_; 
v_unused_1476_ = lean_ctor_get(v_s_1461_, 2);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_s_1461_, 1);
lean_dec(v_unused_1477_);
v_unused_1478_ = lean_ctor_get(v_s_1461_, 0);
lean_dec(v_unused_1478_);
v___x_1469_ = v_s_1461_;
v_isShared_1470_ = v_isSharedCheck_1475_;
goto v_resetjp_1468_;
}
else
{
lean_dec(v_s_1461_);
v___x_1469_ = lean_box(0);
v_isShared_1470_ = v_isSharedCheck_1475_;
goto v_resetjp_1468_;
}
v_resetjp_1468_:
{
lean_object* v___x_1471_; lean_object* v___x_1473_; 
v___x_1471_ = lean_nat_add(v_startInclusive_1464_, v___x_1467_);
lean_dec(v___x_1467_);
lean_dec(v_startInclusive_1464_);
if (v_isShared_1470_ == 0)
{
lean_ctor_set(v___x_1469_, 1, v___x_1471_);
v___x_1473_ = v___x_1469_;
goto v_reusejp_1472_;
}
else
{
lean_object* v_reuseFailAlloc_1474_; 
v_reuseFailAlloc_1474_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1474_, 0, v_str_1463_);
lean_ctor_set(v_reuseFailAlloc_1474_, 1, v___x_1471_);
lean_ctor_set(v_reuseFailAlloc_1474_, 2, v_endExclusive_1465_);
v___x_1473_ = v_reuseFailAlloc_1474_;
goto v_reusejp_1472_;
}
v_reusejp_1472_:
{
return v___x_1473_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___redArg(lean_object* v_s_1479_, lean_object* v_inst_1480_){
_start:
{
lean_object* v_str_1481_; lean_object* v_startInclusive_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1486_; uint8_t v_isShared_1487_; uint8_t v_isSharedCheck_1492_; 
v_str_1481_ = lean_ctor_get(v_s_1479_, 0);
lean_inc_ref(v_str_1481_);
v_startInclusive_1482_ = lean_ctor_get(v_s_1479_, 1);
lean_inc(v_startInclusive_1482_);
v___x_1483_ = lean_unsigned_to_nat(0u);
v___x_1484_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1479_, v___x_1483_, v_inst_1480_);
v_isSharedCheck_1492_ = !lean_is_exclusive(v_s_1479_);
if (v_isSharedCheck_1492_ == 0)
{
lean_object* v_unused_1493_; lean_object* v_unused_1494_; lean_object* v_unused_1495_; 
v_unused_1493_ = lean_ctor_get(v_s_1479_, 2);
lean_dec(v_unused_1493_);
v_unused_1494_ = lean_ctor_get(v_s_1479_, 1);
lean_dec(v_unused_1494_);
v_unused_1495_ = lean_ctor_get(v_s_1479_, 0);
lean_dec(v_unused_1495_);
v___x_1486_ = v_s_1479_;
v_isShared_1487_ = v_isSharedCheck_1492_;
goto v_resetjp_1485_;
}
else
{
lean_dec(v_s_1479_);
v___x_1486_ = lean_box(0);
v_isShared_1487_ = v_isSharedCheck_1492_;
goto v_resetjp_1485_;
}
v_resetjp_1485_:
{
lean_object* v___x_1488_; lean_object* v___x_1490_; 
v___x_1488_ = lean_nat_add(v_startInclusive_1482_, v___x_1484_);
lean_dec(v___x_1484_);
if (v_isShared_1487_ == 0)
{
lean_ctor_set(v___x_1486_, 2, v___x_1488_);
v___x_1490_ = v___x_1486_;
goto v_reusejp_1489_;
}
else
{
lean_object* v_reuseFailAlloc_1491_; 
v_reuseFailAlloc_1491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1491_, 0, v_str_1481_);
lean_ctor_set(v_reuseFailAlloc_1491_, 1, v_startInclusive_1482_);
lean_ctor_set(v_reuseFailAlloc_1491_, 2, v___x_1488_);
v___x_1490_ = v_reuseFailAlloc_1491_;
goto v_reusejp_1489_;
}
v_reusejp_1489_:
{
return v___x_1490_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile(lean_object* v_00_u03c1_1496_, lean_object* v_s_1497_, lean_object* v_pat_1498_, lean_object* v_inst_1499_){
_start:
{
lean_object* v_str_1500_; lean_object* v_startInclusive_1501_; lean_object* v___x_1502_; lean_object* v___x_1503_; lean_object* v___x_1505_; uint8_t v_isShared_1506_; uint8_t v_isSharedCheck_1511_; 
v_str_1500_ = lean_ctor_get(v_s_1497_, 0);
lean_inc_ref(v_str_1500_);
v_startInclusive_1501_ = lean_ctor_get(v_s_1497_, 1);
lean_inc(v_startInclusive_1501_);
v___x_1502_ = lean_unsigned_to_nat(0u);
v___x_1503_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1497_, v___x_1502_, v_inst_1499_);
v_isSharedCheck_1511_ = !lean_is_exclusive(v_s_1497_);
if (v_isSharedCheck_1511_ == 0)
{
lean_object* v_unused_1512_; lean_object* v_unused_1513_; lean_object* v_unused_1514_; 
v_unused_1512_ = lean_ctor_get(v_s_1497_, 2);
lean_dec(v_unused_1512_);
v_unused_1513_ = lean_ctor_get(v_s_1497_, 1);
lean_dec(v_unused_1513_);
v_unused_1514_ = lean_ctor_get(v_s_1497_, 0);
lean_dec(v_unused_1514_);
v___x_1505_ = v_s_1497_;
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
else
{
lean_dec(v_s_1497_);
v___x_1505_ = lean_box(0);
v_isShared_1506_ = v_isSharedCheck_1511_;
goto v_resetjp_1504_;
}
v_resetjp_1504_:
{
lean_object* v___x_1507_; lean_object* v___x_1509_; 
v___x_1507_ = lean_nat_add(v_startInclusive_1501_, v___x_1503_);
lean_dec(v___x_1503_);
if (v_isShared_1506_ == 0)
{
lean_ctor_set(v___x_1505_, 2, v___x_1507_);
v___x_1509_ = v___x_1505_;
goto v_reusejp_1508_;
}
else
{
lean_object* v_reuseFailAlloc_1510_; 
v_reuseFailAlloc_1510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1510_, 0, v_str_1500_);
lean_ctor_set(v_reuseFailAlloc_1510_, 1, v_startInclusive_1501_);
lean_ctor_set(v_reuseFailAlloc_1510_, 2, v___x_1507_);
v___x_1509_ = v_reuseFailAlloc_1510_;
goto v_reusejp_1508_;
}
v_reusejp_1508_:
{
return v___x_1509_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___boxed(lean_object* v_00_u03c1_1515_, lean_object* v_s_1516_, lean_object* v_pat_1517_, lean_object* v_inst_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_String_Slice_takeWhile(v_00_u03c1_1515_, v_s_1516_, v_pat_1517_, v_inst_1518_);
lean_dec(v_pat_1517_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1(lean_object* v___x_1520_, lean_object* v_x1_1521_, lean_object* v_x2_1522_, lean_object* v_x3_1523_){
_start:
{
if (lean_obj_tag(v_x1_1521_) == 0)
{
lean_object* v___x_1524_; 
v___x_1524_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1524_, 0, v___x_1520_);
return v___x_1524_;
}
else
{
lean_object* v_startPos_1525_; lean_object* v___x_1526_; lean_object* v___x_1527_; 
lean_dec(v___x_1520_);
v_startPos_1525_ = lean_ctor_get(v_x1_1521_, 0);
lean_inc(v_startPos_1525_);
v___x_1526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1526_, 0, v_startPos_1525_);
v___x_1527_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1527_, 0, v___x_1526_);
return v___x_1527_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1___boxed(lean_object* v___x_1528_, lean_object* v_x1_1529_, lean_object* v_x2_1530_, lean_object* v_x3_1531_){
_start:
{
lean_object* v_res_1532_; 
v_res_1532_ = l_String_Slice_find_x3f___redArg___lam__1(v___x_1528_, v_x1_1529_, v_x2_1530_, v_x3_1531_);
lean_dec(v_x3_1531_);
lean_dec_ref(v_x1_1529_);
return v_res_1532_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg(lean_object* v_inst_1535_, lean_object* v_s_1536_, lean_object* v_inst_1537_){
_start:
{
lean_object* v___f_1538_; lean_object* v_searcher_1539_; lean_object* v___x_1540_; lean_object* v___f_1541_; lean_object* v___x_1542_; 
v___f_1538_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1536_);
v_searcher_1539_ = lean_apply_1(v_inst_1537_, v_s_1536_);
v___x_1540_ = lean_box(0);
v___f_1541_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1542_ = lean_apply_7(v_inst_1535_, v_s_1536_, v___f_1538_, lean_box(0), lean_box(0), v_searcher_1539_, v___x_1540_, v___f_1541_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f(lean_object* v_00_u03c1_1543_, lean_object* v_00_u03c3_1544_, lean_object* v_inst_1545_, lean_object* v_inst_1546_, lean_object* v_s_1547_, lean_object* v_pat_1548_, lean_object* v_inst_1549_){
_start:
{
lean_object* v___f_1550_; lean_object* v_searcher_1551_; lean_object* v___x_1552_; lean_object* v___f_1553_; lean_object* v___x_1554_; 
v___f_1550_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1547_);
v_searcher_1551_ = lean_apply_1(v_inst_1549_, v_s_1547_);
v___x_1552_ = lean_box(0);
v___f_1553_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1554_ = lean_apply_7(v_inst_1546_, v_s_1547_, v___f_1550_, lean_box(0), lean_box(0), v_searcher_1551_, v___x_1552_, v___f_1553_);
return v___x_1554_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___boxed(lean_object* v_00_u03c1_1555_, lean_object* v_00_u03c3_1556_, lean_object* v_inst_1557_, lean_object* v_inst_1558_, lean_object* v_s_1559_, lean_object* v_pat_1560_, lean_object* v_inst_1561_){
_start:
{
lean_object* v_res_1562_; 
v_res_1562_ = l_String_Slice_find_x3f(v_00_u03c1_1555_, v_00_u03c3_1556_, v_inst_1557_, v_inst_1558_, v_s_1559_, v_pat_1560_, v_inst_1561_);
lean_dec(v_pat_1560_);
lean_dec(v_inst_1557_);
return v_res_1562_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___redArg(lean_object* v_inst_1563_, lean_object* v_s_1564_, lean_object* v_inst_1565_){
_start:
{
lean_object* v___f_1566_; lean_object* v_searcher_1567_; lean_object* v___x_1568_; lean_object* v___f_1569_; lean_object* v___x_1570_; 
v___f_1566_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1564_, 2);
v_searcher_1567_ = lean_apply_1(v_inst_1565_, v_s_1564_);
v___x_1568_ = lean_box(0);
v___f_1569_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1570_ = lean_apply_7(v_inst_1563_, v_s_1564_, v___f_1566_, lean_box(0), lean_box(0), v_searcher_1567_, v___x_1568_, v___f_1569_);
if (lean_obj_tag(v___x_1570_) == 0)
{
lean_object* v_startInclusive_1571_; lean_object* v_endExclusive_1572_; lean_object* v___x_1573_; 
v_startInclusive_1571_ = lean_ctor_get(v_s_1564_, 1);
lean_inc(v_startInclusive_1571_);
v_endExclusive_1572_ = lean_ctor_get(v_s_1564_, 2);
lean_inc(v_endExclusive_1572_);
lean_dec_ref(v_s_1564_);
v___x_1573_ = lean_nat_sub(v_endExclusive_1572_, v_startInclusive_1571_);
lean_dec(v_startInclusive_1571_);
lean_dec(v_endExclusive_1572_);
return v___x_1573_;
}
else
{
lean_object* v_val_1574_; 
lean_dec_ref(v_s_1564_);
v_val_1574_ = lean_ctor_get(v___x_1570_, 0);
lean_inc(v_val_1574_);
lean_dec_ref_known(v___x_1570_, 1);
return v_val_1574_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find(lean_object* v_00_u03c1_1575_, lean_object* v_00_u03c3_1576_, lean_object* v_inst_1577_, lean_object* v_inst_1578_, lean_object* v_s_1579_, lean_object* v_pat_1580_, lean_object* v_inst_1581_){
_start:
{
lean_object* v___f_1582_; lean_object* v_searcher_1583_; lean_object* v___x_1584_; lean_object* v___f_1585_; lean_object* v___x_1586_; 
v___f_1582_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1579_, 2);
v_searcher_1583_ = lean_apply_1(v_inst_1581_, v_s_1579_);
v___x_1584_ = lean_box(0);
v___f_1585_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1586_ = lean_apply_7(v_inst_1578_, v_s_1579_, v___f_1582_, lean_box(0), lean_box(0), v_searcher_1583_, v___x_1584_, v___f_1585_);
if (lean_obj_tag(v___x_1586_) == 0)
{
lean_object* v_startInclusive_1587_; lean_object* v_endExclusive_1588_; lean_object* v___x_1589_; 
v_startInclusive_1587_ = lean_ctor_get(v_s_1579_, 1);
lean_inc(v_startInclusive_1587_);
v_endExclusive_1588_ = lean_ctor_get(v_s_1579_, 2);
lean_inc(v_endExclusive_1588_);
lean_dec_ref(v_s_1579_);
v___x_1589_ = lean_nat_sub(v_endExclusive_1588_, v_startInclusive_1587_);
lean_dec(v_startInclusive_1587_);
lean_dec(v_endExclusive_1588_);
return v___x_1589_;
}
else
{
lean_object* v_val_1590_; 
lean_dec_ref(v_s_1579_);
v_val_1590_ = lean_ctor_get(v___x_1586_, 0);
lean_inc(v_val_1590_);
lean_dec_ref_known(v___x_1586_, 1);
return v_val_1590_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___boxed(lean_object* v_00_u03c1_1591_, lean_object* v_00_u03c3_1592_, lean_object* v_inst_1593_, lean_object* v_inst_1594_, lean_object* v_s_1595_, lean_object* v_pat_1596_, lean_object* v_inst_1597_){
_start:
{
lean_object* v_res_1598_; 
v_res_1598_ = l_String_Slice_find(v_00_u03c1_1591_, v_00_u03c3_1592_, v_inst_1593_, v_inst_1594_, v_s_1595_, v_pat_1596_, v_inst_1597_);
lean_dec(v_pat_1596_);
lean_dec(v_inst_1593_);
return v_res_1598_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1(uint8_t v___x_1602_, lean_object* v_x1_1603_, lean_object* v_x2_1604_, uint8_t v_x3_1605_){
_start:
{
if (lean_obj_tag(v_x1_1603_) == 1)
{
lean_object* v___x_1606_; 
v___x_1606_ = ((lean_object*)(l_String_Slice_contains___redArg___lam__1___closed__0));
return v___x_1606_;
}
else
{
lean_object* v___x_1607_; lean_object* v___x_1608_; 
v___x_1607_ = lean_box(v___x_1602_);
v___x_1608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1608_, 0, v___x_1607_);
return v___x_1608_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1___boxed(lean_object* v___x_1609_, lean_object* v_x1_1610_, lean_object* v_x2_1611_, lean_object* v_x3_1612_){
_start:
{
uint8_t v___x_82__boxed_1613_; uint8_t v_x3_85__boxed_1614_; lean_object* v_res_1615_; 
v___x_82__boxed_1613_ = lean_unbox(v___x_1609_);
v_x3_85__boxed_1614_ = lean_unbox(v_x3_1612_);
v_res_1615_ = l_String_Slice_contains___redArg___lam__1(v___x_82__boxed_1613_, v_x1_1610_, v_x2_1611_, v_x3_85__boxed_1614_);
lean_dec_ref(v_x1_1610_);
return v_res_1615_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___redArg(lean_object* v_inst_1619_, lean_object* v_s_1620_, lean_object* v_inst_1621_){
_start:
{
lean_object* v___f_1622_; lean_object* v_searcher_1623_; uint8_t v___x_1624_; lean_object* v___f_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; uint8_t v___x_1628_; 
v___f_1622_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1620_);
v_searcher_1623_ = lean_apply_1(v_inst_1621_, v_s_1620_);
v___x_1624_ = 0;
v___f_1625_ = ((lean_object*)(l_String_Slice_contains___redArg___closed__0));
v___x_1626_ = lean_box(v___x_1624_);
v___x_1627_ = lean_apply_7(v_inst_1619_, v_s_1620_, v___f_1622_, lean_box(0), lean_box(0), v_searcher_1623_, v___x_1626_, v___f_1625_);
v___x_1628_ = lean_unbox(v___x_1627_);
return v___x_1628_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___boxed(lean_object* v_inst_1629_, lean_object* v_s_1630_, lean_object* v_inst_1631_){
_start:
{
uint8_t v_res_1632_; lean_object* v_r_1633_; 
v_res_1632_ = l_String_Slice_contains___redArg(v_inst_1629_, v_s_1630_, v_inst_1631_);
v_r_1633_ = lean_box(v_res_1632_);
return v_r_1633_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains(lean_object* v_00_u03c1_1634_, lean_object* v_00_u03c3_1635_, lean_object* v_inst_1636_, lean_object* v_inst_1637_, lean_object* v_s_1638_, lean_object* v_pat_1639_, lean_object* v_inst_1640_){
_start:
{
uint8_t v___x_1641_; 
v___x_1641_ = l_String_Slice_contains___redArg(v_inst_1637_, v_s_1638_, v_inst_1640_);
return v___x_1641_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___boxed(lean_object* v_00_u03c1_1642_, lean_object* v_00_u03c3_1643_, lean_object* v_inst_1644_, lean_object* v_inst_1645_, lean_object* v_s_1646_, lean_object* v_pat_1647_, lean_object* v_inst_1648_){
_start:
{
uint8_t v_res_1649_; lean_object* v_r_1650_; 
v_res_1649_ = l_String_Slice_contains(v_00_u03c1_1642_, v_00_u03c3_1643_, v_inst_1644_, v_inst_1645_, v_s_1646_, v_pat_1647_, v_inst_1648_);
lean_dec(v_pat_1647_);
lean_dec(v_inst_1644_);
v_r_1650_ = lean_box(v_res_1649_);
return v_r_1650_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any___redArg(lean_object* v_inst_1651_, lean_object* v_s_1652_, lean_object* v_inst_1653_){
_start:
{
uint8_t v___x_1654_; 
v___x_1654_ = l_String_Slice_contains___redArg(v_inst_1651_, v_s_1652_, v_inst_1653_);
return v___x_1654_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___redArg___boxed(lean_object* v_inst_1655_, lean_object* v_s_1656_, lean_object* v_inst_1657_){
_start:
{
uint8_t v_res_1658_; lean_object* v_r_1659_; 
v_res_1658_ = l_String_Slice_any___redArg(v_inst_1655_, v_s_1656_, v_inst_1657_);
v_r_1659_ = lean_box(v_res_1658_);
return v_r_1659_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any(lean_object* v_00_u03c1_1660_, lean_object* v_00_u03c3_1661_, lean_object* v_inst_1662_, lean_object* v_inst_1663_, lean_object* v_s_1664_, lean_object* v_pat_1665_, lean_object* v_inst_1666_){
_start:
{
uint8_t v___x_1667_; 
v___x_1667_ = l_String_Slice_contains___redArg(v_inst_1663_, v_s_1664_, v_inst_1666_);
return v___x_1667_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___boxed(lean_object* v_00_u03c1_1668_, lean_object* v_00_u03c3_1669_, lean_object* v_inst_1670_, lean_object* v_inst_1671_, lean_object* v_s_1672_, lean_object* v_pat_1673_, lean_object* v_inst_1674_){
_start:
{
uint8_t v_res_1675_; lean_object* v_r_1676_; 
v_res_1675_ = l_String_Slice_any(v_00_u03c1_1668_, v_00_u03c3_1669_, v_inst_1670_, v_inst_1671_, v_s_1672_, v_pat_1673_, v_inst_1674_);
lean_dec(v_pat_1673_);
lean_dec(v_inst_1670_);
v_r_1676_ = lean_box(v_res_1675_);
return v_r_1676_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all___redArg(lean_object* v_s_1677_, lean_object* v_inst_1678_){
_start:
{
lean_object* v_startInclusive_1679_; lean_object* v_endExclusive_1680_; lean_object* v___x_1681_; lean_object* v___x_1682_; lean_object* v___x_1683_; uint8_t v_decide_1684_; 
v_startInclusive_1679_ = lean_ctor_get(v_s_1677_, 1);
v_endExclusive_1680_ = lean_ctor_get(v_s_1677_, 2);
v___x_1681_ = lean_unsigned_to_nat(0u);
v___x_1682_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1677_, v___x_1681_, v_inst_1678_);
v___x_1683_ = lean_nat_sub(v_endExclusive_1680_, v_startInclusive_1679_);
v_decide_1684_ = lean_nat_dec_eq(v___x_1682_, v___x_1683_);
lean_dec(v___x_1683_);
lean_dec(v___x_1682_);
return v_decide_1684_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___redArg___boxed(lean_object* v_s_1685_, lean_object* v_inst_1686_){
_start:
{
uint8_t v_res_1687_; lean_object* v_r_1688_; 
v_res_1687_ = l_String_Slice_all___redArg(v_s_1685_, v_inst_1686_);
lean_dec_ref(v_s_1685_);
v_r_1688_ = lean_box(v_res_1687_);
return v_r_1688_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all(lean_object* v_00_u03c1_1689_, lean_object* v_s_1690_, lean_object* v_pat_1691_, lean_object* v_inst_1692_){
_start:
{
lean_object* v_startInclusive_1693_; lean_object* v_endExclusive_1694_; lean_object* v___x_1695_; lean_object* v___x_1696_; lean_object* v___x_1697_; uint8_t v_decide_1698_; 
v_startInclusive_1693_ = lean_ctor_get(v_s_1690_, 1);
v_endExclusive_1694_ = lean_ctor_get(v_s_1690_, 2);
v___x_1695_ = lean_unsigned_to_nat(0u);
v___x_1696_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1690_, v___x_1695_, v_inst_1692_);
v___x_1697_ = lean_nat_sub(v_endExclusive_1694_, v_startInclusive_1693_);
v_decide_1698_ = lean_nat_dec_eq(v___x_1696_, v___x_1697_);
lean_dec(v___x_1697_);
lean_dec(v___x_1696_);
return v_decide_1698_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___boxed(lean_object* v_00_u03c1_1699_, lean_object* v_s_1700_, lean_object* v_pat_1701_, lean_object* v_inst_1702_){
_start:
{
uint8_t v_res_1703_; lean_object* v_r_1704_; 
v_res_1703_ = l_String_Slice_all(v_00_u03c1_1699_, v_s_1700_, v_pat_1701_, v_inst_1702_);
lean_dec(v_pat_1701_);
lean_dec_ref(v_s_1700_);
v_r_1704_ = lean_box(v_res_1703_);
return v_r_1704_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith___redArg(lean_object* v_s_1705_, lean_object* v_inst_1706_){
_start:
{
lean_object* v_endsWith_1707_; lean_object* v___x_1708_; uint8_t v___x_1709_; 
v_endsWith_1707_ = lean_ctor_get(v_inst_1706_, 2);
lean_inc_ref(v_endsWith_1707_);
lean_dec_ref(v_inst_1706_);
v___x_1708_ = lean_apply_1(v_endsWith_1707_, v_s_1705_);
v___x_1709_ = lean_unbox(v___x_1708_);
return v___x_1709_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___redArg___boxed(lean_object* v_s_1710_, lean_object* v_inst_1711_){
_start:
{
uint8_t v_res_1712_; lean_object* v_r_1713_; 
v_res_1712_ = l_String_Slice_endsWith___redArg(v_s_1710_, v_inst_1711_);
v_r_1713_ = lean_box(v_res_1712_);
return v_r_1713_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith(lean_object* v_00_u03c1_1714_, lean_object* v_s_1715_, lean_object* v_pat_1716_, lean_object* v_inst_1717_){
_start:
{
lean_object* v_endsWith_1718_; lean_object* v___x_1719_; uint8_t v___x_1720_; 
v_endsWith_1718_ = lean_ctor_get(v_inst_1717_, 2);
lean_inc_ref(v_endsWith_1718_);
lean_dec_ref(v_inst_1717_);
v___x_1719_ = lean_apply_1(v_endsWith_1718_, v_s_1715_);
v___x_1720_ = lean_unbox(v___x_1719_);
return v___x_1720_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___boxed(lean_object* v_00_u03c1_1721_, lean_object* v_s_1722_, lean_object* v_pat_1723_, lean_object* v_inst_1724_){
_start:
{
uint8_t v_res_1725_; lean_object* v_r_1726_; 
v_res_1725_ = l_String_Slice_endsWith(v_00_u03c1_1721_, v_s_1722_, v_pat_1723_, v_inst_1724_);
lean_dec(v_pat_1723_);
v_r_1726_ = lean_box(v_res_1725_);
return v_r_1726_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg(lean_object* v_x_1727_){
_start:
{
lean_object* v___x_1728_; 
v___x_1728_ = lean_obj_tag_nat(v_x_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg___boxed(lean_object* v_x_1729_){
_start:
{
lean_object* v_res_1730_; 
v_res_1730_ = l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg(v_x_1729_);
lean_dec(v_x_1729_);
return v_res_1730_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl(lean_object* v_00_u03c3_1731_, lean_object* v_00_u03c1_1732_, lean_object* v_pat_1733_, lean_object* v_s_1734_, lean_object* v_inst_1735_, lean_object* v_x_1736_){
_start:
{
lean_object* v___x_1737_; 
v___x_1737_ = lean_obj_tag_nat(v_x_1736_);
return v___x_1737_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___boxed(lean_object* v_00_u03c3_1738_, lean_object* v_00_u03c1_1739_, lean_object* v_pat_1740_, lean_object* v_s_1741_, lean_object* v_inst_1742_, lean_object* v_x_1743_){
_start:
{
lean_object* v_res_1744_; 
v_res_1744_ = l_String_Slice_RevSplitIterator_ctorIdx___impl(v_00_u03c3_1738_, v_00_u03c1_1739_, v_pat_1740_, v_s_1741_, v_inst_1742_, v_x_1743_);
lean_dec(v_x_1743_);
lean_dec(v_inst_1742_);
lean_dec_ref(v_s_1741_);
lean_dec(v_pat_1740_);
return v_res_1744_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___redArg(lean_object* v_t_1745_, lean_object* v_k_1746_){
_start:
{
if (lean_obj_tag(v_t_1745_) == 0)
{
lean_object* v_currPos_1747_; lean_object* v_searcher_1748_; lean_object* v___x_1749_; 
v_currPos_1747_ = lean_ctor_get(v_t_1745_, 0);
lean_inc(v_currPos_1747_);
v_searcher_1748_ = lean_ctor_get(v_t_1745_, 1);
lean_inc(v_searcher_1748_);
lean_dec_ref_known(v_t_1745_, 2);
v___x_1749_ = lean_apply_2(v_k_1746_, v_currPos_1747_, v_searcher_1748_);
return v___x_1749_;
}
else
{
return v_k_1746_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim(lean_object* v_00_u03c3_1750_, lean_object* v_00_u03c1_1751_, lean_object* v_pat_1752_, lean_object* v_s_1753_, lean_object* v_inst_1754_, lean_object* v_motive_1755_, lean_object* v_ctorIdx_1756_, lean_object* v_t_1757_, lean_object* v_h_1758_, lean_object* v_k_1759_){
_start:
{
lean_object* v___x_1760_; 
v___x_1760_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1757_, v_k_1759_);
return v___x_1760_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_1761_, lean_object* v_00_u03c1_1762_, lean_object* v_pat_1763_, lean_object* v_s_1764_, lean_object* v_inst_1765_, lean_object* v_motive_1766_, lean_object* v_ctorIdx_1767_, lean_object* v_t_1768_, lean_object* v_h_1769_, lean_object* v_k_1770_){
_start:
{
lean_object* v_res_1771_; 
v_res_1771_ = l_String_Slice_RevSplitIterator_ctorElim(v_00_u03c3_1761_, v_00_u03c1_1762_, v_pat_1763_, v_s_1764_, v_inst_1765_, v_motive_1766_, v_ctorIdx_1767_, v_t_1768_, v_h_1769_, v_k_1770_);
lean_dec(v_ctorIdx_1767_);
lean_dec(v_inst_1765_);
lean_dec_ref(v_s_1764_);
lean_dec(v_pat_1763_);
return v_res_1771_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___redArg(lean_object* v_t_1772_, lean_object* v_operating_1773_){
_start:
{
lean_object* v___x_1774_; 
v___x_1774_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1772_, v_operating_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim(lean_object* v_00_u03c3_1775_, lean_object* v_00_u03c1_1776_, lean_object* v_pat_1777_, lean_object* v_s_1778_, lean_object* v_inst_1779_, lean_object* v_motive_1780_, lean_object* v_t_1781_, lean_object* v_h_1782_, lean_object* v_operating_1783_){
_start:
{
lean_object* v___x_1784_; 
v___x_1784_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1781_, v_operating_1783_);
return v___x_1784_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_1785_, lean_object* v_00_u03c1_1786_, lean_object* v_pat_1787_, lean_object* v_s_1788_, lean_object* v_inst_1789_, lean_object* v_motive_1790_, lean_object* v_t_1791_, lean_object* v_h_1792_, lean_object* v_operating_1793_){
_start:
{
lean_object* v_res_1794_; 
v_res_1794_ = l_String_Slice_RevSplitIterator_operating_elim(v_00_u03c3_1785_, v_00_u03c1_1786_, v_pat_1787_, v_s_1788_, v_inst_1789_, v_motive_1790_, v_t_1791_, v_h_1792_, v_operating_1793_);
lean_dec(v_inst_1789_);
lean_dec_ref(v_s_1788_);
lean_dec(v_pat_1787_);
return v_res_1794_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___redArg(lean_object* v_t_1795_, lean_object* v_atEnd_1796_){
_start:
{
lean_object* v___x_1797_; 
v___x_1797_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1795_, v_atEnd_1796_);
return v___x_1797_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim(lean_object* v_00_u03c3_1798_, lean_object* v_00_u03c1_1799_, lean_object* v_pat_1800_, lean_object* v_s_1801_, lean_object* v_inst_1802_, lean_object* v_motive_1803_, lean_object* v_t_1804_, lean_object* v_h_1805_, lean_object* v_atEnd_1806_){
_start:
{
lean_object* v___x_1807_; 
v___x_1807_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1804_, v_atEnd_1806_);
return v___x_1807_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_1808_, lean_object* v_00_u03c1_1809_, lean_object* v_pat_1810_, lean_object* v_s_1811_, lean_object* v_inst_1812_, lean_object* v_motive_1813_, lean_object* v_t_1814_, lean_object* v_h_1815_, lean_object* v_atEnd_1816_){
_start:
{
lean_object* v_res_1817_; 
v_res_1817_ = l_String_Slice_RevSplitIterator_atEnd_elim(v_00_u03c3_1808_, v_00_u03c1_1809_, v_pat_1810_, v_s_1811_, v_inst_1812_, v_motive_1813_, v_t_1814_, v_h_1815_, v_atEnd_1816_);
lean_dec(v_inst_1812_);
lean_dec_ref(v_s_1811_);
lean_dec(v_pat_1810_);
return v_res_1817_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg(){
_start:
{
lean_object* v___x_1819_; 
v___x_1819_ = lean_box(1);
return v___x_1819_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg___boxed(lean_object* v___dummy_1820_){
_start:
{
lean_object* v_res_1821_; 
v_res_1821_ = l_String_Slice_instInhabitedRevSplitIterator_default___redArg();
return v_res_1821_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default(lean_object* v_00_u03c3_1822_, lean_object* v_00_u03c1_1823_, lean_object* v_pat_1824_, lean_object* v_s_1825_, lean_object* v_inst_1826_){
_start:
{
lean_object* v___x_1827_; 
v___x_1827_ = lean_box(1);
return v___x_1827_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___boxed(lean_object* v_00_u03c3_1828_, lean_object* v_00_u03c1_1829_, lean_object* v_pat_1830_, lean_object* v_s_1831_, lean_object* v_inst_1832_){
_start:
{
lean_object* v_res_1833_; 
v_res_1833_ = l_String_Slice_instInhabitedRevSplitIterator_default(v_00_u03c3_1828_, v_00_u03c1_1829_, v_pat_1830_, v_s_1831_, v_inst_1832_);
lean_dec(v_inst_1832_);
lean_dec_ref(v_s_1831_);
lean_dec(v_pat_1830_);
return v_res_1833_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg(){
_start:
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_box(1);
return v___x_1835_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg___boxed(lean_object* v___dummy_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_String_Slice_instInhabitedRevSplitIterator___redArg();
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator(lean_object* v_a_1838_, lean_object* v_a_1839_, lean_object* v_a_1840_, lean_object* v_a_1841_, lean_object* v_a_1842_){
_start:
{
lean_object* v___x_1843_; 
v___x_1843_ = lean_box(1);
return v___x_1843_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___boxed(lean_object* v_a_1844_, lean_object* v_a_1845_, lean_object* v_a_1846_, lean_object* v_a_1847_, lean_object* v_a_1848_){
_start:
{
lean_object* v_res_1849_; 
v_res_1849_ = l_String_Slice_instInhabitedRevSplitIterator(v_a_1844_, v_a_1845_, v_a_1846_, v_a_1847_, v_a_1848_);
lean_dec(v_a_1848_);
lean_dec_ref(v_a_1847_);
lean_dec(v_a_1846_);
return v_res_1849_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0(lean_object* v_inst_1850_, lean_object* v_s_1851_, lean_object* v_inst_1852_, lean_object* v_x_1853_){
_start:
{
if (lean_obj_tag(v_x_1853_) == 0)
{
lean_object* v_currPos_1854_; lean_object* v_searcher_1855_; lean_object* v___x_1857_; uint8_t v_isShared_1858_; uint8_t v_isSharedCheck_1913_; 
v_currPos_1854_ = lean_ctor_get(v_x_1853_, 0);
v_searcher_1855_ = lean_ctor_get(v_x_1853_, 1);
v_isSharedCheck_1913_ = !lean_is_exclusive(v_x_1853_);
if (v_isSharedCheck_1913_ == 0)
{
v___x_1857_ = v_x_1853_;
v_isShared_1858_ = v_isSharedCheck_1913_;
goto v_resetjp_1856_;
}
else
{
lean_inc(v_searcher_1855_);
lean_inc(v_currPos_1854_);
lean_dec(v_x_1853_);
v___x_1857_ = lean_box(0);
v_isShared_1858_ = v_isSharedCheck_1913_;
goto v_resetjp_1856_;
}
v_resetjp_1856_:
{
lean_object* v___x_1859_; 
lean_inc_ref(v_s_1851_);
v___x_1859_ = lean_apply_2(v_inst_1850_, v_s_1851_, v_searcher_1855_);
switch(lean_obj_tag(v___x_1859_))
{
case 0:
{
lean_object* v_out_1860_; 
v_out_1860_ = lean_ctor_get(v___x_1859_, 1);
lean_inc(v_out_1860_);
if (lean_obj_tag(v_out_1860_) == 0)
{
lean_object* v_it_1861_; lean_object* v___x_1863_; 
lean_dec_ref_known(v_out_1860_, 2);
lean_dec_ref(v_s_1851_);
v_it_1861_ = lean_ctor_get(v___x_1859_, 0);
lean_inc(v_it_1861_);
lean_dec_ref_known(v___x_1859_, 2);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 1, v_it_1861_);
v___x_1863_ = v___x_1857_;
goto v_reusejp_1862_;
}
else
{
lean_object* v_reuseFailAlloc_1866_; 
v_reuseFailAlloc_1866_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1866_, 0, v_currPos_1854_);
lean_ctor_set(v_reuseFailAlloc_1866_, 1, v_it_1861_);
v___x_1863_ = v_reuseFailAlloc_1866_;
goto v_reusejp_1862_;
}
v_reusejp_1862_:
{
lean_object* v___x_1864_; lean_object* v___x_1865_; 
v___x_1864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1864_, 0, v___x_1863_);
v___x_1865_ = lean_apply_2(v_inst_1852_, lean_box(0), v___x_1864_);
return v___x_1865_;
}
}
else
{
lean_object* v_it_1867_; lean_object* v___x_1869_; uint8_t v_isShared_1870_; uint8_t v_isSharedCheck_1881_; 
v_it_1867_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1881_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1881_ == 0)
{
lean_object* v_unused_1882_; 
v_unused_1882_ = lean_ctor_get(v___x_1859_, 1);
lean_dec(v_unused_1882_);
v___x_1869_ = v___x_1859_;
v_isShared_1870_ = v_isSharedCheck_1881_;
goto v_resetjp_1868_;
}
else
{
lean_inc(v_it_1867_);
lean_dec(v___x_1859_);
v___x_1869_ = lean_box(0);
v_isShared_1870_ = v_isSharedCheck_1881_;
goto v_resetjp_1868_;
}
v_resetjp_1868_:
{
lean_object* v_startPos_1871_; lean_object* v_endPos_1872_; lean_object* v_slice_1873_; lean_object* v_nextIt_1875_; 
v_startPos_1871_ = lean_ctor_get(v_out_1860_, 0);
lean_inc(v_startPos_1871_);
v_endPos_1872_ = lean_ctor_get(v_out_1860_, 1);
lean_inc(v_endPos_1872_);
lean_dec_ref_known(v_out_1860_, 2);
v_slice_1873_ = l_String_Slice_slice_x21(v_s_1851_, v_endPos_1872_, v_currPos_1854_);
lean_dec(v_currPos_1854_);
lean_dec(v_endPos_1872_);
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 1, v_it_1867_);
lean_ctor_set(v___x_1857_, 0, v_startPos_1871_);
v_nextIt_1875_ = v___x_1857_;
goto v_reusejp_1874_;
}
else
{
lean_object* v_reuseFailAlloc_1880_; 
v_reuseFailAlloc_1880_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1880_, 0, v_startPos_1871_);
lean_ctor_set(v_reuseFailAlloc_1880_, 1, v_it_1867_);
v_nextIt_1875_ = v_reuseFailAlloc_1880_;
goto v_reusejp_1874_;
}
v_reusejp_1874_:
{
lean_object* v___x_1877_; 
if (v_isShared_1870_ == 0)
{
lean_ctor_set(v___x_1869_, 1, v_slice_1873_);
lean_ctor_set(v___x_1869_, 0, v_nextIt_1875_);
v___x_1877_ = v___x_1869_;
goto v_reusejp_1876_;
}
else
{
lean_object* v_reuseFailAlloc_1879_; 
v_reuseFailAlloc_1879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1879_, 0, v_nextIt_1875_);
lean_ctor_set(v_reuseFailAlloc_1879_, 1, v_slice_1873_);
v___x_1877_ = v_reuseFailAlloc_1879_;
goto v_reusejp_1876_;
}
v_reusejp_1876_:
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_apply_2(v_inst_1852_, lean_box(0), v___x_1877_);
return v___x_1878_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1883_; lean_object* v___x_1885_; uint8_t v_isShared_1886_; uint8_t v_isSharedCheck_1894_; 
lean_dec_ref(v_s_1851_);
v_it_1883_ = lean_ctor_get(v___x_1859_, 0);
v_isSharedCheck_1894_ = !lean_is_exclusive(v___x_1859_);
if (v_isSharedCheck_1894_ == 0)
{
v___x_1885_ = v___x_1859_;
v_isShared_1886_ = v_isSharedCheck_1894_;
goto v_resetjp_1884_;
}
else
{
lean_inc(v_it_1883_);
lean_dec(v___x_1859_);
v___x_1885_ = lean_box(0);
v_isShared_1886_ = v_isSharedCheck_1894_;
goto v_resetjp_1884_;
}
v_resetjp_1884_:
{
lean_object* v___x_1888_; 
if (v_isShared_1858_ == 0)
{
lean_ctor_set(v___x_1857_, 1, v_it_1883_);
v___x_1888_ = v___x_1857_;
goto v_reusejp_1887_;
}
else
{
lean_object* v_reuseFailAlloc_1893_; 
v_reuseFailAlloc_1893_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1893_, 0, v_currPos_1854_);
lean_ctor_set(v_reuseFailAlloc_1893_, 1, v_it_1883_);
v___x_1888_ = v_reuseFailAlloc_1893_;
goto v_reusejp_1887_;
}
v_reusejp_1887_:
{
lean_object* v___x_1890_; 
if (v_isShared_1886_ == 0)
{
lean_ctor_set(v___x_1885_, 0, v___x_1888_);
v___x_1890_ = v___x_1885_;
goto v_reusejp_1889_;
}
else
{
lean_object* v_reuseFailAlloc_1892_; 
v_reuseFailAlloc_1892_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1892_, 0, v___x_1888_);
v___x_1890_ = v_reuseFailAlloc_1892_;
goto v_reusejp_1889_;
}
v_reusejp_1889_:
{
lean_object* v___x_1891_; 
v___x_1891_ = lean_apply_2(v_inst_1852_, lean_box(0), v___x_1890_);
return v___x_1891_;
}
}
}
}
default: 
{
lean_object* v___x_1895_; uint8_t v_decide_1896_; 
lean_del_object(v___x_1857_);
v___x_1895_ = lean_unsigned_to_nat(0u);
v_decide_1896_ = lean_nat_dec_eq(v_currPos_1854_, v___x_1895_);
if (v_decide_1896_ == 0)
{
lean_object* v_str_1897_; lean_object* v_startInclusive_1898_; lean_object* v___x_1900_; uint8_t v_isShared_1901_; uint8_t v_isSharedCheck_1909_; 
v_str_1897_ = lean_ctor_get(v_s_1851_, 0);
v_startInclusive_1898_ = lean_ctor_get(v_s_1851_, 1);
v_isSharedCheck_1909_ = !lean_is_exclusive(v_s_1851_);
if (v_isSharedCheck_1909_ == 0)
{
lean_object* v_unused_1910_; 
v_unused_1910_ = lean_ctor_get(v_s_1851_, 2);
lean_dec(v_unused_1910_);
v___x_1900_ = v_s_1851_;
v_isShared_1901_ = v_isSharedCheck_1909_;
goto v_resetjp_1899_;
}
else
{
lean_inc(v_startInclusive_1898_);
lean_inc(v_str_1897_);
lean_dec(v_s_1851_);
v___x_1900_ = lean_box(0);
v_isShared_1901_ = v_isSharedCheck_1909_;
goto v_resetjp_1899_;
}
v_resetjp_1899_:
{
lean_object* v___x_1902_; lean_object* v_slice_1904_; 
v___x_1902_ = lean_nat_add(v_startInclusive_1898_, v_currPos_1854_);
lean_dec(v_currPos_1854_);
if (v_isShared_1901_ == 0)
{
lean_ctor_set(v___x_1900_, 2, v___x_1902_);
v_slice_1904_ = v___x_1900_;
goto v_reusejp_1903_;
}
else
{
lean_object* v_reuseFailAlloc_1908_; 
v_reuseFailAlloc_1908_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1908_, 0, v_str_1897_);
lean_ctor_set(v_reuseFailAlloc_1908_, 1, v_startInclusive_1898_);
lean_ctor_set(v_reuseFailAlloc_1908_, 2, v___x_1902_);
v_slice_1904_ = v_reuseFailAlloc_1908_;
goto v_reusejp_1903_;
}
v_reusejp_1903_:
{
lean_object* v___x_1905_; lean_object* v___x_1906_; lean_object* v___x_1907_; 
v___x_1905_ = lean_box(1);
v___x_1906_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1906_, 0, v___x_1905_);
lean_ctor_set(v___x_1906_, 1, v_slice_1904_);
v___x_1907_ = lean_apply_2(v_inst_1852_, lean_box(0), v___x_1906_);
return v___x_1907_;
}
}
}
else
{
lean_object* v___x_1911_; lean_object* v___x_1912_; 
lean_dec(v_currPos_1854_);
lean_dec_ref(v_s_1851_);
v___x_1911_ = lean_box(2);
v___x_1912_ = lean_apply_2(v_inst_1852_, lean_box(0), v___x_1911_);
return v___x_1912_;
}
}
}
}
}
else
{
lean_object* v___x_1914_; lean_object* v___x_1915_; 
lean_dec_ref(v_s_1851_);
lean_dec(v_inst_1850_);
v___x_1914_ = lean_box(2);
v___x_1915_ = lean_apply_2(v_inst_1852_, lean_box(0), v___x_1914_);
return v___x_1915_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg(lean_object* v_inst_1916_, lean_object* v_s_1917_, lean_object* v_inst_1918_){
_start:
{
lean_object* v___f_1919_; 
v___f_1919_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1919_, 0, v_inst_1916_);
lean_closure_set(v___f_1919_, 1, v_s_1917_);
lean_closure_set(v___f_1919_, 2, v_inst_1918_);
return v___f_1919_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure(lean_object* v_00_u03c1_1920_, lean_object* v_00_u03c1_1921_, lean_object* v_00_u03c3_1922_, lean_object* v_inst_1923_, lean_object* v_inst_1924_, lean_object* v_m_1925_, lean_object* v_s_1926_, lean_object* v_inst_1927_){
_start:
{
lean_object* v___f_1928_; 
v___f_1928_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1928_, 0, v_inst_1923_);
lean_closure_set(v___f_1928_, 1, v_s_1926_);
lean_closure_set(v___f_1928_, 2, v_inst_1927_);
return v___f_1928_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___boxed(lean_object* v_00_u03c1_1929_, lean_object* v_00_u03c1_1930_, lean_object* v_00_u03c3_1931_, lean_object* v_inst_1932_, lean_object* v_inst_1933_, lean_object* v_m_1934_, lean_object* v_s_1935_, lean_object* v_inst_1936_){
_start:
{
lean_object* v_res_1937_; 
v_res_1937_ = l_String_Slice_RevSplitIterator_instIteratorOfPure(v_00_u03c1_1929_, v_00_u03c1_1930_, v_00_u03c3_1931_, v_inst_1932_, v_inst_1933_, v_m_1934_, v_s_1935_, v_inst_1936_);
lean_dec(v_inst_1933_);
lean_dec(v_00_u03c1_1930_);
return v_res_1937_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___redArg(lean_object* v_x_1938_){
_start:
{
if (lean_obj_tag(v_x_1938_) == 0)
{
lean_object* v_searcher_1939_; lean_object* v___x_1940_; 
v_searcher_1939_ = lean_ctor_get(v_x_1938_, 1);
lean_inc(v_searcher_1939_);
v___x_1940_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1940_, 0, v_searcher_1939_);
return v___x_1940_;
}
else
{
lean_object* v___x_1941_; 
v___x_1941_ = lean_box(0);
return v___x_1941_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___redArg___boxed(lean_object* v_x_1942_){
_start:
{
lean_object* v_res_1943_; 
v_res_1943_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_1942_);
lean_dec(v_x_1942_);
return v_res_1943_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption(lean_object* v_00_u03c1_1944_, lean_object* v_00_u03c1_1945_, lean_object* v_00_u03c3_1946_, lean_object* v_inst_1947_, lean_object* v_s_1948_, lean_object* v_x_1949_){
_start:
{
lean_object* v___x_1950_; 
v___x_1950_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_1949_);
return v___x_1950_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption___boxed(lean_object* v_00_u03c1_1951_, lean_object* v_00_u03c1_1952_, lean_object* v_00_u03c3_1953_, lean_object* v_inst_1954_, lean_object* v_s_1955_, lean_object* v_x_1956_){
_start:
{
lean_object* v_res_1957_; 
v_res_1957_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_toOption(v_00_u03c1_1951_, v_00_u03c1_1952_, v_00_u03c3_1953_, v_inst_1954_, v_s_1955_, v_x_1956_);
lean_dec(v_x_1956_);
lean_dec_ref(v_s_1955_);
lean_dec(v_inst_1954_);
lean_dec(v_00_u03c1_1952_);
return v_res_1957_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(lean_object* v_x_1958_, lean_object* v_h__1_1959_, lean_object* v_h__2_1960_){
_start:
{
if (lean_obj_tag(v_x_1958_) == 0)
{
lean_object* v_currPos_1961_; lean_object* v_searcher_1962_; lean_object* v___x_1963_; 
lean_dec(v_h__2_1960_);
v_currPos_1961_ = lean_ctor_get(v_x_1958_, 0);
lean_inc(v_currPos_1961_);
v_searcher_1962_ = lean_ctor_get(v_x_1958_, 1);
lean_inc(v_searcher_1962_);
lean_dec_ref_known(v_x_1958_, 2);
v___x_1963_ = lean_apply_2(v_h__1_1959_, v_currPos_1961_, v_searcher_1962_);
return v___x_1963_;
}
else
{
lean_object* v___x_1964_; lean_object* v___x_1965_; 
lean_dec(v_h__1_1959_);
v___x_1964_ = lean_box(0);
v___x_1965_ = lean_apply_1(v_h__2_1960_, v___x_1964_);
return v___x_1965_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(lean_object* v_00_u03c1_1966_, lean_object* v_00_u03c1_1967_, lean_object* v_00_u03c3_1968_, lean_object* v_inst_1969_, lean_object* v_m_1970_, lean_object* v_s_1971_, lean_object* v_motive_1972_, lean_object* v_x_1973_, lean_object* v_h__1_1974_, lean_object* v_h__2_1975_){
_start:
{
if (lean_obj_tag(v_x_1973_) == 0)
{
lean_object* v_currPos_1976_; lean_object* v_searcher_1977_; lean_object* v___x_1978_; 
lean_dec(v_h__2_1975_);
v_currPos_1976_ = lean_ctor_get(v_x_1973_, 0);
lean_inc(v_currPos_1976_);
v_searcher_1977_ = lean_ctor_get(v_x_1973_, 1);
lean_inc(v_searcher_1977_);
lean_dec_ref_known(v_x_1973_, 2);
v___x_1978_ = lean_apply_2(v_h__1_1974_, v_currPos_1976_, v_searcher_1977_);
return v___x_1978_;
}
else
{
lean_object* v___x_1979_; lean_object* v___x_1980_; 
lean_dec(v_h__1_1974_);
v___x_1979_ = lean_box(0);
v___x_1980_ = lean_apply_1(v_h__2_1975_, v___x_1979_);
return v___x_1980_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___boxed(lean_object* v_00_u03c1_1981_, lean_object* v_00_u03c1_1982_, lean_object* v_00_u03c3_1983_, lean_object* v_inst_1984_, lean_object* v_m_1985_, lean_object* v_s_1986_, lean_object* v_motive_1987_, lean_object* v_x_1988_, lean_object* v_h__1_1989_, lean_object* v_h__2_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(v_00_u03c1_1981_, v_00_u03c1_1982_, v_00_u03c3_1983_, v_inst_1984_, v_m_1985_, v_s_1986_, v_motive_1987_, v_x_1988_, v_h__1_1989_, v_h__2_1990_);
lean_dec_ref(v_s_1986_);
lean_dec(v_inst_1984_);
lean_dec(v_00_u03c1_1982_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(lean_object* v_x_1992_, lean_object* v_x_1993_, lean_object* v_h__1_1994_, lean_object* v_h__2_1995_, lean_object* v_h__3_1996_, lean_object* v_h__4_1997_, lean_object* v_h__5_1998_, lean_object* v_h__6_1999_, lean_object* v_h__7_2000_, lean_object* v_h__8_2001_){
_start:
{
if (lean_obj_tag(v_x_1992_) == 0)
{
lean_dec(v_h__8_2001_);
lean_dec(v_h__7_2000_);
lean_dec(v_h__6_1999_);
switch(lean_obj_tag(v_x_1993_))
{
case 0:
{
lean_object* v_it_2002_; 
lean_dec(v_h__5_1998_);
lean_dec(v_h__4_1997_);
lean_dec(v_h__3_1996_);
v_it_2002_ = lean_ctor_get(v_x_1993_, 0);
if (lean_obj_tag(v_it_2002_) == 0)
{
lean_object* v_currPos_2003_; lean_object* v_searcher_2004_; lean_object* v_out_2005_; lean_object* v_currPos_2006_; lean_object* v_searcher_2007_; lean_object* v___x_2008_; 
lean_inc_ref(v_it_2002_);
lean_dec(v_h__2_1995_);
v_currPos_2003_ = lean_ctor_get(v_x_1992_, 0);
lean_inc(v_currPos_2003_);
v_searcher_2004_ = lean_ctor_get(v_x_1992_, 1);
lean_inc(v_searcher_2004_);
lean_dec_ref_known(v_x_1992_, 2);
v_out_2005_ = lean_ctor_get(v_x_1993_, 1);
lean_inc(v_out_2005_);
lean_dec_ref_known(v_x_1993_, 2);
v_currPos_2006_ = lean_ctor_get(v_it_2002_, 0);
lean_inc(v_currPos_2006_);
v_searcher_2007_ = lean_ctor_get(v_it_2002_, 1);
lean_inc(v_searcher_2007_);
lean_dec_ref_known(v_it_2002_, 2);
v___x_2008_ = lean_apply_5(v_h__1_1994_, v_currPos_2003_, v_searcher_2004_, v_currPos_2006_, v_searcher_2007_, v_out_2005_);
return v___x_2008_;
}
else
{
lean_object* v_currPos_2009_; lean_object* v_searcher_2010_; lean_object* v_out_2011_; lean_object* v___x_2012_; 
lean_dec(v_h__1_1994_);
v_currPos_2009_ = lean_ctor_get(v_x_1992_, 0);
lean_inc(v_currPos_2009_);
v_searcher_2010_ = lean_ctor_get(v_x_1992_, 1);
lean_inc(v_searcher_2010_);
lean_dec_ref_known(v_x_1992_, 2);
v_out_2011_ = lean_ctor_get(v_x_1993_, 1);
lean_inc(v_out_2011_);
lean_dec_ref_known(v_x_1993_, 2);
v___x_2012_ = lean_apply_3(v_h__2_1995_, v_currPos_2009_, v_searcher_2010_, v_out_2011_);
return v___x_2012_;
}
}
case 1:
{
lean_object* v_it_2013_; 
lean_dec(v_h__5_1998_);
lean_dec(v_h__2_1995_);
lean_dec(v_h__1_1994_);
v_it_2013_ = lean_ctor_get(v_x_1993_, 0);
lean_inc(v_it_2013_);
lean_dec_ref_known(v_x_1993_, 1);
if (lean_obj_tag(v_it_2013_) == 0)
{
lean_object* v_currPos_2014_; lean_object* v_searcher_2015_; lean_object* v_currPos_2016_; lean_object* v_searcher_2017_; lean_object* v___x_2018_; 
lean_dec(v_h__4_1997_);
v_currPos_2014_ = lean_ctor_get(v_x_1992_, 0);
lean_inc(v_currPos_2014_);
v_searcher_2015_ = lean_ctor_get(v_x_1992_, 1);
lean_inc(v_searcher_2015_);
lean_dec_ref_known(v_x_1992_, 2);
v_currPos_2016_ = lean_ctor_get(v_it_2013_, 0);
lean_inc(v_currPos_2016_);
v_searcher_2017_ = lean_ctor_get(v_it_2013_, 1);
lean_inc(v_searcher_2017_);
lean_dec_ref_known(v_it_2013_, 2);
v___x_2018_ = lean_apply_4(v_h__3_1996_, v_currPos_2014_, v_searcher_2015_, v_currPos_2016_, v_searcher_2017_);
return v___x_2018_;
}
else
{
lean_object* v_currPos_2019_; lean_object* v_searcher_2020_; lean_object* v___x_2021_; 
lean_dec(v_h__3_1996_);
v_currPos_2019_ = lean_ctor_get(v_x_1992_, 0);
lean_inc(v_currPos_2019_);
v_searcher_2020_ = lean_ctor_get(v_x_1992_, 1);
lean_inc(v_searcher_2020_);
lean_dec_ref_known(v_x_1992_, 2);
v___x_2021_ = lean_apply_2(v_h__4_1997_, v_currPos_2019_, v_searcher_2020_);
return v___x_2021_;
}
}
default: 
{
lean_object* v_currPos_2022_; lean_object* v_searcher_2023_; lean_object* v___x_2024_; 
lean_dec(v_h__4_1997_);
lean_dec(v_h__3_1996_);
lean_dec(v_h__2_1995_);
lean_dec(v_h__1_1994_);
v_currPos_2022_ = lean_ctor_get(v_x_1992_, 0);
lean_inc(v_currPos_2022_);
v_searcher_2023_ = lean_ctor_get(v_x_1992_, 1);
lean_inc(v_searcher_2023_);
lean_dec_ref_known(v_x_1992_, 2);
v___x_2024_ = lean_apply_2(v_h__5_1998_, v_currPos_2022_, v_searcher_2023_);
return v___x_2024_;
}
}
}
else
{
lean_dec(v_h__5_1998_);
lean_dec(v_h__4_1997_);
lean_dec(v_h__3_1996_);
lean_dec(v_h__2_1995_);
lean_dec(v_h__1_1994_);
switch(lean_obj_tag(v_x_1993_))
{
case 0:
{
lean_object* v_it_2025_; lean_object* v_out_2026_; lean_object* v___x_2027_; 
lean_dec(v_h__8_2001_);
lean_dec(v_h__7_2000_);
v_it_2025_ = lean_ctor_get(v_x_1993_, 0);
lean_inc(v_it_2025_);
v_out_2026_ = lean_ctor_get(v_x_1993_, 1);
lean_inc(v_out_2026_);
lean_dec_ref_known(v_x_1993_, 2);
v___x_2027_ = lean_apply_2(v_h__6_1999_, v_it_2025_, v_out_2026_);
return v___x_2027_;
}
case 1:
{
lean_object* v_it_2028_; lean_object* v___x_2029_; 
lean_dec(v_h__8_2001_);
lean_dec(v_h__6_1999_);
v_it_2028_ = lean_ctor_get(v_x_1993_, 0);
lean_inc(v_it_2028_);
lean_dec_ref_known(v_x_1993_, 1);
v___x_2029_ = lean_apply_1(v_h__7_2000_, v_it_2028_);
return v___x_2029_;
}
default: 
{
lean_object* v___x_2030_; lean_object* v___x_2031_; 
lean_dec(v_h__7_2000_);
lean_dec(v_h__6_1999_);
v___x_2030_ = lean_box(0);
v___x_2031_ = lean_apply_1(v_h__8_2001_, v___x_2030_);
return v___x_2031_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(lean_object* v_00_u03c1_2032_, lean_object* v_00_u03c1_2033_, lean_object* v_00_u03c3_2034_, lean_object* v_inst_2035_, lean_object* v_m_2036_, lean_object* v_s_2037_, lean_object* v_motive_2038_, lean_object* v_x_2039_, lean_object* v_x_2040_, lean_object* v_h__1_2041_, lean_object* v_h__2_2042_, lean_object* v_h__3_2043_, lean_object* v_h__4_2044_, lean_object* v_h__5_2045_, lean_object* v_h__6_2046_, lean_object* v_h__7_2047_, lean_object* v_h__8_2048_){
_start:
{
if (lean_obj_tag(v_x_2039_) == 0)
{
lean_dec(v_h__8_2048_);
lean_dec(v_h__7_2047_);
lean_dec(v_h__6_2046_);
switch(lean_obj_tag(v_x_2040_))
{
case 0:
{
lean_object* v_it_2049_; 
lean_dec(v_h__5_2045_);
lean_dec(v_h__4_2044_);
lean_dec(v_h__3_2043_);
v_it_2049_ = lean_ctor_get(v_x_2040_, 0);
if (lean_obj_tag(v_it_2049_) == 0)
{
lean_object* v_currPos_2050_; lean_object* v_searcher_2051_; lean_object* v_out_2052_; lean_object* v_currPos_2053_; lean_object* v_searcher_2054_; lean_object* v___x_2055_; 
lean_inc_ref(v_it_2049_);
lean_dec(v_h__2_2042_);
v_currPos_2050_ = lean_ctor_get(v_x_2039_, 0);
lean_inc(v_currPos_2050_);
v_searcher_2051_ = lean_ctor_get(v_x_2039_, 1);
lean_inc(v_searcher_2051_);
lean_dec_ref_known(v_x_2039_, 2);
v_out_2052_ = lean_ctor_get(v_x_2040_, 1);
lean_inc(v_out_2052_);
lean_dec_ref_known(v_x_2040_, 2);
v_currPos_2053_ = lean_ctor_get(v_it_2049_, 0);
lean_inc(v_currPos_2053_);
v_searcher_2054_ = lean_ctor_get(v_it_2049_, 1);
lean_inc(v_searcher_2054_);
lean_dec_ref_known(v_it_2049_, 2);
v___x_2055_ = lean_apply_5(v_h__1_2041_, v_currPos_2050_, v_searcher_2051_, v_currPos_2053_, v_searcher_2054_, v_out_2052_);
return v___x_2055_;
}
else
{
lean_object* v_currPos_2056_; lean_object* v_searcher_2057_; lean_object* v_out_2058_; lean_object* v___x_2059_; 
lean_dec(v_h__1_2041_);
v_currPos_2056_ = lean_ctor_get(v_x_2039_, 0);
lean_inc(v_currPos_2056_);
v_searcher_2057_ = lean_ctor_get(v_x_2039_, 1);
lean_inc(v_searcher_2057_);
lean_dec_ref_known(v_x_2039_, 2);
v_out_2058_ = lean_ctor_get(v_x_2040_, 1);
lean_inc(v_out_2058_);
lean_dec_ref_known(v_x_2040_, 2);
v___x_2059_ = lean_apply_3(v_h__2_2042_, v_currPos_2056_, v_searcher_2057_, v_out_2058_);
return v___x_2059_;
}
}
case 1:
{
lean_object* v_it_2060_; 
lean_dec(v_h__5_2045_);
lean_dec(v_h__2_2042_);
lean_dec(v_h__1_2041_);
v_it_2060_ = lean_ctor_get(v_x_2040_, 0);
lean_inc(v_it_2060_);
lean_dec_ref_known(v_x_2040_, 1);
if (lean_obj_tag(v_it_2060_) == 0)
{
lean_object* v_currPos_2061_; lean_object* v_searcher_2062_; lean_object* v_currPos_2063_; lean_object* v_searcher_2064_; lean_object* v___x_2065_; 
lean_dec(v_h__4_2044_);
v_currPos_2061_ = lean_ctor_get(v_x_2039_, 0);
lean_inc(v_currPos_2061_);
v_searcher_2062_ = lean_ctor_get(v_x_2039_, 1);
lean_inc(v_searcher_2062_);
lean_dec_ref_known(v_x_2039_, 2);
v_currPos_2063_ = lean_ctor_get(v_it_2060_, 0);
lean_inc(v_currPos_2063_);
v_searcher_2064_ = lean_ctor_get(v_it_2060_, 1);
lean_inc(v_searcher_2064_);
lean_dec_ref_known(v_it_2060_, 2);
v___x_2065_ = lean_apply_4(v_h__3_2043_, v_currPos_2061_, v_searcher_2062_, v_currPos_2063_, v_searcher_2064_);
return v___x_2065_;
}
else
{
lean_object* v_currPos_2066_; lean_object* v_searcher_2067_; lean_object* v___x_2068_; 
lean_dec(v_h__3_2043_);
v_currPos_2066_ = lean_ctor_get(v_x_2039_, 0);
lean_inc(v_currPos_2066_);
v_searcher_2067_ = lean_ctor_get(v_x_2039_, 1);
lean_inc(v_searcher_2067_);
lean_dec_ref_known(v_x_2039_, 2);
v___x_2068_ = lean_apply_2(v_h__4_2044_, v_currPos_2066_, v_searcher_2067_);
return v___x_2068_;
}
}
default: 
{
lean_object* v_currPos_2069_; lean_object* v_searcher_2070_; lean_object* v___x_2071_; 
lean_dec(v_h__4_2044_);
lean_dec(v_h__3_2043_);
lean_dec(v_h__2_2042_);
lean_dec(v_h__1_2041_);
v_currPos_2069_ = lean_ctor_get(v_x_2039_, 0);
lean_inc(v_currPos_2069_);
v_searcher_2070_ = lean_ctor_get(v_x_2039_, 1);
lean_inc(v_searcher_2070_);
lean_dec_ref_known(v_x_2039_, 2);
v___x_2071_ = lean_apply_2(v_h__5_2045_, v_currPos_2069_, v_searcher_2070_);
return v___x_2071_;
}
}
}
else
{
lean_dec(v_h__5_2045_);
lean_dec(v_h__4_2044_);
lean_dec(v_h__3_2043_);
lean_dec(v_h__2_2042_);
lean_dec(v_h__1_2041_);
switch(lean_obj_tag(v_x_2040_))
{
case 0:
{
lean_object* v_it_2072_; lean_object* v_out_2073_; lean_object* v___x_2074_; 
lean_dec(v_h__8_2048_);
lean_dec(v_h__7_2047_);
v_it_2072_ = lean_ctor_get(v_x_2040_, 0);
lean_inc(v_it_2072_);
v_out_2073_ = lean_ctor_get(v_x_2040_, 1);
lean_inc(v_out_2073_);
lean_dec_ref_known(v_x_2040_, 2);
v___x_2074_ = lean_apply_2(v_h__6_2046_, v_it_2072_, v_out_2073_);
return v___x_2074_;
}
case 1:
{
lean_object* v_it_2075_; lean_object* v___x_2076_; 
lean_dec(v_h__8_2048_);
lean_dec(v_h__6_2046_);
v_it_2075_ = lean_ctor_get(v_x_2040_, 0);
lean_inc(v_it_2075_);
lean_dec_ref_known(v_x_2040_, 1);
v___x_2076_ = lean_apply_1(v_h__7_2047_, v_it_2075_);
return v___x_2076_;
}
default: 
{
lean_object* v___x_2077_; lean_object* v___x_2078_; 
lean_dec(v_h__7_2047_);
lean_dec(v_h__6_2046_);
v___x_2077_ = lean_box(0);
v___x_2078_ = lean_apply_1(v_h__8_2048_, v___x_2077_);
return v___x_2078_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___boxed(lean_object** _args){
lean_object* v_00_u03c1_2079_ = _args[0];
lean_object* v_00_u03c1_2080_ = _args[1];
lean_object* v_00_u03c3_2081_ = _args[2];
lean_object* v_inst_2082_ = _args[3];
lean_object* v_m_2083_ = _args[4];
lean_object* v_s_2084_ = _args[5];
lean_object* v_motive_2085_ = _args[6];
lean_object* v_x_2086_ = _args[7];
lean_object* v_x_2087_ = _args[8];
lean_object* v_h__1_2088_ = _args[9];
lean_object* v_h__2_2089_ = _args[10];
lean_object* v_h__3_2090_ = _args[11];
lean_object* v_h__4_2091_ = _args[12];
lean_object* v_h__5_2092_ = _args[13];
lean_object* v_h__6_2093_ = _args[14];
lean_object* v_h__7_2094_ = _args[15];
lean_object* v_h__8_2095_ = _args[16];
_start:
{
lean_object* v_res_2096_; 
v_res_2096_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(v_00_u03c1_2079_, v_00_u03c1_2080_, v_00_u03c3_2081_, v_inst_2082_, v_m_2083_, v_s_2084_, v_motive_2085_, v_x_2086_, v_x_2087_, v_h__1_2088_, v_h__2_2089_, v_h__3_2090_, v_h__4_2091_, v_h__5_2092_, v_h__6_2093_, v_h__7_2094_, v_h__8_2095_);
lean_dec_ref(v_s_2084_);
lean_dec(v_inst_2082_);
lean_dec(v_00_u03c1_2080_);
return v_res_2096_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_2098_; 
v___x_2098_ = lean_box(0);
return v___x_2098_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation___redArg();
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation(lean_object* v_00_u03c1_2101_, lean_object* v_00_u03c1_2102_, lean_object* v_00_u03c3_2103_, lean_object* v_inst_2104_, lean_object* v_inst_2105_, lean_object* v_s_2106_, lean_object* v_inst_2107_){
_start:
{
lean_object* v___x_2108_; 
v___x_2108_ = lean_box(0);
return v___x_2108_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_2109_, lean_object* v_00_u03c1_2110_, lean_object* v_00_u03c3_2111_, lean_object* v_inst_2112_, lean_object* v_inst_2113_, lean_object* v_s_2114_, lean_object* v_inst_2115_){
_start:
{
lean_object* v_res_2116_; 
v_res_2116_ = l___private_Init_Data_String_Slice_Pattern_0__String_Slice_RevSplitIterator_finitenessRelation(v_00_u03c1_2109_, v_00_u03c1_2110_, v_00_u03c3_2111_, v_inst_2112_, v_inst_2113_, v_s_2114_, v_inst_2115_);
lean_dec_ref(v_s_2114_);
lean_dec(v_inst_2113_);
lean_dec(v_inst_2112_);
lean_dec(v_00_u03c1_2110_);
return v_res_2116_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object* v_toPure_2117_, lean_object* v_recur_2118_, lean_object* v_it_2119_, lean_object* v_____do__lift_2120_){
_start:
{
if (lean_obj_tag(v_____do__lift_2120_) == 0)
{
lean_object* v_a_2121_; lean_object* v___x_2122_; 
lean_dec(v_it_2119_);
lean_dec(v_recur_2118_);
v_a_2121_ = lean_ctor_get(v_____do__lift_2120_, 0);
lean_inc(v_a_2121_);
lean_dec_ref_known(v_____do__lift_2120_, 1);
v___x_2122_ = lean_apply_2(v_toPure_2117_, lean_box(0), v_a_2121_);
return v___x_2122_;
}
else
{
lean_object* v_a_2123_; lean_object* v___x_2124_; 
lean_dec(v_toPure_2117_);
v_a_2123_ = lean_ctor_get(v_____do__lift_2120_, 0);
lean_inc(v_a_2123_);
lean_dec_ref_known(v_____do__lift_2120_, 1);
v___x_2124_ = lean_apply_4(v_recur_2118_, v_it_2119_, v_a_2123_, lean_box(0), lean_box(0));
return v___x_2124_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object* v_toPure_2125_, lean_object* v_recur_2126_, lean_object* v___y_2127_, lean_object* v_acc_2128_, lean_object* v_toBind_2129_, lean_object* v_s_2130_){
_start:
{
switch(lean_obj_tag(v_s_2130_))
{
case 0:
{
lean_object* v_it_2131_; lean_object* v_out_2132_; lean_object* v___f_2133_; lean_object* v___x_2134_; lean_object* v___x_2135_; 
v_it_2131_ = lean_ctor_get(v_s_2130_, 0);
lean_inc(v_it_2131_);
v_out_2132_ = lean_ctor_get(v_s_2130_, 1);
lean_inc(v_out_2132_);
lean_dec_ref_known(v_s_2130_, 2);
v___f_2133_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2133_, 0, v_toPure_2125_);
lean_closure_set(v___f_2133_, 1, v_recur_2126_);
lean_closure_set(v___f_2133_, 2, v_it_2131_);
v___x_2134_ = lean_apply_3(v___y_2127_, v_out_2132_, lean_box(0), v_acc_2128_);
v___x_2135_ = lean_apply_4(v_toBind_2129_, lean_box(0), lean_box(0), v___x_2134_, v___f_2133_);
return v___x_2135_;
}
case 1:
{
lean_object* v_it_2136_; lean_object* v___x_2137_; 
lean_dec(v_toBind_2129_);
lean_dec(v___y_2127_);
lean_dec(v_toPure_2125_);
v_it_2136_ = lean_ctor_get(v_s_2130_, 0);
lean_inc(v_it_2136_);
lean_dec_ref_known(v_s_2130_, 1);
v___x_2137_ = lean_apply_4(v_recur_2126_, v_it_2136_, v_acc_2128_, lean_box(0), lean_box(0));
return v___x_2137_;
}
default: 
{
lean_object* v___x_2138_; 
lean_dec(v_toBind_2129_);
lean_dec(v___y_2127_);
lean_dec(v_recur_2126_);
v___x_2138_ = lean_apply_2(v_toPure_2125_, lean_box(0), v_acc_2128_);
return v___x_2138_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object* v_toPure_2139_, lean_object* v___y_2140_, lean_object* v_toBind_2141_, lean_object* v_inst_2142_, lean_object* v_s_2143_, lean_object* v_toPure_2144_, lean_object* v_lift_2145_, lean_object* v_it_2146_, lean_object* v_acc_2147_, lean_object* v_hP_2148_, lean_object* v_recur_2149_){
_start:
{
lean_object* v___f_2150_; 
v___f_2150_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2150_, 0, v_toPure_2139_);
lean_closure_set(v___f_2150_, 1, v_recur_2149_);
lean_closure_set(v___f_2150_, 2, v___y_2140_);
lean_closure_set(v___f_2150_, 3, v_acc_2147_);
lean_closure_set(v___f_2150_, 4, v_toBind_2141_);
if (lean_obj_tag(v_it_2146_) == 0)
{
lean_object* v_currPos_2151_; lean_object* v_searcher_2152_; lean_object* v___x_2154_; uint8_t v_isShared_2155_; uint8_t v_isSharedCheck_2215_; 
v_currPos_2151_ = lean_ctor_get(v_it_2146_, 0);
v_searcher_2152_ = lean_ctor_get(v_it_2146_, 1);
v_isSharedCheck_2215_ = !lean_is_exclusive(v_it_2146_);
if (v_isSharedCheck_2215_ == 0)
{
v___x_2154_ = v_it_2146_;
v_isShared_2155_ = v_isSharedCheck_2215_;
goto v_resetjp_2153_;
}
else
{
lean_inc(v_searcher_2152_);
lean_inc(v_currPos_2151_);
lean_dec(v_it_2146_);
v___x_2154_ = lean_box(0);
v_isShared_2155_ = v_isSharedCheck_2215_;
goto v_resetjp_2153_;
}
v_resetjp_2153_:
{
lean_object* v___x_2156_; 
lean_inc_ref(v_s_2143_);
v___x_2156_ = lean_apply_2(v_inst_2142_, v_s_2143_, v_searcher_2152_);
switch(lean_obj_tag(v___x_2156_))
{
case 0:
{
lean_object* v_out_2157_; 
v_out_2157_ = lean_ctor_get(v___x_2156_, 1);
lean_inc(v_out_2157_);
if (lean_obj_tag(v_out_2157_) == 0)
{
lean_object* v_it_2158_; lean_object* v___x_2160_; 
lean_dec_ref_known(v_out_2157_, 2);
lean_dec_ref(v_s_2143_);
v_it_2158_ = lean_ctor_get(v___x_2156_, 0);
lean_inc(v_it_2158_);
lean_dec_ref_known(v___x_2156_, 2);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v_it_2158_);
v___x_2160_ = v___x_2154_;
goto v_reusejp_2159_;
}
else
{
lean_object* v_reuseFailAlloc_2164_; 
v_reuseFailAlloc_2164_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2164_, 0, v_currPos_2151_);
lean_ctor_set(v_reuseFailAlloc_2164_, 1, v_it_2158_);
v___x_2160_ = v_reuseFailAlloc_2164_;
goto v_reusejp_2159_;
}
v_reusejp_2159_:
{
lean_object* v___x_2161_; lean_object* v___x_2162_; lean_object* v___x_2163_; 
v___x_2161_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2161_, 0, v___x_2160_);
v___x_2162_ = lean_apply_2(v_toPure_2144_, lean_box(0), v___x_2161_);
v___x_2163_ = lean_apply_4(v_lift_2145_, lean_box(0), lean_box(0), v___f_2150_, v___x_2162_);
return v___x_2163_;
}
}
else
{
lean_object* v_it_2165_; lean_object* v___x_2167_; uint8_t v_isShared_2168_; uint8_t v_isSharedCheck_2180_; 
v_it_2165_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2180_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2180_ == 0)
{
lean_object* v_unused_2181_; 
v_unused_2181_ = lean_ctor_get(v___x_2156_, 1);
lean_dec(v_unused_2181_);
v___x_2167_ = v___x_2156_;
v_isShared_2168_ = v_isSharedCheck_2180_;
goto v_resetjp_2166_;
}
else
{
lean_inc(v_it_2165_);
lean_dec(v___x_2156_);
v___x_2167_ = lean_box(0);
v_isShared_2168_ = v_isSharedCheck_2180_;
goto v_resetjp_2166_;
}
v_resetjp_2166_:
{
lean_object* v_startPos_2169_; lean_object* v_endPos_2170_; lean_object* v_slice_2171_; lean_object* v_nextIt_2173_; 
v_startPos_2169_ = lean_ctor_get(v_out_2157_, 0);
lean_inc(v_startPos_2169_);
v_endPos_2170_ = lean_ctor_get(v_out_2157_, 1);
lean_inc(v_endPos_2170_);
lean_dec_ref_known(v_out_2157_, 2);
v_slice_2171_ = l_String_Slice_slice_x21(v_s_2143_, v_endPos_2170_, v_currPos_2151_);
lean_dec(v_currPos_2151_);
lean_dec(v_endPos_2170_);
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v_it_2165_);
lean_ctor_set(v___x_2154_, 0, v_startPos_2169_);
v_nextIt_2173_ = v___x_2154_;
goto v_reusejp_2172_;
}
else
{
lean_object* v_reuseFailAlloc_2179_; 
v_reuseFailAlloc_2179_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2179_, 0, v_startPos_2169_);
lean_ctor_set(v_reuseFailAlloc_2179_, 1, v_it_2165_);
v_nextIt_2173_ = v_reuseFailAlloc_2179_;
goto v_reusejp_2172_;
}
v_reusejp_2172_:
{
lean_object* v___x_2175_; 
if (v_isShared_2168_ == 0)
{
lean_ctor_set(v___x_2167_, 1, v_slice_2171_);
lean_ctor_set(v___x_2167_, 0, v_nextIt_2173_);
v___x_2175_ = v___x_2167_;
goto v_reusejp_2174_;
}
else
{
lean_object* v_reuseFailAlloc_2178_; 
v_reuseFailAlloc_2178_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2178_, 0, v_nextIt_2173_);
lean_ctor_set(v_reuseFailAlloc_2178_, 1, v_slice_2171_);
v___x_2175_ = v_reuseFailAlloc_2178_;
goto v_reusejp_2174_;
}
v_reusejp_2174_:
{
lean_object* v___x_2176_; lean_object* v___x_2177_; 
v___x_2176_ = lean_apply_2(v_toPure_2144_, lean_box(0), v___x_2175_);
v___x_2177_ = lean_apply_4(v_lift_2145_, lean_box(0), lean_box(0), v___f_2150_, v___x_2176_);
return v___x_2177_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2182_; lean_object* v___x_2184_; uint8_t v_isShared_2185_; uint8_t v_isSharedCheck_2194_; 
lean_dec_ref(v_s_2143_);
v_it_2182_ = lean_ctor_get(v___x_2156_, 0);
v_isSharedCheck_2194_ = !lean_is_exclusive(v___x_2156_);
if (v_isSharedCheck_2194_ == 0)
{
v___x_2184_ = v___x_2156_;
v_isShared_2185_ = v_isSharedCheck_2194_;
goto v_resetjp_2183_;
}
else
{
lean_inc(v_it_2182_);
lean_dec(v___x_2156_);
v___x_2184_ = lean_box(0);
v_isShared_2185_ = v_isSharedCheck_2194_;
goto v_resetjp_2183_;
}
v_resetjp_2183_:
{
lean_object* v___x_2187_; 
if (v_isShared_2155_ == 0)
{
lean_ctor_set(v___x_2154_, 1, v_it_2182_);
v___x_2187_ = v___x_2154_;
goto v_reusejp_2186_;
}
else
{
lean_object* v_reuseFailAlloc_2193_; 
v_reuseFailAlloc_2193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2193_, 0, v_currPos_2151_);
lean_ctor_set(v_reuseFailAlloc_2193_, 1, v_it_2182_);
v___x_2187_ = v_reuseFailAlloc_2193_;
goto v_reusejp_2186_;
}
v_reusejp_2186_:
{
lean_object* v___x_2189_; 
if (v_isShared_2185_ == 0)
{
lean_ctor_set(v___x_2184_, 0, v___x_2187_);
v___x_2189_ = v___x_2184_;
goto v_reusejp_2188_;
}
else
{
lean_object* v_reuseFailAlloc_2192_; 
v_reuseFailAlloc_2192_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2192_, 0, v___x_2187_);
v___x_2189_ = v_reuseFailAlloc_2192_;
goto v_reusejp_2188_;
}
v_reusejp_2188_:
{
lean_object* v___x_2190_; lean_object* v___x_2191_; 
v___x_2190_ = lean_apply_2(v_toPure_2144_, lean_box(0), v___x_2189_);
v___x_2191_ = lean_apply_4(v_lift_2145_, lean_box(0), lean_box(0), v___f_2150_, v___x_2190_);
return v___x_2191_;
}
}
}
}
default: 
{
lean_object* v___x_2195_; uint8_t v_decide_2196_; 
lean_del_object(v___x_2154_);
v___x_2195_ = lean_unsigned_to_nat(0u);
v_decide_2196_ = lean_nat_dec_eq(v_currPos_2151_, v___x_2195_);
if (v_decide_2196_ == 0)
{
lean_object* v_str_2197_; lean_object* v_startInclusive_2198_; lean_object* v___x_2200_; uint8_t v_isShared_2201_; uint8_t v_isSharedCheck_2210_; 
v_str_2197_ = lean_ctor_get(v_s_2143_, 0);
v_startInclusive_2198_ = lean_ctor_get(v_s_2143_, 1);
v_isSharedCheck_2210_ = !lean_is_exclusive(v_s_2143_);
if (v_isSharedCheck_2210_ == 0)
{
lean_object* v_unused_2211_; 
v_unused_2211_ = lean_ctor_get(v_s_2143_, 2);
lean_dec(v_unused_2211_);
v___x_2200_ = v_s_2143_;
v_isShared_2201_ = v_isSharedCheck_2210_;
goto v_resetjp_2199_;
}
else
{
lean_inc(v_startInclusive_2198_);
lean_inc(v_str_2197_);
lean_dec(v_s_2143_);
v___x_2200_ = lean_box(0);
v_isShared_2201_ = v_isSharedCheck_2210_;
goto v_resetjp_2199_;
}
v_resetjp_2199_:
{
lean_object* v___x_2202_; lean_object* v_slice_2204_; 
v___x_2202_ = lean_nat_add(v_startInclusive_2198_, v_currPos_2151_);
lean_dec(v_currPos_2151_);
if (v_isShared_2201_ == 0)
{
lean_ctor_set(v___x_2200_, 2, v___x_2202_);
v_slice_2204_ = v___x_2200_;
goto v_reusejp_2203_;
}
else
{
lean_object* v_reuseFailAlloc_2209_; 
v_reuseFailAlloc_2209_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2209_, 0, v_str_2197_);
lean_ctor_set(v_reuseFailAlloc_2209_, 1, v_startInclusive_2198_);
lean_ctor_set(v_reuseFailAlloc_2209_, 2, v___x_2202_);
v_slice_2204_ = v_reuseFailAlloc_2209_;
goto v_reusejp_2203_;
}
v_reusejp_2203_:
{
lean_object* v___x_2205_; lean_object* v___x_2206_; lean_object* v___x_2207_; lean_object* v___x_2208_; 
v___x_2205_ = lean_box(1);
v___x_2206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2206_, 0, v___x_2205_);
lean_ctor_set(v___x_2206_, 1, v_slice_2204_);
v___x_2207_ = lean_apply_2(v_toPure_2144_, lean_box(0), v___x_2206_);
v___x_2208_ = lean_apply_4(v_lift_2145_, lean_box(0), lean_box(0), v___f_2150_, v___x_2207_);
return v___x_2208_;
}
}
}
else
{
lean_object* v___x_2212_; lean_object* v___x_2213_; lean_object* v___x_2214_; 
lean_dec(v_currPos_2151_);
lean_dec_ref(v_s_2143_);
v___x_2212_ = lean_box(2);
v___x_2213_ = lean_apply_2(v_toPure_2144_, lean_box(0), v___x_2212_);
v___x_2214_ = lean_apply_4(v_lift_2145_, lean_box(0), lean_box(0), v___f_2150_, v___x_2213_);
return v___x_2214_;
}
}
}
}
}
else
{
lean_object* v___x_2216_; lean_object* v___x_2217_; lean_object* v___x_2218_; 
lean_dec_ref(v_s_2143_);
lean_dec(v_inst_2142_);
v___x_2216_ = lean_box(2);
v___x_2217_ = lean_apply_2(v_toPure_2144_, lean_box(0), v___x_2216_);
v___x_2218_ = lean_apply_4(v_lift_2145_, lean_box(0), lean_box(0), v___f_2150_, v___x_2217_);
return v___x_2218_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object* v_inst_2219_, lean_object* v_inst_2220_, lean_object* v_s_2221_, lean_object* v_toPure_2222_, lean_object* v_lift_2223_, lean_object* v_00_u03b3_2224_, lean_object* v_Pl_2225_, lean_object* v_it_2226_, lean_object* v_init_2227_, lean_object* v___y_2228_){
_start:
{
lean_object* v_toApplicative_2229_; lean_object* v_toBind_2230_; lean_object* v_toPure_2231_; lean_object* v___f_2232_; lean_object* v___x_2233_; 
v_toApplicative_2229_ = lean_ctor_get(v_inst_2219_, 0);
lean_inc_ref(v_toApplicative_2229_);
v_toBind_2230_ = lean_ctor_get(v_inst_2219_, 1);
lean_inc(v_toBind_2230_);
lean_dec_ref(v_inst_2219_);
v_toPure_2231_ = lean_ctor_get(v_toApplicative_2229_, 1);
lean_inc(v_toPure_2231_);
lean_dec_ref(v_toApplicative_2229_);
v___f_2232_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2), 11, 7);
lean_closure_set(v___f_2232_, 0, v_toPure_2231_);
lean_closure_set(v___f_2232_, 1, v___y_2228_);
lean_closure_set(v___f_2232_, 2, v_toBind_2230_);
lean_closure_set(v___f_2232_, 3, v_inst_2220_);
lean_closure_set(v___f_2232_, 4, v_s_2221_);
lean_closure_set(v___f_2232_, 5, v_toPure_2222_);
lean_closure_set(v___f_2232_, 6, v_lift_2223_);
v___x_2233_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2232_, v_it_2226_, v_init_2227_, lean_box(0));
return v___x_2233_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(lean_object* v_inst_2234_, lean_object* v_s_2235_, lean_object* v_inst_2236_, lean_object* v_inst_2237_){
_start:
{
lean_object* v_toApplicative_2238_; lean_object* v_toPure_2239_; lean_object* v___f_2240_; 
v_toApplicative_2238_ = lean_ctor_get(v_inst_2236_, 0);
lean_inc_ref(v_toApplicative_2238_);
lean_dec_ref(v_inst_2236_);
v_toPure_2239_ = lean_ctor_get(v_toApplicative_2238_, 1);
lean_inc(v_toPure_2239_);
lean_dec_ref(v_toApplicative_2238_);
v___f_2240_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3), 10, 4);
lean_closure_set(v___f_2240_, 0, v_inst_2237_);
lean_closure_set(v___f_2240_, 1, v_inst_2234_);
lean_closure_set(v___f_2240_, 2, v_s_2235_);
lean_closure_set(v___f_2240_, 3, v_toPure_2239_);
return v___f_2240_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(lean_object* v_00_u03c1_2241_, lean_object* v_00_u03c1_2242_, lean_object* v_00_u03c3_2243_, lean_object* v_inst_2244_, lean_object* v_inst_2245_, lean_object* v_m_2246_, lean_object* v_n_2247_, lean_object* v_s_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_){
_start:
{
lean_object* v___x_2251_; 
v___x_2251_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(v_inst_2244_, v_s_2248_, v_inst_2249_, v_inst_2250_);
return v___x_2251_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___boxed(lean_object* v_00_u03c1_2252_, lean_object* v_00_u03c1_2253_, lean_object* v_00_u03c3_2254_, lean_object* v_inst_2255_, lean_object* v_inst_2256_, lean_object* v_m_2257_, lean_object* v_n_2258_, lean_object* v_s_2259_, lean_object* v_inst_2260_, lean_object* v_inst_2261_){
_start:
{
lean_object* v_res_2262_; 
v_res_2262_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(v_00_u03c1_2252_, v_00_u03c1_2253_, v_00_u03c3_2254_, v_inst_2255_, v_inst_2256_, v_m_2257_, v_n_2258_, v_s_2259_, v_inst_2260_, v_inst_2261_);
lean_dec(v_inst_2256_);
lean_dec(v_00_u03c1_2253_);
return v_res_2262_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___redArg(lean_object* v_s_2263_, lean_object* v_inst_2264_){
_start:
{
lean_object* v_startInclusive_2265_; lean_object* v_endExclusive_2266_; lean_object* v___x_2267_; lean_object* v___x_2268_; lean_object* v___x_2269_; 
v_startInclusive_2265_ = lean_ctor_get(v_s_2263_, 1);
v_endExclusive_2266_ = lean_ctor_get(v_s_2263_, 2);
v___x_2267_ = lean_nat_sub(v_endExclusive_2266_, v_startInclusive_2265_);
v___x_2268_ = lean_apply_1(v_inst_2264_, v_s_2263_);
v___x_2269_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2269_, 0, v___x_2267_);
lean_ctor_set(v___x_2269_, 1, v___x_2268_);
return v___x_2269_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit(lean_object* v_00_u03c3_2270_, lean_object* v_00_u03c1_2271_, lean_object* v_s_2272_, lean_object* v_pat_2273_, lean_object* v_inst_2274_){
_start:
{
lean_object* v___x_2275_; 
v___x_2275_ = l_String_Slice_revSplit___redArg(v_s_2272_, v_inst_2274_);
return v___x_2275_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___boxed(lean_object* v_00_u03c3_2276_, lean_object* v_00_u03c1_2277_, lean_object* v_s_2278_, lean_object* v_pat_2279_, lean_object* v_inst_2280_){
_start:
{
lean_object* v_res_2281_; 
v_res_2281_ = l_String_Slice_revSplit(v_00_u03c3_2276_, v_00_u03c1_2277_, v_s_2278_, v_pat_2279_, v_inst_2280_);
lean_dec(v_pat_2279_);
return v_res_2281_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___redArg(lean_object* v_s_2282_, lean_object* v_inst_2283_){
_start:
{
lean_object* v_skipSuffix_x3f_2284_; lean_object* v___x_2285_; 
v_skipSuffix_x3f_2284_ = lean_ctor_get(v_inst_2283_, 0);
lean_inc_ref(v_skipSuffix_x3f_2284_);
lean_dec_ref(v_inst_2283_);
v___x_2285_ = lean_apply_1(v_skipSuffix_x3f_2284_, v_s_2282_);
return v___x_2285_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f(lean_object* v_00_u03c1_2286_, lean_object* v_s_2287_, lean_object* v_pat_2288_, lean_object* v_inst_2289_){
_start:
{
lean_object* v_skipSuffix_x3f_2290_; lean_object* v___x_2291_; 
v_skipSuffix_x3f_2290_ = lean_ctor_get(v_inst_2289_, 0);
lean_inc_ref(v_skipSuffix_x3f_2290_);
lean_dec_ref(v_inst_2289_);
v___x_2291_ = lean_apply_1(v_skipSuffix_x3f_2290_, v_s_2287_);
return v___x_2291_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___boxed(lean_object* v_00_u03c1_2292_, lean_object* v_s_2293_, lean_object* v_pat_2294_, lean_object* v_inst_2295_){
_start:
{
lean_object* v_res_2296_; 
v_res_2296_ = l_String_Slice_skipSuffix_x3f(v_00_u03c1_2292_, v_s_2293_, v_pat_2294_, v_inst_2295_);
lean_dec(v_pat_2294_);
return v_res_2296_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg(lean_object* v_s_2297_, lean_object* v_pos_2298_, lean_object* v_inst_2299_){
_start:
{
lean_object* v_str_2300_; lean_object* v_startInclusive_2301_; lean_object* v___x_2303_; uint8_t v_isShared_2304_; uint8_t v_isSharedCheck_2319_; 
v_str_2300_ = lean_ctor_get(v_s_2297_, 0);
v_startInclusive_2301_ = lean_ctor_get(v_s_2297_, 1);
v_isSharedCheck_2319_ = !lean_is_exclusive(v_s_2297_);
if (v_isSharedCheck_2319_ == 0)
{
lean_object* v_unused_2320_; 
v_unused_2320_ = lean_ctor_get(v_s_2297_, 2);
lean_dec(v_unused_2320_);
v___x_2303_ = v_s_2297_;
v_isShared_2304_ = v_isSharedCheck_2319_;
goto v_resetjp_2302_;
}
else
{
lean_inc(v_startInclusive_2301_);
lean_inc(v_str_2300_);
lean_dec(v_s_2297_);
v___x_2303_ = lean_box(0);
v_isShared_2304_ = v_isSharedCheck_2319_;
goto v_resetjp_2302_;
}
v_resetjp_2302_:
{
lean_object* v_skipSuffix_x3f_2305_; lean_object* v___x_2306_; lean_object* v___x_2308_; 
v_skipSuffix_x3f_2305_ = lean_ctor_get(v_inst_2299_, 0);
lean_inc_ref(v_skipSuffix_x3f_2305_);
lean_dec_ref(v_inst_2299_);
v___x_2306_ = lean_nat_add(v_startInclusive_2301_, v_pos_2298_);
if (v_isShared_2304_ == 0)
{
lean_ctor_set(v___x_2303_, 2, v___x_2306_);
v___x_2308_ = v___x_2303_;
goto v_reusejp_2307_;
}
else
{
lean_object* v_reuseFailAlloc_2318_; 
v_reuseFailAlloc_2318_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2318_, 0, v_str_2300_);
lean_ctor_set(v_reuseFailAlloc_2318_, 1, v_startInclusive_2301_);
lean_ctor_set(v_reuseFailAlloc_2318_, 2, v___x_2306_);
v___x_2308_ = v_reuseFailAlloc_2318_;
goto v_reusejp_2307_;
}
v_reusejp_2307_:
{
lean_object* v___x_2309_; 
v___x_2309_ = lean_apply_1(v_skipSuffix_x3f_2305_, v___x_2308_);
if (lean_obj_tag(v___x_2309_) == 0)
{
return v___x_2309_;
}
else
{
lean_object* v_val_2310_; lean_object* v___x_2312_; uint8_t v_isShared_2313_; uint8_t v_isSharedCheck_2317_; 
v_val_2310_ = lean_ctor_get(v___x_2309_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2309_);
if (v_isSharedCheck_2317_ == 0)
{
v___x_2312_ = v___x_2309_;
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
else
{
lean_inc(v_val_2310_);
lean_dec(v___x_2309_);
v___x_2312_ = lean_box(0);
v_isShared_2313_ = v_isSharedCheck_2317_;
goto v_resetjp_2311_;
}
v_resetjp_2311_:
{
lean_object* v___x_2315_; 
if (v_isShared_2313_ == 0)
{
v___x_2315_ = v___x_2312_;
goto v_reusejp_2314_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_val_2310_);
v___x_2315_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2314_;
}
v_reusejp_2314_:
{
return v___x_2315_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg___boxed(lean_object* v_s_2321_, lean_object* v_pos_2322_, lean_object* v_inst_2323_){
_start:
{
lean_object* v_res_2324_; 
v_res_2324_ = l_String_Slice_Pos_revSkip_x3f___redArg(v_s_2321_, v_pos_2322_, v_inst_2323_);
lean_dec(v_pos_2322_);
return v_res_2324_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f(lean_object* v_00_u03c1_2325_, lean_object* v_s_2326_, lean_object* v_pos_2327_, lean_object* v_pat_2328_, lean_object* v_inst_2329_){
_start:
{
lean_object* v_str_2330_; lean_object* v_startInclusive_2331_; lean_object* v___x_2333_; uint8_t v_isShared_2334_; uint8_t v_isSharedCheck_2349_; 
v_str_2330_ = lean_ctor_get(v_s_2326_, 0);
v_startInclusive_2331_ = lean_ctor_get(v_s_2326_, 1);
v_isSharedCheck_2349_ = !lean_is_exclusive(v_s_2326_);
if (v_isSharedCheck_2349_ == 0)
{
lean_object* v_unused_2350_; 
v_unused_2350_ = lean_ctor_get(v_s_2326_, 2);
lean_dec(v_unused_2350_);
v___x_2333_ = v_s_2326_;
v_isShared_2334_ = v_isSharedCheck_2349_;
goto v_resetjp_2332_;
}
else
{
lean_inc(v_startInclusive_2331_);
lean_inc(v_str_2330_);
lean_dec(v_s_2326_);
v___x_2333_ = lean_box(0);
v_isShared_2334_ = v_isSharedCheck_2349_;
goto v_resetjp_2332_;
}
v_resetjp_2332_:
{
lean_object* v_skipSuffix_x3f_2335_; lean_object* v___x_2336_; lean_object* v___x_2338_; 
v_skipSuffix_x3f_2335_ = lean_ctor_get(v_inst_2329_, 0);
lean_inc_ref(v_skipSuffix_x3f_2335_);
lean_dec_ref(v_inst_2329_);
v___x_2336_ = lean_nat_add(v_startInclusive_2331_, v_pos_2327_);
if (v_isShared_2334_ == 0)
{
lean_ctor_set(v___x_2333_, 2, v___x_2336_);
v___x_2338_ = v___x_2333_;
goto v_reusejp_2337_;
}
else
{
lean_object* v_reuseFailAlloc_2348_; 
v_reuseFailAlloc_2348_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2348_, 0, v_str_2330_);
lean_ctor_set(v_reuseFailAlloc_2348_, 1, v_startInclusive_2331_);
lean_ctor_set(v_reuseFailAlloc_2348_, 2, v___x_2336_);
v___x_2338_ = v_reuseFailAlloc_2348_;
goto v_reusejp_2337_;
}
v_reusejp_2337_:
{
lean_object* v___x_2339_; 
v___x_2339_ = lean_apply_1(v_skipSuffix_x3f_2335_, v___x_2338_);
if (lean_obj_tag(v___x_2339_) == 0)
{
return v___x_2339_;
}
else
{
lean_object* v_val_2340_; lean_object* v___x_2342_; uint8_t v_isShared_2343_; uint8_t v_isSharedCheck_2347_; 
v_val_2340_ = lean_ctor_get(v___x_2339_, 0);
v_isSharedCheck_2347_ = !lean_is_exclusive(v___x_2339_);
if (v_isSharedCheck_2347_ == 0)
{
v___x_2342_ = v___x_2339_;
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
else
{
lean_inc(v_val_2340_);
lean_dec(v___x_2339_);
v___x_2342_ = lean_box(0);
v_isShared_2343_ = v_isSharedCheck_2347_;
goto v_resetjp_2341_;
}
v_resetjp_2341_:
{
lean_object* v___x_2345_; 
if (v_isShared_2343_ == 0)
{
v___x_2345_ = v___x_2342_;
goto v_reusejp_2344_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_val_2340_);
v___x_2345_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2344_;
}
v_reusejp_2344_:
{
return v___x_2345_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_2351_, lean_object* v_s_2352_, lean_object* v_pos_2353_, lean_object* v_pat_2354_, lean_object* v_inst_2355_){
_start:
{
lean_object* v_res_2356_; 
v_res_2356_ = l_String_Slice_Pos_revSkip_x3f(v_00_u03c1_2351_, v_s_2352_, v_pos_2353_, v_pat_2354_, v_inst_2355_);
lean_dec(v_pat_2354_);
lean_dec(v_pos_2353_);
return v_res_2356_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___redArg(lean_object* v_s_2357_, lean_object* v_inst_2358_){
_start:
{
lean_object* v_skipSuffix_x3f_2359_; lean_object* v___x_2360_; 
v_skipSuffix_x3f_2359_ = lean_ctor_get(v_inst_2358_, 0);
lean_inc_ref(v_skipSuffix_x3f_2359_);
lean_dec_ref(v_inst_2358_);
lean_inc_ref(v_s_2357_);
v___x_2360_ = lean_apply_1(v_skipSuffix_x3f_2359_, v_s_2357_);
if (lean_obj_tag(v___x_2360_) == 0)
{
lean_object* v___x_2361_; 
lean_dec_ref(v_s_2357_);
v___x_2361_ = lean_box(0);
return v___x_2361_;
}
else
{
lean_object* v_val_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2380_; 
v_val_2362_ = lean_ctor_get(v___x_2360_, 0);
v_isSharedCheck_2380_ = !lean_is_exclusive(v___x_2360_);
if (v_isSharedCheck_2380_ == 0)
{
v___x_2364_ = v___x_2360_;
v_isShared_2365_ = v_isSharedCheck_2380_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_val_2362_);
lean_dec(v___x_2360_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2380_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v_str_2366_; lean_object* v_startInclusive_2367_; lean_object* v___x_2369_; uint8_t v_isShared_2370_; uint8_t v_isSharedCheck_2378_; 
v_str_2366_ = lean_ctor_get(v_s_2357_, 0);
v_startInclusive_2367_ = lean_ctor_get(v_s_2357_, 1);
v_isSharedCheck_2378_ = !lean_is_exclusive(v_s_2357_);
if (v_isSharedCheck_2378_ == 0)
{
lean_object* v_unused_2379_; 
v_unused_2379_ = lean_ctor_get(v_s_2357_, 2);
lean_dec(v_unused_2379_);
v___x_2369_ = v_s_2357_;
v_isShared_2370_ = v_isSharedCheck_2378_;
goto v_resetjp_2368_;
}
else
{
lean_inc(v_startInclusive_2367_);
lean_inc(v_str_2366_);
lean_dec(v_s_2357_);
v___x_2369_ = lean_box(0);
v_isShared_2370_ = v_isSharedCheck_2378_;
goto v_resetjp_2368_;
}
v_resetjp_2368_:
{
lean_object* v___x_2371_; lean_object* v___x_2373_; 
v___x_2371_ = lean_nat_add(v_startInclusive_2367_, v_val_2362_);
lean_dec(v_val_2362_);
if (v_isShared_2370_ == 0)
{
lean_ctor_set(v___x_2369_, 2, v___x_2371_);
v___x_2373_ = v___x_2369_;
goto v_reusejp_2372_;
}
else
{
lean_object* v_reuseFailAlloc_2377_; 
v_reuseFailAlloc_2377_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2377_, 0, v_str_2366_);
lean_ctor_set(v_reuseFailAlloc_2377_, 1, v_startInclusive_2367_);
lean_ctor_set(v_reuseFailAlloc_2377_, 2, v___x_2371_);
v___x_2373_ = v_reuseFailAlloc_2377_;
goto v_reusejp_2372_;
}
v_reusejp_2372_:
{
lean_object* v___x_2375_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 0, v___x_2373_);
v___x_2375_ = v___x_2364_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2376_; 
v_reuseFailAlloc_2376_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2376_, 0, v___x_2373_);
v___x_2375_ = v_reuseFailAlloc_2376_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
return v___x_2375_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f(lean_object* v_00_u03c1_2381_, lean_object* v_s_2382_, lean_object* v_pat_2383_, lean_object* v_inst_2384_){
_start:
{
lean_object* v_skipSuffix_x3f_2385_; lean_object* v___x_2386_; 
v_skipSuffix_x3f_2385_ = lean_ctor_get(v_inst_2384_, 0);
lean_inc_ref(v_skipSuffix_x3f_2385_);
lean_dec_ref(v_inst_2384_);
lean_inc_ref(v_s_2382_);
v___x_2386_ = lean_apply_1(v_skipSuffix_x3f_2385_, v_s_2382_);
if (lean_obj_tag(v___x_2386_) == 0)
{
lean_object* v___x_2387_; 
lean_dec_ref(v_s_2382_);
v___x_2387_ = lean_box(0);
return v___x_2387_;
}
else
{
lean_object* v_val_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2406_; 
v_val_2388_ = lean_ctor_get(v___x_2386_, 0);
v_isSharedCheck_2406_ = !lean_is_exclusive(v___x_2386_);
if (v_isSharedCheck_2406_ == 0)
{
v___x_2390_ = v___x_2386_;
v_isShared_2391_ = v_isSharedCheck_2406_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_val_2388_);
lean_dec(v___x_2386_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2406_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v_str_2392_; lean_object* v_startInclusive_2393_; lean_object* v___x_2395_; uint8_t v_isShared_2396_; uint8_t v_isSharedCheck_2404_; 
v_str_2392_ = lean_ctor_get(v_s_2382_, 0);
v_startInclusive_2393_ = lean_ctor_get(v_s_2382_, 1);
v_isSharedCheck_2404_ = !lean_is_exclusive(v_s_2382_);
if (v_isSharedCheck_2404_ == 0)
{
lean_object* v_unused_2405_; 
v_unused_2405_ = lean_ctor_get(v_s_2382_, 2);
lean_dec(v_unused_2405_);
v___x_2395_ = v_s_2382_;
v_isShared_2396_ = v_isSharedCheck_2404_;
goto v_resetjp_2394_;
}
else
{
lean_inc(v_startInclusive_2393_);
lean_inc(v_str_2392_);
lean_dec(v_s_2382_);
v___x_2395_ = lean_box(0);
v_isShared_2396_ = v_isSharedCheck_2404_;
goto v_resetjp_2394_;
}
v_resetjp_2394_:
{
lean_object* v___x_2397_; lean_object* v___x_2399_; 
v___x_2397_ = lean_nat_add(v_startInclusive_2393_, v_val_2388_);
lean_dec(v_val_2388_);
if (v_isShared_2396_ == 0)
{
lean_ctor_set(v___x_2395_, 2, v___x_2397_);
v___x_2399_ = v___x_2395_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_str_2392_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_startInclusive_2393_);
lean_ctor_set(v_reuseFailAlloc_2403_, 2, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2401_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2399_);
v___x_2401_ = v___x_2390_;
goto v_reusejp_2400_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2399_);
v___x_2401_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2400_;
}
v_reusejp_2400_:
{
return v___x_2401_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_2407_, lean_object* v_s_2408_, lean_object* v_pat_2409_, lean_object* v_inst_2410_){
_start:
{
lean_object* v_res_2411_; 
v_res_2411_ = l_String_Slice_dropSuffix_x3f(v_00_u03c1_2407_, v_s_2408_, v_pat_2409_, v_inst_2410_);
lean_dec(v_pat_2409_);
return v_res_2411_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___redArg(lean_object* v_s_2412_, lean_object* v_inst_2413_){
_start:
{
lean_object* v_skipSuffix_x3f_2414_; lean_object* v___x_2415_; 
v_skipSuffix_x3f_2414_ = lean_ctor_get(v_inst_2413_, 0);
lean_inc_ref(v_skipSuffix_x3f_2414_);
lean_dec_ref(v_inst_2413_);
lean_inc_ref(v_s_2412_);
v___x_2415_ = lean_apply_1(v_skipSuffix_x3f_2414_, v_s_2412_);
if (lean_obj_tag(v___x_2415_) == 0)
{
return v_s_2412_;
}
else
{
lean_object* v_val_2416_; lean_object* v_str_2417_; lean_object* v_startInclusive_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2426_; 
v_val_2416_ = lean_ctor_get(v___x_2415_, 0);
lean_inc(v_val_2416_);
lean_dec_ref_known(v___x_2415_, 1);
v_str_2417_ = lean_ctor_get(v_s_2412_, 0);
v_startInclusive_2418_ = lean_ctor_get(v_s_2412_, 1);
v_isSharedCheck_2426_ = !lean_is_exclusive(v_s_2412_);
if (v_isSharedCheck_2426_ == 0)
{
lean_object* v_unused_2427_; 
v_unused_2427_ = lean_ctor_get(v_s_2412_, 2);
lean_dec(v_unused_2427_);
v___x_2420_ = v_s_2412_;
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_startInclusive_2418_);
lean_inc(v_str_2417_);
lean_dec(v_s_2412_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2426_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2422_ = lean_nat_add(v_startInclusive_2418_, v_val_2416_);
lean_dec(v_val_2416_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 2, v___x_2422_);
v___x_2424_ = v___x_2420_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2425_; 
v_reuseFailAlloc_2425_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2425_, 0, v_str_2417_);
lean_ctor_set(v_reuseFailAlloc_2425_, 1, v_startInclusive_2418_);
lean_ctor_set(v_reuseFailAlloc_2425_, 2, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2425_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
return v___x_2424_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix(lean_object* v_00_u03c1_2428_, lean_object* v_s_2429_, lean_object* v_pat_2430_, lean_object* v_inst_2431_){
_start:
{
lean_object* v___x_2432_; 
v___x_2432_ = l_String_Slice_dropSuffix___redArg(v_s_2429_, v_inst_2431_);
return v___x_2432_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___boxed(lean_object* v_00_u03c1_2433_, lean_object* v_s_2434_, lean_object* v_pat_2435_, lean_object* v_inst_2436_){
_start:
{
lean_object* v_res_2437_; 
v_res_2437_ = l_String_Slice_dropSuffix(v_00_u03c1_2433_, v_s_2434_, v_pat_2435_, v_inst_2436_);
lean_dec(v_pat_2435_);
return v_res_2437_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object* v_s_2438_, lean_object* v_pos_2439_, lean_object* v_inst_2440_){
_start:
{
lean_object* v_str_2441_; lean_object* v_startInclusive_2442_; lean_object* v_skipSuffix_x3f_2443_; lean_object* v___x_2444_; lean_object* v___x_2445_; lean_object* v___x_2446_; 
v_str_2441_ = lean_ctor_get(v_s_2438_, 0);
v_startInclusive_2442_ = lean_ctor_get(v_s_2438_, 1);
v_skipSuffix_x3f_2443_ = lean_ctor_get(v_inst_2440_, 0);
v___x_2444_ = lean_nat_add(v_startInclusive_2442_, v_pos_2439_);
lean_inc(v_startInclusive_2442_);
lean_inc_ref(v_str_2441_);
v___x_2445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2445_, 0, v_str_2441_);
lean_ctor_set(v___x_2445_, 1, v_startInclusive_2442_);
lean_ctor_set(v___x_2445_, 2, v___x_2444_);
lean_inc_ref(v_skipSuffix_x3f_2443_);
v___x_2446_ = lean_apply_1(v_skipSuffix_x3f_2443_, v___x_2445_);
if (lean_obj_tag(v___x_2446_) == 0)
{
lean_dec_ref(v_inst_2440_);
return v_pos_2439_;
}
else
{
lean_object* v_val_2447_; lean_object* v___x_2448_; lean_object* v___x_2449_; uint8_t v___x_2450_; 
v_val_2447_ = lean_ctor_get(v___x_2446_, 0);
lean_inc(v_val_2447_);
lean_dec_ref_known(v___x_2446_, 1);
v___x_2448_ = lean_unsigned_to_nat(1u);
v___x_2449_ = lean_nat_add(v_val_2447_, v___x_2448_);
v___x_2450_ = lean_nat_dec_le(v___x_2449_, v_pos_2439_);
lean_dec(v___x_2449_);
if (v___x_2450_ == 0)
{
lean_dec(v_val_2447_);
lean_dec_ref(v_inst_2440_);
return v_pos_2439_;
}
else
{
lean_dec(v_pos_2439_);
v_pos_2439_ = v_val_2447_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg___boxed(lean_object* v_s_2452_, lean_object* v_pos_2453_, lean_object* v_inst_2454_){
_start:
{
lean_object* v_res_2455_; 
v_res_2455_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2452_, v_pos_2453_, v_inst_2454_);
lean_dec_ref(v_s_2452_);
return v_res_2455_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile(lean_object* v_00_u03c1_2456_, lean_object* v_s_2457_, lean_object* v_pos_2458_, lean_object* v_pat_2459_, lean_object* v_inst_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2457_, v_pos_2458_, v_inst_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_2462_, lean_object* v_s_2463_, lean_object* v_pos_2464_, lean_object* v_pat_2465_, lean_object* v_inst_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_String_Slice_Pos_revSkipWhile(v_00_u03c1_2462_, v_s_2463_, v_pos_2464_, v_pat_2465_, v_inst_2466_);
lean_dec(v_pat_2465_);
lean_dec_ref(v_s_2463_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg(lean_object* v_s_2468_, lean_object* v_inst_2469_){
_start:
{
lean_object* v_startInclusive_2470_; lean_object* v_endExclusive_2471_; lean_object* v___x_2472_; lean_object* v___x_2473_; 
v_startInclusive_2470_ = lean_ctor_get(v_s_2468_, 1);
v_endExclusive_2471_ = lean_ctor_get(v_s_2468_, 2);
v___x_2472_ = lean_nat_sub(v_endExclusive_2471_, v_startInclusive_2470_);
v___x_2473_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2468_, v___x_2472_, v_inst_2469_);
return v___x_2473_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg___boxed(lean_object* v_s_2474_, lean_object* v_inst_2475_){
_start:
{
lean_object* v_res_2476_; 
v_res_2476_ = l_String_Slice_skipSuffixWhile___redArg(v_s_2474_, v_inst_2475_);
lean_dec_ref(v_s_2474_);
return v_res_2476_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile(lean_object* v_00_u03c1_2477_, lean_object* v_s_2478_, lean_object* v_pat_2479_, lean_object* v_inst_2480_){
_start:
{
lean_object* v_startInclusive_2481_; lean_object* v_endExclusive_2482_; lean_object* v___x_2483_; lean_object* v___x_2484_; 
v_startInclusive_2481_ = lean_ctor_get(v_s_2478_, 1);
v_endExclusive_2482_ = lean_ctor_get(v_s_2478_, 2);
v___x_2483_ = lean_nat_sub(v_endExclusive_2482_, v_startInclusive_2481_);
v___x_2484_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2478_, v___x_2483_, v_inst_2480_);
return v___x_2484_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___boxed(lean_object* v_00_u03c1_2485_, lean_object* v_s_2486_, lean_object* v_pat_2487_, lean_object* v_inst_2488_){
_start:
{
lean_object* v_res_2489_; 
v_res_2489_ = l_String_Slice_skipSuffixWhile(v_00_u03c1_2485_, v_s_2486_, v_pat_2487_, v_inst_2488_);
lean_dec(v_pat_2487_);
lean_dec_ref(v_s_2486_);
return v_res_2489_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_revAll___redArg(lean_object* v_s_2490_, lean_object* v_inst_2491_){
_start:
{
lean_object* v_startInclusive_2492_; lean_object* v_endExclusive_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2496_; uint8_t v_decide_2497_; 
v_startInclusive_2492_ = lean_ctor_get(v_s_2490_, 1);
v_endExclusive_2493_ = lean_ctor_get(v_s_2490_, 2);
v___x_2494_ = lean_nat_sub(v_endExclusive_2493_, v_startInclusive_2492_);
v___x_2495_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2490_, v___x_2494_, v_inst_2491_);
v___x_2496_ = lean_unsigned_to_nat(0u);
v_decide_2497_ = lean_nat_dec_eq(v___x_2495_, v___x_2496_);
lean_dec(v___x_2495_);
return v_decide_2497_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___redArg___boxed(lean_object* v_s_2498_, lean_object* v_inst_2499_){
_start:
{
uint8_t v_res_2500_; lean_object* v_r_2501_; 
v_res_2500_ = l_String_Slice_revAll___redArg(v_s_2498_, v_inst_2499_);
lean_dec_ref(v_s_2498_);
v_r_2501_ = lean_box(v_res_2500_);
return v_r_2501_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_revAll(lean_object* v_00_u03c1_2502_, lean_object* v_s_2503_, lean_object* v_pat_2504_, lean_object* v_inst_2505_){
_start:
{
lean_object* v_startInclusive_2506_; lean_object* v_endExclusive_2507_; lean_object* v___x_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v_decide_2511_; 
v_startInclusive_2506_ = lean_ctor_get(v_s_2503_, 1);
v_endExclusive_2507_ = lean_ctor_get(v_s_2503_, 2);
v___x_2508_ = lean_nat_sub(v_endExclusive_2507_, v_startInclusive_2506_);
v___x_2509_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2503_, v___x_2508_, v_inst_2505_);
v___x_2510_ = lean_unsigned_to_nat(0u);
v_decide_2511_ = lean_nat_dec_eq(v___x_2509_, v___x_2510_);
lean_dec(v___x_2509_);
return v_decide_2511_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___boxed(lean_object* v_00_u03c1_2512_, lean_object* v_s_2513_, lean_object* v_pat_2514_, lean_object* v_inst_2515_){
_start:
{
uint8_t v_res_2516_; lean_object* v_r_2517_; 
v_res_2516_ = l_String_Slice_revAll(v_00_u03c1_2512_, v_s_2513_, v_pat_2514_, v_inst_2515_);
lean_dec(v_pat_2514_);
lean_dec_ref(v_s_2513_);
v_r_2517_ = lean_box(v_res_2516_);
return v_r_2517_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object* v_s_2518_, lean_object* v_inst_2519_){
_start:
{
lean_object* v_str_2520_; lean_object* v_startInclusive_2521_; lean_object* v_endExclusive_2522_; lean_object* v___x_2523_; lean_object* v___x_2524_; lean_object* v___x_2526_; uint8_t v_isShared_2527_; uint8_t v_isSharedCheck_2532_; 
v_str_2520_ = lean_ctor_get(v_s_2518_, 0);
lean_inc_ref(v_str_2520_);
v_startInclusive_2521_ = lean_ctor_get(v_s_2518_, 1);
lean_inc(v_startInclusive_2521_);
v_endExclusive_2522_ = lean_ctor_get(v_s_2518_, 2);
v___x_2523_ = lean_nat_sub(v_endExclusive_2522_, v_startInclusive_2521_);
v___x_2524_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2518_, v___x_2523_, v_inst_2519_);
v_isSharedCheck_2532_ = !lean_is_exclusive(v_s_2518_);
if (v_isSharedCheck_2532_ == 0)
{
lean_object* v_unused_2533_; lean_object* v_unused_2534_; lean_object* v_unused_2535_; 
v_unused_2533_ = lean_ctor_get(v_s_2518_, 2);
lean_dec(v_unused_2533_);
v_unused_2534_ = lean_ctor_get(v_s_2518_, 1);
lean_dec(v_unused_2534_);
v_unused_2535_ = lean_ctor_get(v_s_2518_, 0);
lean_dec(v_unused_2535_);
v___x_2526_ = v_s_2518_;
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
else
{
lean_dec(v_s_2518_);
v___x_2526_ = lean_box(0);
v_isShared_2527_ = v_isSharedCheck_2532_;
goto v_resetjp_2525_;
}
v_resetjp_2525_:
{
lean_object* v___x_2528_; lean_object* v___x_2530_; 
v___x_2528_ = lean_nat_add(v_startInclusive_2521_, v___x_2524_);
lean_dec(v___x_2524_);
if (v_isShared_2527_ == 0)
{
lean_ctor_set(v___x_2526_, 2, v___x_2528_);
v___x_2530_ = v___x_2526_;
goto v_reusejp_2529_;
}
else
{
lean_object* v_reuseFailAlloc_2531_; 
v_reuseFailAlloc_2531_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2531_, 0, v_str_2520_);
lean_ctor_set(v_reuseFailAlloc_2531_, 1, v_startInclusive_2521_);
lean_ctor_set(v_reuseFailAlloc_2531_, 2, v___x_2528_);
v___x_2530_ = v_reuseFailAlloc_2531_;
goto v_reusejp_2529_;
}
v_reusejp_2529_:
{
return v___x_2530_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object* v_00_u03c1_2536_, lean_object* v_s_2537_, lean_object* v_pat_2538_, lean_object* v_inst_2539_){
_start:
{
lean_object* v_str_2540_; lean_object* v_startInclusive_2541_; lean_object* v_endExclusive_2542_; lean_object* v___x_2543_; lean_object* v___x_2544_; lean_object* v___x_2546_; uint8_t v_isShared_2547_; uint8_t v_isSharedCheck_2552_; 
v_str_2540_ = lean_ctor_get(v_s_2537_, 0);
lean_inc_ref(v_str_2540_);
v_startInclusive_2541_ = lean_ctor_get(v_s_2537_, 1);
lean_inc(v_startInclusive_2541_);
v_endExclusive_2542_ = lean_ctor_get(v_s_2537_, 2);
v___x_2543_ = lean_nat_sub(v_endExclusive_2542_, v_startInclusive_2541_);
v___x_2544_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2537_, v___x_2543_, v_inst_2539_);
v_isSharedCheck_2552_ = !lean_is_exclusive(v_s_2537_);
if (v_isSharedCheck_2552_ == 0)
{
lean_object* v_unused_2553_; lean_object* v_unused_2554_; lean_object* v_unused_2555_; 
v_unused_2553_ = lean_ctor_get(v_s_2537_, 2);
lean_dec(v_unused_2553_);
v_unused_2554_ = lean_ctor_get(v_s_2537_, 1);
lean_dec(v_unused_2554_);
v_unused_2555_ = lean_ctor_get(v_s_2537_, 0);
lean_dec(v_unused_2555_);
v___x_2546_ = v_s_2537_;
v_isShared_2547_ = v_isSharedCheck_2552_;
goto v_resetjp_2545_;
}
else
{
lean_dec(v_s_2537_);
v___x_2546_ = lean_box(0);
v_isShared_2547_ = v_isSharedCheck_2552_;
goto v_resetjp_2545_;
}
v_resetjp_2545_:
{
lean_object* v___x_2548_; lean_object* v___x_2550_; 
v___x_2548_ = lean_nat_add(v_startInclusive_2541_, v___x_2544_);
lean_dec(v___x_2544_);
if (v_isShared_2547_ == 0)
{
lean_ctor_set(v___x_2546_, 2, v___x_2548_);
v___x_2550_ = v___x_2546_;
goto v_reusejp_2549_;
}
else
{
lean_object* v_reuseFailAlloc_2551_; 
v_reuseFailAlloc_2551_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2551_, 0, v_str_2540_);
lean_ctor_set(v_reuseFailAlloc_2551_, 1, v_startInclusive_2541_);
lean_ctor_set(v_reuseFailAlloc_2551_, 2, v___x_2548_);
v___x_2550_ = v_reuseFailAlloc_2551_;
goto v_reusejp_2549_;
}
v_reusejp_2549_:
{
return v___x_2550_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object* v_00_u03c1_2556_, lean_object* v_s_2557_, lean_object* v_pat_2558_, lean_object* v_inst_2559_){
_start:
{
lean_object* v_res_2560_; 
v_res_2560_ = l_String_Slice_dropEndWhile(v_00_u03c1_2556_, v_s_2557_, v_pat_2558_, v_inst_2559_);
lean_dec(v_pat_2558_);
return v_res_2560_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiEnd___closed__0(void){
_start:
{
lean_object* v___x_2561_; lean_object* v___x_2562_; 
v___x_2561_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_2562_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_2561_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object* v_s_2563_){
_start:
{
lean_object* v___x_2564_; lean_object* v_str_2565_; lean_object* v_startInclusive_2566_; lean_object* v_endExclusive_2567_; lean_object* v___x_2568_; lean_object* v___x_2569_; lean_object* v___x_2571_; uint8_t v_isShared_2572_; uint8_t v_isSharedCheck_2577_; 
v___x_2564_ = lean_obj_once(&l_String_Slice_trimAsciiEnd___closed__0, &l_String_Slice_trimAsciiEnd___closed__0_once, _init_l_String_Slice_trimAsciiEnd___closed__0);
v_str_2565_ = lean_ctor_get(v_s_2563_, 0);
lean_inc_ref(v_str_2565_);
v_startInclusive_2566_ = lean_ctor_get(v_s_2563_, 1);
lean_inc(v_startInclusive_2566_);
v_endExclusive_2567_ = lean_ctor_get(v_s_2563_, 2);
v___x_2568_ = lean_nat_sub(v_endExclusive_2567_, v_startInclusive_2566_);
v___x_2569_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2563_, v___x_2568_, v___x_2564_);
v_isSharedCheck_2577_ = !lean_is_exclusive(v_s_2563_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; lean_object* v_unused_2579_; lean_object* v_unused_2580_; 
v_unused_2578_ = lean_ctor_get(v_s_2563_, 2);
lean_dec(v_unused_2578_);
v_unused_2579_ = lean_ctor_get(v_s_2563_, 1);
lean_dec(v_unused_2579_);
v_unused_2580_ = lean_ctor_get(v_s_2563_, 0);
lean_dec(v_unused_2580_);
v___x_2571_ = v_s_2563_;
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
else
{
lean_dec(v_s_2563_);
v___x_2571_ = lean_box(0);
v_isShared_2572_ = v_isSharedCheck_2577_;
goto v_resetjp_2570_;
}
v_resetjp_2570_:
{
lean_object* v___x_2573_; lean_object* v___x_2575_; 
v___x_2573_ = lean_nat_add(v_startInclusive_2566_, v___x_2569_);
lean_dec(v___x_2569_);
if (v_isShared_2572_ == 0)
{
lean_ctor_set(v___x_2571_, 2, v___x_2573_);
v___x_2575_ = v___x_2571_;
goto v_reusejp_2574_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_str_2565_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_startInclusive_2566_);
lean_ctor_set(v_reuseFailAlloc_2576_, 2, v___x_2573_);
v___x_2575_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2574_;
}
v_reusejp_2574_:
{
return v___x_2575_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___redArg(lean_object* v_s_2581_, lean_object* v_inst_2582_){
_start:
{
lean_object* v_str_2583_; lean_object* v_startInclusive_2584_; lean_object* v_endExclusive_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; lean_object* v___x_2589_; uint8_t v_isShared_2590_; uint8_t v_isSharedCheck_2595_; 
v_str_2583_ = lean_ctor_get(v_s_2581_, 0);
lean_inc_ref(v_str_2583_);
v_startInclusive_2584_ = lean_ctor_get(v_s_2581_, 1);
lean_inc(v_startInclusive_2584_);
v_endExclusive_2585_ = lean_ctor_get(v_s_2581_, 2);
lean_inc(v_endExclusive_2585_);
v___x_2586_ = lean_nat_sub(v_endExclusive_2585_, v_startInclusive_2584_);
v___x_2587_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2581_, v___x_2586_, v_inst_2582_);
v_isSharedCheck_2595_ = !lean_is_exclusive(v_s_2581_);
if (v_isSharedCheck_2595_ == 0)
{
lean_object* v_unused_2596_; lean_object* v_unused_2597_; lean_object* v_unused_2598_; 
v_unused_2596_ = lean_ctor_get(v_s_2581_, 2);
lean_dec(v_unused_2596_);
v_unused_2597_ = lean_ctor_get(v_s_2581_, 1);
lean_dec(v_unused_2597_);
v_unused_2598_ = lean_ctor_get(v_s_2581_, 0);
lean_dec(v_unused_2598_);
v___x_2589_ = v_s_2581_;
v_isShared_2590_ = v_isSharedCheck_2595_;
goto v_resetjp_2588_;
}
else
{
lean_dec(v_s_2581_);
v___x_2589_ = lean_box(0);
v_isShared_2590_ = v_isSharedCheck_2595_;
goto v_resetjp_2588_;
}
v_resetjp_2588_:
{
lean_object* v___x_2591_; lean_object* v___x_2593_; 
v___x_2591_ = lean_nat_add(v_startInclusive_2584_, v___x_2587_);
lean_dec(v___x_2587_);
lean_dec(v_startInclusive_2584_);
if (v_isShared_2590_ == 0)
{
lean_ctor_set(v___x_2589_, 1, v___x_2591_);
v___x_2593_ = v___x_2589_;
goto v_reusejp_2592_;
}
else
{
lean_object* v_reuseFailAlloc_2594_; 
v_reuseFailAlloc_2594_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2594_, 0, v_str_2583_);
lean_ctor_set(v_reuseFailAlloc_2594_, 1, v___x_2591_);
lean_ctor_set(v_reuseFailAlloc_2594_, 2, v_endExclusive_2585_);
v___x_2593_ = v_reuseFailAlloc_2594_;
goto v_reusejp_2592_;
}
v_reusejp_2592_:
{
return v___x_2593_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile(lean_object* v_00_u03c1_2599_, lean_object* v_s_2600_, lean_object* v_pat_2601_, lean_object* v_inst_2602_){
_start:
{
lean_object* v_str_2603_; lean_object* v_startInclusive_2604_; lean_object* v_endExclusive_2605_; lean_object* v___x_2606_; lean_object* v___x_2607_; lean_object* v___x_2609_; uint8_t v_isShared_2610_; uint8_t v_isSharedCheck_2615_; 
v_str_2603_ = lean_ctor_get(v_s_2600_, 0);
lean_inc_ref(v_str_2603_);
v_startInclusive_2604_ = lean_ctor_get(v_s_2600_, 1);
lean_inc(v_startInclusive_2604_);
v_endExclusive_2605_ = lean_ctor_get(v_s_2600_, 2);
lean_inc(v_endExclusive_2605_);
v___x_2606_ = lean_nat_sub(v_endExclusive_2605_, v_startInclusive_2604_);
v___x_2607_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2600_, v___x_2606_, v_inst_2602_);
v_isSharedCheck_2615_ = !lean_is_exclusive(v_s_2600_);
if (v_isSharedCheck_2615_ == 0)
{
lean_object* v_unused_2616_; lean_object* v_unused_2617_; lean_object* v_unused_2618_; 
v_unused_2616_ = lean_ctor_get(v_s_2600_, 2);
lean_dec(v_unused_2616_);
v_unused_2617_ = lean_ctor_get(v_s_2600_, 1);
lean_dec(v_unused_2617_);
v_unused_2618_ = lean_ctor_get(v_s_2600_, 0);
lean_dec(v_unused_2618_);
v___x_2609_ = v_s_2600_;
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
else
{
lean_dec(v_s_2600_);
v___x_2609_ = lean_box(0);
v_isShared_2610_ = v_isSharedCheck_2615_;
goto v_resetjp_2608_;
}
v_resetjp_2608_:
{
lean_object* v___x_2611_; lean_object* v___x_2613_; 
v___x_2611_ = lean_nat_add(v_startInclusive_2604_, v___x_2607_);
lean_dec(v___x_2607_);
lean_dec(v_startInclusive_2604_);
if (v_isShared_2610_ == 0)
{
lean_ctor_set(v___x_2609_, 1, v___x_2611_);
v___x_2613_ = v___x_2609_;
goto v_reusejp_2612_;
}
else
{
lean_object* v_reuseFailAlloc_2614_; 
v_reuseFailAlloc_2614_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2614_, 0, v_str_2603_);
lean_ctor_set(v_reuseFailAlloc_2614_, 1, v___x_2611_);
lean_ctor_set(v_reuseFailAlloc_2614_, 2, v_endExclusive_2605_);
v___x_2613_ = v_reuseFailAlloc_2614_;
goto v_reusejp_2612_;
}
v_reusejp_2612_:
{
return v___x_2613_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___boxed(lean_object* v_00_u03c1_2619_, lean_object* v_s_2620_, lean_object* v_pat_2621_, lean_object* v_inst_2622_){
_start:
{
lean_object* v_res_2623_; 
v_res_2623_ = l_String_Slice_takeEndWhile(v_00_u03c1_2619_, v_s_2620_, v_pat_2621_, v_inst_2622_);
lean_dec(v_pat_2621_);
return v_res_2623_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___redArg(lean_object* v_inst_2624_, lean_object* v_s_2625_, lean_object* v_inst_2626_){
_start:
{
lean_object* v___f_2627_; lean_object* v_searcher_2628_; lean_object* v___x_2629_; lean_object* v___f_2630_; lean_object* v___x_2631_; 
v___f_2627_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_2625_);
v_searcher_2628_ = lean_apply_1(v_inst_2626_, v_s_2625_);
v___x_2629_ = lean_box(0);
v___f_2630_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_2631_ = lean_apply_7(v_inst_2624_, v_s_2625_, v___f_2627_, lean_box(0), lean_box(0), v_searcher_2628_, v___x_2629_, v___f_2630_);
return v___x_2631_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f(lean_object* v_00_u03c3_2632_, lean_object* v_inst_2633_, lean_object* v_inst_2634_, lean_object* v_00_u03c1_2635_, lean_object* v_s_2636_, lean_object* v_pat_2637_, lean_object* v_inst_2638_){
_start:
{
lean_object* v___x_2639_; 
v___x_2639_ = l_String_Slice_revFind_x3f___redArg(v_inst_2634_, v_s_2636_, v_inst_2638_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___boxed(lean_object* v_00_u03c3_2640_, lean_object* v_inst_2641_, lean_object* v_inst_2642_, lean_object* v_00_u03c1_2643_, lean_object* v_s_2644_, lean_object* v_pat_2645_, lean_object* v_inst_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_String_Slice_revFind_x3f(v_00_u03c3_2640_, v_inst_2641_, v_inst_2642_, v_00_u03c1_2643_, v_s_2644_, v_pat_2645_, v_inst_2646_);
lean_dec(v_pat_2645_);
lean_dec(v_inst_2641_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(lean_object* v_s_2648_, lean_object* v_pos_2649_){
_start:
{
lean_object* v_str_2650_; lean_object* v_startInclusive_2651_; lean_object* v_endExclusive_2652_; lean_object* v___x_2653_; lean_object* v___x_2662_; lean_object* v___x_2663_; uint8_t v_decide_2664_; 
v_str_2650_ = lean_ctor_get(v_s_2648_, 0);
v_startInclusive_2651_ = lean_ctor_get(v_s_2648_, 1);
v_endExclusive_2652_ = lean_ctor_get(v_s_2648_, 2);
v___x_2653_ = lean_nat_add(v_startInclusive_2651_, v_pos_2649_);
v___x_2662_ = lean_unsigned_to_nat(0u);
v___x_2663_ = lean_nat_sub(v_endExclusive_2652_, v___x_2653_);
v_decide_2664_ = lean_nat_dec_eq(v___x_2662_, v___x_2663_);
lean_dec(v___x_2663_);
if (v_decide_2664_ == 0)
{
uint32_t v___x_2665_; uint32_t v___x_2666_; uint8_t v___x_2667_; 
v___x_2665_ = lean_string_utf8_get_fast(v_str_2650_, v___x_2653_);
v___x_2666_ = 32;
v___x_2667_ = lean_uint32_dec_eq(v___x_2665_, v___x_2666_);
if (v___x_2667_ == 0)
{
uint32_t v___x_2668_; uint8_t v___x_2669_; 
v___x_2668_ = 9;
v___x_2669_ = lean_uint32_dec_eq(v___x_2665_, v___x_2668_);
if (v___x_2669_ == 0)
{
uint32_t v___x_2670_; uint8_t v___x_2671_; 
v___x_2670_ = 13;
v___x_2671_ = lean_uint32_dec_eq(v___x_2665_, v___x_2670_);
if (v___x_2671_ == 0)
{
uint32_t v___x_2672_; uint8_t v___x_2673_; 
v___x_2672_ = 10;
v___x_2673_ = lean_uint32_dec_eq(v___x_2665_, v___x_2672_);
if (v___x_2673_ == 0)
{
lean_dec(v___x_2653_);
return v_pos_2649_;
}
else
{
goto v___jp_2654_;
}
}
else
{
goto v___jp_2654_;
}
}
else
{
goto v___jp_2654_;
}
}
else
{
goto v___jp_2654_;
}
}
else
{
lean_dec(v___x_2653_);
return v_pos_2649_;
}
v___jp_2654_:
{
lean_object* v___x_2655_; lean_object* v___x_2656_; lean_object* v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; uint8_t v___x_2660_; 
v___x_2655_ = lean_string_utf8_next_fast(v_str_2650_, v___x_2653_);
v___x_2656_ = lean_nat_sub(v___x_2655_, v___x_2653_);
lean_dec(v___x_2653_);
v___x_2657_ = lean_nat_add(v_pos_2649_, v___x_2656_);
lean_dec(v___x_2656_);
v___x_2658_ = lean_unsigned_to_nat(1u);
v___x_2659_ = lean_nat_add(v_pos_2649_, v___x_2658_);
v___x_2660_ = lean_nat_dec_le(v___x_2659_, v___x_2657_);
lean_dec(v___x_2659_);
if (v___x_2660_ == 0)
{
lean_dec(v___x_2657_);
return v_pos_2649_;
}
else
{
lean_dec(v_pos_2649_);
v_pos_2649_ = v___x_2657_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0___boxed(lean_object* v_s_2674_, lean_object* v_pos_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2674_, v_pos_2675_);
lean_dec_ref(v_s_2674_);
return v_res_2676_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(lean_object* v_s_2677_, lean_object* v_pos_2678_){
_start:
{
lean_object* v_str_2679_; lean_object* v_startInclusive_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; uint8_t v_decide_2684_; 
v_str_2679_ = lean_ctor_get(v_s_2677_, 0);
v_startInclusive_2680_ = lean_ctor_get(v_s_2677_, 1);
v___x_2681_ = lean_nat_add(v_startInclusive_2680_, v_pos_2678_);
v___x_2682_ = lean_nat_sub(v___x_2681_, v_startInclusive_2680_);
v___x_2683_ = lean_unsigned_to_nat(0u);
v_decide_2684_ = lean_nat_dec_eq(v___x_2682_, v___x_2683_);
if (v_decide_2684_ == 0)
{
lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2687_; lean_object* v___x_2688_; lean_object* v___x_2693_; uint32_t v___x_2694_; uint32_t v___x_2695_; uint8_t v___x_2696_; 
lean_inc(v_startInclusive_2680_);
lean_inc_ref(v_str_2679_);
v___x_2685_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2685_, 0, v_str_2679_);
lean_ctor_set(v___x_2685_, 1, v_startInclusive_2680_);
lean_ctor_set(v___x_2685_, 2, v___x_2681_);
v___x_2686_ = lean_unsigned_to_nat(1u);
v___x_2687_ = lean_nat_sub(v___x_2682_, v___x_2686_);
lean_dec(v___x_2682_);
v___x_2688_ = l_String_Slice_posLE(v___x_2685_, v___x_2687_);
lean_dec_ref_known(v___x_2685_, 3);
v___x_2693_ = lean_nat_add(v_startInclusive_2680_, v___x_2688_);
v___x_2694_ = lean_string_utf8_get_fast(v_str_2679_, v___x_2693_);
lean_dec(v___x_2693_);
v___x_2695_ = 32;
v___x_2696_ = lean_uint32_dec_eq(v___x_2694_, v___x_2695_);
if (v___x_2696_ == 0)
{
uint32_t v___x_2697_; uint8_t v___x_2698_; 
v___x_2697_ = 9;
v___x_2698_ = lean_uint32_dec_eq(v___x_2694_, v___x_2697_);
if (v___x_2698_ == 0)
{
uint32_t v___x_2699_; uint8_t v___x_2700_; 
v___x_2699_ = 13;
v___x_2700_ = lean_uint32_dec_eq(v___x_2694_, v___x_2699_);
if (v___x_2700_ == 0)
{
uint32_t v___x_2701_; uint8_t v___x_2702_; 
v___x_2701_ = 10;
v___x_2702_ = lean_uint32_dec_eq(v___x_2694_, v___x_2701_);
if (v___x_2702_ == 0)
{
lean_dec(v___x_2688_);
return v_pos_2678_;
}
else
{
goto v___jp_2689_;
}
}
else
{
goto v___jp_2689_;
}
}
else
{
goto v___jp_2689_;
}
}
else
{
goto v___jp_2689_;
}
v___jp_2689_:
{
lean_object* v___x_2690_; uint8_t v___x_2691_; 
v___x_2690_ = lean_nat_add(v___x_2688_, v___x_2686_);
v___x_2691_ = lean_nat_dec_le(v___x_2690_, v_pos_2678_);
lean_dec(v___x_2690_);
if (v___x_2691_ == 0)
{
lean_dec(v___x_2688_);
return v_pos_2678_;
}
else
{
lean_dec(v_pos_2678_);
v_pos_2678_ = v___x_2688_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2682_);
lean_dec(v___x_2681_);
return v_pos_2678_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1___boxed(lean_object* v_s_2703_, lean_object* v_pos_2704_){
_start:
{
lean_object* v_res_2705_; 
v_res_2705_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v_s_2703_, v_pos_2704_);
lean_dec_ref(v_s_2703_);
return v_res_2705_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAscii(lean_object* v_s_2706_){
_start:
{
lean_object* v_str_2707_; lean_object* v_startInclusive_2708_; lean_object* v_endExclusive_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2723_; 
v_str_2707_ = lean_ctor_get(v_s_2706_, 0);
lean_inc_ref(v_str_2707_);
v_startInclusive_2708_ = lean_ctor_get(v_s_2706_, 1);
lean_inc(v_startInclusive_2708_);
v_endExclusive_2709_ = lean_ctor_get(v_s_2706_, 2);
lean_inc(v_endExclusive_2709_);
v___x_2710_ = lean_unsigned_to_nat(0u);
v___x_2711_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2706_, v___x_2710_);
v_isSharedCheck_2723_ = !lean_is_exclusive(v_s_2706_);
if (v_isSharedCheck_2723_ == 0)
{
lean_object* v_unused_2724_; lean_object* v_unused_2725_; lean_object* v_unused_2726_; 
v_unused_2724_ = lean_ctor_get(v_s_2706_, 2);
lean_dec(v_unused_2724_);
v_unused_2725_ = lean_ctor_get(v_s_2706_, 1);
lean_dec(v_unused_2725_);
v_unused_2726_ = lean_ctor_get(v_s_2706_, 0);
lean_dec(v_unused_2726_);
v___x_2713_ = v_s_2706_;
v_isShared_2714_ = v_isSharedCheck_2723_;
goto v_resetjp_2712_;
}
else
{
lean_dec(v_s_2706_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2723_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2715_ = lean_nat_add(v_startInclusive_2708_, v___x_2711_);
lean_dec(v___x_2711_);
lean_dec(v_startInclusive_2708_);
lean_inc(v_endExclusive_2709_);
lean_inc(v___x_2715_);
lean_inc_ref(v_str_2707_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 1, v___x_2715_);
v___x_2717_ = v___x_2713_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2722_; 
v_reuseFailAlloc_2722_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2722_, 0, v_str_2707_);
lean_ctor_set(v_reuseFailAlloc_2722_, 1, v___x_2715_);
lean_ctor_set(v_reuseFailAlloc_2722_, 2, v_endExclusive_2709_);
v___x_2717_ = v_reuseFailAlloc_2722_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; lean_object* v___x_2721_; 
v___x_2718_ = lean_nat_sub(v_endExclusive_2709_, v___x_2715_);
lean_dec(v_endExclusive_2709_);
v___x_2719_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v___x_2717_, v___x_2718_);
lean_dec_ref(v___x_2717_);
v___x_2720_ = lean_nat_add(v___x_2715_, v___x_2719_);
lean_dec(v___x_2719_);
v___x_2721_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2721_, 0, v_str_2707_);
lean_ctor_set(v___x_2721_, 1, v___x_2715_);
lean_ctor_set(v___x_2721_, 2, v___x_2720_);
return v___x_2721_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines_lineMap(lean_object* v_s_2727_){
_start:
{
lean_object* v_str_2728_; lean_object* v_startInclusive_2729_; lean_object* v_endExclusive_2730_; lean_object* v___x_2731_; lean_object* v___x_2732_; uint8_t v_decide_2733_; 
v_str_2728_ = lean_ctor_get(v_s_2727_, 0);
v_startInclusive_2729_ = lean_ctor_get(v_s_2727_, 1);
v_endExclusive_2730_ = lean_ctor_get(v_s_2727_, 2);
v___x_2731_ = lean_nat_sub(v_endExclusive_2730_, v_startInclusive_2729_);
v___x_2732_ = lean_unsigned_to_nat(0u);
v_decide_2733_ = lean_nat_dec_eq(v___x_2731_, v___x_2732_);
if (v_decide_2733_ == 0)
{
uint32_t v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint32_t v___x_2739_; uint8_t v___x_2740_; 
v___x_2734_ = 10;
v___x_2735_ = lean_unsigned_to_nat(1u);
v___x_2736_ = lean_nat_sub(v___x_2731_, v___x_2735_);
lean_dec(v___x_2731_);
v___x_2737_ = l_String_Slice_posLE(v_s_2727_, v___x_2736_);
v___x_2738_ = lean_nat_add(v_startInclusive_2729_, v___x_2737_);
lean_dec(v___x_2737_);
v___x_2739_ = lean_string_utf8_get_fast(v_str_2728_, v___x_2738_);
v___x_2740_ = lean_uint32_dec_eq(v___x_2739_, v___x_2734_);
if (v___x_2740_ == 0)
{
lean_dec(v___x_2738_);
return v_s_2727_;
}
else
{
lean_object* v___x_2742_; uint8_t v_isShared_2743_; uint8_t v_isSharedCheck_2756_; 
lean_inc(v_startInclusive_2729_);
lean_inc_ref(v_str_2728_);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_s_2727_);
if (v_isSharedCheck_2756_ == 0)
{
lean_object* v_unused_2757_; lean_object* v_unused_2758_; lean_object* v_unused_2759_; 
v_unused_2757_ = lean_ctor_get(v_s_2727_, 2);
lean_dec(v_unused_2757_);
v_unused_2758_ = lean_ctor_get(v_s_2727_, 1);
lean_dec(v_unused_2758_);
v_unused_2759_ = lean_ctor_get(v_s_2727_, 0);
lean_dec(v_unused_2759_);
v___x_2742_ = v_s_2727_;
v_isShared_2743_ = v_isSharedCheck_2756_;
goto v_resetjp_2741_;
}
else
{
lean_dec(v_s_2727_);
v___x_2742_ = lean_box(0);
v_isShared_2743_ = v_isSharedCheck_2756_;
goto v_resetjp_2741_;
}
v_resetjp_2741_:
{
lean_object* v___x_2745_; 
lean_inc(v___x_2738_);
lean_inc(v_startInclusive_2729_);
lean_inc_ref(v_str_2728_);
if (v_isShared_2743_ == 0)
{
lean_ctor_set(v___x_2742_, 2, v___x_2738_);
v___x_2745_ = v___x_2742_;
goto v_reusejp_2744_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_str_2728_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_startInclusive_2729_);
lean_ctor_set(v_reuseFailAlloc_2755_, 2, v___x_2738_);
v___x_2745_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2744_;
}
v_reusejp_2744_:
{
lean_object* v___x_2746_; uint8_t v_decide_2747_; 
v___x_2746_ = lean_nat_sub(v___x_2738_, v_startInclusive_2729_);
lean_dec(v___x_2738_);
v_decide_2747_ = lean_nat_dec_eq(v___x_2746_, v___x_2732_);
if (v_decide_2747_ == 0)
{
uint32_t v___x_2748_; lean_object* v___x_2749_; lean_object* v___x_2750_; lean_object* v___x_2751_; uint32_t v___x_2752_; uint8_t v___x_2753_; 
v___x_2748_ = 13;
v___x_2749_ = lean_nat_sub(v___x_2746_, v___x_2735_);
lean_dec(v___x_2746_);
v___x_2750_ = l_String_Slice_posLE(v___x_2745_, v___x_2749_);
v___x_2751_ = lean_nat_add(v_startInclusive_2729_, v___x_2750_);
lean_dec(v___x_2750_);
v___x_2752_ = lean_string_utf8_get_fast(v_str_2728_, v___x_2751_);
v___x_2753_ = lean_uint32_dec_eq(v___x_2752_, v___x_2748_);
if (v___x_2753_ == 0)
{
lean_dec(v___x_2751_);
lean_dec(v_startInclusive_2729_);
lean_dec_ref(v_str_2728_);
return v___x_2745_;
}
else
{
lean_object* v___x_2754_; 
lean_dec_ref(v___x_2745_);
v___x_2754_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2754_, 0, v_str_2728_);
lean_ctor_set(v___x_2754_, 1, v_startInclusive_2729_);
lean_ctor_set(v___x_2754_, 2, v___x_2751_);
return v___x_2754_;
}
}
else
{
lean_dec(v___x_2746_);
lean_dec(v_startInclusive_2729_);
lean_dec_ref(v_str_2728_);
return v___x_2745_;
}
}
}
}
}
else
{
lean_dec(v___x_2731_);
return v_s_2727_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg(){
_start:
{
lean_object* v___x_2763_; 
v___x_2763_ = ((lean_object*)(l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___closed__0));
return v___x_2763_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___boxed(lean_object* v___dummy_2764_){
_start:
{
lean_object* v_res_2765_; 
v_res_2765_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
return v_res_2765_;
}
}
static lean_object* _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_2766_; 
v___x_2766_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
return v___x_2766_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(lean_object* v_s_2767_){
_start:
{
lean_object* v___x_2768_; 
v___x_2768_ = lean_obj_once(&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0, &l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_once, _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0);
return v___x_2768_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(lean_object* v_s_2769_){
_start:
{
lean_object* v_res_2770_; 
v_res_2770_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_2769_);
lean_dec_ref(v_s_2769_);
return v_res_2770_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines(lean_object* v_s_2771_){
_start:
{
lean_object* v___x_2772_; 
v___x_2772_ = lean_obj_once(&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0, &l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_once, _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0);
return v___x_2772_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines___boxed(lean_object* v_s_2773_){
_start:
{
lean_object* v_res_2774_; 
v_res_2774_ = l_String_Slice_lines(v_s_2773_);
lean_dec_ref(v_s_2773_);
return v_res_2774_;
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
