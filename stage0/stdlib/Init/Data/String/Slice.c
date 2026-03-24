// Lean compiler output
// Module: Init.Data.String.Slice
// Imports: public import Init.Data.String.Pattern public import Init.Data.Ord.Basic public import Init.Data.Iterators.Combinators.FilterMap public import Init.Data.String.ToSlice public import Init.Data.String.Subslice public import Init.Data.String.Iter.Basic public import Init.Data.String.Iterate import Init.Data.Iterators.Consumers.Collect import Init.Data.Iterators.Consumers.Loop import Init.Data.Option.Lemmas import Init.Data.String.Termination import Init.Omega
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
lean_object* lean_string_utf8_extract(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw___aux__1(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(lean_object*);
extern lean_object* l_Int_instInhabited;
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instHAppend___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_instHAppend___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instHAppend___closed__0 = (const lean_object*)&l_String_Slice_instHAppend___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instHAppend = (const lean_object*)&l_String_Slice_instHAppend___closed__0_value;
LEAN_EXPORT uint8_t l_String_Slice_beq(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_beq___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instBEq___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_beq___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instBEq___closed__0 = (const lean_object*)&l_String_Slice_instBEq___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instBEq = (const lean_object*)&l_String_Slice_instBEq___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_toString(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toString___boxed(lean_object*);
static const lean_closure_object l_String_Slice_instToString___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_toString___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instToString___closed__0 = (const lean_object*)&l_String_Slice_instToString___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instToString = (const lean_object*)&l_String_Slice_instToString___closed__0_value;
uint64_t lean_slice_hash(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_hash___boxed(lean_object*);
static const lean_closure_object l_String_Slice_instHashable___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_hash___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instHashable___closed__0 = (const lean_object*)&l_String_Slice_instHashable___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instHashable = (const lean_object*)&l_String_Slice_instHashable___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_instLT;
uint8_t lean_slice_dec_lt(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLt___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_instOrd___lam__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instOrd___lam__0___boxed(lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_instOrd___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_instOrd___lam__0___boxed, .m_arity = 2, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instOrd___closed__0 = (const lean_object*)&l_String_Slice_instOrd___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instOrd = (const lean_object*)&l_String_Slice_instOrd___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_instLE;
LEAN_EXPORT uint8_t l_String_Slice_instDecidableLE(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLE___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_startsWith___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_startsWith___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_startsWith(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_startsWith___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx(uint8_t);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___redArg(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___boxed(lean_object**);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_revSkipWhile_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_revSkipWhile_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_revSkipWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_String_Slice_trimAsciiEnd___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_trimAsciiEnd___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object*, lean_object*);
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
LEAN_EXPORT uint8_t l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_lines_lineMap(lean_object*);
static const lean_ctor_object l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0 = (const lean_object*)&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_lines(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_lines___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_isNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_isNat___closed__0 = (const lean_object*)&l_String_Slice_isNat___closed__0_value;
LEAN_EXPORT uint8_t l_String_Slice_isNat(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_toNat_x21_spec__0(lean_object*);
static const lean_string_object l_String_Slice_toNat_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 23, .m_capacity = 23, .m_length = 22, .m_data = "Init.Data.String.Slice"};
static const lean_object* l_String_Slice_toNat_x21___closed__0 = (const lean_object*)&l_String_Slice_toNat_x21___closed__0_value;
static const lean_string_object l_String_Slice_toNat_x21___closed__1_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 20, .m_capacity = 20, .m_length = 19, .m_data = "String.Slice.toNat!"};
static const lean_object* l_String_Slice_toNat_x21___closed__1 = (const lean_object*)&l_String_Slice_toNat_x21___closed__1_value;
static const lean_string_object l_String_Slice_toNat_x21___closed__2_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Nat expected"};
static const lean_object* l_String_Slice_toNat_x21___closed__2 = (const lean_object*)&l_String_Slice_toNat_x21___closed__2_value;
static lean_once_cell_t l_String_Slice_toNat_x21___closed__3_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_toNat_x21___closed__3;
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_front(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_isInt(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toInt_x3f(lean_object*);
static const lean_string_object l_String_Slice_toInt_x21___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = 0, .m_other = 0, .m_tag = 249}, .m_size = 13, .m_capacity = 13, .m_length = 12, .m_data = "Int expected"};
static const lean_object* l_String_Slice_toInt_x21___closed__0 = (const lean_object*)&l_String_Slice_toInt_x21___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_toInt_x21(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object*);
LEAN_EXPORT uint32_t l_String_Slice_back(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_join(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_join___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object*);
static const lean_closure_object l_String_Slice_instToFormat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_String_Slice_instToFormat___lam__0___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_instToFormat___closed__0 = (const lean_object*)&l_String_Slice_instToFormat___closed__0_value;
LEAN_EXPORT const lean_object* l_String_Slice_instToFormat = (const lean_object*)&l_String_Slice_instToFormat___closed__0_value;
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0(lean_object* v_s_1_, lean_object* v_t_2_){
_start:
{
lean_object* v_str_3_; lean_object* v_startInclusive_4_; lean_object* v_endExclusive_5_; lean_object* v___x_6_; lean_object* v___x_7_; 
v_str_3_ = lean_ctor_get(v_t_2_, 0);
v_startInclusive_4_ = lean_ctor_get(v_t_2_, 1);
v_endExclusive_5_ = lean_ctor_get(v_t_2_, 2);
v___x_6_ = lean_string_utf8_extract(v_str_3_, v_startInclusive_4_, v_endExclusive_5_);
v___x_7_ = lean_string_append(v_s_1_, v___x_6_);
lean_dec_ref(v___x_6_);
return v___x_7_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instHAppend___lam__0___boxed(lean_object* v_s_8_, lean_object* v_t_9_){
_start:
{
lean_object* v_res_10_; 
v_res_10_ = l_String_Slice_instHAppend___lam__0(v_s_8_, v_t_9_);
lean_dec_ref(v_t_9_);
return v_res_10_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_beq(lean_object* v_s1_13_, lean_object* v_s2_14_){
_start:
{
lean_object* v_str_15_; lean_object* v_startInclusive_16_; lean_object* v_endExclusive_17_; lean_object* v_str_18_; lean_object* v_startInclusive_19_; lean_object* v_endExclusive_20_; lean_object* v___x_21_; lean_object* v___x_22_; uint8_t v___x_23_; 
v_str_15_ = lean_ctor_get(v_s1_13_, 0);
v_startInclusive_16_ = lean_ctor_get(v_s1_13_, 1);
v_endExclusive_17_ = lean_ctor_get(v_s1_13_, 2);
v_str_18_ = lean_ctor_get(v_s2_14_, 0);
v_startInclusive_19_ = lean_ctor_get(v_s2_14_, 1);
v_endExclusive_20_ = lean_ctor_get(v_s2_14_, 2);
v___x_21_ = lean_nat_sub(v_endExclusive_17_, v_startInclusive_16_);
v___x_22_ = lean_nat_sub(v_endExclusive_20_, v_startInclusive_19_);
v___x_23_ = lean_nat_dec_eq(v___x_21_, v___x_22_);
lean_dec(v___x_22_);
if (v___x_23_ == 0)
{
lean_dec(v___x_21_);
return v___x_23_;
}
else
{
uint8_t v___x_24_; 
v___x_24_ = lean_string_memcmp(v_str_15_, v_str_18_, v_startInclusive_16_, v_startInclusive_19_, v___x_21_);
lean_dec(v___x_21_);
return v___x_24_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_beq___boxed(lean_object* v_s1_25_, lean_object* v_s2_26_){
_start:
{
uint8_t v_res_27_; lean_object* v_r_28_; 
v_res_27_ = l_String_Slice_beq(v_s1_25_, v_s2_26_);
lean_dec_ref(v_s2_26_);
lean_dec_ref(v_s1_25_);
v_r_28_ = lean_box(v_res_27_);
return v_r_28_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toString(lean_object* v_s_31_){
_start:
{
lean_object* v_str_32_; lean_object* v_startInclusive_33_; lean_object* v_endExclusive_34_; lean_object* v___x_35_; 
v_str_32_ = lean_ctor_get(v_s_31_, 0);
v_startInclusive_33_ = lean_ctor_get(v_s_31_, 1);
v_endExclusive_34_ = lean_ctor_get(v_s_31_, 2);
v___x_35_ = lean_string_utf8_extract(v_str_32_, v_startInclusive_33_, v_endExclusive_34_);
return v___x_35_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toString___boxed(lean_object* v_s_36_){
_start:
{
lean_object* v_res_37_; 
v_res_37_ = l_String_Slice_toString(v_s_36_);
lean_dec_ref(v_s_36_);
return v_res_37_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_hash___boxed(lean_object* v_s_41_){
_start:
{
uint64_t v_res_42_; lean_object* v_r_43_; 
v_res_42_ = lean_slice_hash(v_s_41_);
lean_dec_ref(v_s_41_);
v_r_43_ = lean_box_uint64(v_res_42_);
return v_r_43_;
}
}
static lean_object* _init_l_String_Slice_instLT(void){
_start:
{
lean_object* v___x_46_; 
v___x_46_ = lean_box(0);
return v___x_46_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLt___boxed(lean_object* v_x_49_, lean_object* v_y_50_){
_start:
{
uint8_t v_res_51_; lean_object* v_r_52_; 
v_res_51_ = lean_slice_dec_lt(v_x_49_, v_y_50_);
lean_dec_ref(v_y_50_);
lean_dec_ref(v_x_49_);
v_r_52_ = lean_box(v_res_51_);
return v_r_52_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instOrd___lam__0(lean_object* v_x_53_, lean_object* v_y_54_){
_start:
{
uint8_t v___x_55_; 
v___x_55_ = lean_slice_dec_lt(v_x_53_, v_y_54_);
if (v___x_55_ == 0)
{
uint8_t v___x_56_; 
v___x_56_ = l_String_Slice_beq(v_x_53_, v_y_54_);
if (v___x_56_ == 0)
{
uint8_t v___x_57_; 
v___x_57_ = 2;
return v___x_57_;
}
else
{
uint8_t v___x_58_; 
v___x_58_ = 1;
return v___x_58_;
}
}
else
{
uint8_t v___x_59_; 
v___x_59_ = 0;
return v___x_59_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_instOrd___lam__0___boxed(lean_object* v_x_60_, lean_object* v_y_61_){
_start:
{
uint8_t v_res_62_; lean_object* v_r_63_; 
v_res_62_ = l_String_Slice_instOrd___lam__0(v_x_60_, v_y_61_);
lean_dec_ref(v_y_61_);
lean_dec_ref(v_x_60_);
v_r_63_ = lean_box(v_res_62_);
return v_r_63_;
}
}
static lean_object* _init_l_String_Slice_instLE(void){
_start:
{
lean_object* v___x_66_; 
v___x_66_ = lean_box(0);
return v___x_66_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_instDecidableLE(lean_object* v_x_67_, lean_object* v_y_68_){
_start:
{
uint8_t v___x_69_; 
v___x_69_ = lean_slice_dec_lt(v_x_67_, v_y_68_);
if (v___x_69_ == 0)
{
uint8_t v___x_70_; 
v___x_70_ = 1;
return v___x_70_;
}
else
{
uint8_t v___x_71_; 
v___x_71_ = 0;
return v___x_71_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLE___boxed(lean_object* v_x_72_, lean_object* v_y_73_){
_start:
{
uint8_t v_res_74_; lean_object* v_r_75_; 
v_res_74_ = l_String_Slice_instDecidableLE(v_x_72_, v_y_73_);
lean_dec_ref(v_y_73_);
lean_dec_ref(v_x_72_);
v_r_75_ = lean_box(v_res_74_);
return v_r_75_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_startsWith___redArg(lean_object* v_s_76_, lean_object* v_inst_77_){
_start:
{
lean_object* v_startsWith_78_; lean_object* v___x_79_; uint8_t v___x_80_; 
v_startsWith_78_ = lean_ctor_get(v_inst_77_, 2);
lean_inc_ref(v_startsWith_78_);
lean_dec_ref(v_inst_77_);
v___x_79_ = lean_apply_1(v_startsWith_78_, v_s_76_);
v___x_80_ = lean_unbox(v___x_79_);
return v___x_80_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startsWith___redArg___boxed(lean_object* v_s_81_, lean_object* v_inst_82_){
_start:
{
uint8_t v_res_83_; lean_object* v_r_84_; 
v_res_83_ = l_String_Slice_startsWith___redArg(v_s_81_, v_inst_82_);
v_r_84_ = lean_box(v_res_83_);
return v_r_84_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_startsWith(lean_object* v_00_u03c1_85_, lean_object* v_s_86_, lean_object* v_pat_87_, lean_object* v_inst_88_){
_start:
{
lean_object* v_startsWith_89_; lean_object* v___x_90_; uint8_t v___x_91_; 
v_startsWith_89_ = lean_ctor_get(v_inst_88_, 2);
lean_inc_ref(v_startsWith_89_);
lean_dec_ref(v_inst_88_);
v___x_90_ = lean_apply_1(v_startsWith_89_, v_s_86_);
v___x_91_ = lean_unbox(v___x_90_);
return v___x_91_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_startsWith___boxed(lean_object* v_00_u03c1_92_, lean_object* v_s_93_, lean_object* v_pat_94_, lean_object* v_inst_95_){
_start:
{
uint8_t v_res_96_; lean_object* v_r_97_; 
v_res_96_ = l_String_Slice_startsWith(v_00_u03c1_92_, v_s_93_, v_pat_94_, v_inst_95_);
lean_dec(v_pat_94_);
v_r_97_ = lean_box(v_res_96_);
return v_r_97_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___redArg(lean_object* v_x_98_){
_start:
{
if (lean_obj_tag(v_x_98_) == 0)
{
lean_object* v___x_99_; 
v___x_99_ = lean_unsigned_to_nat(0u);
return v___x_99_;
}
else
{
lean_object* v___x_100_; 
v___x_100_ = lean_unsigned_to_nat(1u);
return v___x_100_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___redArg___boxed(lean_object* v_x_101_){
_start:
{
lean_object* v_res_102_; 
v_res_102_ = l_String_Slice_SplitIterator_ctorIdx___redArg(v_x_101_);
lean_dec(v_x_101_);
return v_res_102_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx(lean_object* v_00_u03c3_103_, lean_object* v_00_u03c1_104_, lean_object* v_pat_105_, lean_object* v_s_106_, lean_object* v_inst_107_, lean_object* v_x_108_){
_start:
{
lean_object* v___x_109_; 
v___x_109_ = l_String_Slice_SplitIterator_ctorIdx___redArg(v_x_108_);
return v___x_109_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___boxed(lean_object* v_00_u03c3_110_, lean_object* v_00_u03c1_111_, lean_object* v_pat_112_, lean_object* v_s_113_, lean_object* v_inst_114_, lean_object* v_x_115_){
_start:
{
lean_object* v_res_116_; 
v_res_116_ = l_String_Slice_SplitIterator_ctorIdx(v_00_u03c3_110_, v_00_u03c1_111_, v_pat_112_, v_s_113_, v_inst_114_, v_x_115_);
lean_dec(v_x_115_);
lean_dec(v_inst_114_);
lean_dec_ref(v_s_113_);
lean_dec(v_pat_112_);
return v_res_116_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___redArg(lean_object* v_t_117_, lean_object* v_k_118_){
_start:
{
if (lean_obj_tag(v_t_117_) == 0)
{
lean_object* v_currPos_119_; lean_object* v_searcher_120_; lean_object* v___x_121_; 
v_currPos_119_ = lean_ctor_get(v_t_117_, 0);
lean_inc(v_currPos_119_);
v_searcher_120_ = lean_ctor_get(v_t_117_, 1);
lean_inc(v_searcher_120_);
lean_dec_ref(v_t_117_);
v___x_121_ = lean_apply_2(v_k_118_, v_currPos_119_, v_searcher_120_);
return v___x_121_;
}
else
{
return v_k_118_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim(lean_object* v_00_u03c3_122_, lean_object* v_00_u03c1_123_, lean_object* v_pat_124_, lean_object* v_s_125_, lean_object* v_inst_126_, lean_object* v_motive_127_, lean_object* v_ctorIdx_128_, lean_object* v_t_129_, lean_object* v_h_130_, lean_object* v_k_131_){
_start:
{
lean_object* v___x_132_; 
v___x_132_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_129_, v_k_131_);
return v___x_132_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_133_, lean_object* v_00_u03c1_134_, lean_object* v_pat_135_, lean_object* v_s_136_, lean_object* v_inst_137_, lean_object* v_motive_138_, lean_object* v_ctorIdx_139_, lean_object* v_t_140_, lean_object* v_h_141_, lean_object* v_k_142_){
_start:
{
lean_object* v_res_143_; 
v_res_143_ = l_String_Slice_SplitIterator_ctorElim(v_00_u03c3_133_, v_00_u03c1_134_, v_pat_135_, v_s_136_, v_inst_137_, v_motive_138_, v_ctorIdx_139_, v_t_140_, v_h_141_, v_k_142_);
lean_dec(v_ctorIdx_139_);
lean_dec(v_inst_137_);
lean_dec_ref(v_s_136_);
lean_dec(v_pat_135_);
return v_res_143_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___redArg(lean_object* v_t_144_, lean_object* v_operating_145_){
_start:
{
lean_object* v___x_146_; 
v___x_146_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_144_, v_operating_145_);
return v___x_146_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim(lean_object* v_00_u03c3_147_, lean_object* v_00_u03c1_148_, lean_object* v_pat_149_, lean_object* v_s_150_, lean_object* v_inst_151_, lean_object* v_motive_152_, lean_object* v_t_153_, lean_object* v_h_154_, lean_object* v_operating_155_){
_start:
{
lean_object* v___x_156_; 
v___x_156_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_153_, v_operating_155_);
return v___x_156_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_157_, lean_object* v_00_u03c1_158_, lean_object* v_pat_159_, lean_object* v_s_160_, lean_object* v_inst_161_, lean_object* v_motive_162_, lean_object* v_t_163_, lean_object* v_h_164_, lean_object* v_operating_165_){
_start:
{
lean_object* v_res_166_; 
v_res_166_ = l_String_Slice_SplitIterator_operating_elim(v_00_u03c3_157_, v_00_u03c1_158_, v_pat_159_, v_s_160_, v_inst_161_, v_motive_162_, v_t_163_, v_h_164_, v_operating_165_);
lean_dec(v_inst_161_);
lean_dec_ref(v_s_160_);
lean_dec(v_pat_159_);
return v_res_166_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___redArg(lean_object* v_t_167_, lean_object* v_atEnd_168_){
_start:
{
lean_object* v___x_169_; 
v___x_169_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_167_, v_atEnd_168_);
return v___x_169_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim(lean_object* v_00_u03c3_170_, lean_object* v_00_u03c1_171_, lean_object* v_pat_172_, lean_object* v_s_173_, lean_object* v_inst_174_, lean_object* v_motive_175_, lean_object* v_t_176_, lean_object* v_h_177_, lean_object* v_atEnd_178_){
_start:
{
lean_object* v___x_179_; 
v___x_179_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_176_, v_atEnd_178_);
return v___x_179_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_180_, lean_object* v_00_u03c1_181_, lean_object* v_pat_182_, lean_object* v_s_183_, lean_object* v_inst_184_, lean_object* v_motive_185_, lean_object* v_t_186_, lean_object* v_h_187_, lean_object* v_atEnd_188_){
_start:
{
lean_object* v_res_189_; 
v_res_189_ = l_String_Slice_SplitIterator_atEnd_elim(v_00_u03c3_180_, v_00_u03c1_181_, v_pat_182_, v_s_183_, v_inst_184_, v_motive_185_, v_t_186_, v_h_187_, v_atEnd_188_);
lean_dec(v_inst_184_);
lean_dec_ref(v_s_183_);
lean_dec(v_pat_182_);
return v_res_189_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default(lean_object* v_a_190_, lean_object* v_a_191_, lean_object* v_a_192_, lean_object* v_a_193_, lean_object* v_a_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(1);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___boxed(lean_object* v_a_196_, lean_object* v_a_197_, lean_object* v_a_198_, lean_object* v_a_199_, lean_object* v_a_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_String_Slice_instInhabitedSplitIterator_default(v_a_196_, v_a_197_, v_a_198_, v_a_199_, v_a_200_);
lean_dec(v_a_200_);
lean_dec_ref(v_a_199_);
lean_dec(v_a_198_);
return v_res_201_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator(lean_object* v_a_202_, lean_object* v_a_203_, lean_object* v_a_204_, lean_object* v_a_205_, lean_object* v_a_206_){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(1);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___boxed(lean_object* v_a_208_, lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_){
_start:
{
lean_object* v_res_213_; 
v_res_213_ = l_String_Slice_instInhabitedSplitIterator(v_a_208_, v_a_209_, v_a_210_, v_a_211_, v_a_212_);
lean_dec(v_a_212_);
lean_dec_ref(v_a_211_);
lean_dec(v_a_210_);
return v_res_213_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx(uint8_t v_x_214_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___boxed(lean_object* v_x_215_){
_start:
{
uint8_t v_x_boxed_216_; lean_object* v_res_217_; 
v_x_boxed_216_ = lean_unbox(v_x_215_);
v_res_217_ = l_String_Slice_SplitIterator_PlausibleStep_ctorIdx(v_x_boxed_216_);
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0(lean_object* v_inst_218_, lean_object* v_s_219_, lean_object* v_x_220_){
_start:
{
if (lean_obj_tag(v_x_220_) == 0)
{
lean_object* v_currPos_221_; lean_object* v_searcher_222_; lean_object* v___x_224_; uint8_t v_isShared_225_; uint8_t v_isSharedCheck_265_; 
v_currPos_221_ = lean_ctor_get(v_x_220_, 0);
v_searcher_222_ = lean_ctor_get(v_x_220_, 1);
v_isSharedCheck_265_ = !lean_is_exclusive(v_x_220_);
if (v_isSharedCheck_265_ == 0)
{
v___x_224_ = v_x_220_;
v_isShared_225_ = v_isSharedCheck_265_;
goto v_resetjp_223_;
}
else
{
lean_inc(v_searcher_222_);
lean_inc(v_currPos_221_);
lean_dec(v_x_220_);
v___x_224_ = lean_box(0);
v_isShared_225_ = v_isSharedCheck_265_;
goto v_resetjp_223_;
}
v_resetjp_223_:
{
lean_object* v___x_226_; 
lean_inc_ref(v_s_219_);
v___x_226_ = lean_apply_2(v_inst_218_, v_s_219_, v_searcher_222_);
switch(lean_obj_tag(v___x_226_))
{
case 0:
{
lean_object* v_out_227_; 
v_out_227_ = lean_ctor_get(v___x_226_, 1);
lean_inc(v_out_227_);
if (lean_obj_tag(v_out_227_) == 0)
{
lean_object* v_it_228_; lean_object* v___x_230_; 
lean_dec_ref(v_out_227_);
lean_dec_ref(v_s_219_);
v_it_228_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_it_228_);
lean_dec_ref(v___x_226_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_it_228_);
v___x_230_ = v___x_224_;
goto v_reusejp_229_;
}
else
{
lean_object* v_reuseFailAlloc_232_; 
v_reuseFailAlloc_232_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_232_, 0, v_currPos_221_);
lean_ctor_set(v_reuseFailAlloc_232_, 1, v_it_228_);
v___x_230_ = v_reuseFailAlloc_232_;
goto v_reusejp_229_;
}
v_reusejp_229_:
{
lean_object* v___x_231_; 
v___x_231_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_231_, 0, v___x_230_);
return v___x_231_;
}
}
else
{
lean_object* v_it_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_246_; 
v_it_233_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_246_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_246_ == 0)
{
lean_object* v_unused_247_; 
v_unused_247_ = lean_ctor_get(v___x_226_, 1);
lean_dec(v_unused_247_);
v___x_235_ = v___x_226_;
v_isShared_236_ = v_isSharedCheck_246_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_it_233_);
lean_dec(v___x_226_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_246_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v_startPos_237_; lean_object* v_endPos_238_; lean_object* v_slice_239_; lean_object* v_nextIt_241_; 
v_startPos_237_ = lean_ctor_get(v_out_227_, 0);
lean_inc(v_startPos_237_);
v_endPos_238_ = lean_ctor_get(v_out_227_, 1);
lean_inc(v_endPos_238_);
lean_dec_ref(v_out_227_);
v_slice_239_ = l_String_Slice_subslice_x21(v_s_219_, v_currPos_221_, v_startPos_237_);
lean_dec_ref(v_s_219_);
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_it_233_);
lean_ctor_set(v___x_224_, 0, v_endPos_238_);
v_nextIt_241_ = v___x_224_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_245_; 
v_reuseFailAlloc_245_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_245_, 0, v_endPos_238_);
lean_ctor_set(v_reuseFailAlloc_245_, 1, v_it_233_);
v_nextIt_241_ = v_reuseFailAlloc_245_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_243_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_slice_239_);
lean_ctor_set(v___x_235_, 0, v_nextIt_241_);
v___x_243_ = v___x_235_;
goto v_reusejp_242_;
}
else
{
lean_object* v_reuseFailAlloc_244_; 
v_reuseFailAlloc_244_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_244_, 0, v_nextIt_241_);
lean_ctor_set(v_reuseFailAlloc_244_, 1, v_slice_239_);
v___x_243_ = v_reuseFailAlloc_244_;
goto v_reusejp_242_;
}
v_reusejp_242_:
{
return v___x_243_;
}
}
}
}
}
case 1:
{
lean_object* v_it_248_; lean_object* v___x_250_; uint8_t v_isShared_251_; uint8_t v_isSharedCheck_258_; 
lean_dec_ref(v_s_219_);
v_it_248_ = lean_ctor_get(v___x_226_, 0);
v_isSharedCheck_258_ = !lean_is_exclusive(v___x_226_);
if (v_isSharedCheck_258_ == 0)
{
v___x_250_ = v___x_226_;
v_isShared_251_ = v_isSharedCheck_258_;
goto v_resetjp_249_;
}
else
{
lean_inc(v_it_248_);
lean_dec(v___x_226_);
v___x_250_ = lean_box(0);
v_isShared_251_ = v_isSharedCheck_258_;
goto v_resetjp_249_;
}
v_resetjp_249_:
{
lean_object* v___x_253_; 
if (v_isShared_225_ == 0)
{
lean_ctor_set(v___x_224_, 1, v_it_248_);
v___x_253_ = v___x_224_;
goto v_reusejp_252_;
}
else
{
lean_object* v_reuseFailAlloc_257_; 
v_reuseFailAlloc_257_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_257_, 0, v_currPos_221_);
lean_ctor_set(v_reuseFailAlloc_257_, 1, v_it_248_);
v___x_253_ = v_reuseFailAlloc_257_;
goto v_reusejp_252_;
}
v_reusejp_252_:
{
lean_object* v___x_255_; 
if (v_isShared_251_ == 0)
{
lean_ctor_set(v___x_250_, 0, v___x_253_);
v___x_255_ = v___x_250_;
goto v_reusejp_254_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v___x_253_);
v___x_255_ = v_reuseFailAlloc_256_;
goto v_reusejp_254_;
}
v_reusejp_254_:
{
return v___x_255_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_259_; lean_object* v_endExclusive_260_; lean_object* v___x_261_; lean_object* v_slice_262_; lean_object* v___x_263_; lean_object* v___x_264_; 
lean_del_object(v___x_224_);
v_startInclusive_259_ = lean_ctor_get(v_s_219_, 1);
lean_inc(v_startInclusive_259_);
v_endExclusive_260_ = lean_ctor_get(v_s_219_, 2);
lean_inc(v_endExclusive_260_);
lean_dec_ref(v_s_219_);
v___x_261_ = lean_nat_sub(v_endExclusive_260_, v_startInclusive_259_);
lean_dec(v_startInclusive_259_);
lean_dec(v_endExclusive_260_);
v_slice_262_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_262_, 0, v_currPos_221_);
lean_ctor_set(v_slice_262_, 1, v___x_261_);
v___x_263_ = lean_box(1);
v___x_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_264_, 0, v___x_263_);
lean_ctor_set(v___x_264_, 1, v_slice_262_);
return v___x_264_;
}
}
}
}
else
{
lean_object* v___x_266_; 
lean_dec_ref(v_s_219_);
lean_dec(v_inst_218_);
v___x_266_ = lean_box(2);
return v___x_266_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg(lean_object* v_inst_267_, lean_object* v_s_268_){
_start:
{
lean_object* v___f_269_; 
v___f_269_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0), 3, 2);
lean_closure_set(v___f_269_, 0, v_inst_267_);
lean_closure_set(v___f_269_, 1, v_s_268_);
return v___f_269_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice(lean_object* v_00_u03c1_270_, lean_object* v_00_u03c3_271_, lean_object* v_inst_272_, lean_object* v_pat_273_, lean_object* v_inst_274_, lean_object* v_s_275_){
_start:
{
lean_object* v___f_276_; 
v___f_276_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0), 3, 2);
lean_closure_set(v___f_276_, 0, v_inst_272_);
lean_closure_set(v___f_276_, 1, v_s_275_);
return v___f_276_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___boxed(lean_object* v_00_u03c1_277_, lean_object* v_00_u03c3_278_, lean_object* v_inst_279_, lean_object* v_pat_280_, lean_object* v_inst_281_, lean_object* v_s_282_){
_start:
{
lean_object* v_res_283_; 
v_res_283_ = l_String_Slice_SplitIterator_instIteratorIdSubslice(v_00_u03c1_277_, v_00_u03c3_278_, v_inst_279_, v_pat_280_, v_inst_281_, v_s_282_);
lean_dec(v_inst_281_);
lean_dec(v_pat_280_);
return v_res_283_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(lean_object* v_x_284_){
_start:
{
if (lean_obj_tag(v_x_284_) == 0)
{
lean_object* v_searcher_285_; lean_object* v___x_286_; 
v_searcher_285_ = lean_ctor_get(v_x_284_, 1);
lean_inc(v_searcher_285_);
v___x_286_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_286_, 0, v_searcher_285_);
return v___x_286_;
}
else
{
lean_object* v___x_287_; 
v___x_287_ = lean_box(0);
return v___x_287_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg___boxed(lean_object* v_x_288_){
_start:
{
lean_object* v_res_289_; 
v_res_289_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(v_x_288_);
lean_dec(v_x_288_);
return v_res_289_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption(lean_object* v_00_u03c1_290_, lean_object* v_00_u03c3_291_, lean_object* v_pat_292_, lean_object* v_inst_293_, lean_object* v_s_294_, lean_object* v_x_295_){
_start:
{
lean_object* v___x_296_; 
v___x_296_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(v_x_295_);
return v___x_296_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___boxed(lean_object* v_00_u03c1_297_, lean_object* v_00_u03c3_298_, lean_object* v_pat_299_, lean_object* v_inst_300_, lean_object* v_s_301_, lean_object* v_x_302_){
_start:
{
lean_object* v_res_303_; 
v_res_303_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption(v_00_u03c1_297_, v_00_u03c3_298_, v_pat_299_, v_inst_300_, v_s_301_, v_x_302_);
lean_dec(v_x_302_);
lean_dec_ref(v_s_301_);
lean_dec(v_inst_300_);
lean_dec(v_pat_299_);
return v_res_303_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___redArg(lean_object* v_x_304_, lean_object* v_h__1_305_, lean_object* v_h__2_306_){
_start:
{
if (lean_obj_tag(v_x_304_) == 0)
{
lean_object* v_currPos_307_; lean_object* v_searcher_308_; lean_object* v___x_309_; 
lean_dec(v_h__2_306_);
v_currPos_307_ = lean_ctor_get(v_x_304_, 0);
lean_inc(v_currPos_307_);
v_searcher_308_ = lean_ctor_get(v_x_304_, 1);
lean_inc(v_searcher_308_);
lean_dec_ref(v_x_304_);
v___x_309_ = lean_apply_2(v_h__1_305_, v_currPos_307_, v_searcher_308_);
return v___x_309_;
}
else
{
lean_object* v___x_310_; lean_object* v___x_311_; 
lean_dec(v_h__1_305_);
v___x_310_ = lean_box(0);
v___x_311_ = lean_apply_1(v_h__2_306_, v___x_310_);
return v___x_311_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(lean_object* v_00_u03c1_312_, lean_object* v_00_u03c3_313_, lean_object* v_pat_314_, lean_object* v_inst_315_, lean_object* v_s_316_, lean_object* v_motive_317_, lean_object* v_x_318_, lean_object* v_h__1_319_, lean_object* v_h__2_320_){
_start:
{
if (lean_obj_tag(v_x_318_) == 0)
{
lean_object* v_currPos_321_; lean_object* v_searcher_322_; lean_object* v___x_323_; 
lean_dec(v_h__2_320_);
v_currPos_321_ = lean_ctor_get(v_x_318_, 0);
lean_inc(v_currPos_321_);
v_searcher_322_ = lean_ctor_get(v_x_318_, 1);
lean_inc(v_searcher_322_);
lean_dec_ref(v_x_318_);
v___x_323_ = lean_apply_2(v_h__1_319_, v_currPos_321_, v_searcher_322_);
return v___x_323_;
}
else
{
lean_object* v___x_324_; lean_object* v___x_325_; 
lean_dec(v_h__1_319_);
v___x_324_ = lean_box(0);
v___x_325_ = lean_apply_1(v_h__2_320_, v___x_324_);
return v___x_325_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___boxed(lean_object* v_00_u03c1_326_, lean_object* v_00_u03c3_327_, lean_object* v_pat_328_, lean_object* v_inst_329_, lean_object* v_s_330_, lean_object* v_motive_331_, lean_object* v_x_332_, lean_object* v_h__1_333_, lean_object* v_h__2_334_){
_start:
{
lean_object* v_res_335_; 
v_res_335_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(v_00_u03c1_326_, v_00_u03c3_327_, v_pat_328_, v_inst_329_, v_s_330_, v_motive_331_, v_x_332_, v_h__1_333_, v_h__2_334_);
lean_dec_ref(v_s_330_);
lean_dec(v_inst_329_);
lean_dec(v_pat_328_);
return v_res_335_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object* v_x_336_, lean_object* v_h__1_337_, lean_object* v_h__2_338_, lean_object* v_h__3_339_, lean_object* v_h__4_340_){
_start:
{
switch(lean_obj_tag(v_x_336_))
{
case 0:
{
lean_object* v_out_341_; 
lean_dec(v_h__4_340_);
lean_dec(v_h__3_339_);
v_out_341_ = lean_ctor_get(v_x_336_, 1);
lean_inc(v_out_341_);
if (lean_obj_tag(v_out_341_) == 0)
{
lean_object* v_it_342_; lean_object* v_startPos_343_; lean_object* v_endPos_344_; lean_object* v___x_345_; 
lean_dec(v_h__1_337_);
v_it_342_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_it_342_);
lean_dec_ref(v_x_336_);
v_startPos_343_ = lean_ctor_get(v_out_341_, 0);
lean_inc(v_startPos_343_);
v_endPos_344_ = lean_ctor_get(v_out_341_, 1);
lean_inc(v_endPos_344_);
lean_dec_ref(v_out_341_);
v___x_345_ = lean_apply_5(v_h__2_338_, v_it_342_, v_startPos_343_, v_endPos_344_, lean_box(0), lean_box(0));
return v___x_345_;
}
else
{
lean_object* v_it_346_; lean_object* v_startPos_347_; lean_object* v_endPos_348_; lean_object* v___x_349_; 
lean_dec(v_h__2_338_);
v_it_346_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_it_346_);
lean_dec_ref(v_x_336_);
v_startPos_347_ = lean_ctor_get(v_out_341_, 0);
lean_inc(v_startPos_347_);
v_endPos_348_ = lean_ctor_get(v_out_341_, 1);
lean_inc(v_endPos_348_);
lean_dec_ref(v_out_341_);
v___x_349_ = lean_apply_5(v_h__1_337_, v_it_346_, v_startPos_347_, v_endPos_348_, lean_box(0), lean_box(0));
return v___x_349_;
}
}
case 1:
{
lean_object* v_it_350_; lean_object* v___x_351_; 
lean_dec(v_h__4_340_);
lean_dec(v_h__2_338_);
lean_dec(v_h__1_337_);
v_it_350_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_it_350_);
lean_dec_ref(v_x_336_);
v___x_351_ = lean_apply_3(v_h__3_339_, v_it_350_, lean_box(0), lean_box(0));
return v___x_351_;
}
default: 
{
lean_object* v___x_352_; 
lean_dec(v_h__3_339_);
lean_dec(v_h__2_338_);
lean_dec(v_h__1_337_);
v___x_352_ = lean_apply_2(v_h__4_340_, lean_box(0), lean_box(0));
return v___x_352_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object* v_00_u03c3_353_, lean_object* v_inst_354_, lean_object* v_s_355_, lean_object* v_searcher_356_, lean_object* v_motive_357_, lean_object* v_x_358_, lean_object* v_h__1_359_, lean_object* v_h__2_360_, lean_object* v_h__3_361_, lean_object* v_h__4_362_){
_start:
{
switch(lean_obj_tag(v_x_358_))
{
case 0:
{
lean_object* v_out_363_; 
lean_dec(v_h__4_362_);
lean_dec(v_h__3_361_);
v_out_363_ = lean_ctor_get(v_x_358_, 1);
lean_inc(v_out_363_);
if (lean_obj_tag(v_out_363_) == 0)
{
lean_object* v_it_364_; lean_object* v_startPos_365_; lean_object* v_endPos_366_; lean_object* v___x_367_; 
lean_dec(v_h__1_359_);
v_it_364_ = lean_ctor_get(v_x_358_, 0);
lean_inc(v_it_364_);
lean_dec_ref(v_x_358_);
v_startPos_365_ = lean_ctor_get(v_out_363_, 0);
lean_inc(v_startPos_365_);
v_endPos_366_ = lean_ctor_get(v_out_363_, 1);
lean_inc(v_endPos_366_);
lean_dec_ref(v_out_363_);
v___x_367_ = lean_apply_5(v_h__2_360_, v_it_364_, v_startPos_365_, v_endPos_366_, lean_box(0), lean_box(0));
return v___x_367_;
}
else
{
lean_object* v_it_368_; lean_object* v_startPos_369_; lean_object* v_endPos_370_; lean_object* v___x_371_; 
lean_dec(v_h__2_360_);
v_it_368_ = lean_ctor_get(v_x_358_, 0);
lean_inc(v_it_368_);
lean_dec_ref(v_x_358_);
v_startPos_369_ = lean_ctor_get(v_out_363_, 0);
lean_inc(v_startPos_369_);
v_endPos_370_ = lean_ctor_get(v_out_363_, 1);
lean_inc(v_endPos_370_);
lean_dec_ref(v_out_363_);
v___x_371_ = lean_apply_5(v_h__1_359_, v_it_368_, v_startPos_369_, v_endPos_370_, lean_box(0), lean_box(0));
return v___x_371_;
}
}
case 1:
{
lean_object* v_it_372_; lean_object* v___x_373_; 
lean_dec(v_h__4_362_);
lean_dec(v_h__2_360_);
lean_dec(v_h__1_359_);
v_it_372_ = lean_ctor_get(v_x_358_, 0);
lean_inc(v_it_372_);
lean_dec_ref(v_x_358_);
v___x_373_ = lean_apply_3(v_h__3_361_, v_it_372_, lean_box(0), lean_box(0));
return v___x_373_;
}
default: 
{
lean_object* v___x_374_; 
lean_dec(v_h__3_361_);
lean_dec(v_h__2_360_);
lean_dec(v_h__1_359_);
v___x_374_ = lean_apply_2(v_h__4_362_, lean_box(0), lean_box(0));
return v___x_374_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object* v_00_u03c3_375_, lean_object* v_inst_376_, lean_object* v_s_377_, lean_object* v_searcher_378_, lean_object* v_motive_379_, lean_object* v_x_380_, lean_object* v_h__1_381_, lean_object* v_h__2_382_, lean_object* v_h__3_383_, lean_object* v_h__4_384_){
_start:
{
lean_object* v_res_385_; 
v_res_385_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(v_00_u03c3_375_, v_inst_376_, v_s_377_, v_searcher_378_, v_motive_379_, v_x_380_, v_h__1_381_, v_h__2_382_, v_h__3_383_, v_h__4_384_);
lean_dec(v_searcher_378_);
lean_dec_ref(v_s_377_);
lean_dec(v_inst_376_);
return v_res_385_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___redArg(lean_object* v_x_386_, lean_object* v_x_387_, lean_object* v_h__1_388_, lean_object* v_h__2_389_, lean_object* v_h__3_390_, lean_object* v_h__4_391_, lean_object* v_h__5_392_, lean_object* v_h__6_393_, lean_object* v_h__7_394_, lean_object* v_h__8_395_){
_start:
{
if (lean_obj_tag(v_x_386_) == 0)
{
lean_dec(v_h__8_395_);
lean_dec(v_h__7_394_);
lean_dec(v_h__6_393_);
switch(lean_obj_tag(v_x_387_))
{
case 0:
{
lean_object* v_it_396_; 
lean_dec(v_h__5_392_);
lean_dec(v_h__4_391_);
lean_dec(v_h__3_390_);
v_it_396_ = lean_ctor_get(v_x_387_, 0);
if (lean_obj_tag(v_it_396_) == 0)
{
lean_object* v_currPos_397_; lean_object* v_searcher_398_; lean_object* v_out_399_; lean_object* v_currPos_400_; lean_object* v_searcher_401_; lean_object* v___x_402_; 
lean_inc_ref(v_it_396_);
lean_dec(v_h__2_389_);
v_currPos_397_ = lean_ctor_get(v_x_386_, 0);
lean_inc(v_currPos_397_);
v_searcher_398_ = lean_ctor_get(v_x_386_, 1);
lean_inc(v_searcher_398_);
lean_dec_ref(v_x_386_);
v_out_399_ = lean_ctor_get(v_x_387_, 1);
lean_inc(v_out_399_);
lean_dec_ref(v_x_387_);
v_currPos_400_ = lean_ctor_get(v_it_396_, 0);
lean_inc(v_currPos_400_);
v_searcher_401_ = lean_ctor_get(v_it_396_, 1);
lean_inc(v_searcher_401_);
lean_dec_ref(v_it_396_);
v___x_402_ = lean_apply_5(v_h__1_388_, v_currPos_397_, v_searcher_398_, v_currPos_400_, v_searcher_401_, v_out_399_);
return v___x_402_;
}
else
{
lean_object* v_currPos_403_; lean_object* v_searcher_404_; lean_object* v_out_405_; lean_object* v___x_406_; 
lean_dec(v_h__1_388_);
v_currPos_403_ = lean_ctor_get(v_x_386_, 0);
lean_inc(v_currPos_403_);
v_searcher_404_ = lean_ctor_get(v_x_386_, 1);
lean_inc(v_searcher_404_);
lean_dec_ref(v_x_386_);
v_out_405_ = lean_ctor_get(v_x_387_, 1);
lean_inc(v_out_405_);
lean_dec_ref(v_x_387_);
v___x_406_ = lean_apply_3(v_h__2_389_, v_currPos_403_, v_searcher_404_, v_out_405_);
return v___x_406_;
}
}
case 1:
{
lean_object* v_it_407_; 
lean_dec(v_h__5_392_);
lean_dec(v_h__2_389_);
lean_dec(v_h__1_388_);
v_it_407_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_it_407_);
lean_dec_ref(v_x_387_);
if (lean_obj_tag(v_it_407_) == 0)
{
lean_object* v_currPos_408_; lean_object* v_searcher_409_; lean_object* v_currPos_410_; lean_object* v_searcher_411_; lean_object* v___x_412_; 
lean_dec(v_h__4_391_);
v_currPos_408_ = lean_ctor_get(v_x_386_, 0);
lean_inc(v_currPos_408_);
v_searcher_409_ = lean_ctor_get(v_x_386_, 1);
lean_inc(v_searcher_409_);
lean_dec_ref(v_x_386_);
v_currPos_410_ = lean_ctor_get(v_it_407_, 0);
lean_inc(v_currPos_410_);
v_searcher_411_ = lean_ctor_get(v_it_407_, 1);
lean_inc(v_searcher_411_);
lean_dec_ref(v_it_407_);
v___x_412_ = lean_apply_4(v_h__3_390_, v_currPos_408_, v_searcher_409_, v_currPos_410_, v_searcher_411_);
return v___x_412_;
}
else
{
lean_object* v_currPos_413_; lean_object* v_searcher_414_; lean_object* v___x_415_; 
lean_dec(v_h__3_390_);
v_currPos_413_ = lean_ctor_get(v_x_386_, 0);
lean_inc(v_currPos_413_);
v_searcher_414_ = lean_ctor_get(v_x_386_, 1);
lean_inc(v_searcher_414_);
lean_dec_ref(v_x_386_);
v___x_415_ = lean_apply_2(v_h__4_391_, v_currPos_413_, v_searcher_414_);
return v___x_415_;
}
}
default: 
{
lean_object* v_currPos_416_; lean_object* v_searcher_417_; lean_object* v___x_418_; 
lean_dec(v_h__4_391_);
lean_dec(v_h__3_390_);
lean_dec(v_h__2_389_);
lean_dec(v_h__1_388_);
v_currPos_416_ = lean_ctor_get(v_x_386_, 0);
lean_inc(v_currPos_416_);
v_searcher_417_ = lean_ctor_get(v_x_386_, 1);
lean_inc(v_searcher_417_);
lean_dec_ref(v_x_386_);
v___x_418_ = lean_apply_2(v_h__5_392_, v_currPos_416_, v_searcher_417_);
return v___x_418_;
}
}
}
else
{
lean_dec(v_h__5_392_);
lean_dec(v_h__4_391_);
lean_dec(v_h__3_390_);
lean_dec(v_h__2_389_);
lean_dec(v_h__1_388_);
switch(lean_obj_tag(v_x_387_))
{
case 0:
{
lean_object* v_it_419_; lean_object* v_out_420_; lean_object* v___x_421_; 
lean_dec(v_h__8_395_);
lean_dec(v_h__7_394_);
v_it_419_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_it_419_);
v_out_420_ = lean_ctor_get(v_x_387_, 1);
lean_inc(v_out_420_);
lean_dec_ref(v_x_387_);
v___x_421_ = lean_apply_2(v_h__6_393_, v_it_419_, v_out_420_);
return v___x_421_;
}
case 1:
{
lean_object* v_it_422_; lean_object* v___x_423_; 
lean_dec(v_h__8_395_);
lean_dec(v_h__6_393_);
v_it_422_ = lean_ctor_get(v_x_387_, 0);
lean_inc(v_it_422_);
lean_dec_ref(v_x_387_);
v___x_423_ = lean_apply_1(v_h__7_394_, v_it_422_);
return v___x_423_;
}
default: 
{
lean_object* v___x_424_; lean_object* v___x_425_; 
lean_dec(v_h__7_394_);
lean_dec(v_h__6_393_);
v___x_424_ = lean_box(0);
v___x_425_ = lean_apply_1(v_h__8_395_, v___x_424_);
return v___x_425_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(lean_object* v_00_u03c1_426_, lean_object* v_00_u03c3_427_, lean_object* v_pat_428_, lean_object* v_inst_429_, lean_object* v_s_430_, lean_object* v_motive_431_, lean_object* v_x_432_, lean_object* v_x_433_, lean_object* v_h__1_434_, lean_object* v_h__2_435_, lean_object* v_h__3_436_, lean_object* v_h__4_437_, lean_object* v_h__5_438_, lean_object* v_h__6_439_, lean_object* v_h__7_440_, lean_object* v_h__8_441_){
_start:
{
if (lean_obj_tag(v_x_432_) == 0)
{
lean_dec(v_h__8_441_);
lean_dec(v_h__7_440_);
lean_dec(v_h__6_439_);
switch(lean_obj_tag(v_x_433_))
{
case 0:
{
lean_object* v_it_442_; 
lean_dec(v_h__5_438_);
lean_dec(v_h__4_437_);
lean_dec(v_h__3_436_);
v_it_442_ = lean_ctor_get(v_x_433_, 0);
if (lean_obj_tag(v_it_442_) == 0)
{
lean_object* v_currPos_443_; lean_object* v_searcher_444_; lean_object* v_out_445_; lean_object* v_currPos_446_; lean_object* v_searcher_447_; lean_object* v___x_448_; 
lean_inc_ref(v_it_442_);
lean_dec(v_h__2_435_);
v_currPos_443_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_currPos_443_);
v_searcher_444_ = lean_ctor_get(v_x_432_, 1);
lean_inc(v_searcher_444_);
lean_dec_ref(v_x_432_);
v_out_445_ = lean_ctor_get(v_x_433_, 1);
lean_inc(v_out_445_);
lean_dec_ref(v_x_433_);
v_currPos_446_ = lean_ctor_get(v_it_442_, 0);
lean_inc(v_currPos_446_);
v_searcher_447_ = lean_ctor_get(v_it_442_, 1);
lean_inc(v_searcher_447_);
lean_dec_ref(v_it_442_);
v___x_448_ = lean_apply_5(v_h__1_434_, v_currPos_443_, v_searcher_444_, v_currPos_446_, v_searcher_447_, v_out_445_);
return v___x_448_;
}
else
{
lean_object* v_currPos_449_; lean_object* v_searcher_450_; lean_object* v_out_451_; lean_object* v___x_452_; 
lean_dec(v_h__1_434_);
v_currPos_449_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_currPos_449_);
v_searcher_450_ = lean_ctor_get(v_x_432_, 1);
lean_inc(v_searcher_450_);
lean_dec_ref(v_x_432_);
v_out_451_ = lean_ctor_get(v_x_433_, 1);
lean_inc(v_out_451_);
lean_dec_ref(v_x_433_);
v___x_452_ = lean_apply_3(v_h__2_435_, v_currPos_449_, v_searcher_450_, v_out_451_);
return v___x_452_;
}
}
case 1:
{
lean_object* v_it_453_; 
lean_dec(v_h__5_438_);
lean_dec(v_h__2_435_);
lean_dec(v_h__1_434_);
v_it_453_ = lean_ctor_get(v_x_433_, 0);
lean_inc(v_it_453_);
lean_dec_ref(v_x_433_);
if (lean_obj_tag(v_it_453_) == 0)
{
lean_object* v_currPos_454_; lean_object* v_searcher_455_; lean_object* v_currPos_456_; lean_object* v_searcher_457_; lean_object* v___x_458_; 
lean_dec(v_h__4_437_);
v_currPos_454_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_currPos_454_);
v_searcher_455_ = lean_ctor_get(v_x_432_, 1);
lean_inc(v_searcher_455_);
lean_dec_ref(v_x_432_);
v_currPos_456_ = lean_ctor_get(v_it_453_, 0);
lean_inc(v_currPos_456_);
v_searcher_457_ = lean_ctor_get(v_it_453_, 1);
lean_inc(v_searcher_457_);
lean_dec_ref(v_it_453_);
v___x_458_ = lean_apply_4(v_h__3_436_, v_currPos_454_, v_searcher_455_, v_currPos_456_, v_searcher_457_);
return v___x_458_;
}
else
{
lean_object* v_currPos_459_; lean_object* v_searcher_460_; lean_object* v___x_461_; 
lean_dec(v_h__3_436_);
v_currPos_459_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_currPos_459_);
v_searcher_460_ = lean_ctor_get(v_x_432_, 1);
lean_inc(v_searcher_460_);
lean_dec_ref(v_x_432_);
v___x_461_ = lean_apply_2(v_h__4_437_, v_currPos_459_, v_searcher_460_);
return v___x_461_;
}
}
default: 
{
lean_object* v_currPos_462_; lean_object* v_searcher_463_; lean_object* v___x_464_; 
lean_dec(v_h__4_437_);
lean_dec(v_h__3_436_);
lean_dec(v_h__2_435_);
lean_dec(v_h__1_434_);
v_currPos_462_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_currPos_462_);
v_searcher_463_ = lean_ctor_get(v_x_432_, 1);
lean_inc(v_searcher_463_);
lean_dec_ref(v_x_432_);
v___x_464_ = lean_apply_2(v_h__5_438_, v_currPos_462_, v_searcher_463_);
return v___x_464_;
}
}
}
else
{
lean_dec(v_h__5_438_);
lean_dec(v_h__4_437_);
lean_dec(v_h__3_436_);
lean_dec(v_h__2_435_);
lean_dec(v_h__1_434_);
switch(lean_obj_tag(v_x_433_))
{
case 0:
{
lean_object* v_it_465_; lean_object* v_out_466_; lean_object* v___x_467_; 
lean_dec(v_h__8_441_);
lean_dec(v_h__7_440_);
v_it_465_ = lean_ctor_get(v_x_433_, 0);
lean_inc(v_it_465_);
v_out_466_ = lean_ctor_get(v_x_433_, 1);
lean_inc(v_out_466_);
lean_dec_ref(v_x_433_);
v___x_467_ = lean_apply_2(v_h__6_439_, v_it_465_, v_out_466_);
return v___x_467_;
}
case 1:
{
lean_object* v_it_468_; lean_object* v___x_469_; 
lean_dec(v_h__8_441_);
lean_dec(v_h__6_439_);
v_it_468_ = lean_ctor_get(v_x_433_, 0);
lean_inc(v_it_468_);
lean_dec_ref(v_x_433_);
v___x_469_ = lean_apply_1(v_h__7_440_, v_it_468_);
return v___x_469_;
}
default: 
{
lean_object* v___x_470_; lean_object* v___x_471_; 
lean_dec(v_h__7_440_);
lean_dec(v_h__6_439_);
v___x_470_ = lean_box(0);
v___x_471_ = lean_apply_1(v_h__8_441_, v___x_470_);
return v___x_471_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___boxed(lean_object* v_00_u03c1_472_, lean_object* v_00_u03c3_473_, lean_object* v_pat_474_, lean_object* v_inst_475_, lean_object* v_s_476_, lean_object* v_motive_477_, lean_object* v_x_478_, lean_object* v_x_479_, lean_object* v_h__1_480_, lean_object* v_h__2_481_, lean_object* v_h__3_482_, lean_object* v_h__4_483_, lean_object* v_h__5_484_, lean_object* v_h__6_485_, lean_object* v_h__7_486_, lean_object* v_h__8_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(v_00_u03c1_472_, v_00_u03c3_473_, v_pat_474_, v_inst_475_, v_s_476_, v_motive_477_, v_x_478_, v_x_479_, v_h__1_480_, v_h__2_481_, v_h__3_482_, v_h__4_483_, v_h__5_484_, v_h__6_485_, v_h__7_486_, v_h__8_487_);
lean_dec_ref(v_s_476_);
lean_dec(v_inst_475_);
lean_dec(v_pat_474_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___redArg(lean_object* v_x_489_, lean_object* v_h__1_490_, lean_object* v_h__2_491_){
_start:
{
if (lean_obj_tag(v_x_489_) == 0)
{
lean_object* v_currPos_492_; lean_object* v_searcher_493_; lean_object* v___x_494_; 
lean_dec(v_h__2_491_);
v_currPos_492_ = lean_ctor_get(v_x_489_, 0);
lean_inc(v_currPos_492_);
v_searcher_493_ = lean_ctor_get(v_x_489_, 1);
lean_inc(v_searcher_493_);
lean_dec_ref(v_x_489_);
v___x_494_ = lean_apply_2(v_h__1_490_, v_currPos_492_, v_searcher_493_);
return v___x_494_;
}
else
{
lean_object* v___x_495_; lean_object* v___x_496_; 
lean_dec(v_h__1_490_);
v___x_495_ = lean_box(0);
v___x_496_ = lean_apply_1(v_h__2_491_, v___x_495_);
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_497_, lean_object* v_00_u03c3_498_, lean_object* v_pat_499_, lean_object* v_inst_500_, lean_object* v_s_501_, lean_object* v_motive_502_, lean_object* v_x_503_, lean_object* v_h__1_504_, lean_object* v_h__2_505_){
_start:
{
if (lean_obj_tag(v_x_503_) == 0)
{
lean_object* v_currPos_506_; lean_object* v_searcher_507_; lean_object* v___x_508_; 
lean_dec(v_h__2_505_);
v_currPos_506_ = lean_ctor_get(v_x_503_, 0);
lean_inc(v_currPos_506_);
v_searcher_507_ = lean_ctor_get(v_x_503_, 1);
lean_inc(v_searcher_507_);
lean_dec_ref(v_x_503_);
v___x_508_ = lean_apply_2(v_h__1_504_, v_currPos_506_, v_searcher_507_);
return v___x_508_;
}
else
{
lean_object* v___x_509_; lean_object* v___x_510_; 
lean_dec(v_h__1_504_);
v___x_509_ = lean_box(0);
v___x_510_ = lean_apply_1(v_h__2_505_, v___x_509_);
return v___x_510_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_511_, lean_object* v_00_u03c3_512_, lean_object* v_pat_513_, lean_object* v_inst_514_, lean_object* v_s_515_, lean_object* v_motive_516_, lean_object* v_x_517_, lean_object* v_h__1_518_, lean_object* v_h__2_519_){
_start:
{
lean_object* v_res_520_; 
v_res_520_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter(v_00_u03c1_511_, v_00_u03c3_512_, v_pat_513_, v_inst_514_, v_s_515_, v_motive_516_, v_x_517_, v_h__1_518_, v_h__2_519_);
lean_dec_ref(v_s_515_);
lean_dec(v_inst_514_);
lean_dec(v_pat_513_);
return v_res_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(lean_object* v_00_u03c1_521_, lean_object* v_00_u03c3_522_, lean_object* v_inst_523_, lean_object* v_pat_524_, lean_object* v_inst_525_, lean_object* v_s_526_, lean_object* v_inst_527_){
_start:
{
lean_object* v___x_528_; 
v___x_528_ = lean_box(0);
return v___x_528_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_529_, lean_object* v_00_u03c3_530_, lean_object* v_inst_531_, lean_object* v_pat_532_, lean_object* v_inst_533_, lean_object* v_s_534_, lean_object* v_inst_535_){
_start:
{
lean_object* v_res_536_; 
v_res_536_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(v_00_u03c1_529_, v_00_u03c3_530_, v_inst_531_, v_pat_532_, v_inst_533_, v_s_534_, v_inst_535_);
lean_dec_ref(v_s_534_);
lean_dec(v_inst_533_);
lean_dec(v_pat_532_);
lean_dec(v_inst_531_);
return v_res_536_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0(lean_object* v_toPure_537_, lean_object* v_recur_538_, lean_object* v_it_539_, lean_object* v_____do__lift_540_){
_start:
{
if (lean_obj_tag(v_____do__lift_540_) == 0)
{
lean_object* v_a_541_; lean_object* v___x_542_; 
lean_dec(v_it_539_);
lean_dec(v_recur_538_);
v_a_541_ = lean_ctor_get(v_____do__lift_540_, 0);
lean_inc(v_a_541_);
lean_dec_ref(v_____do__lift_540_);
v___x_542_ = lean_apply_2(v_toPure_537_, lean_box(0), v_a_541_);
return v___x_542_;
}
else
{
lean_object* v_a_543_; lean_object* v___x_544_; 
lean_dec(v_toPure_537_);
v_a_543_ = lean_ctor_get(v_____do__lift_540_, 0);
lean_inc(v_a_543_);
lean_dec_ref(v_____do__lift_540_);
v___x_544_ = lean_apply_4(v_recur_538_, v_it_539_, v_a_543_, lean_box(0), lean_box(0));
return v___x_544_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1(lean_object* v_toPure_545_, lean_object* v_recur_546_, lean_object* v___y_547_, lean_object* v_acc_548_, lean_object* v_toBind_549_, lean_object* v_s_550_){
_start:
{
switch(lean_obj_tag(v_s_550_))
{
case 0:
{
lean_object* v_it_551_; lean_object* v_out_552_; lean_object* v___f_553_; lean_object* v___x_554_; lean_object* v___x_555_; 
v_it_551_ = lean_ctor_get(v_s_550_, 0);
lean_inc(v_it_551_);
v_out_552_ = lean_ctor_get(v_s_550_, 1);
lean_inc(v_out_552_);
lean_dec_ref(v_s_550_);
v___f_553_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_553_, 0, v_toPure_545_);
lean_closure_set(v___f_553_, 1, v_recur_546_);
lean_closure_set(v___f_553_, 2, v_it_551_);
v___x_554_ = lean_apply_3(v___y_547_, v_out_552_, lean_box(0), v_acc_548_);
v___x_555_ = lean_apply_4(v_toBind_549_, lean_box(0), lean_box(0), v___x_554_, v___f_553_);
return v___x_555_;
}
case 1:
{
lean_object* v_it_556_; lean_object* v___x_557_; 
lean_dec(v_toBind_549_);
lean_dec(v___y_547_);
lean_dec(v_toPure_545_);
v_it_556_ = lean_ctor_get(v_s_550_, 0);
lean_inc(v_it_556_);
lean_dec_ref(v_s_550_);
v___x_557_ = lean_apply_4(v_recur_546_, v_it_556_, v_acc_548_, lean_box(0), lean_box(0));
return v___x_557_;
}
default: 
{
lean_object* v___x_558_; 
lean_dec(v_toBind_549_);
lean_dec(v___y_547_);
lean_dec(v_recur_546_);
v___x_558_ = lean_apply_2(v_toPure_545_, lean_box(0), v_acc_548_);
return v___x_558_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2(lean_object* v_toPure_559_, lean_object* v___y_560_, lean_object* v_toBind_561_, lean_object* v_inst_562_, lean_object* v_s_563_, lean_object* v_lift_564_, lean_object* v_it_565_, lean_object* v_acc_566_, lean_object* v_hP_567_, lean_object* v_recur_568_){
_start:
{
lean_object* v___f_569_; 
v___f_569_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_569_, 0, v_toPure_559_);
lean_closure_set(v___f_569_, 1, v_recur_568_);
lean_closure_set(v___f_569_, 2, v___y_560_);
lean_closure_set(v___f_569_, 3, v_acc_566_);
lean_closure_set(v___f_569_, 4, v_toBind_561_);
if (lean_obj_tag(v_it_565_) == 0)
{
lean_object* v_currPos_570_; lean_object* v_searcher_571_; lean_object* v___x_573_; uint8_t v_isShared_574_; uint8_t v_isSharedCheck_618_; 
v_currPos_570_ = lean_ctor_get(v_it_565_, 0);
v_searcher_571_ = lean_ctor_get(v_it_565_, 1);
v_isSharedCheck_618_ = !lean_is_exclusive(v_it_565_);
if (v_isSharedCheck_618_ == 0)
{
v___x_573_ = v_it_565_;
v_isShared_574_ = v_isSharedCheck_618_;
goto v_resetjp_572_;
}
else
{
lean_inc(v_searcher_571_);
lean_inc(v_currPos_570_);
lean_dec(v_it_565_);
v___x_573_ = lean_box(0);
v_isShared_574_ = v_isSharedCheck_618_;
goto v_resetjp_572_;
}
v_resetjp_572_:
{
lean_object* v___x_575_; 
lean_inc_ref(v_s_563_);
v___x_575_ = lean_apply_2(v_inst_562_, v_s_563_, v_searcher_571_);
switch(lean_obj_tag(v___x_575_))
{
case 0:
{
lean_object* v_out_576_; 
v_out_576_ = lean_ctor_get(v___x_575_, 1);
lean_inc(v_out_576_);
if (lean_obj_tag(v_out_576_) == 0)
{
lean_object* v_it_577_; lean_object* v___x_579_; 
lean_dec_ref(v_out_576_);
lean_dec_ref(v_s_563_);
v_it_577_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_it_577_);
lean_dec_ref(v___x_575_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v_it_577_);
v___x_579_ = v___x_573_;
goto v_reusejp_578_;
}
else
{
lean_object* v_reuseFailAlloc_582_; 
v_reuseFailAlloc_582_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_582_, 0, v_currPos_570_);
lean_ctor_set(v_reuseFailAlloc_582_, 1, v_it_577_);
v___x_579_ = v_reuseFailAlloc_582_;
goto v_reusejp_578_;
}
v_reusejp_578_:
{
lean_object* v___x_580_; lean_object* v___x_581_; 
v___x_580_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_580_, 0, v___x_579_);
v___x_581_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_580_);
return v___x_581_;
}
}
else
{
lean_object* v_it_583_; lean_object* v___x_585_; uint8_t v_isShared_586_; uint8_t v_isSharedCheck_597_; 
v_it_583_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_597_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_597_ == 0)
{
lean_object* v_unused_598_; 
v_unused_598_ = lean_ctor_get(v___x_575_, 1);
lean_dec(v_unused_598_);
v___x_585_ = v___x_575_;
v_isShared_586_ = v_isSharedCheck_597_;
goto v_resetjp_584_;
}
else
{
lean_inc(v_it_583_);
lean_dec(v___x_575_);
v___x_585_ = lean_box(0);
v_isShared_586_ = v_isSharedCheck_597_;
goto v_resetjp_584_;
}
v_resetjp_584_:
{
lean_object* v_startPos_587_; lean_object* v_endPos_588_; lean_object* v_slice_589_; lean_object* v_nextIt_591_; 
v_startPos_587_ = lean_ctor_get(v_out_576_, 0);
lean_inc(v_startPos_587_);
v_endPos_588_ = lean_ctor_get(v_out_576_, 1);
lean_inc(v_endPos_588_);
lean_dec_ref(v_out_576_);
v_slice_589_ = l_String_Slice_subslice_x21(v_s_563_, v_currPos_570_, v_startPos_587_);
lean_dec_ref(v_s_563_);
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v_it_583_);
lean_ctor_set(v___x_573_, 0, v_endPos_588_);
v_nextIt_591_ = v___x_573_;
goto v_reusejp_590_;
}
else
{
lean_object* v_reuseFailAlloc_596_; 
v_reuseFailAlloc_596_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_596_, 0, v_endPos_588_);
lean_ctor_set(v_reuseFailAlloc_596_, 1, v_it_583_);
v_nextIt_591_ = v_reuseFailAlloc_596_;
goto v_reusejp_590_;
}
v_reusejp_590_:
{
lean_object* v___x_593_; 
if (v_isShared_586_ == 0)
{
lean_ctor_set(v___x_585_, 1, v_slice_589_);
lean_ctor_set(v___x_585_, 0, v_nextIt_591_);
v___x_593_ = v___x_585_;
goto v_reusejp_592_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_nextIt_591_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_slice_589_);
v___x_593_ = v_reuseFailAlloc_595_;
goto v_reusejp_592_;
}
v_reusejp_592_:
{
lean_object* v___x_594_; 
v___x_594_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_593_);
return v___x_594_;
}
}
}
}
}
case 1:
{
lean_object* v_it_599_; lean_object* v___x_601_; uint8_t v_isShared_602_; uint8_t v_isSharedCheck_610_; 
lean_dec_ref(v_s_563_);
v_it_599_ = lean_ctor_get(v___x_575_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_575_);
if (v_isSharedCheck_610_ == 0)
{
v___x_601_ = v___x_575_;
v_isShared_602_ = v_isSharedCheck_610_;
goto v_resetjp_600_;
}
else
{
lean_inc(v_it_599_);
lean_dec(v___x_575_);
v___x_601_ = lean_box(0);
v_isShared_602_ = v_isSharedCheck_610_;
goto v_resetjp_600_;
}
v_resetjp_600_:
{
lean_object* v___x_604_; 
if (v_isShared_574_ == 0)
{
lean_ctor_set(v___x_573_, 1, v_it_599_);
v___x_604_ = v___x_573_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_currPos_570_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_it_599_);
v___x_604_ = v_reuseFailAlloc_609_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_606_; 
if (v_isShared_602_ == 0)
{
lean_ctor_set(v___x_601_, 0, v___x_604_);
v___x_606_ = v___x_601_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v___x_604_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; 
v___x_607_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_606_);
return v___x_607_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_611_; lean_object* v_endExclusive_612_; lean_object* v___x_613_; lean_object* v_slice_614_; lean_object* v___x_615_; lean_object* v___x_616_; lean_object* v___x_617_; 
lean_del_object(v___x_573_);
v_startInclusive_611_ = lean_ctor_get(v_s_563_, 1);
lean_inc(v_startInclusive_611_);
v_endExclusive_612_ = lean_ctor_get(v_s_563_, 2);
lean_inc(v_endExclusive_612_);
lean_dec_ref(v_s_563_);
v___x_613_ = lean_nat_sub(v_endExclusive_612_, v_startInclusive_611_);
lean_dec(v_startInclusive_611_);
lean_dec(v_endExclusive_612_);
v_slice_614_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_614_, 0, v_currPos_570_);
lean_ctor_set(v_slice_614_, 1, v___x_613_);
v___x_615_ = lean_box(1);
v___x_616_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_616_, 0, v___x_615_);
lean_ctor_set(v___x_616_, 1, v_slice_614_);
v___x_617_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_616_);
return v___x_617_;
}
}
}
}
else
{
lean_object* v___x_619_; lean_object* v___x_620_; 
lean_dec_ref(v_s_563_);
lean_dec(v_inst_562_);
v___x_619_ = lean_box(2);
v___x_620_ = lean_apply_4(v_lift_564_, lean_box(0), lean_box(0), v___f_569_, v___x_619_);
return v___x_620_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3(lean_object* v_inst_621_, lean_object* v_inst_622_, lean_object* v_s_623_, lean_object* v_lift_624_, lean_object* v_00_u03b3_625_, lean_object* v_Pl_626_, lean_object* v_it_627_, lean_object* v_init_628_, lean_object* v___y_629_){
_start:
{
lean_object* v_toApplicative_630_; lean_object* v_toBind_631_; lean_object* v_toPure_632_; lean_object* v___f_633_; lean_object* v___x_634_; 
v_toApplicative_630_ = lean_ctor_get(v_inst_621_, 0);
lean_inc_ref(v_toApplicative_630_);
v_toBind_631_ = lean_ctor_get(v_inst_621_, 1);
lean_inc(v_toBind_631_);
lean_dec_ref(v_inst_621_);
v_toPure_632_ = lean_ctor_get(v_toApplicative_630_, 1);
lean_inc(v_toPure_632_);
lean_dec_ref(v_toApplicative_630_);
v___f_633_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_633_, 0, v_toPure_632_);
lean_closure_set(v___f_633_, 1, v___y_629_);
lean_closure_set(v___f_633_, 2, v_toBind_631_);
lean_closure_set(v___f_633_, 3, v_inst_622_);
lean_closure_set(v___f_633_, 4, v_s_623_);
lean_closure_set(v___f_633_, 5, v_lift_624_);
v___x_634_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_633_, v_it_627_, v_init_628_, lean_box(0));
return v___x_634_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg(lean_object* v_inst_635_, lean_object* v_s_636_, lean_object* v_inst_637_){
_start:
{
lean_object* v___f_638_; 
v___f_638_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_638_, 0, v_inst_637_);
lean_closure_set(v___f_638_, 1, v_inst_635_);
lean_closure_set(v___f_638_, 2, v_s_636_);
return v___f_638_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(lean_object* v_00_u03c1_639_, lean_object* v_00_u03c3_640_, lean_object* v_inst_641_, lean_object* v_pat_642_, lean_object* v_inst_643_, lean_object* v_n_644_, lean_object* v_s_645_, lean_object* v_inst_646_){
_start:
{
lean_object* v___f_647_; 
v___f_647_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_647_, 0, v_inst_646_);
lean_closure_set(v___f_647_, 1, v_inst_641_);
lean_closure_set(v___f_647_, 2, v_s_645_);
return v___f_647_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___boxed(lean_object* v_00_u03c1_648_, lean_object* v_00_u03c3_649_, lean_object* v_inst_650_, lean_object* v_pat_651_, lean_object* v_inst_652_, lean_object* v_n_653_, lean_object* v_s_654_, lean_object* v_inst_655_){
_start:
{
lean_object* v_res_656_; 
v_res_656_ = l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(v_00_u03c1_648_, v_00_u03c3_649_, v_inst_650_, v_pat_651_, v_inst_652_, v_n_653_, v_s_654_, v_inst_655_);
lean_dec(v_inst_652_);
lean_dec(v_pat_651_);
return v_res_656_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___redArg(lean_object* v_s_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v___x_659_; lean_object* v___x_660_; lean_object* v___x_661_; 
v___x_659_ = lean_unsigned_to_nat(0u);
v___x_660_ = lean_apply_1(v_inst_658_, v_s_657_);
v___x_661_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_661_, 0, v___x_659_);
lean_ctor_set(v___x_661_, 1, v___x_660_);
return v___x_661_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice(lean_object* v_00_u03c1_662_, lean_object* v_00_u03c3_663_, lean_object* v_s_664_, lean_object* v_pat_665_, lean_object* v_inst_666_){
_start:
{
lean_object* v___x_667_; 
v___x_667_ = l_String_Slice_splitToSubslice___redArg(v_s_664_, v_inst_666_);
return v___x_667_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___boxed(lean_object* v_00_u03c1_668_, lean_object* v_00_u03c3_669_, lean_object* v_s_670_, lean_object* v_pat_671_, lean_object* v_inst_672_){
_start:
{
lean_object* v_res_673_; 
v_res_673_ = l_String_Slice_splitToSubslice(v_00_u03c1_668_, v_00_u03c3_669_, v_s_670_, v_pat_671_, v_inst_672_);
lean_dec(v_pat_671_);
return v_res_673_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___redArg(lean_object* v_s_674_, lean_object* v_inst_675_){
_start:
{
lean_object* v___x_676_; 
v___x_676_ = l_String_Slice_splitToSubslice___redArg(v_s_674_, v_inst_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split(lean_object* v_00_u03c1_677_, lean_object* v_00_u03c3_678_, lean_object* v_inst_679_, lean_object* v_s_680_, lean_object* v_pat_681_, lean_object* v_inst_682_){
_start:
{
lean_object* v___x_683_; 
v___x_683_ = l_String_Slice_splitToSubslice___redArg(v_s_680_, v_inst_682_);
return v___x_683_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___boxed(lean_object* v_00_u03c1_684_, lean_object* v_00_u03c3_685_, lean_object* v_inst_686_, lean_object* v_s_687_, lean_object* v_pat_688_, lean_object* v_inst_689_){
_start:
{
lean_object* v_res_690_; 
v_res_690_ = l_String_Slice_split(v_00_u03c1_684_, v_00_u03c3_685_, v_inst_686_, v_s_687_, v_pat_688_, v_inst_689_);
lean_dec(v_pat_688_);
lean_dec(v_inst_686_);
return v_res_690_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(lean_object* v_x_691_){
_start:
{
if (lean_obj_tag(v_x_691_) == 0)
{
lean_object* v___x_692_; 
v___x_692_ = lean_unsigned_to_nat(0u);
return v___x_692_;
}
else
{
lean_object* v___x_693_; 
v___x_693_ = lean_unsigned_to_nat(1u);
return v___x_693_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg___boxed(lean_object* v_x_694_){
_start:
{
lean_object* v_res_695_; 
v_res_695_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(v_x_694_);
lean_dec(v_x_694_);
return v_res_695_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx(lean_object* v_00_u03c3_696_, lean_object* v_00_u03c1_697_, lean_object* v_pat_698_, lean_object* v_s_699_, lean_object* v_inst_700_, lean_object* v_x_701_){
_start:
{
lean_object* v___x_702_; 
v___x_702_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(v_x_701_);
return v___x_702_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___boxed(lean_object* v_00_u03c3_703_, lean_object* v_00_u03c1_704_, lean_object* v_pat_705_, lean_object* v_s_706_, lean_object* v_inst_707_, lean_object* v_x_708_){
_start:
{
lean_object* v_res_709_; 
v_res_709_ = l_String_Slice_SplitInclusiveIterator_ctorIdx(v_00_u03c3_703_, v_00_u03c1_704_, v_pat_705_, v_s_706_, v_inst_707_, v_x_708_);
lean_dec(v_x_708_);
lean_dec(v_inst_707_);
lean_dec_ref(v_s_706_);
lean_dec(v_pat_705_);
return v_res_709_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(lean_object* v_t_710_, lean_object* v_k_711_){
_start:
{
if (lean_obj_tag(v_t_710_) == 0)
{
lean_object* v_currPos_712_; lean_object* v_searcher_713_; lean_object* v___x_714_; 
v_currPos_712_ = lean_ctor_get(v_t_710_, 0);
lean_inc(v_currPos_712_);
v_searcher_713_ = lean_ctor_get(v_t_710_, 1);
lean_inc(v_searcher_713_);
lean_dec_ref(v_t_710_);
v___x_714_ = lean_apply_2(v_k_711_, v_currPos_712_, v_searcher_713_);
return v___x_714_;
}
else
{
return v_k_711_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim(lean_object* v_00_u03c3_715_, lean_object* v_00_u03c1_716_, lean_object* v_pat_717_, lean_object* v_s_718_, lean_object* v_inst_719_, lean_object* v_motive_720_, lean_object* v_ctorIdx_721_, lean_object* v_t_722_, lean_object* v_h_723_, lean_object* v_k_724_){
_start:
{
lean_object* v___x_725_; 
v___x_725_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_722_, v_k_724_);
return v___x_725_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___boxed(lean_object* v_00_u03c3_726_, lean_object* v_00_u03c1_727_, lean_object* v_pat_728_, lean_object* v_s_729_, lean_object* v_inst_730_, lean_object* v_motive_731_, lean_object* v_ctorIdx_732_, lean_object* v_t_733_, lean_object* v_h_734_, lean_object* v_k_735_){
_start:
{
lean_object* v_res_736_; 
v_res_736_ = l_String_Slice_SplitInclusiveIterator_ctorElim(v_00_u03c3_726_, v_00_u03c1_727_, v_pat_728_, v_s_729_, v_inst_730_, v_motive_731_, v_ctorIdx_732_, v_t_733_, v_h_734_, v_k_735_);
lean_dec(v_ctorIdx_732_);
lean_dec(v_inst_730_);
lean_dec_ref(v_s_729_);
lean_dec(v_pat_728_);
return v_res_736_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___redArg(lean_object* v_t_737_, lean_object* v_operating_738_){
_start:
{
lean_object* v___x_739_; 
v___x_739_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_737_, v_operating_738_);
return v___x_739_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim(lean_object* v_00_u03c3_740_, lean_object* v_00_u03c1_741_, lean_object* v_pat_742_, lean_object* v_s_743_, lean_object* v_inst_744_, lean_object* v_motive_745_, lean_object* v_t_746_, lean_object* v_h_747_, lean_object* v_operating_748_){
_start:
{
lean_object* v___x_749_; 
v___x_749_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_746_, v_operating_748_);
return v___x_749_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___boxed(lean_object* v_00_u03c3_750_, lean_object* v_00_u03c1_751_, lean_object* v_pat_752_, lean_object* v_s_753_, lean_object* v_inst_754_, lean_object* v_motive_755_, lean_object* v_t_756_, lean_object* v_h_757_, lean_object* v_operating_758_){
_start:
{
lean_object* v_res_759_; 
v_res_759_ = l_String_Slice_SplitInclusiveIterator_operating_elim(v_00_u03c3_750_, v_00_u03c1_751_, v_pat_752_, v_s_753_, v_inst_754_, v_motive_755_, v_t_756_, v_h_757_, v_operating_758_);
lean_dec(v_inst_754_);
lean_dec_ref(v_s_753_);
lean_dec(v_pat_752_);
return v_res_759_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___redArg(lean_object* v_t_760_, lean_object* v_atEnd_761_){
_start:
{
lean_object* v___x_762_; 
v___x_762_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_760_, v_atEnd_761_);
return v___x_762_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim(lean_object* v_00_u03c3_763_, lean_object* v_00_u03c1_764_, lean_object* v_pat_765_, lean_object* v_s_766_, lean_object* v_inst_767_, lean_object* v_motive_768_, lean_object* v_t_769_, lean_object* v_h_770_, lean_object* v_atEnd_771_){
_start:
{
lean_object* v___x_772_; 
v___x_772_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_769_, v_atEnd_771_);
return v___x_772_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_773_, lean_object* v_00_u03c1_774_, lean_object* v_pat_775_, lean_object* v_s_776_, lean_object* v_inst_777_, lean_object* v_motive_778_, lean_object* v_t_779_, lean_object* v_h_780_, lean_object* v_atEnd_781_){
_start:
{
lean_object* v_res_782_; 
v_res_782_ = l_String_Slice_SplitInclusiveIterator_atEnd_elim(v_00_u03c3_773_, v_00_u03c1_774_, v_pat_775_, v_s_776_, v_inst_777_, v_motive_778_, v_t_779_, v_h_780_, v_atEnd_781_);
lean_dec(v_inst_777_);
lean_dec_ref(v_s_776_);
lean_dec(v_pat_775_);
return v_res_782_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default(lean_object* v_a_783_, lean_object* v_a_784_, lean_object* v_a_785_, lean_object* v_a_786_, lean_object* v_a_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = lean_box(1);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___boxed(lean_object* v_a_789_, lean_object* v_a_790_, lean_object* v_a_791_, lean_object* v_a_792_, lean_object* v_a_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default(v_a_789_, v_a_790_, v_a_791_, v_a_792_, v_a_793_);
lean_dec(v_a_793_);
lean_dec_ref(v_a_792_);
lean_dec(v_a_791_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator(lean_object* v_a_795_, lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_){
_start:
{
lean_object* v___x_800_; 
v___x_800_ = lean_box(1);
return v___x_800_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___boxed(lean_object* v_a_801_, lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_){
_start:
{
lean_object* v_res_806_; 
v_res_806_ = l_String_Slice_instInhabitedSplitInclusiveIterator(v_a_801_, v_a_802_, v_a_803_, v_a_804_, v_a_805_);
lean_dec(v_a_805_);
lean_dec_ref(v_a_804_);
lean_dec(v_a_803_);
return v_res_806_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0(lean_object* v_inst_807_, lean_object* v_s_808_, lean_object* v_x_809_){
_start:
{
if (lean_obj_tag(v_x_809_) == 0)
{
lean_object* v_currPos_810_; lean_object* v_searcher_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_863_; 
v_currPos_810_ = lean_ctor_get(v_x_809_, 0);
v_searcher_811_ = lean_ctor_get(v_x_809_, 1);
v_isSharedCheck_863_ = !lean_is_exclusive(v_x_809_);
if (v_isSharedCheck_863_ == 0)
{
v___x_813_ = v_x_809_;
v_isShared_814_ = v_isSharedCheck_863_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_searcher_811_);
lean_inc(v_currPos_810_);
lean_dec(v_x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_863_;
goto v_resetjp_812_;
}
v_resetjp_812_:
{
lean_object* v___x_815_; 
lean_inc_ref(v_s_808_);
v___x_815_ = lean_apply_2(v_inst_807_, v_s_808_, v_searcher_811_);
switch(lean_obj_tag(v___x_815_))
{
case 0:
{
lean_object* v_out_816_; 
v_out_816_ = lean_ctor_get(v___x_815_, 1);
lean_inc(v_out_816_);
if (lean_obj_tag(v_out_816_) == 0)
{
lean_object* v_it_817_; lean_object* v___x_819_; 
lean_dec_ref(v_out_816_);
lean_dec_ref(v_s_808_);
v_it_817_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_it_817_);
lean_dec_ref(v___x_815_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v_it_817_);
v___x_819_ = v___x_813_;
goto v_reusejp_818_;
}
else
{
lean_object* v_reuseFailAlloc_821_; 
v_reuseFailAlloc_821_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_821_, 0, v_currPos_810_);
lean_ctor_set(v_reuseFailAlloc_821_, 1, v_it_817_);
v___x_819_ = v_reuseFailAlloc_821_;
goto v_reusejp_818_;
}
v_reusejp_818_:
{
lean_object* v___x_820_; 
v___x_820_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_820_, 0, v___x_819_);
return v___x_820_;
}
}
else
{
lean_object* v_it_822_; lean_object* v___x_824_; uint8_t v_isShared_825_; uint8_t v_isSharedCheck_834_; 
v_it_822_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_834_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_834_ == 0)
{
lean_object* v_unused_835_; 
v_unused_835_ = lean_ctor_get(v___x_815_, 1);
lean_dec(v_unused_835_);
v___x_824_ = v___x_815_;
v_isShared_825_ = v_isSharedCheck_834_;
goto v_resetjp_823_;
}
else
{
lean_inc(v_it_822_);
lean_dec(v___x_815_);
v___x_824_ = lean_box(0);
v_isShared_825_ = v_isSharedCheck_834_;
goto v_resetjp_823_;
}
v_resetjp_823_:
{
lean_object* v_endPos_826_; lean_object* v_slice_827_; lean_object* v_nextIt_829_; 
v_endPos_826_ = lean_ctor_get(v_out_816_, 1);
lean_inc(v_endPos_826_);
lean_dec_ref(v_out_816_);
v_slice_827_ = l_String_Slice_slice_x21(v_s_808_, v_currPos_810_, v_endPos_826_);
lean_dec(v_currPos_810_);
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v_it_822_);
lean_ctor_set(v___x_813_, 0, v_endPos_826_);
v_nextIt_829_ = v___x_813_;
goto v_reusejp_828_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_endPos_826_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_it_822_);
v_nextIt_829_ = v_reuseFailAlloc_833_;
goto v_reusejp_828_;
}
v_reusejp_828_:
{
lean_object* v___x_831_; 
if (v_isShared_825_ == 0)
{
lean_ctor_set(v___x_824_, 1, v_slice_827_);
lean_ctor_set(v___x_824_, 0, v_nextIt_829_);
v___x_831_ = v___x_824_;
goto v_reusejp_830_;
}
else
{
lean_object* v_reuseFailAlloc_832_; 
v_reuseFailAlloc_832_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_832_, 0, v_nextIt_829_);
lean_ctor_set(v_reuseFailAlloc_832_, 1, v_slice_827_);
v___x_831_ = v_reuseFailAlloc_832_;
goto v_reusejp_830_;
}
v_reusejp_830_:
{
return v___x_831_;
}
}
}
}
}
case 1:
{
lean_object* v_it_836_; lean_object* v___x_838_; uint8_t v_isShared_839_; uint8_t v_isSharedCheck_846_; 
lean_dec_ref(v_s_808_);
v_it_836_ = lean_ctor_get(v___x_815_, 0);
v_isSharedCheck_846_ = !lean_is_exclusive(v___x_815_);
if (v_isSharedCheck_846_ == 0)
{
v___x_838_ = v___x_815_;
v_isShared_839_ = v_isSharedCheck_846_;
goto v_resetjp_837_;
}
else
{
lean_inc(v_it_836_);
lean_dec(v___x_815_);
v___x_838_ = lean_box(0);
v_isShared_839_ = v_isSharedCheck_846_;
goto v_resetjp_837_;
}
v_resetjp_837_:
{
lean_object* v___x_841_; 
if (v_isShared_814_ == 0)
{
lean_ctor_set(v___x_813_, 1, v_it_836_);
v___x_841_ = v___x_813_;
goto v_reusejp_840_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v_currPos_810_);
lean_ctor_set(v_reuseFailAlloc_845_, 1, v_it_836_);
v___x_841_ = v_reuseFailAlloc_845_;
goto v_reusejp_840_;
}
v_reusejp_840_:
{
lean_object* v___x_843_; 
if (v_isShared_839_ == 0)
{
lean_ctor_set(v___x_838_, 0, v___x_841_);
v___x_843_ = v___x_838_;
goto v_reusejp_842_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v___x_841_);
v___x_843_ = v_reuseFailAlloc_844_;
goto v_reusejp_842_;
}
v_reusejp_842_:
{
return v___x_843_;
}
}
}
}
default: 
{
lean_object* v_str_847_; lean_object* v_startInclusive_848_; lean_object* v_endExclusive_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_862_; 
lean_del_object(v___x_813_);
v_str_847_ = lean_ctor_get(v_s_808_, 0);
v_startInclusive_848_ = lean_ctor_get(v_s_808_, 1);
v_endExclusive_849_ = lean_ctor_get(v_s_808_, 2);
v_isSharedCheck_862_ = !lean_is_exclusive(v_s_808_);
if (v_isSharedCheck_862_ == 0)
{
v___x_851_ = v_s_808_;
v_isShared_852_ = v_isSharedCheck_862_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_endExclusive_849_);
lean_inc(v_startInclusive_848_);
lean_inc(v_str_847_);
lean_dec(v_s_808_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_862_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; uint8_t v___x_854_; 
v___x_853_ = lean_nat_sub(v_endExclusive_849_, v_startInclusive_848_);
v___x_854_ = lean_nat_dec_eq(v_currPos_810_, v___x_853_);
lean_dec(v___x_853_);
if (v___x_854_ == 0)
{
lean_object* v___x_855_; lean_object* v_slice_857_; 
v___x_855_ = lean_nat_add(v_startInclusive_848_, v_currPos_810_);
lean_dec(v_currPos_810_);
lean_dec(v_startInclusive_848_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_855_);
v_slice_857_ = v___x_851_;
goto v_reusejp_856_;
}
else
{
lean_object* v_reuseFailAlloc_860_; 
v_reuseFailAlloc_860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_860_, 0, v_str_847_);
lean_ctor_set(v_reuseFailAlloc_860_, 1, v___x_855_);
lean_ctor_set(v_reuseFailAlloc_860_, 2, v_endExclusive_849_);
v_slice_857_ = v_reuseFailAlloc_860_;
goto v_reusejp_856_;
}
v_reusejp_856_:
{
lean_object* v___x_858_; lean_object* v___x_859_; 
v___x_858_ = lean_box(1);
v___x_859_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_859_, 0, v___x_858_);
lean_ctor_set(v___x_859_, 1, v_slice_857_);
return v___x_859_;
}
}
else
{
lean_object* v___x_861_; 
lean_del_object(v___x_851_);
lean_dec(v_endExclusive_849_);
lean_dec(v_startInclusive_848_);
lean_dec_ref(v_str_847_);
lean_dec(v_currPos_810_);
v___x_861_ = lean_box(2);
return v___x_861_;
}
}
}
}
}
}
else
{
lean_object* v___x_864_; 
lean_dec_ref(v_s_808_);
lean_dec(v_inst_807_);
v___x_864_ = lean_box(2);
return v___x_864_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg(lean_object* v_inst_865_, lean_object* v_s_866_){
_start:
{
lean_object* v___f_867_; 
v___f_867_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_867_, 0, v_inst_865_);
lean_closure_set(v___f_867_, 1, v_s_866_);
return v___f_867_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId(lean_object* v_00_u03c1_868_, lean_object* v_00_u03c3_869_, lean_object* v_inst_870_, lean_object* v_pat_871_, lean_object* v_inst_872_, lean_object* v_s_873_){
_start:
{
lean_object* v___f_874_; 
v___f_874_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_874_, 0, v_inst_870_);
lean_closure_set(v___f_874_, 1, v_s_873_);
return v___f_874_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___boxed(lean_object* v_00_u03c1_875_, lean_object* v_00_u03c3_876_, lean_object* v_inst_877_, lean_object* v_pat_878_, lean_object* v_inst_879_, lean_object* v_s_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l_String_Slice_SplitInclusiveIterator_instIteratorId(v_00_u03c1_875_, v_00_u03c3_876_, v_inst_877_, v_pat_878_, v_inst_879_, v_s_880_);
lean_dec(v_inst_879_);
lean_dec(v_pat_878_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(lean_object* v_x_882_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
lean_object* v_searcher_883_; lean_object* v___x_884_; 
v_searcher_883_ = lean_ctor_get(v_x_882_, 1);
lean_inc(v_searcher_883_);
v___x_884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_884_, 0, v_searcher_883_);
return v___x_884_;
}
else
{
lean_object* v___x_885_; 
v___x_885_ = lean_box(0);
return v___x_885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg___boxed(lean_object* v_x_886_){
_start:
{
lean_object* v_res_887_; 
v_res_887_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_886_);
lean_dec(v_x_886_);
return v_res_887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(lean_object* v_00_u03c1_888_, lean_object* v_00_u03c3_889_, lean_object* v_pat_890_, lean_object* v_inst_891_, lean_object* v_s_892_, lean_object* v_x_893_){
_start:
{
lean_object* v___x_894_; 
v___x_894_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_893_);
return v___x_894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___boxed(lean_object* v_00_u03c1_895_, lean_object* v_00_u03c3_896_, lean_object* v_pat_897_, lean_object* v_inst_898_, lean_object* v_s_899_, lean_object* v_x_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(v_00_u03c1_895_, v_00_u03c3_896_, v_pat_897_, v_inst_898_, v_s_899_, v_x_900_);
lean_dec(v_x_900_);
lean_dec_ref(v_s_899_);
lean_dec(v_inst_898_);
lean_dec(v_pat_897_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___redArg(lean_object* v_x_902_, lean_object* v_h__1_903_, lean_object* v_h__2_904_){
_start:
{
if (lean_obj_tag(v_x_902_) == 0)
{
lean_object* v_currPos_905_; lean_object* v_searcher_906_; lean_object* v___x_907_; 
lean_dec(v_h__2_904_);
v_currPos_905_ = lean_ctor_get(v_x_902_, 0);
lean_inc(v_currPos_905_);
v_searcher_906_ = lean_ctor_get(v_x_902_, 1);
lean_inc(v_searcher_906_);
lean_dec_ref(v_x_902_);
v___x_907_ = lean_apply_2(v_h__1_903_, v_currPos_905_, v_searcher_906_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; lean_object* v___x_909_; 
lean_dec(v_h__1_903_);
v___x_908_ = lean_box(0);
v___x_909_ = lean_apply_1(v_h__2_904_, v___x_908_);
return v___x_909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(lean_object* v_00_u03c1_910_, lean_object* v_00_u03c3_911_, lean_object* v_pat_912_, lean_object* v_inst_913_, lean_object* v_s_914_, lean_object* v_motive_915_, lean_object* v_x_916_, lean_object* v_h__1_917_, lean_object* v_h__2_918_){
_start:
{
if (lean_obj_tag(v_x_916_) == 0)
{
lean_object* v_currPos_919_; lean_object* v_searcher_920_; lean_object* v___x_921_; 
lean_dec(v_h__2_918_);
v_currPos_919_ = lean_ctor_get(v_x_916_, 0);
lean_inc(v_currPos_919_);
v_searcher_920_ = lean_ctor_get(v_x_916_, 1);
lean_inc(v_searcher_920_);
lean_dec_ref(v_x_916_);
v___x_921_ = lean_apply_2(v_h__1_917_, v_currPos_919_, v_searcher_920_);
return v___x_921_;
}
else
{
lean_object* v___x_922_; lean_object* v___x_923_; 
lean_dec(v_h__1_917_);
v___x_922_ = lean_box(0);
v___x_923_ = lean_apply_1(v_h__2_918_, v___x_922_);
return v___x_923_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___boxed(lean_object* v_00_u03c1_924_, lean_object* v_00_u03c3_925_, lean_object* v_pat_926_, lean_object* v_inst_927_, lean_object* v_s_928_, lean_object* v_motive_929_, lean_object* v_x_930_, lean_object* v_h__1_931_, lean_object* v_h__2_932_){
_start:
{
lean_object* v_res_933_; 
v_res_933_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(v_00_u03c1_924_, v_00_u03c3_925_, v_pat_926_, v_inst_927_, v_s_928_, v_motive_929_, v_x_930_, v_h__1_931_, v_h__2_932_);
lean_dec_ref(v_s_928_);
lean_dec(v_inst_927_);
lean_dec(v_pat_926_);
return v_res_933_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___redArg(lean_object* v_x_934_, lean_object* v_x_935_, lean_object* v_h__1_936_, lean_object* v_h__2_937_, lean_object* v_h__3_938_, lean_object* v_h__4_939_, lean_object* v_h__5_940_, lean_object* v_h__6_941_, lean_object* v_h__7_942_, lean_object* v_h__8_943_){
_start:
{
if (lean_obj_tag(v_x_934_) == 0)
{
lean_dec(v_h__8_943_);
lean_dec(v_h__7_942_);
lean_dec(v_h__6_941_);
switch(lean_obj_tag(v_x_935_))
{
case 0:
{
lean_object* v_it_944_; 
lean_dec(v_h__5_940_);
lean_dec(v_h__4_939_);
lean_dec(v_h__3_938_);
v_it_944_ = lean_ctor_get(v_x_935_, 0);
if (lean_obj_tag(v_it_944_) == 0)
{
lean_object* v_currPos_945_; lean_object* v_searcher_946_; lean_object* v_out_947_; lean_object* v_currPos_948_; lean_object* v_searcher_949_; lean_object* v___x_950_; 
lean_inc_ref(v_it_944_);
lean_dec(v_h__2_937_);
v_currPos_945_ = lean_ctor_get(v_x_934_, 0);
lean_inc(v_currPos_945_);
v_searcher_946_ = lean_ctor_get(v_x_934_, 1);
lean_inc(v_searcher_946_);
lean_dec_ref(v_x_934_);
v_out_947_ = lean_ctor_get(v_x_935_, 1);
lean_inc(v_out_947_);
lean_dec_ref(v_x_935_);
v_currPos_948_ = lean_ctor_get(v_it_944_, 0);
lean_inc(v_currPos_948_);
v_searcher_949_ = lean_ctor_get(v_it_944_, 1);
lean_inc(v_searcher_949_);
lean_dec_ref(v_it_944_);
v___x_950_ = lean_apply_5(v_h__1_936_, v_currPos_945_, v_searcher_946_, v_currPos_948_, v_searcher_949_, v_out_947_);
return v___x_950_;
}
else
{
lean_object* v_currPos_951_; lean_object* v_searcher_952_; lean_object* v_out_953_; lean_object* v___x_954_; 
lean_dec(v_h__1_936_);
v_currPos_951_ = lean_ctor_get(v_x_934_, 0);
lean_inc(v_currPos_951_);
v_searcher_952_ = lean_ctor_get(v_x_934_, 1);
lean_inc(v_searcher_952_);
lean_dec_ref(v_x_934_);
v_out_953_ = lean_ctor_get(v_x_935_, 1);
lean_inc(v_out_953_);
lean_dec_ref(v_x_935_);
v___x_954_ = lean_apply_3(v_h__2_937_, v_currPos_951_, v_searcher_952_, v_out_953_);
return v___x_954_;
}
}
case 1:
{
lean_object* v_it_955_; 
lean_dec(v_h__5_940_);
lean_dec(v_h__2_937_);
lean_dec(v_h__1_936_);
v_it_955_ = lean_ctor_get(v_x_935_, 0);
lean_inc(v_it_955_);
lean_dec_ref(v_x_935_);
if (lean_obj_tag(v_it_955_) == 0)
{
lean_object* v_currPos_956_; lean_object* v_searcher_957_; lean_object* v_currPos_958_; lean_object* v_searcher_959_; lean_object* v___x_960_; 
lean_dec(v_h__4_939_);
v_currPos_956_ = lean_ctor_get(v_x_934_, 0);
lean_inc(v_currPos_956_);
v_searcher_957_ = lean_ctor_get(v_x_934_, 1);
lean_inc(v_searcher_957_);
lean_dec_ref(v_x_934_);
v_currPos_958_ = lean_ctor_get(v_it_955_, 0);
lean_inc(v_currPos_958_);
v_searcher_959_ = lean_ctor_get(v_it_955_, 1);
lean_inc(v_searcher_959_);
lean_dec_ref(v_it_955_);
v___x_960_ = lean_apply_4(v_h__3_938_, v_currPos_956_, v_searcher_957_, v_currPos_958_, v_searcher_959_);
return v___x_960_;
}
else
{
lean_object* v_currPos_961_; lean_object* v_searcher_962_; lean_object* v___x_963_; 
lean_dec(v_h__3_938_);
v_currPos_961_ = lean_ctor_get(v_x_934_, 0);
lean_inc(v_currPos_961_);
v_searcher_962_ = lean_ctor_get(v_x_934_, 1);
lean_inc(v_searcher_962_);
lean_dec_ref(v_x_934_);
v___x_963_ = lean_apply_2(v_h__4_939_, v_currPos_961_, v_searcher_962_);
return v___x_963_;
}
}
default: 
{
lean_object* v_currPos_964_; lean_object* v_searcher_965_; lean_object* v___x_966_; 
lean_dec(v_h__4_939_);
lean_dec(v_h__3_938_);
lean_dec(v_h__2_937_);
lean_dec(v_h__1_936_);
v_currPos_964_ = lean_ctor_get(v_x_934_, 0);
lean_inc(v_currPos_964_);
v_searcher_965_ = lean_ctor_get(v_x_934_, 1);
lean_inc(v_searcher_965_);
lean_dec_ref(v_x_934_);
v___x_966_ = lean_apply_2(v_h__5_940_, v_currPos_964_, v_searcher_965_);
return v___x_966_;
}
}
}
else
{
lean_dec(v_h__5_940_);
lean_dec(v_h__4_939_);
lean_dec(v_h__3_938_);
lean_dec(v_h__2_937_);
lean_dec(v_h__1_936_);
switch(lean_obj_tag(v_x_935_))
{
case 0:
{
lean_object* v_it_967_; lean_object* v_out_968_; lean_object* v___x_969_; 
lean_dec(v_h__8_943_);
lean_dec(v_h__7_942_);
v_it_967_ = lean_ctor_get(v_x_935_, 0);
lean_inc(v_it_967_);
v_out_968_ = lean_ctor_get(v_x_935_, 1);
lean_inc(v_out_968_);
lean_dec_ref(v_x_935_);
v___x_969_ = lean_apply_2(v_h__6_941_, v_it_967_, v_out_968_);
return v___x_969_;
}
case 1:
{
lean_object* v_it_970_; lean_object* v___x_971_; 
lean_dec(v_h__8_943_);
lean_dec(v_h__6_941_);
v_it_970_ = lean_ctor_get(v_x_935_, 0);
lean_inc(v_it_970_);
lean_dec_ref(v_x_935_);
v___x_971_ = lean_apply_1(v_h__7_942_, v_it_970_);
return v___x_971_;
}
default: 
{
lean_object* v___x_972_; lean_object* v___x_973_; 
lean_dec(v_h__7_942_);
lean_dec(v_h__6_941_);
v___x_972_ = lean_box(0);
v___x_973_ = lean_apply_1(v_h__8_943_, v___x_972_);
return v___x_973_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(lean_object* v_00_u03c1_974_, lean_object* v_00_u03c3_975_, lean_object* v_pat_976_, lean_object* v_inst_977_, lean_object* v_s_978_, lean_object* v_motive_979_, lean_object* v_x_980_, lean_object* v_x_981_, lean_object* v_h__1_982_, lean_object* v_h__2_983_, lean_object* v_h__3_984_, lean_object* v_h__4_985_, lean_object* v_h__5_986_, lean_object* v_h__6_987_, lean_object* v_h__7_988_, lean_object* v_h__8_989_){
_start:
{
if (lean_obj_tag(v_x_980_) == 0)
{
lean_dec(v_h__8_989_);
lean_dec(v_h__7_988_);
lean_dec(v_h__6_987_);
switch(lean_obj_tag(v_x_981_))
{
case 0:
{
lean_object* v_it_990_; 
lean_dec(v_h__5_986_);
lean_dec(v_h__4_985_);
lean_dec(v_h__3_984_);
v_it_990_ = lean_ctor_get(v_x_981_, 0);
if (lean_obj_tag(v_it_990_) == 0)
{
lean_object* v_currPos_991_; lean_object* v_searcher_992_; lean_object* v_out_993_; lean_object* v_currPos_994_; lean_object* v_searcher_995_; lean_object* v___x_996_; 
lean_inc_ref(v_it_990_);
lean_dec(v_h__2_983_);
v_currPos_991_ = lean_ctor_get(v_x_980_, 0);
lean_inc(v_currPos_991_);
v_searcher_992_ = lean_ctor_get(v_x_980_, 1);
lean_inc(v_searcher_992_);
lean_dec_ref(v_x_980_);
v_out_993_ = lean_ctor_get(v_x_981_, 1);
lean_inc(v_out_993_);
lean_dec_ref(v_x_981_);
v_currPos_994_ = lean_ctor_get(v_it_990_, 0);
lean_inc(v_currPos_994_);
v_searcher_995_ = lean_ctor_get(v_it_990_, 1);
lean_inc(v_searcher_995_);
lean_dec_ref(v_it_990_);
v___x_996_ = lean_apply_5(v_h__1_982_, v_currPos_991_, v_searcher_992_, v_currPos_994_, v_searcher_995_, v_out_993_);
return v___x_996_;
}
else
{
lean_object* v_currPos_997_; lean_object* v_searcher_998_; lean_object* v_out_999_; lean_object* v___x_1000_; 
lean_dec(v_h__1_982_);
v_currPos_997_ = lean_ctor_get(v_x_980_, 0);
lean_inc(v_currPos_997_);
v_searcher_998_ = lean_ctor_get(v_x_980_, 1);
lean_inc(v_searcher_998_);
lean_dec_ref(v_x_980_);
v_out_999_ = lean_ctor_get(v_x_981_, 1);
lean_inc(v_out_999_);
lean_dec_ref(v_x_981_);
v___x_1000_ = lean_apply_3(v_h__2_983_, v_currPos_997_, v_searcher_998_, v_out_999_);
return v___x_1000_;
}
}
case 1:
{
lean_object* v_it_1001_; 
lean_dec(v_h__5_986_);
lean_dec(v_h__2_983_);
lean_dec(v_h__1_982_);
v_it_1001_ = lean_ctor_get(v_x_981_, 0);
lean_inc(v_it_1001_);
lean_dec_ref(v_x_981_);
if (lean_obj_tag(v_it_1001_) == 0)
{
lean_object* v_currPos_1002_; lean_object* v_searcher_1003_; lean_object* v_currPos_1004_; lean_object* v_searcher_1005_; lean_object* v___x_1006_; 
lean_dec(v_h__4_985_);
v_currPos_1002_ = lean_ctor_get(v_x_980_, 0);
lean_inc(v_currPos_1002_);
v_searcher_1003_ = lean_ctor_get(v_x_980_, 1);
lean_inc(v_searcher_1003_);
lean_dec_ref(v_x_980_);
v_currPos_1004_ = lean_ctor_get(v_it_1001_, 0);
lean_inc(v_currPos_1004_);
v_searcher_1005_ = lean_ctor_get(v_it_1001_, 1);
lean_inc(v_searcher_1005_);
lean_dec_ref(v_it_1001_);
v___x_1006_ = lean_apply_4(v_h__3_984_, v_currPos_1002_, v_searcher_1003_, v_currPos_1004_, v_searcher_1005_);
return v___x_1006_;
}
else
{
lean_object* v_currPos_1007_; lean_object* v_searcher_1008_; lean_object* v___x_1009_; 
lean_dec(v_h__3_984_);
v_currPos_1007_ = lean_ctor_get(v_x_980_, 0);
lean_inc(v_currPos_1007_);
v_searcher_1008_ = lean_ctor_get(v_x_980_, 1);
lean_inc(v_searcher_1008_);
lean_dec_ref(v_x_980_);
v___x_1009_ = lean_apply_2(v_h__4_985_, v_currPos_1007_, v_searcher_1008_);
return v___x_1009_;
}
}
default: 
{
lean_object* v_currPos_1010_; lean_object* v_searcher_1011_; lean_object* v___x_1012_; 
lean_dec(v_h__4_985_);
lean_dec(v_h__3_984_);
lean_dec(v_h__2_983_);
lean_dec(v_h__1_982_);
v_currPos_1010_ = lean_ctor_get(v_x_980_, 0);
lean_inc(v_currPos_1010_);
v_searcher_1011_ = lean_ctor_get(v_x_980_, 1);
lean_inc(v_searcher_1011_);
lean_dec_ref(v_x_980_);
v___x_1012_ = lean_apply_2(v_h__5_986_, v_currPos_1010_, v_searcher_1011_);
return v___x_1012_;
}
}
}
else
{
lean_dec(v_h__5_986_);
lean_dec(v_h__4_985_);
lean_dec(v_h__3_984_);
lean_dec(v_h__2_983_);
lean_dec(v_h__1_982_);
switch(lean_obj_tag(v_x_981_))
{
case 0:
{
lean_object* v_it_1013_; lean_object* v_out_1014_; lean_object* v___x_1015_; 
lean_dec(v_h__8_989_);
lean_dec(v_h__7_988_);
v_it_1013_ = lean_ctor_get(v_x_981_, 0);
lean_inc(v_it_1013_);
v_out_1014_ = lean_ctor_get(v_x_981_, 1);
lean_inc(v_out_1014_);
lean_dec_ref(v_x_981_);
v___x_1015_ = lean_apply_2(v_h__6_987_, v_it_1013_, v_out_1014_);
return v___x_1015_;
}
case 1:
{
lean_object* v_it_1016_; lean_object* v___x_1017_; 
lean_dec(v_h__8_989_);
lean_dec(v_h__6_987_);
v_it_1016_ = lean_ctor_get(v_x_981_, 0);
lean_inc(v_it_1016_);
lean_dec_ref(v_x_981_);
v___x_1017_ = lean_apply_1(v_h__7_988_, v_it_1016_);
return v___x_1017_;
}
default: 
{
lean_object* v___x_1018_; lean_object* v___x_1019_; 
lean_dec(v_h__7_988_);
lean_dec(v_h__6_987_);
v___x_1018_ = lean_box(0);
v___x_1019_ = lean_apply_1(v_h__8_989_, v___x_1018_);
return v___x_1019_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___boxed(lean_object* v_00_u03c1_1020_, lean_object* v_00_u03c3_1021_, lean_object* v_pat_1022_, lean_object* v_inst_1023_, lean_object* v_s_1024_, lean_object* v_motive_1025_, lean_object* v_x_1026_, lean_object* v_x_1027_, lean_object* v_h__1_1028_, lean_object* v_h__2_1029_, lean_object* v_h__3_1030_, lean_object* v_h__4_1031_, lean_object* v_h__5_1032_, lean_object* v_h__6_1033_, lean_object* v_h__7_1034_, lean_object* v_h__8_1035_){
_start:
{
lean_object* v_res_1036_; 
v_res_1036_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(v_00_u03c1_1020_, v_00_u03c3_1021_, v_pat_1022_, v_inst_1023_, v_s_1024_, v_motive_1025_, v_x_1026_, v_x_1027_, v_h__1_1028_, v_h__2_1029_, v_h__3_1030_, v_h__4_1031_, v_h__5_1032_, v_h__6_1033_, v_h__7_1034_, v_h__8_1035_);
lean_dec_ref(v_s_1024_);
lean_dec(v_inst_1023_);
lean_dec(v_pat_1022_);
return v_res_1036_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___redArg(lean_object* v_x_1037_, lean_object* v_h__1_1038_, lean_object* v_h__2_1039_){
_start:
{
if (lean_obj_tag(v_x_1037_) == 0)
{
lean_object* v_currPos_1040_; lean_object* v_searcher_1041_; lean_object* v___x_1042_; 
lean_dec(v_h__2_1039_);
v_currPos_1040_ = lean_ctor_get(v_x_1037_, 0);
lean_inc(v_currPos_1040_);
v_searcher_1041_ = lean_ctor_get(v_x_1037_, 1);
lean_inc(v_searcher_1041_);
lean_dec_ref(v_x_1037_);
v___x_1042_ = lean_apply_2(v_h__1_1038_, v_currPos_1040_, v_searcher_1041_);
return v___x_1042_;
}
else
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
lean_dec(v_h__1_1038_);
v___x_1043_ = lean_box(0);
v___x_1044_ = lean_apply_1(v_h__2_1039_, v___x_1043_);
return v___x_1044_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_1045_, lean_object* v_00_u03c3_1046_, lean_object* v_pat_1047_, lean_object* v_inst_1048_, lean_object* v_s_1049_, lean_object* v_motive_1050_, lean_object* v_x_1051_, lean_object* v_h__1_1052_, lean_object* v_h__2_1053_){
_start:
{
if (lean_obj_tag(v_x_1051_) == 0)
{
lean_object* v_currPos_1054_; lean_object* v_searcher_1055_; lean_object* v___x_1056_; 
lean_dec(v_h__2_1053_);
v_currPos_1054_ = lean_ctor_get(v_x_1051_, 0);
lean_inc(v_currPos_1054_);
v_searcher_1055_ = lean_ctor_get(v_x_1051_, 1);
lean_inc(v_searcher_1055_);
lean_dec_ref(v_x_1051_);
v___x_1056_ = lean_apply_2(v_h__1_1052_, v_currPos_1054_, v_searcher_1055_);
return v___x_1056_;
}
else
{
lean_object* v___x_1057_; lean_object* v___x_1058_; 
lean_dec(v_h__1_1052_);
v___x_1057_ = lean_box(0);
v___x_1058_ = lean_apply_1(v_h__2_1053_, v___x_1057_);
return v___x_1058_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_1059_, lean_object* v_00_u03c3_1060_, lean_object* v_pat_1061_, lean_object* v_inst_1062_, lean_object* v_s_1063_, lean_object* v_motive_1064_, lean_object* v_x_1065_, lean_object* v_h__1_1066_, lean_object* v_h__2_1067_){
_start:
{
lean_object* v_res_1068_; 
v_res_1068_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(v_00_u03c1_1059_, v_00_u03c3_1060_, v_pat_1061_, v_inst_1062_, v_s_1063_, v_motive_1064_, v_x_1065_, v_h__1_1066_, v_h__2_1067_);
lean_dec_ref(v_s_1063_);
lean_dec(v_inst_1062_);
lean_dec(v_pat_1061_);
return v_res_1068_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(lean_object* v_00_u03c1_1069_, lean_object* v_00_u03c3_1070_, lean_object* v_inst_1071_, lean_object* v_pat_1072_, lean_object* v_inst_1073_, lean_object* v_s_1074_, lean_object* v_inst_1075_){
_start:
{
lean_object* v___x_1076_; 
v___x_1076_ = lean_box(0);
return v___x_1076_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_1077_, lean_object* v_00_u03c3_1078_, lean_object* v_inst_1079_, lean_object* v_pat_1080_, lean_object* v_inst_1081_, lean_object* v_s_1082_, lean_object* v_inst_1083_){
_start:
{
lean_object* v_res_1084_; 
v_res_1084_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(v_00_u03c1_1077_, v_00_u03c3_1078_, v_inst_1079_, v_pat_1080_, v_inst_1081_, v_s_1082_, v_inst_1083_);
lean_dec_ref(v_s_1082_);
lean_dec(v_inst_1081_);
lean_dec(v_pat_1080_);
lean_dec(v_inst_1079_);
return v_res_1084_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0(lean_object* v_toPure_1085_, lean_object* v_recur_1086_, lean_object* v_it_1087_, lean_object* v_____do__lift_1088_){
_start:
{
if (lean_obj_tag(v_____do__lift_1088_) == 0)
{
lean_object* v_a_1089_; lean_object* v___x_1090_; 
lean_dec(v_it_1087_);
lean_dec(v_recur_1086_);
v_a_1089_ = lean_ctor_get(v_____do__lift_1088_, 0);
lean_inc(v_a_1089_);
lean_dec_ref(v_____do__lift_1088_);
v___x_1090_ = lean_apply_2(v_toPure_1085_, lean_box(0), v_a_1089_);
return v___x_1090_;
}
else
{
lean_object* v_a_1091_; lean_object* v___x_1092_; 
lean_dec(v_toPure_1085_);
v_a_1091_ = lean_ctor_get(v_____do__lift_1088_, 0);
lean_inc(v_a_1091_);
lean_dec_ref(v_____do__lift_1088_);
v___x_1092_ = lean_apply_4(v_recur_1086_, v_it_1087_, v_a_1091_, lean_box(0), lean_box(0));
return v___x_1092_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1(lean_object* v_toPure_1093_, lean_object* v_recur_1094_, lean_object* v___y_1095_, lean_object* v_acc_1096_, lean_object* v_toBind_1097_, lean_object* v_s_1098_){
_start:
{
switch(lean_obj_tag(v_s_1098_))
{
case 0:
{
lean_object* v_it_1099_; lean_object* v_out_1100_; lean_object* v___f_1101_; lean_object* v___x_1102_; lean_object* v___x_1103_; 
v_it_1099_ = lean_ctor_get(v_s_1098_, 0);
lean_inc(v_it_1099_);
v_out_1100_ = lean_ctor_get(v_s_1098_, 1);
lean_inc(v_out_1100_);
lean_dec_ref(v_s_1098_);
v___f_1101_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1101_, 0, v_toPure_1093_);
lean_closure_set(v___f_1101_, 1, v_recur_1094_);
lean_closure_set(v___f_1101_, 2, v_it_1099_);
v___x_1102_ = lean_apply_3(v___y_1095_, v_out_1100_, lean_box(0), v_acc_1096_);
v___x_1103_ = lean_apply_4(v_toBind_1097_, lean_box(0), lean_box(0), v___x_1102_, v___f_1101_);
return v___x_1103_;
}
case 1:
{
lean_object* v_it_1104_; lean_object* v___x_1105_; 
lean_dec(v_toBind_1097_);
lean_dec(v___y_1095_);
lean_dec(v_toPure_1093_);
v_it_1104_ = lean_ctor_get(v_s_1098_, 0);
lean_inc(v_it_1104_);
lean_dec_ref(v_s_1098_);
v___x_1105_ = lean_apply_4(v_recur_1094_, v_it_1104_, v_acc_1096_, lean_box(0), lean_box(0));
return v___x_1105_;
}
default: 
{
lean_object* v___x_1106_; 
lean_dec(v_toBind_1097_);
lean_dec(v___y_1095_);
lean_dec(v_recur_1094_);
v___x_1106_ = lean_apply_2(v_toPure_1093_, lean_box(0), v_acc_1096_);
return v___x_1106_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2(lean_object* v_toPure_1107_, lean_object* v___y_1108_, lean_object* v_toBind_1109_, lean_object* v_inst_1110_, lean_object* v_s_1111_, lean_object* v_lift_1112_, lean_object* v_it_1113_, lean_object* v_acc_1114_, lean_object* v_hP_1115_, lean_object* v_recur_1116_){
_start:
{
lean_object* v___f_1117_; 
v___f_1117_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_1117_, 0, v_toPure_1107_);
lean_closure_set(v___f_1117_, 1, v_recur_1116_);
lean_closure_set(v___f_1117_, 2, v___y_1108_);
lean_closure_set(v___f_1117_, 3, v_acc_1114_);
lean_closure_set(v___f_1117_, 4, v_toBind_1109_);
if (lean_obj_tag(v_it_1113_) == 0)
{
lean_object* v_currPos_1118_; lean_object* v_searcher_1119_; lean_object* v___x_1121_; uint8_t v_isShared_1122_; uint8_t v_isSharedCheck_1176_; 
v_currPos_1118_ = lean_ctor_get(v_it_1113_, 0);
v_searcher_1119_ = lean_ctor_get(v_it_1113_, 1);
v_isSharedCheck_1176_ = !lean_is_exclusive(v_it_1113_);
if (v_isSharedCheck_1176_ == 0)
{
v___x_1121_ = v_it_1113_;
v_isShared_1122_ = v_isSharedCheck_1176_;
goto v_resetjp_1120_;
}
else
{
lean_inc(v_searcher_1119_);
lean_inc(v_currPos_1118_);
lean_dec(v_it_1113_);
v___x_1121_ = lean_box(0);
v_isShared_1122_ = v_isSharedCheck_1176_;
goto v_resetjp_1120_;
}
v_resetjp_1120_:
{
lean_object* v___x_1123_; 
lean_inc_ref(v_s_1111_);
v___x_1123_ = lean_apply_2(v_inst_1110_, v_s_1111_, v_searcher_1119_);
switch(lean_obj_tag(v___x_1123_))
{
case 0:
{
lean_object* v_out_1124_; 
v_out_1124_ = lean_ctor_get(v___x_1123_, 1);
lean_inc(v_out_1124_);
if (lean_obj_tag(v_out_1124_) == 0)
{
lean_object* v_it_1125_; lean_object* v___x_1127_; 
lean_dec_ref(v_out_1124_);
lean_dec_ref(v_s_1111_);
v_it_1125_ = lean_ctor_get(v___x_1123_, 0);
lean_inc(v_it_1125_);
lean_dec_ref(v___x_1123_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v_it_1125_);
v___x_1127_ = v___x_1121_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_currPos_1118_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_it_1125_);
v___x_1127_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; lean_object* v___x_1129_; 
v___x_1128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1128_, 0, v___x_1127_);
v___x_1129_ = lean_apply_4(v_lift_1112_, lean_box(0), lean_box(0), v___f_1117_, v___x_1128_);
return v___x_1129_;
}
}
else
{
lean_object* v_it_1131_; lean_object* v___x_1133_; uint8_t v_isShared_1134_; uint8_t v_isSharedCheck_1144_; 
v_it_1131_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1144_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1144_ == 0)
{
lean_object* v_unused_1145_; 
v_unused_1145_ = lean_ctor_get(v___x_1123_, 1);
lean_dec(v_unused_1145_);
v___x_1133_ = v___x_1123_;
v_isShared_1134_ = v_isSharedCheck_1144_;
goto v_resetjp_1132_;
}
else
{
lean_inc(v_it_1131_);
lean_dec(v___x_1123_);
v___x_1133_ = lean_box(0);
v_isShared_1134_ = v_isSharedCheck_1144_;
goto v_resetjp_1132_;
}
v_resetjp_1132_:
{
lean_object* v_endPos_1135_; lean_object* v_slice_1136_; lean_object* v_nextIt_1138_; 
v_endPos_1135_ = lean_ctor_get(v_out_1124_, 1);
lean_inc(v_endPos_1135_);
lean_dec_ref(v_out_1124_);
v_slice_1136_ = l_String_Slice_slice_x21(v_s_1111_, v_currPos_1118_, v_endPos_1135_);
lean_dec(v_currPos_1118_);
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v_it_1131_);
lean_ctor_set(v___x_1121_, 0, v_endPos_1135_);
v_nextIt_1138_ = v___x_1121_;
goto v_reusejp_1137_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_endPos_1135_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_it_1131_);
v_nextIt_1138_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1137_;
}
v_reusejp_1137_:
{
lean_object* v___x_1140_; 
if (v_isShared_1134_ == 0)
{
lean_ctor_set(v___x_1133_, 1, v_slice_1136_);
lean_ctor_set(v___x_1133_, 0, v_nextIt_1138_);
v___x_1140_ = v___x_1133_;
goto v_reusejp_1139_;
}
else
{
lean_object* v_reuseFailAlloc_1142_; 
v_reuseFailAlloc_1142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1142_, 0, v_nextIt_1138_);
lean_ctor_set(v_reuseFailAlloc_1142_, 1, v_slice_1136_);
v___x_1140_ = v_reuseFailAlloc_1142_;
goto v_reusejp_1139_;
}
v_reusejp_1139_:
{
lean_object* v___x_1141_; 
v___x_1141_ = lean_apply_4(v_lift_1112_, lean_box(0), lean_box(0), v___f_1117_, v___x_1140_);
return v___x_1141_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1157_; 
lean_dec_ref(v_s_1111_);
v_it_1146_ = lean_ctor_get(v___x_1123_, 0);
v_isSharedCheck_1157_ = !lean_is_exclusive(v___x_1123_);
if (v_isSharedCheck_1157_ == 0)
{
v___x_1148_ = v___x_1123_;
v_isShared_1149_ = v_isSharedCheck_1157_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_it_1146_);
lean_dec(v___x_1123_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1157_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1151_; 
if (v_isShared_1122_ == 0)
{
lean_ctor_set(v___x_1121_, 1, v_it_1146_);
v___x_1151_ = v___x_1121_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v_currPos_1118_);
lean_ctor_set(v_reuseFailAlloc_1156_, 1, v_it_1146_);
v___x_1151_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1153_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 0, v___x_1151_);
v___x_1153_ = v___x_1148_;
goto v_reusejp_1152_;
}
else
{
lean_object* v_reuseFailAlloc_1155_; 
v_reuseFailAlloc_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1155_, 0, v___x_1151_);
v___x_1153_ = v_reuseFailAlloc_1155_;
goto v_reusejp_1152_;
}
v_reusejp_1152_:
{
lean_object* v___x_1154_; 
v___x_1154_ = lean_apply_4(v_lift_1112_, lean_box(0), lean_box(0), v___f_1117_, v___x_1153_);
return v___x_1154_;
}
}
}
}
default: 
{
lean_object* v_str_1158_; lean_object* v_startInclusive_1159_; lean_object* v_endExclusive_1160_; lean_object* v___x_1162_; uint8_t v_isShared_1163_; uint8_t v_isSharedCheck_1175_; 
lean_del_object(v___x_1121_);
v_str_1158_ = lean_ctor_get(v_s_1111_, 0);
v_startInclusive_1159_ = lean_ctor_get(v_s_1111_, 1);
v_endExclusive_1160_ = lean_ctor_get(v_s_1111_, 2);
v_isSharedCheck_1175_ = !lean_is_exclusive(v_s_1111_);
if (v_isSharedCheck_1175_ == 0)
{
v___x_1162_ = v_s_1111_;
v_isShared_1163_ = v_isSharedCheck_1175_;
goto v_resetjp_1161_;
}
else
{
lean_inc(v_endExclusive_1160_);
lean_inc(v_startInclusive_1159_);
lean_inc(v_str_1158_);
lean_dec(v_s_1111_);
v___x_1162_ = lean_box(0);
v_isShared_1163_ = v_isSharedCheck_1175_;
goto v_resetjp_1161_;
}
v_resetjp_1161_:
{
lean_object* v___x_1164_; uint8_t v___x_1165_; 
v___x_1164_ = lean_nat_sub(v_endExclusive_1160_, v_startInclusive_1159_);
v___x_1165_ = lean_nat_dec_eq(v_currPos_1118_, v___x_1164_);
lean_dec(v___x_1164_);
if (v___x_1165_ == 0)
{
lean_object* v___x_1166_; lean_object* v_slice_1168_; 
v___x_1166_ = lean_nat_add(v_startInclusive_1159_, v_currPos_1118_);
lean_dec(v_currPos_1118_);
lean_dec(v_startInclusive_1159_);
if (v_isShared_1163_ == 0)
{
lean_ctor_set(v___x_1162_, 1, v___x_1166_);
v_slice_1168_ = v___x_1162_;
goto v_reusejp_1167_;
}
else
{
lean_object* v_reuseFailAlloc_1172_; 
v_reuseFailAlloc_1172_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1172_, 0, v_str_1158_);
lean_ctor_set(v_reuseFailAlloc_1172_, 1, v___x_1166_);
lean_ctor_set(v_reuseFailAlloc_1172_, 2, v_endExclusive_1160_);
v_slice_1168_ = v_reuseFailAlloc_1172_;
goto v_reusejp_1167_;
}
v_reusejp_1167_:
{
lean_object* v___x_1169_; lean_object* v___x_1170_; lean_object* v___x_1171_; 
v___x_1169_ = lean_box(1);
v___x_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1170_, 0, v___x_1169_);
lean_ctor_set(v___x_1170_, 1, v_slice_1168_);
v___x_1171_ = lean_apply_4(v_lift_1112_, lean_box(0), lean_box(0), v___f_1117_, v___x_1170_);
return v___x_1171_;
}
}
else
{
lean_object* v___x_1173_; lean_object* v___x_1174_; 
lean_del_object(v___x_1162_);
lean_dec(v_endExclusive_1160_);
lean_dec(v_startInclusive_1159_);
lean_dec_ref(v_str_1158_);
lean_dec(v_currPos_1118_);
v___x_1173_ = lean_box(2);
v___x_1174_ = lean_apply_4(v_lift_1112_, lean_box(0), lean_box(0), v___f_1117_, v___x_1173_);
return v___x_1174_;
}
}
}
}
}
}
else
{
lean_object* v___x_1177_; lean_object* v___x_1178_; 
lean_dec_ref(v_s_1111_);
lean_dec(v_inst_1110_);
v___x_1177_ = lean_box(2);
v___x_1178_ = lean_apply_4(v_lift_1112_, lean_box(0), lean_box(0), v___f_1117_, v___x_1177_);
return v___x_1178_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3(lean_object* v_inst_1179_, lean_object* v_inst_1180_, lean_object* v_s_1181_, lean_object* v_lift_1182_, lean_object* v_00_u03b3_1183_, lean_object* v_Pl_1184_, lean_object* v_it_1185_, lean_object* v_init_1186_, lean_object* v___y_1187_){
_start:
{
lean_object* v_toApplicative_1188_; lean_object* v_toBind_1189_; lean_object* v_toPure_1190_; lean_object* v___f_1191_; lean_object* v___x_1192_; 
v_toApplicative_1188_ = lean_ctor_get(v_inst_1179_, 0);
lean_inc_ref(v_toApplicative_1188_);
v_toBind_1189_ = lean_ctor_get(v_inst_1179_, 1);
lean_inc(v_toBind_1189_);
lean_dec_ref(v_inst_1179_);
v_toPure_1190_ = lean_ctor_get(v_toApplicative_1188_, 1);
lean_inc(v_toPure_1190_);
lean_dec_ref(v_toApplicative_1188_);
v___f_1191_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_1191_, 0, v_toPure_1190_);
lean_closure_set(v___f_1191_, 1, v___y_1187_);
lean_closure_set(v___f_1191_, 2, v_toBind_1189_);
lean_closure_set(v___f_1191_, 3, v_inst_1180_);
lean_closure_set(v___f_1191_, 4, v_s_1181_);
lean_closure_set(v___f_1191_, 5, v_lift_1182_);
v___x_1192_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1191_, v_it_1185_, v_init_1186_, lean_box(0));
return v___x_1192_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg(lean_object* v_inst_1193_, lean_object* v_inst_1194_, lean_object* v_s_1195_){
_start:
{
lean_object* v___f_1196_; 
v___f_1196_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1196_, 0, v_inst_1194_);
lean_closure_set(v___f_1196_, 1, v_inst_1193_);
lean_closure_set(v___f_1196_, 2, v_s_1195_);
return v___f_1196_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(lean_object* v_00_u03c1_1197_, lean_object* v_00_u03c3_1198_, lean_object* v_inst_1199_, lean_object* v_pat_1200_, lean_object* v_inst_1201_, lean_object* v_n_1202_, lean_object* v_inst_1203_, lean_object* v_s_1204_){
_start:
{
lean_object* v___f_1205_; 
v___f_1205_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1205_, 0, v_inst_1203_);
lean_closure_set(v___f_1205_, 1, v_inst_1199_);
lean_closure_set(v___f_1205_, 2, v_s_1204_);
return v___f_1205_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___boxed(lean_object* v_00_u03c1_1206_, lean_object* v_00_u03c3_1207_, lean_object* v_inst_1208_, lean_object* v_pat_1209_, lean_object* v_inst_1210_, lean_object* v_n_1211_, lean_object* v_inst_1212_, lean_object* v_s_1213_){
_start:
{
lean_object* v_res_1214_; 
v_res_1214_ = l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(v_00_u03c1_1206_, v_00_u03c3_1207_, v_inst_1208_, v_pat_1209_, v_inst_1210_, v_n_1211_, v_inst_1212_, v_s_1213_);
lean_dec(v_inst_1210_);
lean_dec(v_pat_1209_);
return v_res_1214_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___redArg(lean_object* v_s_1215_, lean_object* v_inst_1216_){
_start:
{
lean_object* v___x_1217_; lean_object* v___x_1218_; lean_object* v___x_1219_; 
v___x_1217_ = lean_unsigned_to_nat(0u);
v___x_1218_ = lean_apply_1(v_inst_1216_, v_s_1215_);
v___x_1219_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1219_, 0, v___x_1217_);
lean_ctor_set(v___x_1219_, 1, v___x_1218_);
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive(lean_object* v_00_u03c1_1220_, lean_object* v_00_u03c3_1221_, lean_object* v_s_1222_, lean_object* v_pat_1223_, lean_object* v_inst_1224_){
_start:
{
lean_object* v___x_1225_; 
v___x_1225_ = l_String_Slice_splitInclusive___redArg(v_s_1222_, v_inst_1224_);
return v___x_1225_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___boxed(lean_object* v_00_u03c1_1226_, lean_object* v_00_u03c3_1227_, lean_object* v_s_1228_, lean_object* v_pat_1229_, lean_object* v_inst_1230_){
_start:
{
lean_object* v_res_1231_; 
v_res_1231_ = l_String_Slice_splitInclusive(v_00_u03c1_1226_, v_00_u03c3_1227_, v_s_1228_, v_pat_1229_, v_inst_1230_);
lean_dec(v_pat_1229_);
return v_res_1231_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___redArg(lean_object* v_s_1232_, lean_object* v_inst_1233_){
_start:
{
lean_object* v_skipPrefix_x3f_1234_; lean_object* v___x_1235_; 
v_skipPrefix_x3f_1234_ = lean_ctor_get(v_inst_1233_, 0);
lean_inc_ref(v_skipPrefix_x3f_1234_);
lean_dec_ref(v_inst_1233_);
v___x_1235_ = lean_apply_1(v_skipPrefix_x3f_1234_, v_s_1232_);
return v___x_1235_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f(lean_object* v_00_u03c1_1236_, lean_object* v_s_1237_, lean_object* v_pat_1238_, lean_object* v_inst_1239_){
_start:
{
lean_object* v_skipPrefix_x3f_1240_; lean_object* v___x_1241_; 
v_skipPrefix_x3f_1240_ = lean_ctor_get(v_inst_1239_, 0);
lean_inc_ref(v_skipPrefix_x3f_1240_);
lean_dec_ref(v_inst_1239_);
v___x_1241_ = lean_apply_1(v_skipPrefix_x3f_1240_, v_s_1237_);
return v___x_1241_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___boxed(lean_object* v_00_u03c1_1242_, lean_object* v_s_1243_, lean_object* v_pat_1244_, lean_object* v_inst_1245_){
_start:
{
lean_object* v_res_1246_; 
v_res_1246_ = l_String_Slice_skipPrefix_x3f(v_00_u03c1_1242_, v_s_1243_, v_pat_1244_, v_inst_1245_);
lean_dec(v_pat_1244_);
return v_res_1246_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg(lean_object* v_s_1247_, lean_object* v_pos_1248_, lean_object* v_inst_1249_){
_start:
{
lean_object* v_str_1250_; lean_object* v_startInclusive_1251_; lean_object* v_endExclusive_1252_; lean_object* v___x_1254_; uint8_t v_isShared_1255_; uint8_t v_isSharedCheck_1271_; 
v_str_1250_ = lean_ctor_get(v_s_1247_, 0);
v_startInclusive_1251_ = lean_ctor_get(v_s_1247_, 1);
v_endExclusive_1252_ = lean_ctor_get(v_s_1247_, 2);
v_isSharedCheck_1271_ = !lean_is_exclusive(v_s_1247_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1254_ = v_s_1247_;
v_isShared_1255_ = v_isSharedCheck_1271_;
goto v_resetjp_1253_;
}
else
{
lean_inc(v_endExclusive_1252_);
lean_inc(v_startInclusive_1251_);
lean_inc(v_str_1250_);
lean_dec(v_s_1247_);
v___x_1254_ = lean_box(0);
v_isShared_1255_ = v_isSharedCheck_1271_;
goto v_resetjp_1253_;
}
v_resetjp_1253_:
{
lean_object* v_skipPrefix_x3f_1256_; lean_object* v___x_1257_; lean_object* v___x_1259_; 
v_skipPrefix_x3f_1256_ = lean_ctor_get(v_inst_1249_, 0);
lean_inc_ref(v_skipPrefix_x3f_1256_);
lean_dec_ref(v_inst_1249_);
v___x_1257_ = lean_nat_add(v_startInclusive_1251_, v_pos_1248_);
lean_dec(v_startInclusive_1251_);
if (v_isShared_1255_ == 0)
{
lean_ctor_set(v___x_1254_, 1, v___x_1257_);
v___x_1259_ = v___x_1254_;
goto v_reusejp_1258_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v_str_1250_);
lean_ctor_set(v_reuseFailAlloc_1270_, 1, v___x_1257_);
lean_ctor_set(v_reuseFailAlloc_1270_, 2, v_endExclusive_1252_);
v___x_1259_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1258_;
}
v_reusejp_1258_:
{
lean_object* v___x_1260_; 
v___x_1260_ = lean_apply_1(v_skipPrefix_x3f_1256_, v___x_1259_);
if (lean_obj_tag(v___x_1260_) == 0)
{
return v___x_1260_;
}
else
{
lean_object* v_val_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1269_; 
v_val_1261_ = lean_ctor_get(v___x_1260_, 0);
v_isSharedCheck_1269_ = !lean_is_exclusive(v___x_1260_);
if (v_isSharedCheck_1269_ == 0)
{
v___x_1263_ = v___x_1260_;
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_val_1261_);
lean_dec(v___x_1260_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1269_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_nat_add(v_pos_1248_, v_val_1261_);
lean_dec(v_val_1261_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 0, v___x_1265_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1268_; 
v_reuseFailAlloc_1268_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1268_, 0, v___x_1265_);
v___x_1267_ = v_reuseFailAlloc_1268_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
return v___x_1267_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg___boxed(lean_object* v_s_1272_, lean_object* v_pos_1273_, lean_object* v_inst_1274_){
_start:
{
lean_object* v_res_1275_; 
v_res_1275_ = l_String_Slice_Pos_skip_x3f___redArg(v_s_1272_, v_pos_1273_, v_inst_1274_);
lean_dec(v_pos_1273_);
return v_res_1275_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f(lean_object* v_00_u03c1_1276_, lean_object* v_s_1277_, lean_object* v_pos_1278_, lean_object* v_pat_1279_, lean_object* v_inst_1280_){
_start:
{
lean_object* v_str_1281_; lean_object* v_startInclusive_1282_; lean_object* v_endExclusive_1283_; lean_object* v___x_1285_; uint8_t v_isShared_1286_; uint8_t v_isSharedCheck_1302_; 
v_str_1281_ = lean_ctor_get(v_s_1277_, 0);
v_startInclusive_1282_ = lean_ctor_get(v_s_1277_, 1);
v_endExclusive_1283_ = lean_ctor_get(v_s_1277_, 2);
v_isSharedCheck_1302_ = !lean_is_exclusive(v_s_1277_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1285_ = v_s_1277_;
v_isShared_1286_ = v_isSharedCheck_1302_;
goto v_resetjp_1284_;
}
else
{
lean_inc(v_endExclusive_1283_);
lean_inc(v_startInclusive_1282_);
lean_inc(v_str_1281_);
lean_dec(v_s_1277_);
v___x_1285_ = lean_box(0);
v_isShared_1286_ = v_isSharedCheck_1302_;
goto v_resetjp_1284_;
}
v_resetjp_1284_:
{
lean_object* v_skipPrefix_x3f_1287_; lean_object* v___x_1288_; lean_object* v___x_1290_; 
v_skipPrefix_x3f_1287_ = lean_ctor_get(v_inst_1280_, 0);
lean_inc_ref(v_skipPrefix_x3f_1287_);
lean_dec_ref(v_inst_1280_);
v___x_1288_ = lean_nat_add(v_startInclusive_1282_, v_pos_1278_);
lean_dec(v_startInclusive_1282_);
if (v_isShared_1286_ == 0)
{
lean_ctor_set(v___x_1285_, 1, v___x_1288_);
v___x_1290_ = v___x_1285_;
goto v_reusejp_1289_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v_str_1281_);
lean_ctor_set(v_reuseFailAlloc_1301_, 1, v___x_1288_);
lean_ctor_set(v_reuseFailAlloc_1301_, 2, v_endExclusive_1283_);
v___x_1290_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1289_;
}
v_reusejp_1289_:
{
lean_object* v___x_1291_; 
v___x_1291_ = lean_apply_1(v_skipPrefix_x3f_1287_, v___x_1290_);
if (lean_obj_tag(v___x_1291_) == 0)
{
return v___x_1291_;
}
else
{
lean_object* v_val_1292_; lean_object* v___x_1294_; uint8_t v_isShared_1295_; uint8_t v_isSharedCheck_1300_; 
v_val_1292_ = lean_ctor_get(v___x_1291_, 0);
v_isSharedCheck_1300_ = !lean_is_exclusive(v___x_1291_);
if (v_isSharedCheck_1300_ == 0)
{
v___x_1294_ = v___x_1291_;
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
else
{
lean_inc(v_val_1292_);
lean_dec(v___x_1291_);
v___x_1294_ = lean_box(0);
v_isShared_1295_ = v_isSharedCheck_1300_;
goto v_resetjp_1293_;
}
v_resetjp_1293_:
{
lean_object* v___x_1296_; lean_object* v___x_1298_; 
v___x_1296_ = lean_nat_add(v_pos_1278_, v_val_1292_);
lean_dec(v_val_1292_);
if (v_isShared_1295_ == 0)
{
lean_ctor_set(v___x_1294_, 0, v___x_1296_);
v___x_1298_ = v___x_1294_;
goto v_reusejp_1297_;
}
else
{
lean_object* v_reuseFailAlloc_1299_; 
v_reuseFailAlloc_1299_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1299_, 0, v___x_1296_);
v___x_1298_ = v_reuseFailAlloc_1299_;
goto v_reusejp_1297_;
}
v_reusejp_1297_:
{
return v___x_1298_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_1303_, lean_object* v_s_1304_, lean_object* v_pos_1305_, lean_object* v_pat_1306_, lean_object* v_inst_1307_){
_start:
{
lean_object* v_res_1308_; 
v_res_1308_ = l_String_Slice_Pos_skip_x3f(v_00_u03c1_1303_, v_s_1304_, v_pos_1305_, v_pat_1306_, v_inst_1307_);
lean_dec(v_pat_1306_);
lean_dec(v_pos_1305_);
return v_res_1308_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___redArg(lean_object* v_s_1309_, lean_object* v_inst_1310_){
_start:
{
lean_object* v_skipPrefix_x3f_1311_; lean_object* v___x_1312_; 
v_skipPrefix_x3f_1311_ = lean_ctor_get(v_inst_1310_, 0);
lean_inc_ref(v_skipPrefix_x3f_1311_);
lean_dec_ref(v_inst_1310_);
lean_inc_ref(v_s_1309_);
v___x_1312_ = lean_apply_1(v_skipPrefix_x3f_1311_, v_s_1309_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v___x_1313_; 
lean_dec_ref(v_s_1309_);
v___x_1313_ = lean_box(0);
return v___x_1313_;
}
else
{
lean_object* v_val_1314_; lean_object* v___x_1316_; uint8_t v_isShared_1317_; uint8_t v_isSharedCheck_1332_; 
v_val_1314_ = lean_ctor_get(v___x_1312_, 0);
v_isSharedCheck_1332_ = !lean_is_exclusive(v___x_1312_);
if (v_isSharedCheck_1332_ == 0)
{
v___x_1316_ = v___x_1312_;
v_isShared_1317_ = v_isSharedCheck_1332_;
goto v_resetjp_1315_;
}
else
{
lean_inc(v_val_1314_);
lean_dec(v___x_1312_);
v___x_1316_ = lean_box(0);
v_isShared_1317_ = v_isSharedCheck_1332_;
goto v_resetjp_1315_;
}
v_resetjp_1315_:
{
lean_object* v_str_1318_; lean_object* v_startInclusive_1319_; lean_object* v_endExclusive_1320_; lean_object* v___x_1322_; uint8_t v_isShared_1323_; uint8_t v_isSharedCheck_1331_; 
v_str_1318_ = lean_ctor_get(v_s_1309_, 0);
v_startInclusive_1319_ = lean_ctor_get(v_s_1309_, 1);
v_endExclusive_1320_ = lean_ctor_get(v_s_1309_, 2);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_s_1309_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1322_ = v_s_1309_;
v_isShared_1323_ = v_isSharedCheck_1331_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_endExclusive_1320_);
lean_inc(v_startInclusive_1319_);
lean_inc(v_str_1318_);
lean_dec(v_s_1309_);
v___x_1322_ = lean_box(0);
v_isShared_1323_ = v_isSharedCheck_1331_;
goto v_resetjp_1321_;
}
v_resetjp_1321_:
{
lean_object* v___x_1324_; lean_object* v___x_1326_; 
v___x_1324_ = lean_nat_add(v_startInclusive_1319_, v_val_1314_);
lean_dec(v_val_1314_);
lean_dec(v_startInclusive_1319_);
if (v_isShared_1323_ == 0)
{
lean_ctor_set(v___x_1322_, 1, v___x_1324_);
v___x_1326_ = v___x_1322_;
goto v_reusejp_1325_;
}
else
{
lean_object* v_reuseFailAlloc_1330_; 
v_reuseFailAlloc_1330_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1330_, 0, v_str_1318_);
lean_ctor_set(v_reuseFailAlloc_1330_, 1, v___x_1324_);
lean_ctor_set(v_reuseFailAlloc_1330_, 2, v_endExclusive_1320_);
v___x_1326_ = v_reuseFailAlloc_1330_;
goto v_reusejp_1325_;
}
v_reusejp_1325_:
{
lean_object* v___x_1328_; 
if (v_isShared_1317_ == 0)
{
lean_ctor_set(v___x_1316_, 0, v___x_1326_);
v___x_1328_ = v___x_1316_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1329_; 
v_reuseFailAlloc_1329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1329_, 0, v___x_1326_);
v___x_1328_ = v_reuseFailAlloc_1329_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
return v___x_1328_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f(lean_object* v_00_u03c1_1333_, lean_object* v_s_1334_, lean_object* v_pat_1335_, lean_object* v_inst_1336_){
_start:
{
lean_object* v_skipPrefix_x3f_1337_; lean_object* v___x_1338_; 
v_skipPrefix_x3f_1337_ = lean_ctor_get(v_inst_1336_, 0);
lean_inc_ref(v_skipPrefix_x3f_1337_);
lean_dec_ref(v_inst_1336_);
lean_inc_ref(v_s_1334_);
v___x_1338_ = lean_apply_1(v_skipPrefix_x3f_1337_, v_s_1334_);
if (lean_obj_tag(v___x_1338_) == 0)
{
lean_object* v___x_1339_; 
lean_dec_ref(v_s_1334_);
v___x_1339_ = lean_box(0);
return v___x_1339_;
}
else
{
lean_object* v_val_1340_; lean_object* v___x_1342_; uint8_t v_isShared_1343_; uint8_t v_isSharedCheck_1358_; 
v_val_1340_ = lean_ctor_get(v___x_1338_, 0);
v_isSharedCheck_1358_ = !lean_is_exclusive(v___x_1338_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1342_ = v___x_1338_;
v_isShared_1343_ = v_isSharedCheck_1358_;
goto v_resetjp_1341_;
}
else
{
lean_inc(v_val_1340_);
lean_dec(v___x_1338_);
v___x_1342_ = lean_box(0);
v_isShared_1343_ = v_isSharedCheck_1358_;
goto v_resetjp_1341_;
}
v_resetjp_1341_:
{
lean_object* v_str_1344_; lean_object* v_startInclusive_1345_; lean_object* v_endExclusive_1346_; lean_object* v___x_1348_; uint8_t v_isShared_1349_; uint8_t v_isSharedCheck_1357_; 
v_str_1344_ = lean_ctor_get(v_s_1334_, 0);
v_startInclusive_1345_ = lean_ctor_get(v_s_1334_, 1);
v_endExclusive_1346_ = lean_ctor_get(v_s_1334_, 2);
v_isSharedCheck_1357_ = !lean_is_exclusive(v_s_1334_);
if (v_isSharedCheck_1357_ == 0)
{
v___x_1348_ = v_s_1334_;
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
else
{
lean_inc(v_endExclusive_1346_);
lean_inc(v_startInclusive_1345_);
lean_inc(v_str_1344_);
lean_dec(v_s_1334_);
v___x_1348_ = lean_box(0);
v_isShared_1349_ = v_isSharedCheck_1357_;
goto v_resetjp_1347_;
}
v_resetjp_1347_:
{
lean_object* v___x_1350_; lean_object* v___x_1352_; 
v___x_1350_ = lean_nat_add(v_startInclusive_1345_, v_val_1340_);
lean_dec(v_val_1340_);
lean_dec(v_startInclusive_1345_);
if (v_isShared_1349_ == 0)
{
lean_ctor_set(v___x_1348_, 1, v___x_1350_);
v___x_1352_ = v___x_1348_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v_str_1344_);
lean_ctor_set(v_reuseFailAlloc_1356_, 1, v___x_1350_);
lean_ctor_set(v_reuseFailAlloc_1356_, 2, v_endExclusive_1346_);
v___x_1352_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
lean_object* v___x_1354_; 
if (v_isShared_1343_ == 0)
{
lean_ctor_set(v___x_1342_, 0, v___x_1352_);
v___x_1354_ = v___x_1342_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1355_; 
v_reuseFailAlloc_1355_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1355_, 0, v___x_1352_);
v___x_1354_ = v_reuseFailAlloc_1355_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
return v___x_1354_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_1359_, lean_object* v_s_1360_, lean_object* v_pat_1361_, lean_object* v_inst_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_String_Slice_dropPrefix_x3f(v_00_u03c1_1359_, v_s_1360_, v_pat_1361_, v_inst_1362_);
lean_dec(v_pat_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___redArg(lean_object* v_s_1364_, lean_object* v_inst_1365_){
_start:
{
lean_object* v_skipPrefix_x3f_1366_; lean_object* v___x_1367_; 
v_skipPrefix_x3f_1366_ = lean_ctor_get(v_inst_1365_, 0);
lean_inc_ref(v_skipPrefix_x3f_1366_);
lean_dec_ref(v_inst_1365_);
lean_inc_ref(v_s_1364_);
v___x_1367_ = lean_apply_1(v_skipPrefix_x3f_1366_, v_s_1364_);
if (lean_obj_tag(v___x_1367_) == 0)
{
return v_s_1364_;
}
else
{
lean_object* v_val_1368_; lean_object* v_str_1369_; lean_object* v_startInclusive_1370_; lean_object* v_endExclusive_1371_; lean_object* v___x_1373_; uint8_t v_isShared_1374_; uint8_t v_isSharedCheck_1379_; 
v_val_1368_ = lean_ctor_get(v___x_1367_, 0);
lean_inc(v_val_1368_);
lean_dec_ref(v___x_1367_);
v_str_1369_ = lean_ctor_get(v_s_1364_, 0);
v_startInclusive_1370_ = lean_ctor_get(v_s_1364_, 1);
v_endExclusive_1371_ = lean_ctor_get(v_s_1364_, 2);
v_isSharedCheck_1379_ = !lean_is_exclusive(v_s_1364_);
if (v_isSharedCheck_1379_ == 0)
{
v___x_1373_ = v_s_1364_;
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
else
{
lean_inc(v_endExclusive_1371_);
lean_inc(v_startInclusive_1370_);
lean_inc(v_str_1369_);
lean_dec(v_s_1364_);
v___x_1373_ = lean_box(0);
v_isShared_1374_ = v_isSharedCheck_1379_;
goto v_resetjp_1372_;
}
v_resetjp_1372_:
{
lean_object* v___x_1375_; lean_object* v___x_1377_; 
v___x_1375_ = lean_nat_add(v_startInclusive_1370_, v_val_1368_);
lean_dec(v_val_1368_);
lean_dec(v_startInclusive_1370_);
if (v_isShared_1374_ == 0)
{
lean_ctor_set(v___x_1373_, 1, v___x_1375_);
v___x_1377_ = v___x_1373_;
goto v_reusejp_1376_;
}
else
{
lean_object* v_reuseFailAlloc_1378_; 
v_reuseFailAlloc_1378_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1378_, 0, v_str_1369_);
lean_ctor_set(v_reuseFailAlloc_1378_, 1, v___x_1375_);
lean_ctor_set(v_reuseFailAlloc_1378_, 2, v_endExclusive_1371_);
v___x_1377_ = v_reuseFailAlloc_1378_;
goto v_reusejp_1376_;
}
v_reusejp_1376_:
{
return v___x_1377_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix(lean_object* v_00_u03c1_1380_, lean_object* v_s_1381_, lean_object* v_pat_1382_, lean_object* v_inst_1383_){
_start:
{
lean_object* v___x_1384_; 
v___x_1384_ = l_String_Slice_dropPrefix___redArg(v_s_1381_, v_inst_1383_);
return v___x_1384_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___boxed(lean_object* v_00_u03c1_1385_, lean_object* v_s_1386_, lean_object* v_pat_1387_, lean_object* v_inst_1388_){
_start:
{
lean_object* v_res_1389_; 
v_res_1389_ = l_String_Slice_dropPrefix(v_00_u03c1_1385_, v_s_1386_, v_pat_1387_, v_inst_1388_);
lean_dec(v_pat_1387_);
return v_res_1389_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__0(lean_object* v_x_1390_, lean_object* v_x_1391_, lean_object* v_f_1392_, lean_object* v_c_1393_){
_start:
{
lean_object* v___x_1394_; 
v___x_1394_ = lean_apply_1(v_f_1392_, v_c_1393_);
return v___x_1394_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1(lean_object* v_s_1395_, lean_object* v_inst_1396_, lean_object* v_replacement_1397_, lean_object* v_x1_1398_, lean_object* v_x2_1399_, lean_object* v_x3_1400_){
_start:
{
if (lean_obj_tag(v_x1_1398_) == 0)
{
lean_object* v_startPos_1401_; lean_object* v_endPos_1402_; lean_object* v___x_1403_; lean_object* v_str_1404_; lean_object* v_startInclusive_1405_; lean_object* v_endExclusive_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
lean_dec(v_replacement_1397_);
lean_dec_ref(v_inst_1396_);
v_startPos_1401_ = lean_ctor_get(v_x1_1398_, 0);
v_endPos_1402_ = lean_ctor_get(v_x1_1398_, 1);
v___x_1403_ = l_String_Slice_slice_x21(v_s_1395_, v_startPos_1401_, v_endPos_1402_);
v_str_1404_ = lean_ctor_get(v___x_1403_, 0);
lean_inc_ref(v_str_1404_);
v_startInclusive_1405_ = lean_ctor_get(v___x_1403_, 1);
lean_inc(v_startInclusive_1405_);
v_endExclusive_1406_ = lean_ctor_get(v___x_1403_, 2);
lean_inc(v_endExclusive_1406_);
lean_dec_ref(v___x_1403_);
v___x_1407_ = lean_string_utf8_extract(v_str_1404_, v_startInclusive_1405_, v_endExclusive_1406_);
lean_dec(v_endExclusive_1406_);
lean_dec(v_startInclusive_1405_);
lean_dec_ref(v_str_1404_);
v___x_1408_ = lean_string_append(v_x3_1400_, v___x_1407_);
lean_dec_ref(v___x_1407_);
v___x_1409_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1409_, 0, v___x_1408_);
return v___x_1409_;
}
else
{
lean_object* v___x_1410_; lean_object* v_str_1411_; lean_object* v_startInclusive_1412_; lean_object* v_endExclusive_1413_; lean_object* v___x_1414_; lean_object* v___x_1415_; lean_object* v___x_1416_; 
lean_dec_ref(v_s_1395_);
v___x_1410_ = lean_apply_1(v_inst_1396_, v_replacement_1397_);
v_str_1411_ = lean_ctor_get(v___x_1410_, 0);
lean_inc_ref(v_str_1411_);
v_startInclusive_1412_ = lean_ctor_get(v___x_1410_, 1);
lean_inc(v_startInclusive_1412_);
v_endExclusive_1413_ = lean_ctor_get(v___x_1410_, 2);
lean_inc(v_endExclusive_1413_);
lean_dec_ref(v___x_1410_);
v___x_1414_ = lean_string_utf8_extract(v_str_1411_, v_startInclusive_1412_, v_endExclusive_1413_);
lean_dec(v_endExclusive_1413_);
lean_dec(v_startInclusive_1412_);
lean_dec_ref(v_str_1411_);
v___x_1415_ = lean_string_append(v_x3_1400_, v___x_1414_);
lean_dec_ref(v___x_1414_);
v___x_1416_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1416_, 0, v___x_1415_);
return v___x_1416_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1___boxed(lean_object* v_s_1417_, lean_object* v_inst_1418_, lean_object* v_replacement_1419_, lean_object* v_x1_1420_, lean_object* v_x2_1421_, lean_object* v_x3_1422_){
_start:
{
lean_object* v_res_1423_; 
v_res_1423_ = l_String_Slice_replace___redArg___lam__1(v_s_1417_, v_inst_1418_, v_replacement_1419_, v_x1_1420_, v_x2_1421_, v_x3_1422_);
lean_dec_ref(v_x1_1420_);
return v_res_1423_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg(lean_object* v_inst_1426_, lean_object* v_inst_1427_, lean_object* v_s_1428_, lean_object* v_inst_1429_, lean_object* v_replacement_1430_){
_start:
{
lean_object* v___f_1431_; lean_object* v___f_1432_; lean_object* v___x_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; 
v___f_1431_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1428_);
v___f_1432_ = lean_alloc_closure((void*)(l_String_Slice_replace___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1432_, 0, v_s_1428_);
lean_closure_set(v___f_1432_, 1, v_inst_1427_);
lean_closure_set(v___f_1432_, 2, v_replacement_1430_);
v___x_1433_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
lean_inc_ref(v_s_1428_);
v___x_1434_ = lean_apply_1(v_inst_1429_, v_s_1428_);
v___x_1435_ = lean_apply_7(v_inst_1426_, v_s_1428_, v___f_1431_, lean_box(0), lean_box(0), v___x_1434_, v___x_1433_, v___f_1432_);
return v___x_1435_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace(lean_object* v_00_u03c1_1436_, lean_object* v_00_u03c3_1437_, lean_object* v_inst_1438_, lean_object* v_inst_1439_, lean_object* v_00_u03b1_1440_, lean_object* v_inst_1441_, lean_object* v_s_1442_, lean_object* v_pattern_1443_, lean_object* v_inst_1444_, lean_object* v_replacement_1445_){
_start:
{
lean_object* v___x_1446_; 
v___x_1446_ = l_String_Slice_replace___redArg(v_inst_1439_, v_inst_1441_, v_s_1442_, v_inst_1444_, v_replacement_1445_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___boxed(lean_object* v_00_u03c1_1447_, lean_object* v_00_u03c3_1448_, lean_object* v_inst_1449_, lean_object* v_inst_1450_, lean_object* v_00_u03b1_1451_, lean_object* v_inst_1452_, lean_object* v_s_1453_, lean_object* v_pattern_1454_, lean_object* v_inst_1455_, lean_object* v_replacement_1456_){
_start:
{
lean_object* v_res_1457_; 
v_res_1457_ = l_String_Slice_replace(v_00_u03c1_1447_, v_00_u03c3_1448_, v_inst_1449_, v_inst_1450_, v_00_u03b1_1451_, v_inst_1452_, v_s_1453_, v_pattern_1454_, v_inst_1455_, v_replacement_1456_);
lean_dec(v_pattern_1454_);
lean_dec(v_inst_1449_);
return v_res_1457_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object* v_s_1458_, lean_object* v_n_1459_){
_start:
{
lean_object* v_str_1460_; lean_object* v_startInclusive_1461_; lean_object* v_endExclusive_1462_; lean_object* v___x_1463_; lean_object* v___x_1464_; lean_object* v___x_1466_; uint8_t v_isShared_1467_; uint8_t v_isSharedCheck_1472_; 
v_str_1460_ = lean_ctor_get(v_s_1458_, 0);
lean_inc_ref(v_str_1460_);
v_startInclusive_1461_ = lean_ctor_get(v_s_1458_, 1);
lean_inc(v_startInclusive_1461_);
v_endExclusive_1462_ = lean_ctor_get(v_s_1458_, 2);
lean_inc(v_endExclusive_1462_);
v___x_1463_ = lean_unsigned_to_nat(0u);
v___x_1464_ = l_String_Slice_Pos_nextn(v_s_1458_, v___x_1463_, v_n_1459_);
v_isSharedCheck_1472_ = !lean_is_exclusive(v_s_1458_);
if (v_isSharedCheck_1472_ == 0)
{
lean_object* v_unused_1473_; lean_object* v_unused_1474_; lean_object* v_unused_1475_; 
v_unused_1473_ = lean_ctor_get(v_s_1458_, 2);
lean_dec(v_unused_1473_);
v_unused_1474_ = lean_ctor_get(v_s_1458_, 1);
lean_dec(v_unused_1474_);
v_unused_1475_ = lean_ctor_get(v_s_1458_, 0);
lean_dec(v_unused_1475_);
v___x_1466_ = v_s_1458_;
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
else
{
lean_dec(v_s_1458_);
v___x_1466_ = lean_box(0);
v_isShared_1467_ = v_isSharedCheck_1472_;
goto v_resetjp_1465_;
}
v_resetjp_1465_:
{
lean_object* v___x_1468_; lean_object* v___x_1470_; 
v___x_1468_ = lean_nat_add(v_startInclusive_1461_, v___x_1464_);
lean_dec(v___x_1464_);
lean_dec(v_startInclusive_1461_);
if (v_isShared_1467_ == 0)
{
lean_ctor_set(v___x_1466_, 1, v___x_1468_);
v___x_1470_ = v___x_1466_;
goto v_reusejp_1469_;
}
else
{
lean_object* v_reuseFailAlloc_1471_; 
v_reuseFailAlloc_1471_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1471_, 0, v_str_1460_);
lean_ctor_set(v_reuseFailAlloc_1471_, 1, v___x_1468_);
lean_ctor_set(v_reuseFailAlloc_1471_, 2, v_endExclusive_1462_);
v___x_1470_ = v_reuseFailAlloc_1471_;
goto v_reusejp_1469_;
}
v_reusejp_1469_:
{
return v___x_1470_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object* v_s_1476_, lean_object* v_pos_1477_, lean_object* v_inst_1478_){
_start:
{
lean_object* v_skipPrefix_x3f_1479_; lean_object* v_str_1480_; lean_object* v_startInclusive_1481_; lean_object* v_endExclusive_1482_; lean_object* v___x_1483_; lean_object* v___x_1484_; lean_object* v___x_1485_; 
v_skipPrefix_x3f_1479_ = lean_ctor_get(v_inst_1478_, 0);
v_str_1480_ = lean_ctor_get(v_s_1476_, 0);
v_startInclusive_1481_ = lean_ctor_get(v_s_1476_, 1);
v_endExclusive_1482_ = lean_ctor_get(v_s_1476_, 2);
v___x_1483_ = lean_nat_add(v_startInclusive_1481_, v_pos_1477_);
lean_inc(v_endExclusive_1482_);
lean_inc_ref(v_str_1480_);
v___x_1484_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1484_, 0, v_str_1480_);
lean_ctor_set(v___x_1484_, 1, v___x_1483_);
lean_ctor_set(v___x_1484_, 2, v_endExclusive_1482_);
lean_inc_ref(v_skipPrefix_x3f_1479_);
v___x_1485_ = lean_apply_1(v_skipPrefix_x3f_1479_, v___x_1484_);
if (lean_obj_tag(v___x_1485_) == 1)
{
lean_object* v_val_1486_; lean_object* v___x_1487_; uint8_t v___x_1488_; 
v_val_1486_ = lean_ctor_get(v___x_1485_, 0);
lean_inc(v_val_1486_);
lean_dec_ref(v___x_1485_);
v___x_1487_ = lean_nat_add(v_pos_1477_, v_val_1486_);
lean_dec(v_val_1486_);
v___x_1488_ = l_String_instDecidableLtRaw___aux__1(v_pos_1477_, v___x_1487_);
if (v___x_1488_ == 0)
{
lean_dec(v___x_1487_);
lean_dec_ref(v_inst_1478_);
return v_pos_1477_;
}
else
{
lean_dec(v_pos_1477_);
v_pos_1477_ = v___x_1487_;
goto _start;
}
}
else
{
lean_dec(v___x_1485_);
lean_dec_ref(v_inst_1478_);
return v_pos_1477_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg___boxed(lean_object* v_s_1490_, lean_object* v_pos_1491_, lean_object* v_inst_1492_){
_start:
{
lean_object* v_res_1493_; 
v_res_1493_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1490_, v_pos_1491_, v_inst_1492_);
lean_dec_ref(v_s_1490_);
return v_res_1493_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile(lean_object* v_00_u03c1_1494_, lean_object* v_s_1495_, lean_object* v_pos_1496_, lean_object* v_pat_1497_, lean_object* v_inst_1498_){
_start:
{
lean_object* v___x_1499_; 
v___x_1499_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1495_, v_pos_1496_, v_inst_1498_);
return v___x_1499_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___boxed(lean_object* v_00_u03c1_1500_, lean_object* v_s_1501_, lean_object* v_pos_1502_, lean_object* v_pat_1503_, lean_object* v_inst_1504_){
_start:
{
lean_object* v_res_1505_; 
v_res_1505_ = l_String_Slice_Pos_skipWhile(v_00_u03c1_1500_, v_s_1501_, v_pos_1502_, v_pat_1503_, v_inst_1504_);
lean_dec(v_pat_1503_);
lean_dec_ref(v_s_1501_);
return v_res_1505_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object* v_x_1506_, lean_object* v_h__1_1507_, lean_object* v_h__2_1508_){
_start:
{
if (lean_obj_tag(v_x_1506_) == 1)
{
lean_object* v_val_1509_; lean_object* v___x_1510_; 
lean_dec(v_h__2_1508_);
v_val_1509_ = lean_ctor_get(v_x_1506_, 0);
lean_inc(v_val_1509_);
lean_dec_ref(v_x_1506_);
v___x_1510_ = lean_apply_1(v_h__1_1507_, v_val_1509_);
return v___x_1510_;
}
else
{
lean_object* v___x_1511_; 
lean_dec(v_h__1_1507_);
v___x_1511_ = lean_apply_2(v_h__2_1508_, v_x_1506_, lean_box(0));
return v___x_1511_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object* v_s_1512_, lean_object* v_pos_1513_, lean_object* v_motive_1514_, lean_object* v_x_1515_, lean_object* v_h__1_1516_, lean_object* v_h__2_1517_){
_start:
{
if (lean_obj_tag(v_x_1515_) == 1)
{
lean_object* v_val_1518_; lean_object* v___x_1519_; 
lean_dec(v_h__2_1517_);
v_val_1518_ = lean_ctor_get(v_x_1515_, 0);
lean_inc(v_val_1518_);
lean_dec_ref(v_x_1515_);
v___x_1519_ = lean_apply_1(v_h__1_1516_, v_val_1518_);
return v___x_1519_;
}
else
{
lean_object* v___x_1520_; 
lean_dec(v_h__1_1516_);
v___x_1520_ = lean_apply_2(v_h__2_1517_, v_x_1515_, lean_box(0));
return v___x_1520_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object* v_s_1521_, lean_object* v_pos_1522_, lean_object* v_motive_1523_, lean_object* v_x_1524_, lean_object* v_h__1_1525_, lean_object* v_h__2_1526_){
_start:
{
lean_object* v_res_1527_; 
v_res_1527_ = l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_1521_, v_pos_1522_, v_motive_1523_, v_x_1524_, v_h__1_1525_, v_h__2_1526_);
lean_dec(v_pos_1522_);
lean_dec_ref(v_s_1521_);
return v_res_1527_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg(lean_object* v_s_1528_, lean_object* v_inst_1529_){
_start:
{
lean_object* v___x_1530_; lean_object* v___x_1531_; 
v___x_1530_ = lean_unsigned_to_nat(0u);
v___x_1531_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1528_, v___x_1530_, v_inst_1529_);
return v___x_1531_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg___boxed(lean_object* v_s_1532_, lean_object* v_inst_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_String_Slice_skipPrefixWhile___redArg(v_s_1532_, v_inst_1533_);
lean_dec_ref(v_s_1532_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile(lean_object* v_00_u03c1_1535_, lean_object* v_s_1536_, lean_object* v_pat_1537_, lean_object* v_inst_1538_){
_start:
{
lean_object* v___x_1539_; lean_object* v___x_1540_; 
v___x_1539_ = lean_unsigned_to_nat(0u);
v___x_1540_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1536_, v___x_1539_, v_inst_1538_);
return v___x_1540_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___boxed(lean_object* v_00_u03c1_1541_, lean_object* v_s_1542_, lean_object* v_pat_1543_, lean_object* v_inst_1544_){
_start:
{
lean_object* v_res_1545_; 
v_res_1545_ = l_String_Slice_skipPrefixWhile(v_00_u03c1_1541_, v_s_1542_, v_pat_1543_, v_inst_1544_);
lean_dec(v_pat_1543_);
lean_dec_ref(v_s_1542_);
return v_res_1545_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg(lean_object* v_s_1546_, lean_object* v_inst_1547_){
_start:
{
lean_object* v_str_1548_; lean_object* v_startInclusive_1549_; lean_object* v_endExclusive_1550_; lean_object* v___x_1551_; lean_object* v___x_1552_; lean_object* v___x_1554_; uint8_t v_isShared_1555_; uint8_t v_isSharedCheck_1560_; 
v_str_1548_ = lean_ctor_get(v_s_1546_, 0);
lean_inc_ref(v_str_1548_);
v_startInclusive_1549_ = lean_ctor_get(v_s_1546_, 1);
lean_inc(v_startInclusive_1549_);
v_endExclusive_1550_ = lean_ctor_get(v_s_1546_, 2);
lean_inc(v_endExclusive_1550_);
v___x_1551_ = lean_unsigned_to_nat(0u);
v___x_1552_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1546_, v___x_1551_, v_inst_1547_);
v_isSharedCheck_1560_ = !lean_is_exclusive(v_s_1546_);
if (v_isSharedCheck_1560_ == 0)
{
lean_object* v_unused_1561_; lean_object* v_unused_1562_; lean_object* v_unused_1563_; 
v_unused_1561_ = lean_ctor_get(v_s_1546_, 2);
lean_dec(v_unused_1561_);
v_unused_1562_ = lean_ctor_get(v_s_1546_, 1);
lean_dec(v_unused_1562_);
v_unused_1563_ = lean_ctor_get(v_s_1546_, 0);
lean_dec(v_unused_1563_);
v___x_1554_ = v_s_1546_;
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
else
{
lean_dec(v_s_1546_);
v___x_1554_ = lean_box(0);
v_isShared_1555_ = v_isSharedCheck_1560_;
goto v_resetjp_1553_;
}
v_resetjp_1553_:
{
lean_object* v___x_1556_; lean_object* v___x_1558_; 
v___x_1556_ = lean_nat_add(v_startInclusive_1549_, v___x_1552_);
lean_dec(v___x_1552_);
lean_dec(v_startInclusive_1549_);
if (v_isShared_1555_ == 0)
{
lean_ctor_set(v___x_1554_, 1, v___x_1556_);
v___x_1558_ = v___x_1554_;
goto v_reusejp_1557_;
}
else
{
lean_object* v_reuseFailAlloc_1559_; 
v_reuseFailAlloc_1559_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1559_, 0, v_str_1548_);
lean_ctor_set(v_reuseFailAlloc_1559_, 1, v___x_1556_);
lean_ctor_set(v_reuseFailAlloc_1559_, 2, v_endExclusive_1550_);
v___x_1558_ = v_reuseFailAlloc_1559_;
goto v_reusejp_1557_;
}
v_reusejp_1557_:
{
return v___x_1558_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile(lean_object* v_00_u03c1_1564_, lean_object* v_s_1565_, lean_object* v_pat_1566_, lean_object* v_inst_1567_){
_start:
{
lean_object* v_str_1568_; lean_object* v_startInclusive_1569_; lean_object* v_endExclusive_1570_; lean_object* v___x_1571_; lean_object* v___x_1572_; lean_object* v___x_1574_; uint8_t v_isShared_1575_; uint8_t v_isSharedCheck_1580_; 
v_str_1568_ = lean_ctor_get(v_s_1565_, 0);
lean_inc_ref(v_str_1568_);
v_startInclusive_1569_ = lean_ctor_get(v_s_1565_, 1);
lean_inc(v_startInclusive_1569_);
v_endExclusive_1570_ = lean_ctor_get(v_s_1565_, 2);
lean_inc(v_endExclusive_1570_);
v___x_1571_ = lean_unsigned_to_nat(0u);
v___x_1572_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1565_, v___x_1571_, v_inst_1567_);
v_isSharedCheck_1580_ = !lean_is_exclusive(v_s_1565_);
if (v_isSharedCheck_1580_ == 0)
{
lean_object* v_unused_1581_; lean_object* v_unused_1582_; lean_object* v_unused_1583_; 
v_unused_1581_ = lean_ctor_get(v_s_1565_, 2);
lean_dec(v_unused_1581_);
v_unused_1582_ = lean_ctor_get(v_s_1565_, 1);
lean_dec(v_unused_1582_);
v_unused_1583_ = lean_ctor_get(v_s_1565_, 0);
lean_dec(v_unused_1583_);
v___x_1574_ = v_s_1565_;
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
else
{
lean_dec(v_s_1565_);
v___x_1574_ = lean_box(0);
v_isShared_1575_ = v_isSharedCheck_1580_;
goto v_resetjp_1573_;
}
v_resetjp_1573_:
{
lean_object* v___x_1576_; lean_object* v___x_1578_; 
v___x_1576_ = lean_nat_add(v_startInclusive_1569_, v___x_1572_);
lean_dec(v___x_1572_);
lean_dec(v_startInclusive_1569_);
if (v_isShared_1575_ == 0)
{
lean_ctor_set(v___x_1574_, 1, v___x_1576_);
v___x_1578_ = v___x_1574_;
goto v_reusejp_1577_;
}
else
{
lean_object* v_reuseFailAlloc_1579_; 
v_reuseFailAlloc_1579_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1579_, 0, v_str_1568_);
lean_ctor_set(v_reuseFailAlloc_1579_, 1, v___x_1576_);
lean_ctor_set(v_reuseFailAlloc_1579_, 2, v_endExclusive_1570_);
v___x_1578_ = v_reuseFailAlloc_1579_;
goto v_reusejp_1577_;
}
v_reusejp_1577_:
{
return v___x_1578_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___boxed(lean_object* v_00_u03c1_1584_, lean_object* v_s_1585_, lean_object* v_pat_1586_, lean_object* v_inst_1587_){
_start:
{
lean_object* v_res_1588_; 
v_res_1588_ = l_String_Slice_dropWhile(v_00_u03c1_1584_, v_s_1585_, v_pat_1586_, v_inst_1587_);
lean_dec(v_pat_1586_);
return v_res_1588_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiStart___closed__1(void){
_start:
{
lean_object* v___x_1590_; lean_object* v___x_1591_; 
v___x_1590_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_1591_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1590_);
return v___x_1591_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart(lean_object* v_s_1592_){
_start:
{
lean_object* v___x_1593_; lean_object* v_str_1594_; lean_object* v_startInclusive_1595_; lean_object* v_endExclusive_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1606_; 
v___x_1593_ = lean_obj_once(&l_String_Slice_trimAsciiStart___closed__1, &l_String_Slice_trimAsciiStart___closed__1_once, _init_l_String_Slice_trimAsciiStart___closed__1);
v_str_1594_ = lean_ctor_get(v_s_1592_, 0);
lean_inc_ref(v_str_1594_);
v_startInclusive_1595_ = lean_ctor_get(v_s_1592_, 1);
lean_inc(v_startInclusive_1595_);
v_endExclusive_1596_ = lean_ctor_get(v_s_1592_, 2);
lean_inc(v_endExclusive_1596_);
v___x_1597_ = lean_unsigned_to_nat(0u);
v___x_1598_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1592_, v___x_1597_, v___x_1593_);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_s_1592_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; 
v_unused_1607_ = lean_ctor_get(v_s_1592_, 2);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_s_1592_, 1);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_s_1592_, 0);
lean_dec(v_unused_1609_);
v___x_1600_ = v_s_1592_;
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
else
{
lean_dec(v_s_1592_);
v___x_1600_ = lean_box(0);
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
v_resetjp_1599_:
{
lean_object* v___x_1602_; lean_object* v___x_1604_; 
v___x_1602_ = lean_nat_add(v_startInclusive_1595_, v___x_1598_);
lean_dec(v___x_1598_);
lean_dec(v_startInclusive_1595_);
if (v_isShared_1601_ == 0)
{
lean_ctor_set(v___x_1600_, 1, v___x_1602_);
v___x_1604_ = v___x_1600_;
goto v_reusejp_1603_;
}
else
{
lean_object* v_reuseFailAlloc_1605_; 
v_reuseFailAlloc_1605_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1605_, 0, v_str_1594_);
lean_ctor_set(v_reuseFailAlloc_1605_, 1, v___x_1602_);
lean_ctor_set(v_reuseFailAlloc_1605_, 2, v_endExclusive_1596_);
v___x_1604_ = v_reuseFailAlloc_1605_;
goto v_reusejp_1603_;
}
v_reusejp_1603_:
{
return v___x_1604_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object* v_s_1610_, lean_object* v_n_1611_){
_start:
{
lean_object* v_str_1612_; lean_object* v_startInclusive_1613_; lean_object* v___x_1614_; lean_object* v___x_1615_; lean_object* v___x_1617_; uint8_t v_isShared_1618_; uint8_t v_isSharedCheck_1623_; 
v_str_1612_ = lean_ctor_get(v_s_1610_, 0);
lean_inc_ref(v_str_1612_);
v_startInclusive_1613_ = lean_ctor_get(v_s_1610_, 1);
lean_inc(v_startInclusive_1613_);
v___x_1614_ = lean_unsigned_to_nat(0u);
v___x_1615_ = l_String_Slice_Pos_nextn(v_s_1610_, v___x_1614_, v_n_1611_);
v_isSharedCheck_1623_ = !lean_is_exclusive(v_s_1610_);
if (v_isSharedCheck_1623_ == 0)
{
lean_object* v_unused_1624_; lean_object* v_unused_1625_; lean_object* v_unused_1626_; 
v_unused_1624_ = lean_ctor_get(v_s_1610_, 2);
lean_dec(v_unused_1624_);
v_unused_1625_ = lean_ctor_get(v_s_1610_, 1);
lean_dec(v_unused_1625_);
v_unused_1626_ = lean_ctor_get(v_s_1610_, 0);
lean_dec(v_unused_1626_);
v___x_1617_ = v_s_1610_;
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
else
{
lean_dec(v_s_1610_);
v___x_1617_ = lean_box(0);
v_isShared_1618_ = v_isSharedCheck_1623_;
goto v_resetjp_1616_;
}
v_resetjp_1616_:
{
lean_object* v___x_1619_; lean_object* v___x_1621_; 
v___x_1619_ = lean_nat_add(v_startInclusive_1613_, v___x_1615_);
lean_dec(v___x_1615_);
if (v_isShared_1618_ == 0)
{
lean_ctor_set(v___x_1617_, 2, v___x_1619_);
v___x_1621_ = v___x_1617_;
goto v_reusejp_1620_;
}
else
{
lean_object* v_reuseFailAlloc_1622_; 
v_reuseFailAlloc_1622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1622_, 0, v_str_1612_);
lean_ctor_set(v_reuseFailAlloc_1622_, 1, v_startInclusive_1613_);
lean_ctor_set(v_reuseFailAlloc_1622_, 2, v___x_1619_);
v___x_1621_ = v_reuseFailAlloc_1622_;
goto v_reusejp_1620_;
}
v_reusejp_1620_:
{
return v___x_1621_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___redArg(lean_object* v_s_1627_, lean_object* v_inst_1628_){
_start:
{
lean_object* v_str_1629_; lean_object* v_startInclusive_1630_; lean_object* v___x_1631_; lean_object* v___x_1632_; lean_object* v___x_1634_; uint8_t v_isShared_1635_; uint8_t v_isSharedCheck_1640_; 
v_str_1629_ = lean_ctor_get(v_s_1627_, 0);
lean_inc_ref(v_str_1629_);
v_startInclusive_1630_ = lean_ctor_get(v_s_1627_, 1);
lean_inc(v_startInclusive_1630_);
v___x_1631_ = lean_unsigned_to_nat(0u);
v___x_1632_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1627_, v___x_1631_, v_inst_1628_);
v_isSharedCheck_1640_ = !lean_is_exclusive(v_s_1627_);
if (v_isSharedCheck_1640_ == 0)
{
lean_object* v_unused_1641_; lean_object* v_unused_1642_; lean_object* v_unused_1643_; 
v_unused_1641_ = lean_ctor_get(v_s_1627_, 2);
lean_dec(v_unused_1641_);
v_unused_1642_ = lean_ctor_get(v_s_1627_, 1);
lean_dec(v_unused_1642_);
v_unused_1643_ = lean_ctor_get(v_s_1627_, 0);
lean_dec(v_unused_1643_);
v___x_1634_ = v_s_1627_;
v_isShared_1635_ = v_isSharedCheck_1640_;
goto v_resetjp_1633_;
}
else
{
lean_dec(v_s_1627_);
v___x_1634_ = lean_box(0);
v_isShared_1635_ = v_isSharedCheck_1640_;
goto v_resetjp_1633_;
}
v_resetjp_1633_:
{
lean_object* v___x_1636_; lean_object* v___x_1638_; 
v___x_1636_ = lean_nat_add(v_startInclusive_1630_, v___x_1632_);
lean_dec(v___x_1632_);
if (v_isShared_1635_ == 0)
{
lean_ctor_set(v___x_1634_, 2, v___x_1636_);
v___x_1638_ = v___x_1634_;
goto v_reusejp_1637_;
}
else
{
lean_object* v_reuseFailAlloc_1639_; 
v_reuseFailAlloc_1639_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1639_, 0, v_str_1629_);
lean_ctor_set(v_reuseFailAlloc_1639_, 1, v_startInclusive_1630_);
lean_ctor_set(v_reuseFailAlloc_1639_, 2, v___x_1636_);
v___x_1638_ = v_reuseFailAlloc_1639_;
goto v_reusejp_1637_;
}
v_reusejp_1637_:
{
return v___x_1638_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile(lean_object* v_00_u03c1_1644_, lean_object* v_s_1645_, lean_object* v_pat_1646_, lean_object* v_inst_1647_){
_start:
{
lean_object* v_str_1648_; lean_object* v_startInclusive_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; lean_object* v___x_1653_; uint8_t v_isShared_1654_; uint8_t v_isSharedCheck_1659_; 
v_str_1648_ = lean_ctor_get(v_s_1645_, 0);
lean_inc_ref(v_str_1648_);
v_startInclusive_1649_ = lean_ctor_get(v_s_1645_, 1);
lean_inc(v_startInclusive_1649_);
v___x_1650_ = lean_unsigned_to_nat(0u);
v___x_1651_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1645_, v___x_1650_, v_inst_1647_);
v_isSharedCheck_1659_ = !lean_is_exclusive(v_s_1645_);
if (v_isSharedCheck_1659_ == 0)
{
lean_object* v_unused_1660_; lean_object* v_unused_1661_; lean_object* v_unused_1662_; 
v_unused_1660_ = lean_ctor_get(v_s_1645_, 2);
lean_dec(v_unused_1660_);
v_unused_1661_ = lean_ctor_get(v_s_1645_, 1);
lean_dec(v_unused_1661_);
v_unused_1662_ = lean_ctor_get(v_s_1645_, 0);
lean_dec(v_unused_1662_);
v___x_1653_ = v_s_1645_;
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
else
{
lean_dec(v_s_1645_);
v___x_1653_ = lean_box(0);
v_isShared_1654_ = v_isSharedCheck_1659_;
goto v_resetjp_1652_;
}
v_resetjp_1652_:
{
lean_object* v___x_1655_; lean_object* v___x_1657_; 
v___x_1655_ = lean_nat_add(v_startInclusive_1649_, v___x_1651_);
lean_dec(v___x_1651_);
if (v_isShared_1654_ == 0)
{
lean_ctor_set(v___x_1653_, 2, v___x_1655_);
v___x_1657_ = v___x_1653_;
goto v_reusejp_1656_;
}
else
{
lean_object* v_reuseFailAlloc_1658_; 
v_reuseFailAlloc_1658_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1658_, 0, v_str_1648_);
lean_ctor_set(v_reuseFailAlloc_1658_, 1, v_startInclusive_1649_);
lean_ctor_set(v_reuseFailAlloc_1658_, 2, v___x_1655_);
v___x_1657_ = v_reuseFailAlloc_1658_;
goto v_reusejp_1656_;
}
v_reusejp_1656_:
{
return v___x_1657_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___boxed(lean_object* v_00_u03c1_1663_, lean_object* v_s_1664_, lean_object* v_pat_1665_, lean_object* v_inst_1666_){
_start:
{
lean_object* v_res_1667_; 
v_res_1667_ = l_String_Slice_takeWhile(v_00_u03c1_1663_, v_s_1664_, v_pat_1665_, v_inst_1666_);
lean_dec(v_pat_1665_);
return v_res_1667_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1(lean_object* v___x_1668_, lean_object* v_x1_1669_, lean_object* v_x2_1670_, lean_object* v_x3_1671_){
_start:
{
if (lean_obj_tag(v_x1_1669_) == 0)
{
lean_object* v___x_1672_; 
v___x_1672_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1672_, 0, v___x_1668_);
return v___x_1672_;
}
else
{
lean_object* v_startPos_1673_; lean_object* v___x_1674_; lean_object* v___x_1675_; 
lean_dec(v___x_1668_);
v_startPos_1673_ = lean_ctor_get(v_x1_1669_, 0);
lean_inc(v_startPos_1673_);
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v_startPos_1673_);
v___x_1675_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1675_, 0, v___x_1674_);
return v___x_1675_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1___boxed(lean_object* v___x_1676_, lean_object* v_x1_1677_, lean_object* v_x2_1678_, lean_object* v_x3_1679_){
_start:
{
lean_object* v_res_1680_; 
v_res_1680_ = l_String_Slice_find_x3f___redArg___lam__1(v___x_1676_, v_x1_1677_, v_x2_1678_, v_x3_1679_);
lean_dec(v_x3_1679_);
lean_dec_ref(v_x1_1677_);
return v_res_1680_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg(lean_object* v_inst_1683_, lean_object* v_s_1684_, lean_object* v_inst_1685_){
_start:
{
lean_object* v___f_1686_; lean_object* v_searcher_1687_; lean_object* v___x_1688_; lean_object* v___f_1689_; lean_object* v___x_1690_; 
v___f_1686_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1684_);
v_searcher_1687_ = lean_apply_1(v_inst_1685_, v_s_1684_);
v___x_1688_ = lean_box(0);
v___f_1689_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1690_ = lean_apply_7(v_inst_1683_, v_s_1684_, v___f_1686_, lean_box(0), lean_box(0), v_searcher_1687_, v___x_1688_, v___f_1689_);
return v___x_1690_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f(lean_object* v_00_u03c1_1691_, lean_object* v_00_u03c3_1692_, lean_object* v_inst_1693_, lean_object* v_inst_1694_, lean_object* v_s_1695_, lean_object* v_pat_1696_, lean_object* v_inst_1697_){
_start:
{
lean_object* v___f_1698_; lean_object* v_searcher_1699_; lean_object* v___x_1700_; lean_object* v___f_1701_; lean_object* v___x_1702_; 
v___f_1698_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1695_);
v_searcher_1699_ = lean_apply_1(v_inst_1697_, v_s_1695_);
v___x_1700_ = lean_box(0);
v___f_1701_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1702_ = lean_apply_7(v_inst_1694_, v_s_1695_, v___f_1698_, lean_box(0), lean_box(0), v_searcher_1699_, v___x_1700_, v___f_1701_);
return v___x_1702_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___boxed(lean_object* v_00_u03c1_1703_, lean_object* v_00_u03c3_1704_, lean_object* v_inst_1705_, lean_object* v_inst_1706_, lean_object* v_s_1707_, lean_object* v_pat_1708_, lean_object* v_inst_1709_){
_start:
{
lean_object* v_res_1710_; 
v_res_1710_ = l_String_Slice_find_x3f(v_00_u03c1_1703_, v_00_u03c3_1704_, v_inst_1705_, v_inst_1706_, v_s_1707_, v_pat_1708_, v_inst_1709_);
lean_dec(v_pat_1708_);
lean_dec(v_inst_1705_);
return v_res_1710_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___redArg(lean_object* v_inst_1711_, lean_object* v_s_1712_, lean_object* v_inst_1713_){
_start:
{
lean_object* v___f_1714_; lean_object* v_searcher_1715_; lean_object* v___x_1716_; lean_object* v___f_1717_; lean_object* v___x_1718_; 
v___f_1714_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1712_);
v_searcher_1715_ = lean_apply_1(v_inst_1713_, v_s_1712_);
v___x_1716_ = lean_box(0);
v___f_1717_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
lean_inc_ref(v_s_1712_);
v___x_1718_ = lean_apply_7(v_inst_1711_, v_s_1712_, v___f_1714_, lean_box(0), lean_box(0), v_searcher_1715_, v___x_1716_, v___f_1717_);
if (lean_obj_tag(v___x_1718_) == 0)
{
lean_object* v_startInclusive_1719_; lean_object* v_endExclusive_1720_; lean_object* v___x_1721_; 
v_startInclusive_1719_ = lean_ctor_get(v_s_1712_, 1);
lean_inc(v_startInclusive_1719_);
v_endExclusive_1720_ = lean_ctor_get(v_s_1712_, 2);
lean_inc(v_endExclusive_1720_);
lean_dec_ref(v_s_1712_);
v___x_1721_ = lean_nat_sub(v_endExclusive_1720_, v_startInclusive_1719_);
lean_dec(v_startInclusive_1719_);
lean_dec(v_endExclusive_1720_);
return v___x_1721_;
}
else
{
lean_object* v_val_1722_; 
lean_dec_ref(v_s_1712_);
v_val_1722_ = lean_ctor_get(v___x_1718_, 0);
lean_inc(v_val_1722_);
lean_dec_ref(v___x_1718_);
return v_val_1722_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find(lean_object* v_00_u03c1_1723_, lean_object* v_00_u03c3_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_s_1727_, lean_object* v_pat_1728_, lean_object* v_inst_1729_){
_start:
{
lean_object* v___f_1730_; lean_object* v_searcher_1731_; lean_object* v___x_1732_; lean_object* v___f_1733_; lean_object* v___x_1734_; 
v___f_1730_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1727_);
v_searcher_1731_ = lean_apply_1(v_inst_1729_, v_s_1727_);
v___x_1732_ = lean_box(0);
v___f_1733_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
lean_inc_ref(v_s_1727_);
v___x_1734_ = lean_apply_7(v_inst_1726_, v_s_1727_, v___f_1730_, lean_box(0), lean_box(0), v_searcher_1731_, v___x_1732_, v___f_1733_);
if (lean_obj_tag(v___x_1734_) == 0)
{
lean_object* v_startInclusive_1735_; lean_object* v_endExclusive_1736_; lean_object* v___x_1737_; 
v_startInclusive_1735_ = lean_ctor_get(v_s_1727_, 1);
lean_inc(v_startInclusive_1735_);
v_endExclusive_1736_ = lean_ctor_get(v_s_1727_, 2);
lean_inc(v_endExclusive_1736_);
lean_dec_ref(v_s_1727_);
v___x_1737_ = lean_nat_sub(v_endExclusive_1736_, v_startInclusive_1735_);
lean_dec(v_startInclusive_1735_);
lean_dec(v_endExclusive_1736_);
return v___x_1737_;
}
else
{
lean_object* v_val_1738_; 
lean_dec_ref(v_s_1727_);
v_val_1738_ = lean_ctor_get(v___x_1734_, 0);
lean_inc(v_val_1738_);
lean_dec_ref(v___x_1734_);
return v_val_1738_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___boxed(lean_object* v_00_u03c1_1739_, lean_object* v_00_u03c3_1740_, lean_object* v_inst_1741_, lean_object* v_inst_1742_, lean_object* v_s_1743_, lean_object* v_pat_1744_, lean_object* v_inst_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_String_Slice_find(v_00_u03c1_1739_, v_00_u03c3_1740_, v_inst_1741_, v_inst_1742_, v_s_1743_, v_pat_1744_, v_inst_1745_);
lean_dec(v_pat_1744_);
lean_dec(v_inst_1741_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1(uint8_t v___x_1750_, lean_object* v_x1_1751_, lean_object* v_x2_1752_, uint8_t v_x3_1753_){
_start:
{
if (lean_obj_tag(v_x1_1751_) == 1)
{
lean_object* v___x_1754_; 
v___x_1754_ = ((lean_object*)(l_String_Slice_contains___redArg___lam__1___closed__0));
return v___x_1754_;
}
else
{
lean_object* v___x_1755_; lean_object* v___x_1756_; 
v___x_1755_ = lean_box(v___x_1750_);
v___x_1756_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1756_, 0, v___x_1755_);
return v___x_1756_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1___boxed(lean_object* v___x_1757_, lean_object* v_x1_1758_, lean_object* v_x2_1759_, lean_object* v_x3_1760_){
_start:
{
uint8_t v___x_86__boxed_1761_; uint8_t v_x3_89__boxed_1762_; lean_object* v_res_1763_; 
v___x_86__boxed_1761_ = lean_unbox(v___x_1757_);
v_x3_89__boxed_1762_ = lean_unbox(v_x3_1760_);
v_res_1763_ = l_String_Slice_contains___redArg___lam__1(v___x_86__boxed_1761_, v_x1_1758_, v_x2_1759_, v_x3_89__boxed_1762_);
lean_dec_ref(v_x1_1758_);
return v_res_1763_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___redArg(lean_object* v_inst_1767_, lean_object* v_s_1768_, lean_object* v_inst_1769_){
_start:
{
lean_object* v___f_1770_; lean_object* v_searcher_1771_; uint8_t v___x_1772_; lean_object* v___f_1773_; lean_object* v___x_1774_; lean_object* v___x_1775_; uint8_t v___x_1776_; 
v___f_1770_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1768_);
v_searcher_1771_ = lean_apply_1(v_inst_1769_, v_s_1768_);
v___x_1772_ = 0;
v___f_1773_ = ((lean_object*)(l_String_Slice_contains___redArg___closed__0));
v___x_1774_ = lean_box(v___x_1772_);
v___x_1775_ = lean_apply_7(v_inst_1767_, v_s_1768_, v___f_1770_, lean_box(0), lean_box(0), v_searcher_1771_, v___x_1774_, v___f_1773_);
v___x_1776_ = lean_unbox(v___x_1775_);
return v___x_1776_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___boxed(lean_object* v_inst_1777_, lean_object* v_s_1778_, lean_object* v_inst_1779_){
_start:
{
uint8_t v_res_1780_; lean_object* v_r_1781_; 
v_res_1780_ = l_String_Slice_contains___redArg(v_inst_1777_, v_s_1778_, v_inst_1779_);
v_r_1781_ = lean_box(v_res_1780_);
return v_r_1781_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains(lean_object* v_00_u03c1_1782_, lean_object* v_00_u03c3_1783_, lean_object* v_inst_1784_, lean_object* v_inst_1785_, lean_object* v_s_1786_, lean_object* v_pat_1787_, lean_object* v_inst_1788_){
_start:
{
uint8_t v___x_1789_; 
v___x_1789_ = l_String_Slice_contains___redArg(v_inst_1785_, v_s_1786_, v_inst_1788_);
return v___x_1789_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___boxed(lean_object* v_00_u03c1_1790_, lean_object* v_00_u03c3_1791_, lean_object* v_inst_1792_, lean_object* v_inst_1793_, lean_object* v_s_1794_, lean_object* v_pat_1795_, lean_object* v_inst_1796_){
_start:
{
uint8_t v_res_1797_; lean_object* v_r_1798_; 
v_res_1797_ = l_String_Slice_contains(v_00_u03c1_1790_, v_00_u03c3_1791_, v_inst_1792_, v_inst_1793_, v_s_1794_, v_pat_1795_, v_inst_1796_);
lean_dec(v_pat_1795_);
lean_dec(v_inst_1792_);
v_r_1798_ = lean_box(v_res_1797_);
return v_r_1798_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any___redArg(lean_object* v_inst_1799_, lean_object* v_s_1800_, lean_object* v_inst_1801_){
_start:
{
uint8_t v___x_1802_; 
v___x_1802_ = l_String_Slice_contains___redArg(v_inst_1799_, v_s_1800_, v_inst_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___redArg___boxed(lean_object* v_inst_1803_, lean_object* v_s_1804_, lean_object* v_inst_1805_){
_start:
{
uint8_t v_res_1806_; lean_object* v_r_1807_; 
v_res_1806_ = l_String_Slice_any___redArg(v_inst_1803_, v_s_1804_, v_inst_1805_);
v_r_1807_ = lean_box(v_res_1806_);
return v_r_1807_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any(lean_object* v_00_u03c1_1808_, lean_object* v_00_u03c3_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_s_1812_, lean_object* v_pat_1813_, lean_object* v_inst_1814_){
_start:
{
uint8_t v___x_1815_; 
v___x_1815_ = l_String_Slice_contains___redArg(v_inst_1811_, v_s_1812_, v_inst_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___boxed(lean_object* v_00_u03c1_1816_, lean_object* v_00_u03c3_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_s_1820_, lean_object* v_pat_1821_, lean_object* v_inst_1822_){
_start:
{
uint8_t v_res_1823_; lean_object* v_r_1824_; 
v_res_1823_ = l_String_Slice_any(v_00_u03c1_1816_, v_00_u03c3_1817_, v_inst_1818_, v_inst_1819_, v_s_1820_, v_pat_1821_, v_inst_1822_);
lean_dec(v_pat_1821_);
lean_dec(v_inst_1818_);
v_r_1824_ = lean_box(v_res_1823_);
return v_r_1824_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all___redArg(lean_object* v_s_1825_, lean_object* v_inst_1826_){
_start:
{
lean_object* v_startInclusive_1827_; lean_object* v_endExclusive_1828_; lean_object* v___x_1829_; lean_object* v___x_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; uint8_t v___x_1833_; 
v_startInclusive_1827_ = lean_ctor_get(v_s_1825_, 1);
v_endExclusive_1828_ = lean_ctor_get(v_s_1825_, 2);
v___x_1829_ = lean_unsigned_to_nat(0u);
v___x_1830_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1825_, v___x_1829_, v_inst_1826_);
v___x_1831_ = lean_nat_add(v_startInclusive_1827_, v___x_1830_);
lean_dec(v___x_1830_);
v___x_1832_ = lean_nat_sub(v_endExclusive_1828_, v___x_1831_);
lean_dec(v___x_1831_);
v___x_1833_ = lean_nat_dec_eq(v___x_1832_, v___x_1829_);
lean_dec(v___x_1832_);
return v___x_1833_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___redArg___boxed(lean_object* v_s_1834_, lean_object* v_inst_1835_){
_start:
{
uint8_t v_res_1836_; lean_object* v_r_1837_; 
v_res_1836_ = l_String_Slice_all___redArg(v_s_1834_, v_inst_1835_);
lean_dec_ref(v_s_1834_);
v_r_1837_ = lean_box(v_res_1836_);
return v_r_1837_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all(lean_object* v_00_u03c1_1838_, lean_object* v_s_1839_, lean_object* v_pat_1840_, lean_object* v_inst_1841_){
_start:
{
lean_object* v_startInclusive_1842_; lean_object* v_endExclusive_1843_; lean_object* v___x_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v_startInclusive_1842_ = lean_ctor_get(v_s_1839_, 1);
v_endExclusive_1843_ = lean_ctor_get(v_s_1839_, 2);
v___x_1844_ = lean_unsigned_to_nat(0u);
v___x_1845_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1839_, v___x_1844_, v_inst_1841_);
v___x_1846_ = lean_nat_add(v_startInclusive_1842_, v___x_1845_);
lean_dec(v___x_1845_);
v___x_1847_ = lean_nat_sub(v_endExclusive_1843_, v___x_1846_);
lean_dec(v___x_1846_);
v___x_1848_ = lean_nat_dec_eq(v___x_1847_, v___x_1844_);
lean_dec(v___x_1847_);
return v___x_1848_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___boxed(lean_object* v_00_u03c1_1849_, lean_object* v_s_1850_, lean_object* v_pat_1851_, lean_object* v_inst_1852_){
_start:
{
uint8_t v_res_1853_; lean_object* v_r_1854_; 
v_res_1853_ = l_String_Slice_all(v_00_u03c1_1849_, v_s_1850_, v_pat_1851_, v_inst_1852_);
lean_dec(v_pat_1851_);
lean_dec_ref(v_s_1850_);
v_r_1854_ = lean_box(v_res_1853_);
return v_r_1854_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith___redArg(lean_object* v_s_1855_, lean_object* v_inst_1856_){
_start:
{
lean_object* v_endsWith_1857_; lean_object* v___x_1858_; uint8_t v___x_1859_; 
v_endsWith_1857_ = lean_ctor_get(v_inst_1856_, 2);
lean_inc_ref(v_endsWith_1857_);
lean_dec_ref(v_inst_1856_);
v___x_1858_ = lean_apply_1(v_endsWith_1857_, v_s_1855_);
v___x_1859_ = lean_unbox(v___x_1858_);
return v___x_1859_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___redArg___boxed(lean_object* v_s_1860_, lean_object* v_inst_1861_){
_start:
{
uint8_t v_res_1862_; lean_object* v_r_1863_; 
v_res_1862_ = l_String_Slice_endsWith___redArg(v_s_1860_, v_inst_1861_);
v_r_1863_ = lean_box(v_res_1862_);
return v_r_1863_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith(lean_object* v_00_u03c1_1864_, lean_object* v_s_1865_, lean_object* v_pat_1866_, lean_object* v_inst_1867_){
_start:
{
lean_object* v_endsWith_1868_; lean_object* v___x_1869_; uint8_t v___x_1870_; 
v_endsWith_1868_ = lean_ctor_get(v_inst_1867_, 2);
lean_inc_ref(v_endsWith_1868_);
lean_dec_ref(v_inst_1867_);
v___x_1869_ = lean_apply_1(v_endsWith_1868_, v_s_1865_);
v___x_1870_ = lean_unbox(v___x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___boxed(lean_object* v_00_u03c1_1871_, lean_object* v_s_1872_, lean_object* v_pat_1873_, lean_object* v_inst_1874_){
_start:
{
uint8_t v_res_1875_; lean_object* v_r_1876_; 
v_res_1875_ = l_String_Slice_endsWith(v_00_u03c1_1871_, v_s_1872_, v_pat_1873_, v_inst_1874_);
lean_dec(v_pat_1873_);
v_r_1876_ = lean_box(v_res_1875_);
return v_r_1876_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___redArg(lean_object* v_x_1877_){
_start:
{
if (lean_obj_tag(v_x_1877_) == 0)
{
lean_object* v___x_1878_; 
v___x_1878_ = lean_unsigned_to_nat(0u);
return v___x_1878_;
}
else
{
lean_object* v___x_1879_; 
v___x_1879_ = lean_unsigned_to_nat(1u);
return v___x_1879_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___redArg___boxed(lean_object* v_x_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_String_Slice_RevSplitIterator_ctorIdx___redArg(v_x_1880_);
lean_dec(v_x_1880_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx(lean_object* v_00_u03c3_1882_, lean_object* v_00_u03c1_1883_, lean_object* v_pat_1884_, lean_object* v_s_1885_, lean_object* v_inst_1886_, lean_object* v_x_1887_){
_start:
{
lean_object* v___x_1888_; 
v___x_1888_ = l_String_Slice_RevSplitIterator_ctorIdx___redArg(v_x_1887_);
return v___x_1888_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___boxed(lean_object* v_00_u03c3_1889_, lean_object* v_00_u03c1_1890_, lean_object* v_pat_1891_, lean_object* v_s_1892_, lean_object* v_inst_1893_, lean_object* v_x_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_String_Slice_RevSplitIterator_ctorIdx(v_00_u03c3_1889_, v_00_u03c1_1890_, v_pat_1891_, v_s_1892_, v_inst_1893_, v_x_1894_);
lean_dec(v_x_1894_);
lean_dec(v_inst_1893_);
lean_dec_ref(v_s_1892_);
lean_dec(v_pat_1891_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___redArg(lean_object* v_t_1896_, lean_object* v_k_1897_){
_start:
{
if (lean_obj_tag(v_t_1896_) == 0)
{
lean_object* v_currPos_1898_; lean_object* v_searcher_1899_; lean_object* v___x_1900_; 
v_currPos_1898_ = lean_ctor_get(v_t_1896_, 0);
lean_inc(v_currPos_1898_);
v_searcher_1899_ = lean_ctor_get(v_t_1896_, 1);
lean_inc(v_searcher_1899_);
lean_dec_ref(v_t_1896_);
v___x_1900_ = lean_apply_2(v_k_1897_, v_currPos_1898_, v_searcher_1899_);
return v___x_1900_;
}
else
{
return v_k_1897_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim(lean_object* v_00_u03c3_1901_, lean_object* v_00_u03c1_1902_, lean_object* v_pat_1903_, lean_object* v_s_1904_, lean_object* v_inst_1905_, lean_object* v_motive_1906_, lean_object* v_ctorIdx_1907_, lean_object* v_t_1908_, lean_object* v_h_1909_, lean_object* v_k_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1908_, v_k_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_1912_, lean_object* v_00_u03c1_1913_, lean_object* v_pat_1914_, lean_object* v_s_1915_, lean_object* v_inst_1916_, lean_object* v_motive_1917_, lean_object* v_ctorIdx_1918_, lean_object* v_t_1919_, lean_object* v_h_1920_, lean_object* v_k_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_String_Slice_RevSplitIterator_ctorElim(v_00_u03c3_1912_, v_00_u03c1_1913_, v_pat_1914_, v_s_1915_, v_inst_1916_, v_motive_1917_, v_ctorIdx_1918_, v_t_1919_, v_h_1920_, v_k_1921_);
lean_dec(v_ctorIdx_1918_);
lean_dec(v_inst_1916_);
lean_dec_ref(v_s_1915_);
lean_dec(v_pat_1914_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___redArg(lean_object* v_t_1923_, lean_object* v_operating_1924_){
_start:
{
lean_object* v___x_1925_; 
v___x_1925_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1923_, v_operating_1924_);
return v___x_1925_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim(lean_object* v_00_u03c3_1926_, lean_object* v_00_u03c1_1927_, lean_object* v_pat_1928_, lean_object* v_s_1929_, lean_object* v_inst_1930_, lean_object* v_motive_1931_, lean_object* v_t_1932_, lean_object* v_h_1933_, lean_object* v_operating_1934_){
_start:
{
lean_object* v___x_1935_; 
v___x_1935_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1932_, v_operating_1934_);
return v___x_1935_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_1936_, lean_object* v_00_u03c1_1937_, lean_object* v_pat_1938_, lean_object* v_s_1939_, lean_object* v_inst_1940_, lean_object* v_motive_1941_, lean_object* v_t_1942_, lean_object* v_h_1943_, lean_object* v_operating_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_String_Slice_RevSplitIterator_operating_elim(v_00_u03c3_1936_, v_00_u03c1_1937_, v_pat_1938_, v_s_1939_, v_inst_1940_, v_motive_1941_, v_t_1942_, v_h_1943_, v_operating_1944_);
lean_dec(v_inst_1940_);
lean_dec_ref(v_s_1939_);
lean_dec(v_pat_1938_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___redArg(lean_object* v_t_1946_, lean_object* v_atEnd_1947_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1946_, v_atEnd_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim(lean_object* v_00_u03c3_1949_, lean_object* v_00_u03c1_1950_, lean_object* v_pat_1951_, lean_object* v_s_1952_, lean_object* v_inst_1953_, lean_object* v_motive_1954_, lean_object* v_t_1955_, lean_object* v_h_1956_, lean_object* v_atEnd_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1955_, v_atEnd_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_1959_, lean_object* v_00_u03c1_1960_, lean_object* v_pat_1961_, lean_object* v_s_1962_, lean_object* v_inst_1963_, lean_object* v_motive_1964_, lean_object* v_t_1965_, lean_object* v_h_1966_, lean_object* v_atEnd_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_String_Slice_RevSplitIterator_atEnd_elim(v_00_u03c3_1959_, v_00_u03c1_1960_, v_pat_1961_, v_s_1962_, v_inst_1963_, v_motive_1964_, v_t_1965_, v_h_1966_, v_atEnd_1967_);
lean_dec(v_inst_1963_);
lean_dec_ref(v_s_1962_);
lean_dec(v_pat_1961_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default(lean_object* v_a_1969_, lean_object* v_a_1970_, lean_object* v_a_1971_, lean_object* v_a_1972_, lean_object* v_a_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_box(1);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___boxed(lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_, lean_object* v_a_1978_, lean_object* v_a_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_String_Slice_instInhabitedRevSplitIterator_default(v_a_1975_, v_a_1976_, v_a_1977_, v_a_1978_, v_a_1979_);
lean_dec(v_a_1979_);
lean_dec_ref(v_a_1978_);
lean_dec(v_a_1977_);
return v_res_1980_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator(lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_, lean_object* v_a_1984_, lean_object* v_a_1985_){
_start:
{
lean_object* v___x_1986_; 
v___x_1986_ = lean_box(1);
return v___x_1986_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___boxed(lean_object* v_a_1987_, lean_object* v_a_1988_, lean_object* v_a_1989_, lean_object* v_a_1990_, lean_object* v_a_1991_){
_start:
{
lean_object* v_res_1992_; 
v_res_1992_ = l_String_Slice_instInhabitedRevSplitIterator(v_a_1987_, v_a_1988_, v_a_1989_, v_a_1990_, v_a_1991_);
lean_dec(v_a_1991_);
lean_dec_ref(v_a_1990_);
lean_dec(v_a_1989_);
return v_res_1992_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0(lean_object* v_inst_1993_, lean_object* v_s_1994_, lean_object* v_inst_1995_, lean_object* v_x_1996_){
_start:
{
if (lean_obj_tag(v_x_1996_) == 0)
{
lean_object* v_currPos_1997_; lean_object* v_searcher_1998_; lean_object* v___x_2000_; uint8_t v_isShared_2001_; uint8_t v_isSharedCheck_2056_; 
v_currPos_1997_ = lean_ctor_get(v_x_1996_, 0);
v_searcher_1998_ = lean_ctor_get(v_x_1996_, 1);
v_isSharedCheck_2056_ = !lean_is_exclusive(v_x_1996_);
if (v_isSharedCheck_2056_ == 0)
{
v___x_2000_ = v_x_1996_;
v_isShared_2001_ = v_isSharedCheck_2056_;
goto v_resetjp_1999_;
}
else
{
lean_inc(v_searcher_1998_);
lean_inc(v_currPos_1997_);
lean_dec(v_x_1996_);
v___x_2000_ = lean_box(0);
v_isShared_2001_ = v_isSharedCheck_2056_;
goto v_resetjp_1999_;
}
v_resetjp_1999_:
{
lean_object* v___x_2002_; 
lean_inc_ref(v_s_1994_);
v___x_2002_ = lean_apply_2(v_inst_1993_, v_s_1994_, v_searcher_1998_);
switch(lean_obj_tag(v___x_2002_))
{
case 0:
{
lean_object* v_out_2003_; 
v_out_2003_ = lean_ctor_get(v___x_2002_, 1);
lean_inc(v_out_2003_);
if (lean_obj_tag(v_out_2003_) == 0)
{
lean_object* v_it_2004_; lean_object* v___x_2006_; 
lean_dec_ref(v_out_2003_);
lean_dec_ref(v_s_1994_);
v_it_2004_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_it_2004_);
lean_dec_ref(v___x_2002_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v_it_2004_);
v___x_2006_ = v___x_2000_;
goto v_reusejp_2005_;
}
else
{
lean_object* v_reuseFailAlloc_2009_; 
v_reuseFailAlloc_2009_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2009_, 0, v_currPos_1997_);
lean_ctor_set(v_reuseFailAlloc_2009_, 1, v_it_2004_);
v___x_2006_ = v_reuseFailAlloc_2009_;
goto v_reusejp_2005_;
}
v_reusejp_2005_:
{
lean_object* v___x_2007_; lean_object* v___x_2008_; 
v___x_2007_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2007_, 0, v___x_2006_);
v___x_2008_ = lean_apply_2(v_inst_1995_, lean_box(0), v___x_2007_);
return v___x_2008_;
}
}
else
{
lean_object* v_it_2010_; lean_object* v___x_2012_; uint8_t v_isShared_2013_; uint8_t v_isSharedCheck_2024_; 
v_it_2010_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2024_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2024_ == 0)
{
lean_object* v_unused_2025_; 
v_unused_2025_ = lean_ctor_get(v___x_2002_, 1);
lean_dec(v_unused_2025_);
v___x_2012_ = v___x_2002_;
v_isShared_2013_ = v_isSharedCheck_2024_;
goto v_resetjp_2011_;
}
else
{
lean_inc(v_it_2010_);
lean_dec(v___x_2002_);
v___x_2012_ = lean_box(0);
v_isShared_2013_ = v_isSharedCheck_2024_;
goto v_resetjp_2011_;
}
v_resetjp_2011_:
{
lean_object* v_startPos_2014_; lean_object* v_endPos_2015_; lean_object* v_slice_2016_; lean_object* v_nextIt_2018_; 
v_startPos_2014_ = lean_ctor_get(v_out_2003_, 0);
lean_inc(v_startPos_2014_);
v_endPos_2015_ = lean_ctor_get(v_out_2003_, 1);
lean_inc(v_endPos_2015_);
lean_dec_ref(v_out_2003_);
v_slice_2016_ = l_String_Slice_slice_x21(v_s_1994_, v_endPos_2015_, v_currPos_1997_);
lean_dec(v_currPos_1997_);
lean_dec(v_endPos_2015_);
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v_it_2010_);
lean_ctor_set(v___x_2000_, 0, v_startPos_2014_);
v_nextIt_2018_ = v___x_2000_;
goto v_reusejp_2017_;
}
else
{
lean_object* v_reuseFailAlloc_2023_; 
v_reuseFailAlloc_2023_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2023_, 0, v_startPos_2014_);
lean_ctor_set(v_reuseFailAlloc_2023_, 1, v_it_2010_);
v_nextIt_2018_ = v_reuseFailAlloc_2023_;
goto v_reusejp_2017_;
}
v_reusejp_2017_:
{
lean_object* v___x_2020_; 
if (v_isShared_2013_ == 0)
{
lean_ctor_set(v___x_2012_, 1, v_slice_2016_);
lean_ctor_set(v___x_2012_, 0, v_nextIt_2018_);
v___x_2020_ = v___x_2012_;
goto v_reusejp_2019_;
}
else
{
lean_object* v_reuseFailAlloc_2022_; 
v_reuseFailAlloc_2022_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2022_, 0, v_nextIt_2018_);
lean_ctor_set(v_reuseFailAlloc_2022_, 1, v_slice_2016_);
v___x_2020_ = v_reuseFailAlloc_2022_;
goto v_reusejp_2019_;
}
v_reusejp_2019_:
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_apply_2(v_inst_1995_, lean_box(0), v___x_2020_);
return v___x_2021_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2026_; lean_object* v___x_2028_; uint8_t v_isShared_2029_; uint8_t v_isSharedCheck_2037_; 
lean_dec_ref(v_s_1994_);
v_it_2026_ = lean_ctor_get(v___x_2002_, 0);
v_isSharedCheck_2037_ = !lean_is_exclusive(v___x_2002_);
if (v_isSharedCheck_2037_ == 0)
{
v___x_2028_ = v___x_2002_;
v_isShared_2029_ = v_isSharedCheck_2037_;
goto v_resetjp_2027_;
}
else
{
lean_inc(v_it_2026_);
lean_dec(v___x_2002_);
v___x_2028_ = lean_box(0);
v_isShared_2029_ = v_isSharedCheck_2037_;
goto v_resetjp_2027_;
}
v_resetjp_2027_:
{
lean_object* v___x_2031_; 
if (v_isShared_2001_ == 0)
{
lean_ctor_set(v___x_2000_, 1, v_it_2026_);
v___x_2031_ = v___x_2000_;
goto v_reusejp_2030_;
}
else
{
lean_object* v_reuseFailAlloc_2036_; 
v_reuseFailAlloc_2036_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2036_, 0, v_currPos_1997_);
lean_ctor_set(v_reuseFailAlloc_2036_, 1, v_it_2026_);
v___x_2031_ = v_reuseFailAlloc_2036_;
goto v_reusejp_2030_;
}
v_reusejp_2030_:
{
lean_object* v___x_2033_; 
if (v_isShared_2029_ == 0)
{
lean_ctor_set(v___x_2028_, 0, v___x_2031_);
v___x_2033_ = v___x_2028_;
goto v_reusejp_2032_;
}
else
{
lean_object* v_reuseFailAlloc_2035_; 
v_reuseFailAlloc_2035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2035_, 0, v___x_2031_);
v___x_2033_ = v_reuseFailAlloc_2035_;
goto v_reusejp_2032_;
}
v_reusejp_2032_:
{
lean_object* v___x_2034_; 
v___x_2034_ = lean_apply_2(v_inst_1995_, lean_box(0), v___x_2033_);
return v___x_2034_;
}
}
}
}
default: 
{
lean_object* v___x_2038_; uint8_t v___x_2039_; 
lean_del_object(v___x_2000_);
v___x_2038_ = lean_unsigned_to_nat(0u);
v___x_2039_ = lean_nat_dec_eq(v_currPos_1997_, v___x_2038_);
if (v___x_2039_ == 0)
{
lean_object* v_str_2040_; lean_object* v_startInclusive_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2052_; 
v_str_2040_ = lean_ctor_get(v_s_1994_, 0);
v_startInclusive_2041_ = lean_ctor_get(v_s_1994_, 1);
v_isSharedCheck_2052_ = !lean_is_exclusive(v_s_1994_);
if (v_isSharedCheck_2052_ == 0)
{
lean_object* v_unused_2053_; 
v_unused_2053_ = lean_ctor_get(v_s_1994_, 2);
lean_dec(v_unused_2053_);
v___x_2043_ = v_s_1994_;
v_isShared_2044_ = v_isSharedCheck_2052_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_startInclusive_2041_);
lean_inc(v_str_2040_);
lean_dec(v_s_1994_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2052_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v___x_2045_; lean_object* v_slice_2047_; 
v___x_2045_ = lean_nat_add(v_startInclusive_2041_, v_currPos_1997_);
lean_dec(v_currPos_1997_);
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 2, v___x_2045_);
v_slice_2047_ = v___x_2043_;
goto v_reusejp_2046_;
}
else
{
lean_object* v_reuseFailAlloc_2051_; 
v_reuseFailAlloc_2051_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2051_, 0, v_str_2040_);
lean_ctor_set(v_reuseFailAlloc_2051_, 1, v_startInclusive_2041_);
lean_ctor_set(v_reuseFailAlloc_2051_, 2, v___x_2045_);
v_slice_2047_ = v_reuseFailAlloc_2051_;
goto v_reusejp_2046_;
}
v_reusejp_2046_:
{
lean_object* v___x_2048_; lean_object* v___x_2049_; lean_object* v___x_2050_; 
v___x_2048_ = lean_box(1);
v___x_2049_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2049_, 0, v___x_2048_);
lean_ctor_set(v___x_2049_, 1, v_slice_2047_);
v___x_2050_ = lean_apply_2(v_inst_1995_, lean_box(0), v___x_2049_);
return v___x_2050_;
}
}
}
else
{
lean_object* v___x_2054_; lean_object* v___x_2055_; 
lean_dec(v_currPos_1997_);
lean_dec_ref(v_s_1994_);
v___x_2054_ = lean_box(2);
v___x_2055_ = lean_apply_2(v_inst_1995_, lean_box(0), v___x_2054_);
return v___x_2055_;
}
}
}
}
}
else
{
lean_object* v___x_2057_; lean_object* v___x_2058_; 
lean_dec_ref(v_s_1994_);
lean_dec(v_inst_1993_);
v___x_2057_ = lean_box(2);
v___x_2058_ = lean_apply_2(v_inst_1995_, lean_box(0), v___x_2057_);
return v___x_2058_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg(lean_object* v_inst_2059_, lean_object* v_s_2060_, lean_object* v_inst_2061_){
_start:
{
lean_object* v___f_2062_; 
v___f_2062_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2062_, 0, v_inst_2059_);
lean_closure_set(v___f_2062_, 1, v_s_2060_);
lean_closure_set(v___f_2062_, 2, v_inst_2061_);
return v___f_2062_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure(lean_object* v_00_u03c1_2063_, lean_object* v_00_u03c1_2064_, lean_object* v_00_u03c3_2065_, lean_object* v_inst_2066_, lean_object* v_inst_2067_, lean_object* v_m_2068_, lean_object* v_s_2069_, lean_object* v_inst_2070_){
_start:
{
lean_object* v___f_2071_; 
v___f_2071_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2071_, 0, v_inst_2066_);
lean_closure_set(v___f_2071_, 1, v_s_2069_);
lean_closure_set(v___f_2071_, 2, v_inst_2070_);
return v___f_2071_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___boxed(lean_object* v_00_u03c1_2072_, lean_object* v_00_u03c1_2073_, lean_object* v_00_u03c3_2074_, lean_object* v_inst_2075_, lean_object* v_inst_2076_, lean_object* v_m_2077_, lean_object* v_s_2078_, lean_object* v_inst_2079_){
_start:
{
lean_object* v_res_2080_; 
v_res_2080_ = l_String_Slice_RevSplitIterator_instIteratorOfPure(v_00_u03c1_2072_, v_00_u03c1_2073_, v_00_u03c3_2074_, v_inst_2075_, v_inst_2076_, v_m_2077_, v_s_2078_, v_inst_2079_);
lean_dec(v_inst_2076_);
lean_dec(v_00_u03c1_2073_);
return v_res_2080_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(lean_object* v_x_2081_){
_start:
{
if (lean_obj_tag(v_x_2081_) == 0)
{
lean_object* v_searcher_2082_; lean_object* v___x_2083_; 
v_searcher_2082_ = lean_ctor_get(v_x_2081_, 1);
lean_inc(v_searcher_2082_);
v___x_2083_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2083_, 0, v_searcher_2082_);
return v___x_2083_;
}
else
{
lean_object* v___x_2084_; 
v___x_2084_ = lean_box(0);
return v___x_2084_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg___boxed(lean_object* v_x_2085_){
_start:
{
lean_object* v_res_2086_; 
v_res_2086_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2085_);
lean_dec(v_x_2085_);
return v_res_2086_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(lean_object* v_00_u03c1_2087_, lean_object* v_00_u03c1_2088_, lean_object* v_00_u03c3_2089_, lean_object* v_inst_2090_, lean_object* v_s_2091_, lean_object* v_x_2092_){
_start:
{
lean_object* v___x_2093_; 
v___x_2093_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2092_);
return v___x_2093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___boxed(lean_object* v_00_u03c1_2094_, lean_object* v_00_u03c1_2095_, lean_object* v_00_u03c3_2096_, lean_object* v_inst_2097_, lean_object* v_s_2098_, lean_object* v_x_2099_){
_start:
{
lean_object* v_res_2100_; 
v_res_2100_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(v_00_u03c1_2094_, v_00_u03c1_2095_, v_00_u03c3_2096_, v_inst_2097_, v_s_2098_, v_x_2099_);
lean_dec(v_x_2099_);
lean_dec_ref(v_s_2098_);
lean_dec(v_inst_2097_);
lean_dec(v_00_u03c1_2095_);
return v_res_2100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(lean_object* v_x_2101_, lean_object* v_h__1_2102_, lean_object* v_h__2_2103_){
_start:
{
if (lean_obj_tag(v_x_2101_) == 0)
{
lean_object* v_currPos_2104_; lean_object* v_searcher_2105_; lean_object* v___x_2106_; 
lean_dec(v_h__2_2103_);
v_currPos_2104_ = lean_ctor_get(v_x_2101_, 0);
lean_inc(v_currPos_2104_);
v_searcher_2105_ = lean_ctor_get(v_x_2101_, 1);
lean_inc(v_searcher_2105_);
lean_dec_ref(v_x_2101_);
v___x_2106_ = lean_apply_2(v_h__1_2102_, v_currPos_2104_, v_searcher_2105_);
return v___x_2106_;
}
else
{
lean_object* v___x_2107_; lean_object* v___x_2108_; 
lean_dec(v_h__1_2102_);
v___x_2107_ = lean_box(0);
v___x_2108_ = lean_apply_1(v_h__2_2103_, v___x_2107_);
return v___x_2108_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(lean_object* v_00_u03c1_2109_, lean_object* v_00_u03c1_2110_, lean_object* v_00_u03c3_2111_, lean_object* v_inst_2112_, lean_object* v_m_2113_, lean_object* v_s_2114_, lean_object* v_motive_2115_, lean_object* v_x_2116_, lean_object* v_h__1_2117_, lean_object* v_h__2_2118_){
_start:
{
if (lean_obj_tag(v_x_2116_) == 0)
{
lean_object* v_currPos_2119_; lean_object* v_searcher_2120_; lean_object* v___x_2121_; 
lean_dec(v_h__2_2118_);
v_currPos_2119_ = lean_ctor_get(v_x_2116_, 0);
lean_inc(v_currPos_2119_);
v_searcher_2120_ = lean_ctor_get(v_x_2116_, 1);
lean_inc(v_searcher_2120_);
lean_dec_ref(v_x_2116_);
v___x_2121_ = lean_apply_2(v_h__1_2117_, v_currPos_2119_, v_searcher_2120_);
return v___x_2121_;
}
else
{
lean_object* v___x_2122_; lean_object* v___x_2123_; 
lean_dec(v_h__1_2117_);
v___x_2122_ = lean_box(0);
v___x_2123_ = lean_apply_1(v_h__2_2118_, v___x_2122_);
return v___x_2123_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___boxed(lean_object* v_00_u03c1_2124_, lean_object* v_00_u03c1_2125_, lean_object* v_00_u03c3_2126_, lean_object* v_inst_2127_, lean_object* v_m_2128_, lean_object* v_s_2129_, lean_object* v_motive_2130_, lean_object* v_x_2131_, lean_object* v_h__1_2132_, lean_object* v_h__2_2133_){
_start:
{
lean_object* v_res_2134_; 
v_res_2134_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(v_00_u03c1_2124_, v_00_u03c1_2125_, v_00_u03c3_2126_, v_inst_2127_, v_m_2128_, v_s_2129_, v_motive_2130_, v_x_2131_, v_h__1_2132_, v_h__2_2133_);
lean_dec_ref(v_s_2129_);
lean_dec(v_inst_2127_);
lean_dec(v_00_u03c1_2125_);
return v_res_2134_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(lean_object* v_x_2135_, lean_object* v_x_2136_, lean_object* v_h__1_2137_, lean_object* v_h__2_2138_, lean_object* v_h__3_2139_, lean_object* v_h__4_2140_, lean_object* v_h__5_2141_, lean_object* v_h__6_2142_, lean_object* v_h__7_2143_, lean_object* v_h__8_2144_){
_start:
{
if (lean_obj_tag(v_x_2135_) == 0)
{
lean_dec(v_h__8_2144_);
lean_dec(v_h__7_2143_);
lean_dec(v_h__6_2142_);
switch(lean_obj_tag(v_x_2136_))
{
case 0:
{
lean_object* v_it_2145_; 
lean_dec(v_h__5_2141_);
lean_dec(v_h__4_2140_);
lean_dec(v_h__3_2139_);
v_it_2145_ = lean_ctor_get(v_x_2136_, 0);
if (lean_obj_tag(v_it_2145_) == 0)
{
lean_object* v_currPos_2146_; lean_object* v_searcher_2147_; lean_object* v_out_2148_; lean_object* v_currPos_2149_; lean_object* v_searcher_2150_; lean_object* v___x_2151_; 
lean_inc_ref(v_it_2145_);
lean_dec(v_h__2_2138_);
v_currPos_2146_ = lean_ctor_get(v_x_2135_, 0);
lean_inc(v_currPos_2146_);
v_searcher_2147_ = lean_ctor_get(v_x_2135_, 1);
lean_inc(v_searcher_2147_);
lean_dec_ref(v_x_2135_);
v_out_2148_ = lean_ctor_get(v_x_2136_, 1);
lean_inc(v_out_2148_);
lean_dec_ref(v_x_2136_);
v_currPos_2149_ = lean_ctor_get(v_it_2145_, 0);
lean_inc(v_currPos_2149_);
v_searcher_2150_ = lean_ctor_get(v_it_2145_, 1);
lean_inc(v_searcher_2150_);
lean_dec_ref(v_it_2145_);
v___x_2151_ = lean_apply_5(v_h__1_2137_, v_currPos_2146_, v_searcher_2147_, v_currPos_2149_, v_searcher_2150_, v_out_2148_);
return v___x_2151_;
}
else
{
lean_object* v_currPos_2152_; lean_object* v_searcher_2153_; lean_object* v_out_2154_; lean_object* v___x_2155_; 
lean_dec(v_h__1_2137_);
v_currPos_2152_ = lean_ctor_get(v_x_2135_, 0);
lean_inc(v_currPos_2152_);
v_searcher_2153_ = lean_ctor_get(v_x_2135_, 1);
lean_inc(v_searcher_2153_);
lean_dec_ref(v_x_2135_);
v_out_2154_ = lean_ctor_get(v_x_2136_, 1);
lean_inc(v_out_2154_);
lean_dec_ref(v_x_2136_);
v___x_2155_ = lean_apply_3(v_h__2_2138_, v_currPos_2152_, v_searcher_2153_, v_out_2154_);
return v___x_2155_;
}
}
case 1:
{
lean_object* v_it_2156_; 
lean_dec(v_h__5_2141_);
lean_dec(v_h__2_2138_);
lean_dec(v_h__1_2137_);
v_it_2156_ = lean_ctor_get(v_x_2136_, 0);
lean_inc(v_it_2156_);
lean_dec_ref(v_x_2136_);
if (lean_obj_tag(v_it_2156_) == 0)
{
lean_object* v_currPos_2157_; lean_object* v_searcher_2158_; lean_object* v_currPos_2159_; lean_object* v_searcher_2160_; lean_object* v___x_2161_; 
lean_dec(v_h__4_2140_);
v_currPos_2157_ = lean_ctor_get(v_x_2135_, 0);
lean_inc(v_currPos_2157_);
v_searcher_2158_ = lean_ctor_get(v_x_2135_, 1);
lean_inc(v_searcher_2158_);
lean_dec_ref(v_x_2135_);
v_currPos_2159_ = lean_ctor_get(v_it_2156_, 0);
lean_inc(v_currPos_2159_);
v_searcher_2160_ = lean_ctor_get(v_it_2156_, 1);
lean_inc(v_searcher_2160_);
lean_dec_ref(v_it_2156_);
v___x_2161_ = lean_apply_4(v_h__3_2139_, v_currPos_2157_, v_searcher_2158_, v_currPos_2159_, v_searcher_2160_);
return v___x_2161_;
}
else
{
lean_object* v_currPos_2162_; lean_object* v_searcher_2163_; lean_object* v___x_2164_; 
lean_dec(v_h__3_2139_);
v_currPos_2162_ = lean_ctor_get(v_x_2135_, 0);
lean_inc(v_currPos_2162_);
v_searcher_2163_ = lean_ctor_get(v_x_2135_, 1);
lean_inc(v_searcher_2163_);
lean_dec_ref(v_x_2135_);
v___x_2164_ = lean_apply_2(v_h__4_2140_, v_currPos_2162_, v_searcher_2163_);
return v___x_2164_;
}
}
default: 
{
lean_object* v_currPos_2165_; lean_object* v_searcher_2166_; lean_object* v___x_2167_; 
lean_dec(v_h__4_2140_);
lean_dec(v_h__3_2139_);
lean_dec(v_h__2_2138_);
lean_dec(v_h__1_2137_);
v_currPos_2165_ = lean_ctor_get(v_x_2135_, 0);
lean_inc(v_currPos_2165_);
v_searcher_2166_ = lean_ctor_get(v_x_2135_, 1);
lean_inc(v_searcher_2166_);
lean_dec_ref(v_x_2135_);
v___x_2167_ = lean_apply_2(v_h__5_2141_, v_currPos_2165_, v_searcher_2166_);
return v___x_2167_;
}
}
}
else
{
lean_dec(v_h__5_2141_);
lean_dec(v_h__4_2140_);
lean_dec(v_h__3_2139_);
lean_dec(v_h__2_2138_);
lean_dec(v_h__1_2137_);
switch(lean_obj_tag(v_x_2136_))
{
case 0:
{
lean_object* v_it_2168_; lean_object* v_out_2169_; lean_object* v___x_2170_; 
lean_dec(v_h__8_2144_);
lean_dec(v_h__7_2143_);
v_it_2168_ = lean_ctor_get(v_x_2136_, 0);
lean_inc(v_it_2168_);
v_out_2169_ = lean_ctor_get(v_x_2136_, 1);
lean_inc(v_out_2169_);
lean_dec_ref(v_x_2136_);
v___x_2170_ = lean_apply_2(v_h__6_2142_, v_it_2168_, v_out_2169_);
return v___x_2170_;
}
case 1:
{
lean_object* v_it_2171_; lean_object* v___x_2172_; 
lean_dec(v_h__8_2144_);
lean_dec(v_h__6_2142_);
v_it_2171_ = lean_ctor_get(v_x_2136_, 0);
lean_inc(v_it_2171_);
lean_dec_ref(v_x_2136_);
v___x_2172_ = lean_apply_1(v_h__7_2143_, v_it_2171_);
return v___x_2172_;
}
default: 
{
lean_object* v___x_2173_; lean_object* v___x_2174_; 
lean_dec(v_h__7_2143_);
lean_dec(v_h__6_2142_);
v___x_2173_ = lean_box(0);
v___x_2174_ = lean_apply_1(v_h__8_2144_, v___x_2173_);
return v___x_2174_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(lean_object* v_00_u03c1_2175_, lean_object* v_00_u03c1_2176_, lean_object* v_00_u03c3_2177_, lean_object* v_inst_2178_, lean_object* v_m_2179_, lean_object* v_s_2180_, lean_object* v_motive_2181_, lean_object* v_x_2182_, lean_object* v_x_2183_, lean_object* v_h__1_2184_, lean_object* v_h__2_2185_, lean_object* v_h__3_2186_, lean_object* v_h__4_2187_, lean_object* v_h__5_2188_, lean_object* v_h__6_2189_, lean_object* v_h__7_2190_, lean_object* v_h__8_2191_){
_start:
{
if (lean_obj_tag(v_x_2182_) == 0)
{
lean_dec(v_h__8_2191_);
lean_dec(v_h__7_2190_);
lean_dec(v_h__6_2189_);
switch(lean_obj_tag(v_x_2183_))
{
case 0:
{
lean_object* v_it_2192_; 
lean_dec(v_h__5_2188_);
lean_dec(v_h__4_2187_);
lean_dec(v_h__3_2186_);
v_it_2192_ = lean_ctor_get(v_x_2183_, 0);
if (lean_obj_tag(v_it_2192_) == 0)
{
lean_object* v_currPos_2193_; lean_object* v_searcher_2194_; lean_object* v_out_2195_; lean_object* v_currPos_2196_; lean_object* v_searcher_2197_; lean_object* v___x_2198_; 
lean_inc_ref(v_it_2192_);
lean_dec(v_h__2_2185_);
v_currPos_2193_ = lean_ctor_get(v_x_2182_, 0);
lean_inc(v_currPos_2193_);
v_searcher_2194_ = lean_ctor_get(v_x_2182_, 1);
lean_inc(v_searcher_2194_);
lean_dec_ref(v_x_2182_);
v_out_2195_ = lean_ctor_get(v_x_2183_, 1);
lean_inc(v_out_2195_);
lean_dec_ref(v_x_2183_);
v_currPos_2196_ = lean_ctor_get(v_it_2192_, 0);
lean_inc(v_currPos_2196_);
v_searcher_2197_ = lean_ctor_get(v_it_2192_, 1);
lean_inc(v_searcher_2197_);
lean_dec_ref(v_it_2192_);
v___x_2198_ = lean_apply_5(v_h__1_2184_, v_currPos_2193_, v_searcher_2194_, v_currPos_2196_, v_searcher_2197_, v_out_2195_);
return v___x_2198_;
}
else
{
lean_object* v_currPos_2199_; lean_object* v_searcher_2200_; lean_object* v_out_2201_; lean_object* v___x_2202_; 
lean_dec(v_h__1_2184_);
v_currPos_2199_ = lean_ctor_get(v_x_2182_, 0);
lean_inc(v_currPos_2199_);
v_searcher_2200_ = lean_ctor_get(v_x_2182_, 1);
lean_inc(v_searcher_2200_);
lean_dec_ref(v_x_2182_);
v_out_2201_ = lean_ctor_get(v_x_2183_, 1);
lean_inc(v_out_2201_);
lean_dec_ref(v_x_2183_);
v___x_2202_ = lean_apply_3(v_h__2_2185_, v_currPos_2199_, v_searcher_2200_, v_out_2201_);
return v___x_2202_;
}
}
case 1:
{
lean_object* v_it_2203_; 
lean_dec(v_h__5_2188_);
lean_dec(v_h__2_2185_);
lean_dec(v_h__1_2184_);
v_it_2203_ = lean_ctor_get(v_x_2183_, 0);
lean_inc(v_it_2203_);
lean_dec_ref(v_x_2183_);
if (lean_obj_tag(v_it_2203_) == 0)
{
lean_object* v_currPos_2204_; lean_object* v_searcher_2205_; lean_object* v_currPos_2206_; lean_object* v_searcher_2207_; lean_object* v___x_2208_; 
lean_dec(v_h__4_2187_);
v_currPos_2204_ = lean_ctor_get(v_x_2182_, 0);
lean_inc(v_currPos_2204_);
v_searcher_2205_ = lean_ctor_get(v_x_2182_, 1);
lean_inc(v_searcher_2205_);
lean_dec_ref(v_x_2182_);
v_currPos_2206_ = lean_ctor_get(v_it_2203_, 0);
lean_inc(v_currPos_2206_);
v_searcher_2207_ = lean_ctor_get(v_it_2203_, 1);
lean_inc(v_searcher_2207_);
lean_dec_ref(v_it_2203_);
v___x_2208_ = lean_apply_4(v_h__3_2186_, v_currPos_2204_, v_searcher_2205_, v_currPos_2206_, v_searcher_2207_);
return v___x_2208_;
}
else
{
lean_object* v_currPos_2209_; lean_object* v_searcher_2210_; lean_object* v___x_2211_; 
lean_dec(v_h__3_2186_);
v_currPos_2209_ = lean_ctor_get(v_x_2182_, 0);
lean_inc(v_currPos_2209_);
v_searcher_2210_ = lean_ctor_get(v_x_2182_, 1);
lean_inc(v_searcher_2210_);
lean_dec_ref(v_x_2182_);
v___x_2211_ = lean_apply_2(v_h__4_2187_, v_currPos_2209_, v_searcher_2210_);
return v___x_2211_;
}
}
default: 
{
lean_object* v_currPos_2212_; lean_object* v_searcher_2213_; lean_object* v___x_2214_; 
lean_dec(v_h__4_2187_);
lean_dec(v_h__3_2186_);
lean_dec(v_h__2_2185_);
lean_dec(v_h__1_2184_);
v_currPos_2212_ = lean_ctor_get(v_x_2182_, 0);
lean_inc(v_currPos_2212_);
v_searcher_2213_ = lean_ctor_get(v_x_2182_, 1);
lean_inc(v_searcher_2213_);
lean_dec_ref(v_x_2182_);
v___x_2214_ = lean_apply_2(v_h__5_2188_, v_currPos_2212_, v_searcher_2213_);
return v___x_2214_;
}
}
}
else
{
lean_dec(v_h__5_2188_);
lean_dec(v_h__4_2187_);
lean_dec(v_h__3_2186_);
lean_dec(v_h__2_2185_);
lean_dec(v_h__1_2184_);
switch(lean_obj_tag(v_x_2183_))
{
case 0:
{
lean_object* v_it_2215_; lean_object* v_out_2216_; lean_object* v___x_2217_; 
lean_dec(v_h__8_2191_);
lean_dec(v_h__7_2190_);
v_it_2215_ = lean_ctor_get(v_x_2183_, 0);
lean_inc(v_it_2215_);
v_out_2216_ = lean_ctor_get(v_x_2183_, 1);
lean_inc(v_out_2216_);
lean_dec_ref(v_x_2183_);
v___x_2217_ = lean_apply_2(v_h__6_2189_, v_it_2215_, v_out_2216_);
return v___x_2217_;
}
case 1:
{
lean_object* v_it_2218_; lean_object* v___x_2219_; 
lean_dec(v_h__8_2191_);
lean_dec(v_h__6_2189_);
v_it_2218_ = lean_ctor_get(v_x_2183_, 0);
lean_inc(v_it_2218_);
lean_dec_ref(v_x_2183_);
v___x_2219_ = lean_apply_1(v_h__7_2190_, v_it_2218_);
return v___x_2219_;
}
default: 
{
lean_object* v___x_2220_; lean_object* v___x_2221_; 
lean_dec(v_h__7_2190_);
lean_dec(v_h__6_2189_);
v___x_2220_ = lean_box(0);
v___x_2221_ = lean_apply_1(v_h__8_2191_, v___x_2220_);
return v___x_2221_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___boxed(lean_object** _args){
lean_object* v_00_u03c1_2222_ = _args[0];
lean_object* v_00_u03c1_2223_ = _args[1];
lean_object* v_00_u03c3_2224_ = _args[2];
lean_object* v_inst_2225_ = _args[3];
lean_object* v_m_2226_ = _args[4];
lean_object* v_s_2227_ = _args[5];
lean_object* v_motive_2228_ = _args[6];
lean_object* v_x_2229_ = _args[7];
lean_object* v_x_2230_ = _args[8];
lean_object* v_h__1_2231_ = _args[9];
lean_object* v_h__2_2232_ = _args[10];
lean_object* v_h__3_2233_ = _args[11];
lean_object* v_h__4_2234_ = _args[12];
lean_object* v_h__5_2235_ = _args[13];
lean_object* v_h__6_2236_ = _args[14];
lean_object* v_h__7_2237_ = _args[15];
lean_object* v_h__8_2238_ = _args[16];
_start:
{
lean_object* v_res_2239_; 
v_res_2239_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(v_00_u03c1_2222_, v_00_u03c1_2223_, v_00_u03c3_2224_, v_inst_2225_, v_m_2226_, v_s_2227_, v_motive_2228_, v_x_2229_, v_x_2230_, v_h__1_2231_, v_h__2_2232_, v_h__3_2233_, v_h__4_2234_, v_h__5_2235_, v_h__6_2236_, v_h__7_2237_, v_h__8_2238_);
lean_dec_ref(v_s_2227_);
lean_dec(v_inst_2225_);
lean_dec(v_00_u03c1_2223_);
return v_res_2239_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___redArg(lean_object* v_x_2240_, lean_object* v_h__1_2241_, lean_object* v_h__2_2242_){
_start:
{
if (lean_obj_tag(v_x_2240_) == 0)
{
lean_object* v_currPos_2243_; lean_object* v_searcher_2244_; lean_object* v___x_2245_; 
lean_dec(v_h__2_2242_);
v_currPos_2243_ = lean_ctor_get(v_x_2240_, 0);
lean_inc(v_currPos_2243_);
v_searcher_2244_ = lean_ctor_get(v_x_2240_, 1);
lean_inc(v_searcher_2244_);
lean_dec_ref(v_x_2240_);
v___x_2245_ = lean_apply_2(v_h__1_2241_, v_currPos_2243_, v_searcher_2244_);
return v___x_2245_;
}
else
{
lean_object* v___x_2246_; lean_object* v___x_2247_; 
lean_dec(v_h__1_2241_);
v___x_2246_ = lean_box(0);
v___x_2247_ = lean_apply_1(v_h__2_2242_, v___x_2246_);
return v___x_2247_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_2248_, lean_object* v_00_u03c1_2249_, lean_object* v_00_u03c3_2250_, lean_object* v_inst_2251_, lean_object* v_s_2252_, lean_object* v_motive_2253_, lean_object* v_x_2254_, lean_object* v_h__1_2255_, lean_object* v_h__2_2256_){
_start:
{
if (lean_obj_tag(v_x_2254_) == 0)
{
lean_object* v_currPos_2257_; lean_object* v_searcher_2258_; lean_object* v___x_2259_; 
lean_dec(v_h__2_2256_);
v_currPos_2257_ = lean_ctor_get(v_x_2254_, 0);
lean_inc(v_currPos_2257_);
v_searcher_2258_ = lean_ctor_get(v_x_2254_, 1);
lean_inc(v_searcher_2258_);
lean_dec_ref(v_x_2254_);
v___x_2259_ = lean_apply_2(v_h__1_2255_, v_currPos_2257_, v_searcher_2258_);
return v___x_2259_;
}
else
{
lean_object* v___x_2260_; lean_object* v___x_2261_; 
lean_dec(v_h__1_2255_);
v___x_2260_ = lean_box(0);
v___x_2261_ = lean_apply_1(v_h__2_2256_, v___x_2260_);
return v___x_2261_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_2262_, lean_object* v_00_u03c1_2263_, lean_object* v_00_u03c3_2264_, lean_object* v_inst_2265_, lean_object* v_s_2266_, lean_object* v_motive_2267_, lean_object* v_x_2268_, lean_object* v_h__1_2269_, lean_object* v_h__2_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(v_00_u03c1_2262_, v_00_u03c1_2263_, v_00_u03c3_2264_, v_inst_2265_, v_s_2266_, v_motive_2267_, v_x_2268_, v_h__1_2269_, v_h__2_2270_);
lean_dec_ref(v_s_2266_);
lean_dec(v_inst_2265_);
lean_dec(v_00_u03c1_2263_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(lean_object* v_00_u03c1_2272_, lean_object* v_00_u03c1_2273_, lean_object* v_00_u03c3_2274_, lean_object* v_inst_2275_, lean_object* v_inst_2276_, lean_object* v_s_2277_, lean_object* v_inst_2278_){
_start:
{
lean_object* v___x_2279_; 
v___x_2279_ = lean_box(0);
return v___x_2279_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_2280_, lean_object* v_00_u03c1_2281_, lean_object* v_00_u03c3_2282_, lean_object* v_inst_2283_, lean_object* v_inst_2284_, lean_object* v_s_2285_, lean_object* v_inst_2286_){
_start:
{
lean_object* v_res_2287_; 
v_res_2287_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(v_00_u03c1_2280_, v_00_u03c1_2281_, v_00_u03c3_2282_, v_inst_2283_, v_inst_2284_, v_s_2285_, v_inst_2286_);
lean_dec_ref(v_s_2285_);
lean_dec(v_inst_2284_);
lean_dec(v_inst_2283_);
lean_dec(v_00_u03c1_2281_);
return v_res_2287_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object* v_toPure_2288_, lean_object* v_recur_2289_, lean_object* v_it_2290_, lean_object* v_____do__lift_2291_){
_start:
{
if (lean_obj_tag(v_____do__lift_2291_) == 0)
{
lean_object* v_a_2292_; lean_object* v___x_2293_; 
lean_dec(v_it_2290_);
lean_dec(v_recur_2289_);
v_a_2292_ = lean_ctor_get(v_____do__lift_2291_, 0);
lean_inc(v_a_2292_);
lean_dec_ref(v_____do__lift_2291_);
v___x_2293_ = lean_apply_2(v_toPure_2288_, lean_box(0), v_a_2292_);
return v___x_2293_;
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2295_; 
lean_dec(v_toPure_2288_);
v_a_2294_ = lean_ctor_get(v_____do__lift_2291_, 0);
lean_inc(v_a_2294_);
lean_dec_ref(v_____do__lift_2291_);
v___x_2295_ = lean_apply_4(v_recur_2289_, v_it_2290_, v_a_2294_, lean_box(0), lean_box(0));
return v___x_2295_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object* v_toPure_2296_, lean_object* v_recur_2297_, lean_object* v___y_2298_, lean_object* v_acc_2299_, lean_object* v_toBind_2300_, lean_object* v_s_2301_){
_start:
{
switch(lean_obj_tag(v_s_2301_))
{
case 0:
{
lean_object* v_it_2302_; lean_object* v_out_2303_; lean_object* v___f_2304_; lean_object* v___x_2305_; lean_object* v___x_2306_; 
v_it_2302_ = lean_ctor_get(v_s_2301_, 0);
lean_inc(v_it_2302_);
v_out_2303_ = lean_ctor_get(v_s_2301_, 1);
lean_inc(v_out_2303_);
lean_dec_ref(v_s_2301_);
v___f_2304_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2304_, 0, v_toPure_2296_);
lean_closure_set(v___f_2304_, 1, v_recur_2297_);
lean_closure_set(v___f_2304_, 2, v_it_2302_);
v___x_2305_ = lean_apply_3(v___y_2298_, v_out_2303_, lean_box(0), v_acc_2299_);
v___x_2306_ = lean_apply_4(v_toBind_2300_, lean_box(0), lean_box(0), v___x_2305_, v___f_2304_);
return v___x_2306_;
}
case 1:
{
lean_object* v_it_2307_; lean_object* v___x_2308_; 
lean_dec(v_toBind_2300_);
lean_dec(v___y_2298_);
lean_dec(v_toPure_2296_);
v_it_2307_ = lean_ctor_get(v_s_2301_, 0);
lean_inc(v_it_2307_);
lean_dec_ref(v_s_2301_);
v___x_2308_ = lean_apply_4(v_recur_2297_, v_it_2307_, v_acc_2299_, lean_box(0), lean_box(0));
return v___x_2308_;
}
default: 
{
lean_object* v___x_2309_; 
lean_dec(v_toBind_2300_);
lean_dec(v___y_2298_);
lean_dec(v_recur_2297_);
v___x_2309_ = lean_apply_2(v_toPure_2296_, lean_box(0), v_acc_2299_);
return v___x_2309_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object* v_toPure_2310_, lean_object* v___y_2311_, lean_object* v_toBind_2312_, lean_object* v_inst_2313_, lean_object* v_s_2314_, lean_object* v_toPure_2315_, lean_object* v_lift_2316_, lean_object* v_it_2317_, lean_object* v_acc_2318_, lean_object* v_hP_2319_, lean_object* v_recur_2320_){
_start:
{
lean_object* v___f_2321_; 
v___f_2321_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2321_, 0, v_toPure_2310_);
lean_closure_set(v___f_2321_, 1, v_recur_2320_);
lean_closure_set(v___f_2321_, 2, v___y_2311_);
lean_closure_set(v___f_2321_, 3, v_acc_2318_);
lean_closure_set(v___f_2321_, 4, v_toBind_2312_);
if (lean_obj_tag(v_it_2317_) == 0)
{
lean_object* v_currPos_2322_; lean_object* v_searcher_2323_; lean_object* v___x_2325_; uint8_t v_isShared_2326_; uint8_t v_isSharedCheck_2386_; 
v_currPos_2322_ = lean_ctor_get(v_it_2317_, 0);
v_searcher_2323_ = lean_ctor_get(v_it_2317_, 1);
v_isSharedCheck_2386_ = !lean_is_exclusive(v_it_2317_);
if (v_isSharedCheck_2386_ == 0)
{
v___x_2325_ = v_it_2317_;
v_isShared_2326_ = v_isSharedCheck_2386_;
goto v_resetjp_2324_;
}
else
{
lean_inc(v_searcher_2323_);
lean_inc(v_currPos_2322_);
lean_dec(v_it_2317_);
v___x_2325_ = lean_box(0);
v_isShared_2326_ = v_isSharedCheck_2386_;
goto v_resetjp_2324_;
}
v_resetjp_2324_:
{
lean_object* v___x_2327_; 
lean_inc_ref(v_s_2314_);
v___x_2327_ = lean_apply_2(v_inst_2313_, v_s_2314_, v_searcher_2323_);
switch(lean_obj_tag(v___x_2327_))
{
case 0:
{
lean_object* v_out_2328_; 
v_out_2328_ = lean_ctor_get(v___x_2327_, 1);
lean_inc(v_out_2328_);
if (lean_obj_tag(v_out_2328_) == 0)
{
lean_object* v_it_2329_; lean_object* v___x_2331_; 
lean_dec_ref(v_out_2328_);
lean_dec_ref(v_s_2314_);
v_it_2329_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_it_2329_);
lean_dec_ref(v___x_2327_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 1, v_it_2329_);
v___x_2331_ = v___x_2325_;
goto v_reusejp_2330_;
}
else
{
lean_object* v_reuseFailAlloc_2335_; 
v_reuseFailAlloc_2335_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2335_, 0, v_currPos_2322_);
lean_ctor_set(v_reuseFailAlloc_2335_, 1, v_it_2329_);
v___x_2331_ = v_reuseFailAlloc_2335_;
goto v_reusejp_2330_;
}
v_reusejp_2330_:
{
lean_object* v___x_2332_; lean_object* v___x_2333_; lean_object* v___x_2334_; 
v___x_2332_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2332_, 0, v___x_2331_);
v___x_2333_ = lean_apply_2(v_toPure_2315_, lean_box(0), v___x_2332_);
v___x_2334_ = lean_apply_4(v_lift_2316_, lean_box(0), lean_box(0), v___f_2321_, v___x_2333_);
return v___x_2334_;
}
}
else
{
lean_object* v_it_2336_; lean_object* v___x_2338_; uint8_t v_isShared_2339_; uint8_t v_isSharedCheck_2351_; 
v_it_2336_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2351_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2351_ == 0)
{
lean_object* v_unused_2352_; 
v_unused_2352_ = lean_ctor_get(v___x_2327_, 1);
lean_dec(v_unused_2352_);
v___x_2338_ = v___x_2327_;
v_isShared_2339_ = v_isSharedCheck_2351_;
goto v_resetjp_2337_;
}
else
{
lean_inc(v_it_2336_);
lean_dec(v___x_2327_);
v___x_2338_ = lean_box(0);
v_isShared_2339_ = v_isSharedCheck_2351_;
goto v_resetjp_2337_;
}
v_resetjp_2337_:
{
lean_object* v_startPos_2340_; lean_object* v_endPos_2341_; lean_object* v_slice_2342_; lean_object* v_nextIt_2344_; 
v_startPos_2340_ = lean_ctor_get(v_out_2328_, 0);
lean_inc(v_startPos_2340_);
v_endPos_2341_ = lean_ctor_get(v_out_2328_, 1);
lean_inc(v_endPos_2341_);
lean_dec_ref(v_out_2328_);
v_slice_2342_ = l_String_Slice_slice_x21(v_s_2314_, v_endPos_2341_, v_currPos_2322_);
lean_dec(v_currPos_2322_);
lean_dec(v_endPos_2341_);
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 1, v_it_2336_);
lean_ctor_set(v___x_2325_, 0, v_startPos_2340_);
v_nextIt_2344_ = v___x_2325_;
goto v_reusejp_2343_;
}
else
{
lean_object* v_reuseFailAlloc_2350_; 
v_reuseFailAlloc_2350_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2350_, 0, v_startPos_2340_);
lean_ctor_set(v_reuseFailAlloc_2350_, 1, v_it_2336_);
v_nextIt_2344_ = v_reuseFailAlloc_2350_;
goto v_reusejp_2343_;
}
v_reusejp_2343_:
{
lean_object* v___x_2346_; 
if (v_isShared_2339_ == 0)
{
lean_ctor_set(v___x_2338_, 1, v_slice_2342_);
lean_ctor_set(v___x_2338_, 0, v_nextIt_2344_);
v___x_2346_ = v___x_2338_;
goto v_reusejp_2345_;
}
else
{
lean_object* v_reuseFailAlloc_2349_; 
v_reuseFailAlloc_2349_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2349_, 0, v_nextIt_2344_);
lean_ctor_set(v_reuseFailAlloc_2349_, 1, v_slice_2342_);
v___x_2346_ = v_reuseFailAlloc_2349_;
goto v_reusejp_2345_;
}
v_reusejp_2345_:
{
lean_object* v___x_2347_; lean_object* v___x_2348_; 
v___x_2347_ = lean_apply_2(v_toPure_2315_, lean_box(0), v___x_2346_);
v___x_2348_ = lean_apply_4(v_lift_2316_, lean_box(0), lean_box(0), v___f_2321_, v___x_2347_);
return v___x_2348_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2353_; lean_object* v___x_2355_; uint8_t v_isShared_2356_; uint8_t v_isSharedCheck_2365_; 
lean_dec_ref(v_s_2314_);
v_it_2353_ = lean_ctor_get(v___x_2327_, 0);
v_isSharedCheck_2365_ = !lean_is_exclusive(v___x_2327_);
if (v_isSharedCheck_2365_ == 0)
{
v___x_2355_ = v___x_2327_;
v_isShared_2356_ = v_isSharedCheck_2365_;
goto v_resetjp_2354_;
}
else
{
lean_inc(v_it_2353_);
lean_dec(v___x_2327_);
v___x_2355_ = lean_box(0);
v_isShared_2356_ = v_isSharedCheck_2365_;
goto v_resetjp_2354_;
}
v_resetjp_2354_:
{
lean_object* v___x_2358_; 
if (v_isShared_2326_ == 0)
{
lean_ctor_set(v___x_2325_, 1, v_it_2353_);
v___x_2358_ = v___x_2325_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2364_; 
v_reuseFailAlloc_2364_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2364_, 0, v_currPos_2322_);
lean_ctor_set(v_reuseFailAlloc_2364_, 1, v_it_2353_);
v___x_2358_ = v_reuseFailAlloc_2364_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2360_; 
if (v_isShared_2356_ == 0)
{
lean_ctor_set(v___x_2355_, 0, v___x_2358_);
v___x_2360_ = v___x_2355_;
goto v_reusejp_2359_;
}
else
{
lean_object* v_reuseFailAlloc_2363_; 
v_reuseFailAlloc_2363_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2363_, 0, v___x_2358_);
v___x_2360_ = v_reuseFailAlloc_2363_;
goto v_reusejp_2359_;
}
v_reusejp_2359_:
{
lean_object* v___x_2361_; lean_object* v___x_2362_; 
v___x_2361_ = lean_apply_2(v_toPure_2315_, lean_box(0), v___x_2360_);
v___x_2362_ = lean_apply_4(v_lift_2316_, lean_box(0), lean_box(0), v___f_2321_, v___x_2361_);
return v___x_2362_;
}
}
}
}
default: 
{
lean_object* v___x_2366_; uint8_t v___x_2367_; 
lean_del_object(v___x_2325_);
v___x_2366_ = lean_unsigned_to_nat(0u);
v___x_2367_ = lean_nat_dec_eq(v_currPos_2322_, v___x_2366_);
if (v___x_2367_ == 0)
{
lean_object* v_str_2368_; lean_object* v_startInclusive_2369_; lean_object* v___x_2371_; uint8_t v_isShared_2372_; uint8_t v_isSharedCheck_2381_; 
v_str_2368_ = lean_ctor_get(v_s_2314_, 0);
v_startInclusive_2369_ = lean_ctor_get(v_s_2314_, 1);
v_isSharedCheck_2381_ = !lean_is_exclusive(v_s_2314_);
if (v_isSharedCheck_2381_ == 0)
{
lean_object* v_unused_2382_; 
v_unused_2382_ = lean_ctor_get(v_s_2314_, 2);
lean_dec(v_unused_2382_);
v___x_2371_ = v_s_2314_;
v_isShared_2372_ = v_isSharedCheck_2381_;
goto v_resetjp_2370_;
}
else
{
lean_inc(v_startInclusive_2369_);
lean_inc(v_str_2368_);
lean_dec(v_s_2314_);
v___x_2371_ = lean_box(0);
v_isShared_2372_ = v_isSharedCheck_2381_;
goto v_resetjp_2370_;
}
v_resetjp_2370_:
{
lean_object* v___x_2373_; lean_object* v_slice_2375_; 
v___x_2373_ = lean_nat_add(v_startInclusive_2369_, v_currPos_2322_);
lean_dec(v_currPos_2322_);
if (v_isShared_2372_ == 0)
{
lean_ctor_set(v___x_2371_, 2, v___x_2373_);
v_slice_2375_ = v___x_2371_;
goto v_reusejp_2374_;
}
else
{
lean_object* v_reuseFailAlloc_2380_; 
v_reuseFailAlloc_2380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2380_, 0, v_str_2368_);
lean_ctor_set(v_reuseFailAlloc_2380_, 1, v_startInclusive_2369_);
lean_ctor_set(v_reuseFailAlloc_2380_, 2, v___x_2373_);
v_slice_2375_ = v_reuseFailAlloc_2380_;
goto v_reusejp_2374_;
}
v_reusejp_2374_:
{
lean_object* v___x_2376_; lean_object* v___x_2377_; lean_object* v___x_2378_; lean_object* v___x_2379_; 
v___x_2376_ = lean_box(1);
v___x_2377_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2377_, 0, v___x_2376_);
lean_ctor_set(v___x_2377_, 1, v_slice_2375_);
v___x_2378_ = lean_apply_2(v_toPure_2315_, lean_box(0), v___x_2377_);
v___x_2379_ = lean_apply_4(v_lift_2316_, lean_box(0), lean_box(0), v___f_2321_, v___x_2378_);
return v___x_2379_;
}
}
}
else
{
lean_object* v___x_2383_; lean_object* v___x_2384_; lean_object* v___x_2385_; 
lean_dec(v_currPos_2322_);
lean_dec_ref(v_s_2314_);
v___x_2383_ = lean_box(2);
v___x_2384_ = lean_apply_2(v_toPure_2315_, lean_box(0), v___x_2383_);
v___x_2385_ = lean_apply_4(v_lift_2316_, lean_box(0), lean_box(0), v___f_2321_, v___x_2384_);
return v___x_2385_;
}
}
}
}
}
else
{
lean_object* v___x_2387_; lean_object* v___x_2388_; lean_object* v___x_2389_; 
lean_dec_ref(v_s_2314_);
lean_dec(v_inst_2313_);
v___x_2387_ = lean_box(2);
v___x_2388_ = lean_apply_2(v_toPure_2315_, lean_box(0), v___x_2387_);
v___x_2389_ = lean_apply_4(v_lift_2316_, lean_box(0), lean_box(0), v___f_2321_, v___x_2388_);
return v___x_2389_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object* v_inst_2390_, lean_object* v_inst_2391_, lean_object* v_s_2392_, lean_object* v_toPure_2393_, lean_object* v_lift_2394_, lean_object* v_00_u03b3_2395_, lean_object* v_Pl_2396_, lean_object* v_it_2397_, lean_object* v_init_2398_, lean_object* v___y_2399_){
_start:
{
lean_object* v_toApplicative_2400_; lean_object* v_toBind_2401_; lean_object* v_toPure_2402_; lean_object* v___f_2403_; lean_object* v___x_2404_; 
v_toApplicative_2400_ = lean_ctor_get(v_inst_2390_, 0);
lean_inc_ref(v_toApplicative_2400_);
v_toBind_2401_ = lean_ctor_get(v_inst_2390_, 1);
lean_inc(v_toBind_2401_);
lean_dec_ref(v_inst_2390_);
v_toPure_2402_ = lean_ctor_get(v_toApplicative_2400_, 1);
lean_inc(v_toPure_2402_);
lean_dec_ref(v_toApplicative_2400_);
v___f_2403_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2), 11, 7);
lean_closure_set(v___f_2403_, 0, v_toPure_2402_);
lean_closure_set(v___f_2403_, 1, v___y_2399_);
lean_closure_set(v___f_2403_, 2, v_toBind_2401_);
lean_closure_set(v___f_2403_, 3, v_inst_2391_);
lean_closure_set(v___f_2403_, 4, v_s_2392_);
lean_closure_set(v___f_2403_, 5, v_toPure_2393_);
lean_closure_set(v___f_2403_, 6, v_lift_2394_);
v___x_2404_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2403_, v_it_2397_, v_init_2398_, lean_box(0));
return v___x_2404_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(lean_object* v_inst_2405_, lean_object* v_s_2406_, lean_object* v_inst_2407_, lean_object* v_inst_2408_){
_start:
{
lean_object* v_toApplicative_2409_; lean_object* v_toPure_2410_; lean_object* v___f_2411_; 
v_toApplicative_2409_ = lean_ctor_get(v_inst_2407_, 0);
lean_inc_ref(v_toApplicative_2409_);
lean_dec_ref(v_inst_2407_);
v_toPure_2410_ = lean_ctor_get(v_toApplicative_2409_, 1);
lean_inc(v_toPure_2410_);
lean_dec_ref(v_toApplicative_2409_);
v___f_2411_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3), 10, 4);
lean_closure_set(v___f_2411_, 0, v_inst_2408_);
lean_closure_set(v___f_2411_, 1, v_inst_2405_);
lean_closure_set(v___f_2411_, 2, v_s_2406_);
lean_closure_set(v___f_2411_, 3, v_toPure_2410_);
return v___f_2411_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(lean_object* v_00_u03c1_2412_, lean_object* v_00_u03c1_2413_, lean_object* v_00_u03c3_2414_, lean_object* v_inst_2415_, lean_object* v_inst_2416_, lean_object* v_m_2417_, lean_object* v_n_2418_, lean_object* v_s_2419_, lean_object* v_inst_2420_, lean_object* v_inst_2421_){
_start:
{
lean_object* v___x_2422_; 
v___x_2422_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(v_inst_2415_, v_s_2419_, v_inst_2420_, v_inst_2421_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___boxed(lean_object* v_00_u03c1_2423_, lean_object* v_00_u03c1_2424_, lean_object* v_00_u03c3_2425_, lean_object* v_inst_2426_, lean_object* v_inst_2427_, lean_object* v_m_2428_, lean_object* v_n_2429_, lean_object* v_s_2430_, lean_object* v_inst_2431_, lean_object* v_inst_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(v_00_u03c1_2423_, v_00_u03c1_2424_, v_00_u03c3_2425_, v_inst_2426_, v_inst_2427_, v_m_2428_, v_n_2429_, v_s_2430_, v_inst_2431_, v_inst_2432_);
lean_dec(v_inst_2427_);
lean_dec(v_00_u03c1_2424_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___redArg(lean_object* v_s_2434_, lean_object* v_inst_2435_){
_start:
{
lean_object* v_startInclusive_2436_; lean_object* v_endExclusive_2437_; lean_object* v___x_2438_; lean_object* v___x_2439_; lean_object* v___x_2440_; 
v_startInclusive_2436_ = lean_ctor_get(v_s_2434_, 1);
v_endExclusive_2437_ = lean_ctor_get(v_s_2434_, 2);
v___x_2438_ = lean_nat_sub(v_endExclusive_2437_, v_startInclusive_2436_);
v___x_2439_ = lean_apply_1(v_inst_2435_, v_s_2434_);
v___x_2440_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2440_, 0, v___x_2438_);
lean_ctor_set(v___x_2440_, 1, v___x_2439_);
return v___x_2440_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit(lean_object* v_00_u03c3_2441_, lean_object* v_00_u03c1_2442_, lean_object* v_s_2443_, lean_object* v_pat_2444_, lean_object* v_inst_2445_){
_start:
{
lean_object* v___x_2446_; 
v___x_2446_ = l_String_Slice_revSplit___redArg(v_s_2443_, v_inst_2445_);
return v___x_2446_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___boxed(lean_object* v_00_u03c3_2447_, lean_object* v_00_u03c1_2448_, lean_object* v_s_2449_, lean_object* v_pat_2450_, lean_object* v_inst_2451_){
_start:
{
lean_object* v_res_2452_; 
v_res_2452_ = l_String_Slice_revSplit(v_00_u03c3_2447_, v_00_u03c1_2448_, v_s_2449_, v_pat_2450_, v_inst_2451_);
lean_dec(v_pat_2450_);
return v_res_2452_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___redArg(lean_object* v_s_2453_, lean_object* v_inst_2454_){
_start:
{
lean_object* v_skipSuffix_x3f_2455_; lean_object* v___x_2456_; 
v_skipSuffix_x3f_2455_ = lean_ctor_get(v_inst_2454_, 0);
lean_inc_ref(v_skipSuffix_x3f_2455_);
lean_dec_ref(v_inst_2454_);
v___x_2456_ = lean_apply_1(v_skipSuffix_x3f_2455_, v_s_2453_);
return v___x_2456_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f(lean_object* v_00_u03c1_2457_, lean_object* v_s_2458_, lean_object* v_pat_2459_, lean_object* v_inst_2460_){
_start:
{
lean_object* v_skipSuffix_x3f_2461_; lean_object* v___x_2462_; 
v_skipSuffix_x3f_2461_ = lean_ctor_get(v_inst_2460_, 0);
lean_inc_ref(v_skipSuffix_x3f_2461_);
lean_dec_ref(v_inst_2460_);
v___x_2462_ = lean_apply_1(v_skipSuffix_x3f_2461_, v_s_2458_);
return v___x_2462_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___boxed(lean_object* v_00_u03c1_2463_, lean_object* v_s_2464_, lean_object* v_pat_2465_, lean_object* v_inst_2466_){
_start:
{
lean_object* v_res_2467_; 
v_res_2467_ = l_String_Slice_skipSuffix_x3f(v_00_u03c1_2463_, v_s_2464_, v_pat_2465_, v_inst_2466_);
lean_dec(v_pat_2465_);
return v_res_2467_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg(lean_object* v_s_2468_, lean_object* v_pos_2469_, lean_object* v_inst_2470_){
_start:
{
lean_object* v_str_2471_; lean_object* v_startInclusive_2472_; lean_object* v_endExclusive_2473_; lean_object* v___x_2475_; uint8_t v_isShared_2476_; uint8_t v_isSharedCheck_2492_; 
v_str_2471_ = lean_ctor_get(v_s_2468_, 0);
v_startInclusive_2472_ = lean_ctor_get(v_s_2468_, 1);
v_endExclusive_2473_ = lean_ctor_get(v_s_2468_, 2);
v_isSharedCheck_2492_ = !lean_is_exclusive(v_s_2468_);
if (v_isSharedCheck_2492_ == 0)
{
v___x_2475_ = v_s_2468_;
v_isShared_2476_ = v_isSharedCheck_2492_;
goto v_resetjp_2474_;
}
else
{
lean_inc(v_endExclusive_2473_);
lean_inc(v_startInclusive_2472_);
lean_inc(v_str_2471_);
lean_dec(v_s_2468_);
v___x_2475_ = lean_box(0);
v_isShared_2476_ = v_isSharedCheck_2492_;
goto v_resetjp_2474_;
}
v_resetjp_2474_:
{
lean_object* v_skipPrefix_x3f_2477_; lean_object* v___x_2478_; lean_object* v___x_2480_; 
v_skipPrefix_x3f_2477_ = lean_ctor_get(v_inst_2470_, 0);
lean_inc_ref(v_skipPrefix_x3f_2477_);
lean_dec_ref(v_inst_2470_);
v___x_2478_ = lean_nat_add(v_startInclusive_2472_, v_pos_2469_);
lean_dec(v_startInclusive_2472_);
if (v_isShared_2476_ == 0)
{
lean_ctor_set(v___x_2475_, 1, v___x_2478_);
v___x_2480_ = v___x_2475_;
goto v_reusejp_2479_;
}
else
{
lean_object* v_reuseFailAlloc_2491_; 
v_reuseFailAlloc_2491_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2491_, 0, v_str_2471_);
lean_ctor_set(v_reuseFailAlloc_2491_, 1, v___x_2478_);
lean_ctor_set(v_reuseFailAlloc_2491_, 2, v_endExclusive_2473_);
v___x_2480_ = v_reuseFailAlloc_2491_;
goto v_reusejp_2479_;
}
v_reusejp_2479_:
{
lean_object* v___x_2481_; 
v___x_2481_ = lean_apply_1(v_skipPrefix_x3f_2477_, v___x_2480_);
if (lean_obj_tag(v___x_2481_) == 0)
{
return v___x_2481_;
}
else
{
lean_object* v_val_2482_; lean_object* v___x_2484_; uint8_t v_isShared_2485_; uint8_t v_isSharedCheck_2490_; 
v_val_2482_ = lean_ctor_get(v___x_2481_, 0);
v_isSharedCheck_2490_ = !lean_is_exclusive(v___x_2481_);
if (v_isSharedCheck_2490_ == 0)
{
v___x_2484_ = v___x_2481_;
v_isShared_2485_ = v_isSharedCheck_2490_;
goto v_resetjp_2483_;
}
else
{
lean_inc(v_val_2482_);
lean_dec(v___x_2481_);
v___x_2484_ = lean_box(0);
v_isShared_2485_ = v_isSharedCheck_2490_;
goto v_resetjp_2483_;
}
v_resetjp_2483_:
{
lean_object* v___x_2486_; lean_object* v___x_2488_; 
v___x_2486_ = lean_nat_add(v_pos_2469_, v_val_2482_);
lean_dec(v_val_2482_);
if (v_isShared_2485_ == 0)
{
lean_ctor_set(v___x_2484_, 0, v___x_2486_);
v___x_2488_ = v___x_2484_;
goto v_reusejp_2487_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v___x_2486_);
v___x_2488_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2487_;
}
v_reusejp_2487_:
{
return v___x_2488_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg___boxed(lean_object* v_s_2493_, lean_object* v_pos_2494_, lean_object* v_inst_2495_){
_start:
{
lean_object* v_res_2496_; 
v_res_2496_ = l_String_Slice_Pos_revSkip_x3f___redArg(v_s_2493_, v_pos_2494_, v_inst_2495_);
lean_dec(v_pos_2494_);
return v_res_2496_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f(lean_object* v_00_u03c1_2497_, lean_object* v_s_2498_, lean_object* v_pos_2499_, lean_object* v_pat_2500_, lean_object* v_inst_2501_){
_start:
{
lean_object* v_str_2502_; lean_object* v_startInclusive_2503_; lean_object* v_endExclusive_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2523_; 
v_str_2502_ = lean_ctor_get(v_s_2498_, 0);
v_startInclusive_2503_ = lean_ctor_get(v_s_2498_, 1);
v_endExclusive_2504_ = lean_ctor_get(v_s_2498_, 2);
v_isSharedCheck_2523_ = !lean_is_exclusive(v_s_2498_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2506_ = v_s_2498_;
v_isShared_2507_ = v_isSharedCheck_2523_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_endExclusive_2504_);
lean_inc(v_startInclusive_2503_);
lean_inc(v_str_2502_);
lean_dec(v_s_2498_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2523_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v_skipPrefix_x3f_2508_; lean_object* v___x_2509_; lean_object* v___x_2511_; 
v_skipPrefix_x3f_2508_ = lean_ctor_get(v_inst_2501_, 0);
lean_inc_ref(v_skipPrefix_x3f_2508_);
lean_dec_ref(v_inst_2501_);
v___x_2509_ = lean_nat_add(v_startInclusive_2503_, v_pos_2499_);
lean_dec(v_startInclusive_2503_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 1, v___x_2509_);
v___x_2511_ = v___x_2506_;
goto v_reusejp_2510_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_str_2502_);
lean_ctor_set(v_reuseFailAlloc_2522_, 1, v___x_2509_);
lean_ctor_set(v_reuseFailAlloc_2522_, 2, v_endExclusive_2504_);
v___x_2511_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2510_;
}
v_reusejp_2510_:
{
lean_object* v___x_2512_; 
v___x_2512_ = lean_apply_1(v_skipPrefix_x3f_2508_, v___x_2511_);
if (lean_obj_tag(v___x_2512_) == 0)
{
return v___x_2512_;
}
else
{
lean_object* v_val_2513_; lean_object* v___x_2515_; uint8_t v_isShared_2516_; uint8_t v_isSharedCheck_2521_; 
v_val_2513_ = lean_ctor_get(v___x_2512_, 0);
v_isSharedCheck_2521_ = !lean_is_exclusive(v___x_2512_);
if (v_isSharedCheck_2521_ == 0)
{
v___x_2515_ = v___x_2512_;
v_isShared_2516_ = v_isSharedCheck_2521_;
goto v_resetjp_2514_;
}
else
{
lean_inc(v_val_2513_);
lean_dec(v___x_2512_);
v___x_2515_ = lean_box(0);
v_isShared_2516_ = v_isSharedCheck_2521_;
goto v_resetjp_2514_;
}
v_resetjp_2514_:
{
lean_object* v___x_2517_; lean_object* v___x_2519_; 
v___x_2517_ = lean_nat_add(v_pos_2499_, v_val_2513_);
lean_dec(v_val_2513_);
if (v_isShared_2516_ == 0)
{
lean_ctor_set(v___x_2515_, 0, v___x_2517_);
v___x_2519_ = v___x_2515_;
goto v_reusejp_2518_;
}
else
{
lean_object* v_reuseFailAlloc_2520_; 
v_reuseFailAlloc_2520_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2520_, 0, v___x_2517_);
v___x_2519_ = v_reuseFailAlloc_2520_;
goto v_reusejp_2518_;
}
v_reusejp_2518_:
{
return v___x_2519_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_2524_, lean_object* v_s_2525_, lean_object* v_pos_2526_, lean_object* v_pat_2527_, lean_object* v_inst_2528_){
_start:
{
lean_object* v_res_2529_; 
v_res_2529_ = l_String_Slice_Pos_revSkip_x3f(v_00_u03c1_2524_, v_s_2525_, v_pos_2526_, v_pat_2527_, v_inst_2528_);
lean_dec(v_pat_2527_);
lean_dec(v_pos_2526_);
return v_res_2529_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___redArg(lean_object* v_s_2530_, lean_object* v_inst_2531_){
_start:
{
lean_object* v_skipSuffix_x3f_2532_; lean_object* v___x_2533_; 
v_skipSuffix_x3f_2532_ = lean_ctor_get(v_inst_2531_, 0);
lean_inc_ref(v_skipSuffix_x3f_2532_);
lean_dec_ref(v_inst_2531_);
lean_inc_ref(v_s_2530_);
v___x_2533_ = lean_apply_1(v_skipSuffix_x3f_2532_, v_s_2530_);
if (lean_obj_tag(v___x_2533_) == 0)
{
lean_object* v___x_2534_; 
lean_dec_ref(v_s_2530_);
v___x_2534_ = lean_box(0);
return v___x_2534_;
}
else
{
lean_object* v_val_2535_; lean_object* v___x_2537_; uint8_t v_isShared_2538_; uint8_t v_isSharedCheck_2553_; 
v_val_2535_ = lean_ctor_get(v___x_2533_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2533_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2537_ = v___x_2533_;
v_isShared_2538_ = v_isSharedCheck_2553_;
goto v_resetjp_2536_;
}
else
{
lean_inc(v_val_2535_);
lean_dec(v___x_2533_);
v___x_2537_ = lean_box(0);
v_isShared_2538_ = v_isSharedCheck_2553_;
goto v_resetjp_2536_;
}
v_resetjp_2536_:
{
lean_object* v_str_2539_; lean_object* v_startInclusive_2540_; lean_object* v___x_2542_; uint8_t v_isShared_2543_; uint8_t v_isSharedCheck_2551_; 
v_str_2539_ = lean_ctor_get(v_s_2530_, 0);
v_startInclusive_2540_ = lean_ctor_get(v_s_2530_, 1);
v_isSharedCheck_2551_ = !lean_is_exclusive(v_s_2530_);
if (v_isSharedCheck_2551_ == 0)
{
lean_object* v_unused_2552_; 
v_unused_2552_ = lean_ctor_get(v_s_2530_, 2);
lean_dec(v_unused_2552_);
v___x_2542_ = v_s_2530_;
v_isShared_2543_ = v_isSharedCheck_2551_;
goto v_resetjp_2541_;
}
else
{
lean_inc(v_startInclusive_2540_);
lean_inc(v_str_2539_);
lean_dec(v_s_2530_);
v___x_2542_ = lean_box(0);
v_isShared_2543_ = v_isSharedCheck_2551_;
goto v_resetjp_2541_;
}
v_resetjp_2541_:
{
lean_object* v___x_2544_; lean_object* v___x_2546_; 
v___x_2544_ = lean_nat_add(v_startInclusive_2540_, v_val_2535_);
lean_dec(v_val_2535_);
if (v_isShared_2543_ == 0)
{
lean_ctor_set(v___x_2542_, 2, v___x_2544_);
v___x_2546_ = v___x_2542_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2550_; 
v_reuseFailAlloc_2550_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2550_, 0, v_str_2539_);
lean_ctor_set(v_reuseFailAlloc_2550_, 1, v_startInclusive_2540_);
lean_ctor_set(v_reuseFailAlloc_2550_, 2, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2550_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
lean_object* v___x_2548_; 
if (v_isShared_2538_ == 0)
{
lean_ctor_set(v___x_2537_, 0, v___x_2546_);
v___x_2548_ = v___x_2537_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2549_; 
v_reuseFailAlloc_2549_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2549_, 0, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2549_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
return v___x_2548_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f(lean_object* v_00_u03c1_2554_, lean_object* v_s_2555_, lean_object* v_pat_2556_, lean_object* v_inst_2557_){
_start:
{
lean_object* v_skipSuffix_x3f_2558_; lean_object* v___x_2559_; 
v_skipSuffix_x3f_2558_ = lean_ctor_get(v_inst_2557_, 0);
lean_inc_ref(v_skipSuffix_x3f_2558_);
lean_dec_ref(v_inst_2557_);
lean_inc_ref(v_s_2555_);
v___x_2559_ = lean_apply_1(v_skipSuffix_x3f_2558_, v_s_2555_);
if (lean_obj_tag(v___x_2559_) == 0)
{
lean_object* v___x_2560_; 
lean_dec_ref(v_s_2555_);
v___x_2560_ = lean_box(0);
return v___x_2560_;
}
else
{
lean_object* v_val_2561_; lean_object* v___x_2563_; uint8_t v_isShared_2564_; uint8_t v_isSharedCheck_2579_; 
v_val_2561_ = lean_ctor_get(v___x_2559_, 0);
v_isSharedCheck_2579_ = !lean_is_exclusive(v___x_2559_);
if (v_isSharedCheck_2579_ == 0)
{
v___x_2563_ = v___x_2559_;
v_isShared_2564_ = v_isSharedCheck_2579_;
goto v_resetjp_2562_;
}
else
{
lean_inc(v_val_2561_);
lean_dec(v___x_2559_);
v___x_2563_ = lean_box(0);
v_isShared_2564_ = v_isSharedCheck_2579_;
goto v_resetjp_2562_;
}
v_resetjp_2562_:
{
lean_object* v_str_2565_; lean_object* v_startInclusive_2566_; lean_object* v___x_2568_; uint8_t v_isShared_2569_; uint8_t v_isSharedCheck_2577_; 
v_str_2565_ = lean_ctor_get(v_s_2555_, 0);
v_startInclusive_2566_ = lean_ctor_get(v_s_2555_, 1);
v_isSharedCheck_2577_ = !lean_is_exclusive(v_s_2555_);
if (v_isSharedCheck_2577_ == 0)
{
lean_object* v_unused_2578_; 
v_unused_2578_ = lean_ctor_get(v_s_2555_, 2);
lean_dec(v_unused_2578_);
v___x_2568_ = v_s_2555_;
v_isShared_2569_ = v_isSharedCheck_2577_;
goto v_resetjp_2567_;
}
else
{
lean_inc(v_startInclusive_2566_);
lean_inc(v_str_2565_);
lean_dec(v_s_2555_);
v___x_2568_ = lean_box(0);
v_isShared_2569_ = v_isSharedCheck_2577_;
goto v_resetjp_2567_;
}
v_resetjp_2567_:
{
lean_object* v___x_2570_; lean_object* v___x_2572_; 
v___x_2570_ = lean_nat_add(v_startInclusive_2566_, v_val_2561_);
lean_dec(v_val_2561_);
if (v_isShared_2569_ == 0)
{
lean_ctor_set(v___x_2568_, 2, v___x_2570_);
v___x_2572_ = v___x_2568_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2576_; 
v_reuseFailAlloc_2576_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2576_, 0, v_str_2565_);
lean_ctor_set(v_reuseFailAlloc_2576_, 1, v_startInclusive_2566_);
lean_ctor_set(v_reuseFailAlloc_2576_, 2, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2576_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
lean_object* v___x_2574_; 
if (v_isShared_2564_ == 0)
{
lean_ctor_set(v___x_2563_, 0, v___x_2572_);
v___x_2574_ = v___x_2563_;
goto v_reusejp_2573_;
}
else
{
lean_object* v_reuseFailAlloc_2575_; 
v_reuseFailAlloc_2575_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2575_, 0, v___x_2572_);
v___x_2574_ = v_reuseFailAlloc_2575_;
goto v_reusejp_2573_;
}
v_reusejp_2573_:
{
return v___x_2574_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_2580_, lean_object* v_s_2581_, lean_object* v_pat_2582_, lean_object* v_inst_2583_){
_start:
{
lean_object* v_res_2584_; 
v_res_2584_ = l_String_Slice_dropSuffix_x3f(v_00_u03c1_2580_, v_s_2581_, v_pat_2582_, v_inst_2583_);
lean_dec(v_pat_2582_);
return v_res_2584_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___redArg(lean_object* v_s_2585_, lean_object* v_inst_2586_){
_start:
{
lean_object* v_skipSuffix_x3f_2587_; lean_object* v___x_2588_; 
v_skipSuffix_x3f_2587_ = lean_ctor_get(v_inst_2586_, 0);
lean_inc_ref(v_skipSuffix_x3f_2587_);
lean_dec_ref(v_inst_2586_);
lean_inc_ref(v_s_2585_);
v___x_2588_ = lean_apply_1(v_skipSuffix_x3f_2587_, v_s_2585_);
if (lean_obj_tag(v___x_2588_) == 0)
{
return v_s_2585_;
}
else
{
lean_object* v_val_2589_; lean_object* v_str_2590_; lean_object* v_startInclusive_2591_; lean_object* v___x_2593_; uint8_t v_isShared_2594_; uint8_t v_isSharedCheck_2599_; 
v_val_2589_ = lean_ctor_get(v___x_2588_, 0);
lean_inc(v_val_2589_);
lean_dec_ref(v___x_2588_);
v_str_2590_ = lean_ctor_get(v_s_2585_, 0);
v_startInclusive_2591_ = lean_ctor_get(v_s_2585_, 1);
v_isSharedCheck_2599_ = !lean_is_exclusive(v_s_2585_);
if (v_isSharedCheck_2599_ == 0)
{
lean_object* v_unused_2600_; 
v_unused_2600_ = lean_ctor_get(v_s_2585_, 2);
lean_dec(v_unused_2600_);
v___x_2593_ = v_s_2585_;
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
else
{
lean_inc(v_startInclusive_2591_);
lean_inc(v_str_2590_);
lean_dec(v_s_2585_);
v___x_2593_ = lean_box(0);
v_isShared_2594_ = v_isSharedCheck_2599_;
goto v_resetjp_2592_;
}
v_resetjp_2592_:
{
lean_object* v___x_2595_; lean_object* v___x_2597_; 
v___x_2595_ = lean_nat_add(v_startInclusive_2591_, v_val_2589_);
lean_dec(v_val_2589_);
if (v_isShared_2594_ == 0)
{
lean_ctor_set(v___x_2593_, 2, v___x_2595_);
v___x_2597_ = v___x_2593_;
goto v_reusejp_2596_;
}
else
{
lean_object* v_reuseFailAlloc_2598_; 
v_reuseFailAlloc_2598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2598_, 0, v_str_2590_);
lean_ctor_set(v_reuseFailAlloc_2598_, 1, v_startInclusive_2591_);
lean_ctor_set(v_reuseFailAlloc_2598_, 2, v___x_2595_);
v___x_2597_ = v_reuseFailAlloc_2598_;
goto v_reusejp_2596_;
}
v_reusejp_2596_:
{
return v___x_2597_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix(lean_object* v_00_u03c1_2601_, lean_object* v_s_2602_, lean_object* v_pat_2603_, lean_object* v_inst_2604_){
_start:
{
lean_object* v___x_2605_; 
v___x_2605_ = l_String_Slice_dropSuffix___redArg(v_s_2602_, v_inst_2604_);
return v___x_2605_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___boxed(lean_object* v_00_u03c1_2606_, lean_object* v_s_2607_, lean_object* v_pat_2608_, lean_object* v_inst_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_String_Slice_dropSuffix(v_00_u03c1_2606_, v_s_2607_, v_pat_2608_, v_inst_2609_);
lean_dec(v_pat_2608_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object* v_s_2611_, lean_object* v_n_2612_){
_start:
{
lean_object* v_str_2613_; lean_object* v_startInclusive_2614_; lean_object* v_endExclusive_2615_; lean_object* v___x_2616_; lean_object* v___x_2617_; lean_object* v___x_2619_; uint8_t v_isShared_2620_; uint8_t v_isSharedCheck_2625_; 
v_str_2613_ = lean_ctor_get(v_s_2611_, 0);
lean_inc_ref(v_str_2613_);
v_startInclusive_2614_ = lean_ctor_get(v_s_2611_, 1);
lean_inc(v_startInclusive_2614_);
v_endExclusive_2615_ = lean_ctor_get(v_s_2611_, 2);
v___x_2616_ = lean_nat_sub(v_endExclusive_2615_, v_startInclusive_2614_);
v___x_2617_ = l_String_Slice_Pos_prevn(v_s_2611_, v___x_2616_, v_n_2612_);
v_isSharedCheck_2625_ = !lean_is_exclusive(v_s_2611_);
if (v_isSharedCheck_2625_ == 0)
{
lean_object* v_unused_2626_; lean_object* v_unused_2627_; lean_object* v_unused_2628_; 
v_unused_2626_ = lean_ctor_get(v_s_2611_, 2);
lean_dec(v_unused_2626_);
v_unused_2627_ = lean_ctor_get(v_s_2611_, 1);
lean_dec(v_unused_2627_);
v_unused_2628_ = lean_ctor_get(v_s_2611_, 0);
lean_dec(v_unused_2628_);
v___x_2619_ = v_s_2611_;
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
else
{
lean_dec(v_s_2611_);
v___x_2619_ = lean_box(0);
v_isShared_2620_ = v_isSharedCheck_2625_;
goto v_resetjp_2618_;
}
v_resetjp_2618_:
{
lean_object* v___x_2621_; lean_object* v___x_2623_; 
v___x_2621_ = lean_nat_add(v_startInclusive_2614_, v___x_2617_);
lean_dec(v___x_2617_);
if (v_isShared_2620_ == 0)
{
lean_ctor_set(v___x_2619_, 2, v___x_2621_);
v___x_2623_ = v___x_2619_;
goto v_reusejp_2622_;
}
else
{
lean_object* v_reuseFailAlloc_2624_; 
v_reuseFailAlloc_2624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2624_, 0, v_str_2613_);
lean_ctor_set(v_reuseFailAlloc_2624_, 1, v_startInclusive_2614_);
lean_ctor_set(v_reuseFailAlloc_2624_, 2, v___x_2621_);
v___x_2623_ = v_reuseFailAlloc_2624_;
goto v_reusejp_2622_;
}
v_reusejp_2622_:
{
return v___x_2623_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object* v_s_2629_, lean_object* v_pos_2630_, lean_object* v_inst_2631_){
_start:
{
lean_object* v_skipSuffix_x3f_2632_; lean_object* v_str_2633_; lean_object* v_startInclusive_2634_; lean_object* v___x_2635_; lean_object* v___x_2636_; lean_object* v___x_2637_; 
v_skipSuffix_x3f_2632_ = lean_ctor_get(v_inst_2631_, 0);
v_str_2633_ = lean_ctor_get(v_s_2629_, 0);
v_startInclusive_2634_ = lean_ctor_get(v_s_2629_, 1);
v___x_2635_ = lean_nat_add(v_startInclusive_2634_, v_pos_2630_);
lean_inc(v_startInclusive_2634_);
lean_inc_ref(v_str_2633_);
v___x_2636_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2636_, 0, v_str_2633_);
lean_ctor_set(v___x_2636_, 1, v_startInclusive_2634_);
lean_ctor_set(v___x_2636_, 2, v___x_2635_);
lean_inc_ref(v_skipSuffix_x3f_2632_);
v___x_2637_ = lean_apply_1(v_skipSuffix_x3f_2632_, v___x_2636_);
if (lean_obj_tag(v___x_2637_) == 1)
{
lean_object* v_val_2638_; uint8_t v___x_2639_; 
v_val_2638_ = lean_ctor_get(v___x_2637_, 0);
lean_inc(v_val_2638_);
lean_dec_ref(v___x_2637_);
v___x_2639_ = l_String_instDecidableLtRaw___aux__1(v_val_2638_, v_pos_2630_);
if (v___x_2639_ == 0)
{
lean_dec(v_val_2638_);
lean_dec_ref(v_inst_2631_);
return v_pos_2630_;
}
else
{
lean_dec(v_pos_2630_);
v_pos_2630_ = v_val_2638_;
goto _start;
}
}
else
{
lean_dec(v___x_2637_);
lean_dec_ref(v_inst_2631_);
return v_pos_2630_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg___boxed(lean_object* v_s_2641_, lean_object* v_pos_2642_, lean_object* v_inst_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2641_, v_pos_2642_, v_inst_2643_);
lean_dec_ref(v_s_2641_);
return v_res_2644_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile(lean_object* v_00_u03c1_2645_, lean_object* v_s_2646_, lean_object* v_pos_2647_, lean_object* v_pat_2648_, lean_object* v_inst_2649_){
_start:
{
lean_object* v___x_2650_; 
v___x_2650_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2646_, v_pos_2647_, v_inst_2649_);
return v___x_2650_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_2651_, lean_object* v_s_2652_, lean_object* v_pos_2653_, lean_object* v_pat_2654_, lean_object* v_inst_2655_){
_start:
{
lean_object* v_res_2656_; 
v_res_2656_ = l_String_Slice_Pos_revSkipWhile(v_00_u03c1_2651_, v_s_2652_, v_pos_2653_, v_pat_2654_, v_inst_2655_);
lean_dec(v_pat_2654_);
lean_dec_ref(v_s_2652_);
return v_res_2656_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_revSkipWhile_match__1_splitter___redArg(lean_object* v_x_2657_, lean_object* v_h__1_2658_, lean_object* v_h__2_2659_){
_start:
{
if (lean_obj_tag(v_x_2657_) == 1)
{
lean_object* v_val_2660_; lean_object* v___x_2661_; 
lean_dec(v_h__2_2659_);
v_val_2660_ = lean_ctor_get(v_x_2657_, 0);
lean_inc(v_val_2660_);
lean_dec_ref(v_x_2657_);
v___x_2661_ = lean_apply_1(v_h__1_2658_, v_val_2660_);
return v___x_2661_;
}
else
{
lean_object* v___x_2662_; 
lean_dec(v_h__1_2658_);
v___x_2662_ = lean_apply_2(v_h__2_2659_, v_x_2657_, lean_box(0));
return v___x_2662_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_revSkipWhile_match__1_splitter(lean_object* v_s_2663_, lean_object* v_pos_2664_, lean_object* v_motive_2665_, lean_object* v_x_2666_, lean_object* v_h__1_2667_, lean_object* v_h__2_2668_){
_start:
{
if (lean_obj_tag(v_x_2666_) == 1)
{
lean_object* v_val_2669_; lean_object* v___x_2670_; 
lean_dec(v_h__2_2668_);
v_val_2669_ = lean_ctor_get(v_x_2666_, 0);
lean_inc(v_val_2669_);
lean_dec_ref(v_x_2666_);
v___x_2670_ = lean_apply_1(v_h__1_2667_, v_val_2669_);
return v___x_2670_;
}
else
{
lean_object* v___x_2671_; 
lean_dec(v_h__1_2667_);
v___x_2671_ = lean_apply_2(v_h__2_2668_, v_x_2666_, lean_box(0));
return v___x_2671_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_revSkipWhile_match__1_splitter___boxed(lean_object* v_s_2672_, lean_object* v_pos_2673_, lean_object* v_motive_2674_, lean_object* v_x_2675_, lean_object* v_h__1_2676_, lean_object* v_h__2_2677_){
_start:
{
lean_object* v_res_2678_; 
v_res_2678_ = l___private_Init_Data_String_Slice_0__String_Slice_Pos_revSkipWhile_match__1_splitter(v_s_2672_, v_pos_2673_, v_motive_2674_, v_x_2675_, v_h__1_2676_, v_h__2_2677_);
lean_dec(v_pos_2673_);
lean_dec_ref(v_s_2672_);
return v_res_2678_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg(lean_object* v_s_2679_, lean_object* v_inst_2680_){
_start:
{
lean_object* v_startInclusive_2681_; lean_object* v_endExclusive_2682_; lean_object* v___x_2683_; lean_object* v___x_2684_; 
v_startInclusive_2681_ = lean_ctor_get(v_s_2679_, 1);
v_endExclusive_2682_ = lean_ctor_get(v_s_2679_, 2);
v___x_2683_ = lean_nat_sub(v_endExclusive_2682_, v_startInclusive_2681_);
v___x_2684_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2679_, v___x_2683_, v_inst_2680_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg___boxed(lean_object* v_s_2685_, lean_object* v_inst_2686_){
_start:
{
lean_object* v_res_2687_; 
v_res_2687_ = l_String_Slice_skipSuffixWhile___redArg(v_s_2685_, v_inst_2686_);
lean_dec_ref(v_s_2685_);
return v_res_2687_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile(lean_object* v_00_u03c1_2688_, lean_object* v_s_2689_, lean_object* v_pat_2690_, lean_object* v_inst_2691_){
_start:
{
lean_object* v_startInclusive_2692_; lean_object* v_endExclusive_2693_; lean_object* v___x_2694_; lean_object* v___x_2695_; 
v_startInclusive_2692_ = lean_ctor_get(v_s_2689_, 1);
v_endExclusive_2693_ = lean_ctor_get(v_s_2689_, 2);
v___x_2694_ = lean_nat_sub(v_endExclusive_2693_, v_startInclusive_2692_);
v___x_2695_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2689_, v___x_2694_, v_inst_2691_);
return v___x_2695_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___boxed(lean_object* v_00_u03c1_2696_, lean_object* v_s_2697_, lean_object* v_pat_2698_, lean_object* v_inst_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_String_Slice_skipSuffixWhile(v_00_u03c1_2696_, v_s_2697_, v_pat_2698_, v_inst_2699_);
lean_dec(v_pat_2698_);
lean_dec_ref(v_s_2697_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object* v_s_2701_, lean_object* v_inst_2702_){
_start:
{
lean_object* v_str_2703_; lean_object* v_startInclusive_2704_; lean_object* v_endExclusive_2705_; lean_object* v___x_2706_; lean_object* v___x_2707_; lean_object* v___x_2709_; uint8_t v_isShared_2710_; uint8_t v_isSharedCheck_2715_; 
v_str_2703_ = lean_ctor_get(v_s_2701_, 0);
lean_inc_ref(v_str_2703_);
v_startInclusive_2704_ = lean_ctor_get(v_s_2701_, 1);
lean_inc(v_startInclusive_2704_);
v_endExclusive_2705_ = lean_ctor_get(v_s_2701_, 2);
v___x_2706_ = lean_nat_sub(v_endExclusive_2705_, v_startInclusive_2704_);
v___x_2707_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2701_, v___x_2706_, v_inst_2702_);
v_isSharedCheck_2715_ = !lean_is_exclusive(v_s_2701_);
if (v_isSharedCheck_2715_ == 0)
{
lean_object* v_unused_2716_; lean_object* v_unused_2717_; lean_object* v_unused_2718_; 
v_unused_2716_ = lean_ctor_get(v_s_2701_, 2);
lean_dec(v_unused_2716_);
v_unused_2717_ = lean_ctor_get(v_s_2701_, 1);
lean_dec(v_unused_2717_);
v_unused_2718_ = lean_ctor_get(v_s_2701_, 0);
lean_dec(v_unused_2718_);
v___x_2709_ = v_s_2701_;
v_isShared_2710_ = v_isSharedCheck_2715_;
goto v_resetjp_2708_;
}
else
{
lean_dec(v_s_2701_);
v___x_2709_ = lean_box(0);
v_isShared_2710_ = v_isSharedCheck_2715_;
goto v_resetjp_2708_;
}
v_resetjp_2708_:
{
lean_object* v___x_2711_; lean_object* v___x_2713_; 
v___x_2711_ = lean_nat_add(v_startInclusive_2704_, v___x_2707_);
lean_dec(v___x_2707_);
if (v_isShared_2710_ == 0)
{
lean_ctor_set(v___x_2709_, 2, v___x_2711_);
v___x_2713_ = v___x_2709_;
goto v_reusejp_2712_;
}
else
{
lean_object* v_reuseFailAlloc_2714_; 
v_reuseFailAlloc_2714_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2714_, 0, v_str_2703_);
lean_ctor_set(v_reuseFailAlloc_2714_, 1, v_startInclusive_2704_);
lean_ctor_set(v_reuseFailAlloc_2714_, 2, v___x_2711_);
v___x_2713_ = v_reuseFailAlloc_2714_;
goto v_reusejp_2712_;
}
v_reusejp_2712_:
{
return v___x_2713_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object* v_00_u03c1_2719_, lean_object* v_s_2720_, lean_object* v_pat_2721_, lean_object* v_inst_2722_){
_start:
{
lean_object* v_str_2723_; lean_object* v_startInclusive_2724_; lean_object* v_endExclusive_2725_; lean_object* v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2729_; uint8_t v_isShared_2730_; uint8_t v_isSharedCheck_2735_; 
v_str_2723_ = lean_ctor_get(v_s_2720_, 0);
lean_inc_ref(v_str_2723_);
v_startInclusive_2724_ = lean_ctor_get(v_s_2720_, 1);
lean_inc(v_startInclusive_2724_);
v_endExclusive_2725_ = lean_ctor_get(v_s_2720_, 2);
v___x_2726_ = lean_nat_sub(v_endExclusive_2725_, v_startInclusive_2724_);
v___x_2727_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2720_, v___x_2726_, v_inst_2722_);
v_isSharedCheck_2735_ = !lean_is_exclusive(v_s_2720_);
if (v_isSharedCheck_2735_ == 0)
{
lean_object* v_unused_2736_; lean_object* v_unused_2737_; lean_object* v_unused_2738_; 
v_unused_2736_ = lean_ctor_get(v_s_2720_, 2);
lean_dec(v_unused_2736_);
v_unused_2737_ = lean_ctor_get(v_s_2720_, 1);
lean_dec(v_unused_2737_);
v_unused_2738_ = lean_ctor_get(v_s_2720_, 0);
lean_dec(v_unused_2738_);
v___x_2729_ = v_s_2720_;
v_isShared_2730_ = v_isSharedCheck_2735_;
goto v_resetjp_2728_;
}
else
{
lean_dec(v_s_2720_);
v___x_2729_ = lean_box(0);
v_isShared_2730_ = v_isSharedCheck_2735_;
goto v_resetjp_2728_;
}
v_resetjp_2728_:
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2731_ = lean_nat_add(v_startInclusive_2724_, v___x_2727_);
lean_dec(v___x_2727_);
if (v_isShared_2730_ == 0)
{
lean_ctor_set(v___x_2729_, 2, v___x_2731_);
v___x_2733_ = v___x_2729_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2734_; 
v_reuseFailAlloc_2734_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2734_, 0, v_str_2723_);
lean_ctor_set(v_reuseFailAlloc_2734_, 1, v_startInclusive_2724_);
lean_ctor_set(v_reuseFailAlloc_2734_, 2, v___x_2731_);
v___x_2733_ = v_reuseFailAlloc_2734_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
return v___x_2733_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object* v_00_u03c1_2739_, lean_object* v_s_2740_, lean_object* v_pat_2741_, lean_object* v_inst_2742_){
_start:
{
lean_object* v_res_2743_; 
v_res_2743_ = l_String_Slice_dropEndWhile(v_00_u03c1_2739_, v_s_2740_, v_pat_2741_, v_inst_2742_);
lean_dec(v_pat_2741_);
return v_res_2743_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiEnd___closed__0(void){
_start:
{
lean_object* v___x_2744_; lean_object* v___x_2745_; 
v___x_2744_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_2745_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_2744_);
return v___x_2745_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object* v_s_2746_){
_start:
{
lean_object* v___x_2747_; lean_object* v_str_2748_; lean_object* v_startInclusive_2749_; lean_object* v_endExclusive_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2760_; 
v___x_2747_ = lean_obj_once(&l_String_Slice_trimAsciiEnd___closed__0, &l_String_Slice_trimAsciiEnd___closed__0_once, _init_l_String_Slice_trimAsciiEnd___closed__0);
v_str_2748_ = lean_ctor_get(v_s_2746_, 0);
lean_inc_ref(v_str_2748_);
v_startInclusive_2749_ = lean_ctor_get(v_s_2746_, 1);
lean_inc(v_startInclusive_2749_);
v_endExclusive_2750_ = lean_ctor_get(v_s_2746_, 2);
v___x_2751_ = lean_nat_sub(v_endExclusive_2750_, v_startInclusive_2749_);
v___x_2752_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2746_, v___x_2751_, v___x_2747_);
v_isSharedCheck_2760_ = !lean_is_exclusive(v_s_2746_);
if (v_isSharedCheck_2760_ == 0)
{
lean_object* v_unused_2761_; lean_object* v_unused_2762_; lean_object* v_unused_2763_; 
v_unused_2761_ = lean_ctor_get(v_s_2746_, 2);
lean_dec(v_unused_2761_);
v_unused_2762_ = lean_ctor_get(v_s_2746_, 1);
lean_dec(v_unused_2762_);
v_unused_2763_ = lean_ctor_get(v_s_2746_, 0);
lean_dec(v_unused_2763_);
v___x_2754_ = v_s_2746_;
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
else
{
lean_dec(v_s_2746_);
v___x_2754_ = lean_box(0);
v_isShared_2755_ = v_isSharedCheck_2760_;
goto v_resetjp_2753_;
}
v_resetjp_2753_:
{
lean_object* v___x_2756_; lean_object* v___x_2758_; 
v___x_2756_ = lean_nat_add(v_startInclusive_2749_, v___x_2752_);
lean_dec(v___x_2752_);
if (v_isShared_2755_ == 0)
{
lean_ctor_set(v___x_2754_, 2, v___x_2756_);
v___x_2758_ = v___x_2754_;
goto v_reusejp_2757_;
}
else
{
lean_object* v_reuseFailAlloc_2759_; 
v_reuseFailAlloc_2759_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2759_, 0, v_str_2748_);
lean_ctor_set(v_reuseFailAlloc_2759_, 1, v_startInclusive_2749_);
lean_ctor_set(v_reuseFailAlloc_2759_, 2, v___x_2756_);
v___x_2758_ = v_reuseFailAlloc_2759_;
goto v_reusejp_2757_;
}
v_reusejp_2757_:
{
return v___x_2758_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object* v_s_2764_, lean_object* v_n_2765_){
_start:
{
lean_object* v_str_2766_; lean_object* v_startInclusive_2767_; lean_object* v_endExclusive_2768_; lean_object* v___x_2769_; lean_object* v___x_2770_; lean_object* v___x_2772_; uint8_t v_isShared_2773_; uint8_t v_isSharedCheck_2778_; 
v_str_2766_ = lean_ctor_get(v_s_2764_, 0);
lean_inc_ref(v_str_2766_);
v_startInclusive_2767_ = lean_ctor_get(v_s_2764_, 1);
lean_inc(v_startInclusive_2767_);
v_endExclusive_2768_ = lean_ctor_get(v_s_2764_, 2);
lean_inc(v_endExclusive_2768_);
v___x_2769_ = lean_nat_sub(v_endExclusive_2768_, v_startInclusive_2767_);
v___x_2770_ = l_String_Slice_Pos_prevn(v_s_2764_, v___x_2769_, v_n_2765_);
v_isSharedCheck_2778_ = !lean_is_exclusive(v_s_2764_);
if (v_isSharedCheck_2778_ == 0)
{
lean_object* v_unused_2779_; lean_object* v_unused_2780_; lean_object* v_unused_2781_; 
v_unused_2779_ = lean_ctor_get(v_s_2764_, 2);
lean_dec(v_unused_2779_);
v_unused_2780_ = lean_ctor_get(v_s_2764_, 1);
lean_dec(v_unused_2780_);
v_unused_2781_ = lean_ctor_get(v_s_2764_, 0);
lean_dec(v_unused_2781_);
v___x_2772_ = v_s_2764_;
v_isShared_2773_ = v_isSharedCheck_2778_;
goto v_resetjp_2771_;
}
else
{
lean_dec(v_s_2764_);
v___x_2772_ = lean_box(0);
v_isShared_2773_ = v_isSharedCheck_2778_;
goto v_resetjp_2771_;
}
v_resetjp_2771_:
{
lean_object* v___x_2774_; lean_object* v___x_2776_; 
v___x_2774_ = lean_nat_add(v_startInclusive_2767_, v___x_2770_);
lean_dec(v___x_2770_);
lean_dec(v_startInclusive_2767_);
if (v_isShared_2773_ == 0)
{
lean_ctor_set(v___x_2772_, 1, v___x_2774_);
v___x_2776_ = v___x_2772_;
goto v_reusejp_2775_;
}
else
{
lean_object* v_reuseFailAlloc_2777_; 
v_reuseFailAlloc_2777_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2777_, 0, v_str_2766_);
lean_ctor_set(v_reuseFailAlloc_2777_, 1, v___x_2774_);
lean_ctor_set(v_reuseFailAlloc_2777_, 2, v_endExclusive_2768_);
v___x_2776_ = v_reuseFailAlloc_2777_;
goto v_reusejp_2775_;
}
v_reusejp_2775_:
{
return v___x_2776_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___redArg(lean_object* v_s_2782_, lean_object* v_inst_2783_){
_start:
{
lean_object* v_str_2784_; lean_object* v_startInclusive_2785_; lean_object* v_endExclusive_2786_; lean_object* v___x_2787_; lean_object* v___x_2788_; lean_object* v___x_2790_; uint8_t v_isShared_2791_; uint8_t v_isSharedCheck_2796_; 
v_str_2784_ = lean_ctor_get(v_s_2782_, 0);
lean_inc_ref(v_str_2784_);
v_startInclusive_2785_ = lean_ctor_get(v_s_2782_, 1);
lean_inc(v_startInclusive_2785_);
v_endExclusive_2786_ = lean_ctor_get(v_s_2782_, 2);
lean_inc(v_endExclusive_2786_);
v___x_2787_ = lean_nat_sub(v_endExclusive_2786_, v_startInclusive_2785_);
v___x_2788_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2782_, v___x_2787_, v_inst_2783_);
v_isSharedCheck_2796_ = !lean_is_exclusive(v_s_2782_);
if (v_isSharedCheck_2796_ == 0)
{
lean_object* v_unused_2797_; lean_object* v_unused_2798_; lean_object* v_unused_2799_; 
v_unused_2797_ = lean_ctor_get(v_s_2782_, 2);
lean_dec(v_unused_2797_);
v_unused_2798_ = lean_ctor_get(v_s_2782_, 1);
lean_dec(v_unused_2798_);
v_unused_2799_ = lean_ctor_get(v_s_2782_, 0);
lean_dec(v_unused_2799_);
v___x_2790_ = v_s_2782_;
v_isShared_2791_ = v_isSharedCheck_2796_;
goto v_resetjp_2789_;
}
else
{
lean_dec(v_s_2782_);
v___x_2790_ = lean_box(0);
v_isShared_2791_ = v_isSharedCheck_2796_;
goto v_resetjp_2789_;
}
v_resetjp_2789_:
{
lean_object* v___x_2792_; lean_object* v___x_2794_; 
v___x_2792_ = lean_nat_add(v_startInclusive_2785_, v___x_2788_);
lean_dec(v___x_2788_);
lean_dec(v_startInclusive_2785_);
if (v_isShared_2791_ == 0)
{
lean_ctor_set(v___x_2790_, 1, v___x_2792_);
v___x_2794_ = v___x_2790_;
goto v_reusejp_2793_;
}
else
{
lean_object* v_reuseFailAlloc_2795_; 
v_reuseFailAlloc_2795_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2795_, 0, v_str_2784_);
lean_ctor_set(v_reuseFailAlloc_2795_, 1, v___x_2792_);
lean_ctor_set(v_reuseFailAlloc_2795_, 2, v_endExclusive_2786_);
v___x_2794_ = v_reuseFailAlloc_2795_;
goto v_reusejp_2793_;
}
v_reusejp_2793_:
{
return v___x_2794_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile(lean_object* v_00_u03c1_2800_, lean_object* v_s_2801_, lean_object* v_pat_2802_, lean_object* v_inst_2803_){
_start:
{
lean_object* v_str_2804_; lean_object* v_startInclusive_2805_; lean_object* v_endExclusive_2806_; lean_object* v___x_2807_; lean_object* v___x_2808_; lean_object* v___x_2810_; uint8_t v_isShared_2811_; uint8_t v_isSharedCheck_2816_; 
v_str_2804_ = lean_ctor_get(v_s_2801_, 0);
lean_inc_ref(v_str_2804_);
v_startInclusive_2805_ = lean_ctor_get(v_s_2801_, 1);
lean_inc(v_startInclusive_2805_);
v_endExclusive_2806_ = lean_ctor_get(v_s_2801_, 2);
lean_inc(v_endExclusive_2806_);
v___x_2807_ = lean_nat_sub(v_endExclusive_2806_, v_startInclusive_2805_);
v___x_2808_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2801_, v___x_2807_, v_inst_2803_);
v_isSharedCheck_2816_ = !lean_is_exclusive(v_s_2801_);
if (v_isSharedCheck_2816_ == 0)
{
lean_object* v_unused_2817_; lean_object* v_unused_2818_; lean_object* v_unused_2819_; 
v_unused_2817_ = lean_ctor_get(v_s_2801_, 2);
lean_dec(v_unused_2817_);
v_unused_2818_ = lean_ctor_get(v_s_2801_, 1);
lean_dec(v_unused_2818_);
v_unused_2819_ = lean_ctor_get(v_s_2801_, 0);
lean_dec(v_unused_2819_);
v___x_2810_ = v_s_2801_;
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
else
{
lean_dec(v_s_2801_);
v___x_2810_ = lean_box(0);
v_isShared_2811_ = v_isSharedCheck_2816_;
goto v_resetjp_2809_;
}
v_resetjp_2809_:
{
lean_object* v___x_2812_; lean_object* v___x_2814_; 
v___x_2812_ = lean_nat_add(v_startInclusive_2805_, v___x_2808_);
lean_dec(v___x_2808_);
lean_dec(v_startInclusive_2805_);
if (v_isShared_2811_ == 0)
{
lean_ctor_set(v___x_2810_, 1, v___x_2812_);
v___x_2814_ = v___x_2810_;
goto v_reusejp_2813_;
}
else
{
lean_object* v_reuseFailAlloc_2815_; 
v_reuseFailAlloc_2815_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2815_, 0, v_str_2804_);
lean_ctor_set(v_reuseFailAlloc_2815_, 1, v___x_2812_);
lean_ctor_set(v_reuseFailAlloc_2815_, 2, v_endExclusive_2806_);
v___x_2814_ = v_reuseFailAlloc_2815_;
goto v_reusejp_2813_;
}
v_reusejp_2813_:
{
return v___x_2814_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___boxed(lean_object* v_00_u03c1_2820_, lean_object* v_s_2821_, lean_object* v_pat_2822_, lean_object* v_inst_2823_){
_start:
{
lean_object* v_res_2824_; 
v_res_2824_ = l_String_Slice_takeEndWhile(v_00_u03c1_2820_, v_s_2821_, v_pat_2822_, v_inst_2823_);
lean_dec(v_pat_2822_);
return v_res_2824_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___redArg(lean_object* v_inst_2825_, lean_object* v_s_2826_, lean_object* v_inst_2827_){
_start:
{
lean_object* v___f_2828_; lean_object* v_searcher_2829_; lean_object* v___x_2830_; lean_object* v___f_2831_; lean_object* v___x_2832_; 
v___f_2828_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_2826_);
v_searcher_2829_ = lean_apply_1(v_inst_2827_, v_s_2826_);
v___x_2830_ = lean_box(0);
v___f_2831_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_2832_ = lean_apply_7(v_inst_2825_, v_s_2826_, v___f_2828_, lean_box(0), lean_box(0), v_searcher_2829_, v___x_2830_, v___f_2831_);
return v___x_2832_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f(lean_object* v_00_u03c3_2833_, lean_object* v_inst_2834_, lean_object* v_inst_2835_, lean_object* v_00_u03c1_2836_, lean_object* v_s_2837_, lean_object* v_pat_2838_, lean_object* v_inst_2839_){
_start:
{
lean_object* v___x_2840_; 
v___x_2840_ = l_String_Slice_revFind_x3f___redArg(v_inst_2835_, v_s_2837_, v_inst_2839_);
return v___x_2840_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___boxed(lean_object* v_00_u03c3_2841_, lean_object* v_inst_2842_, lean_object* v_inst_2843_, lean_object* v_00_u03c1_2844_, lean_object* v_s_2845_, lean_object* v_pat_2846_, lean_object* v_inst_2847_){
_start:
{
lean_object* v_res_2848_; 
v_res_2848_ = l_String_Slice_revFind_x3f(v_00_u03c3_2841_, v_inst_2842_, v_inst_2843_, v_00_u03c1_2844_, v_s_2845_, v_pat_2846_, v_inst_2847_);
lean_dec(v_pat_2846_);
lean_dec(v_inst_2842_);
return v_res_2848_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(lean_object* v_s_2849_, lean_object* v_pos_2850_){
_start:
{
lean_object* v_str_2851_; lean_object* v_startInclusive_2852_; lean_object* v_endExclusive_2853_; lean_object* v___x_2854_; uint8_t v___y_2862_; lean_object* v___x_2863_; lean_object* v___x_2864_; uint8_t v___x_2865_; 
v_str_2851_ = lean_ctor_get(v_s_2849_, 0);
v_startInclusive_2852_ = lean_ctor_get(v_s_2849_, 1);
v_endExclusive_2853_ = lean_ctor_get(v_s_2849_, 2);
v___x_2854_ = lean_nat_add(v_startInclusive_2852_, v_pos_2850_);
v___x_2863_ = lean_unsigned_to_nat(0u);
v___x_2864_ = lean_nat_sub(v_endExclusive_2853_, v___x_2854_);
v___x_2865_ = lean_nat_dec_eq(v___x_2863_, v___x_2864_);
lean_dec(v___x_2864_);
if (v___x_2865_ == 0)
{
uint32_t v___x_2866_; uint8_t v___y_2868_; uint32_t v___x_2873_; uint8_t v___x_2874_; 
v___x_2866_ = lean_string_utf8_get_fast(v_str_2851_, v___x_2854_);
v___x_2873_ = 32;
v___x_2874_ = lean_uint32_dec_eq(v___x_2866_, v___x_2873_);
if (v___x_2874_ == 0)
{
uint32_t v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = 9;
v___x_2876_ = lean_uint32_dec_eq(v___x_2866_, v___x_2875_);
v___y_2868_ = v___x_2876_;
goto v___jp_2867_;
}
else
{
v___y_2868_ = v___x_2874_;
goto v___jp_2867_;
}
v___jp_2867_:
{
if (v___y_2868_ == 0)
{
uint32_t v___x_2869_; uint8_t v___x_2870_; 
v___x_2869_ = 13;
v___x_2870_ = lean_uint32_dec_eq(v___x_2866_, v___x_2869_);
if (v___x_2870_ == 0)
{
uint32_t v___x_2871_; uint8_t v___x_2872_; 
v___x_2871_ = 10;
v___x_2872_ = lean_uint32_dec_eq(v___x_2866_, v___x_2871_);
v___y_2862_ = v___x_2872_;
goto v___jp_2861_;
}
else
{
v___y_2862_ = v___x_2870_;
goto v___jp_2861_;
}
}
else
{
goto v___jp_2855_;
}
}
}
else
{
lean_dec(v___x_2854_);
return v_pos_2850_;
}
v___jp_2855_:
{
lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v___x_2859_; 
v___x_2856_ = lean_string_utf8_next_fast(v_str_2851_, v___x_2854_);
v___x_2857_ = lean_nat_sub(v___x_2856_, v___x_2854_);
lean_dec(v___x_2854_);
v___x_2858_ = lean_nat_add(v_pos_2850_, v___x_2857_);
lean_dec(v___x_2857_);
v___x_2859_ = l_String_instDecidableLtRaw___aux__1(v_pos_2850_, v___x_2858_);
if (v___x_2859_ == 0)
{
lean_dec(v___x_2858_);
return v_pos_2850_;
}
else
{
lean_dec(v_pos_2850_);
v_pos_2850_ = v___x_2858_;
goto _start;
}
}
v___jp_2861_:
{
if (v___y_2862_ == 0)
{
lean_dec(v___x_2854_);
return v_pos_2850_;
}
else
{
goto v___jp_2855_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0___boxed(lean_object* v_s_2877_, lean_object* v_pos_2878_){
_start:
{
lean_object* v_res_2879_; 
v_res_2879_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2877_, v_pos_2878_);
lean_dec_ref(v_s_2877_);
return v_res_2879_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(lean_object* v_s_2880_, lean_object* v_pos_2881_){
_start:
{
lean_object* v_str_2882_; lean_object* v_startInclusive_2883_; lean_object* v___x_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; uint8_t v___x_2887_; 
v_str_2882_ = lean_ctor_get(v_s_2880_, 0);
v_startInclusive_2883_ = lean_ctor_get(v_s_2880_, 1);
v___x_2884_ = lean_nat_add(v_startInclusive_2883_, v_pos_2881_);
v___x_2885_ = lean_nat_sub(v___x_2884_, v_startInclusive_2883_);
v___x_2886_ = lean_unsigned_to_nat(0u);
v___x_2887_ = lean_nat_dec_eq(v___x_2885_, v___x_2886_);
if (v___x_2887_ == 0)
{
lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; lean_object* v___x_2891_; uint8_t v___y_2896_; lean_object* v___x_2897_; uint32_t v___x_2898_; uint8_t v___y_2900_; uint32_t v___x_2905_; uint8_t v___x_2906_; 
lean_inc(v_startInclusive_2883_);
lean_inc_ref(v_str_2882_);
v___x_2888_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2888_, 0, v_str_2882_);
lean_ctor_set(v___x_2888_, 1, v_startInclusive_2883_);
lean_ctor_set(v___x_2888_, 2, v___x_2884_);
v___x_2889_ = lean_unsigned_to_nat(1u);
v___x_2890_ = lean_nat_sub(v___x_2885_, v___x_2889_);
lean_dec(v___x_2885_);
v___x_2891_ = l_String_Slice_posLE(v___x_2888_, v___x_2890_);
lean_dec_ref(v___x_2888_);
v___x_2897_ = lean_nat_add(v_startInclusive_2883_, v___x_2891_);
v___x_2898_ = lean_string_utf8_get_fast(v_str_2882_, v___x_2897_);
lean_dec(v___x_2897_);
v___x_2905_ = 32;
v___x_2906_ = lean_uint32_dec_eq(v___x_2898_, v___x_2905_);
if (v___x_2906_ == 0)
{
uint32_t v___x_2907_; uint8_t v___x_2908_; 
v___x_2907_ = 9;
v___x_2908_ = lean_uint32_dec_eq(v___x_2898_, v___x_2907_);
v___y_2900_ = v___x_2908_;
goto v___jp_2899_;
}
else
{
v___y_2900_ = v___x_2906_;
goto v___jp_2899_;
}
v___jp_2892_:
{
uint8_t v___x_2893_; 
v___x_2893_ = l_String_instDecidableLtRaw___aux__1(v___x_2891_, v_pos_2881_);
if (v___x_2893_ == 0)
{
lean_dec(v___x_2891_);
return v_pos_2881_;
}
else
{
lean_dec(v_pos_2881_);
v_pos_2881_ = v___x_2891_;
goto _start;
}
}
v___jp_2895_:
{
if (v___y_2896_ == 0)
{
lean_dec(v___x_2891_);
return v_pos_2881_;
}
else
{
goto v___jp_2892_;
}
}
v___jp_2899_:
{
if (v___y_2900_ == 0)
{
uint32_t v___x_2901_; uint8_t v___x_2902_; 
v___x_2901_ = 13;
v___x_2902_ = lean_uint32_dec_eq(v___x_2898_, v___x_2901_);
if (v___x_2902_ == 0)
{
uint32_t v___x_2903_; uint8_t v___x_2904_; 
v___x_2903_ = 10;
v___x_2904_ = lean_uint32_dec_eq(v___x_2898_, v___x_2903_);
v___y_2896_ = v___x_2904_;
goto v___jp_2895_;
}
else
{
v___y_2896_ = v___x_2902_;
goto v___jp_2895_;
}
}
else
{
goto v___jp_2892_;
}
}
}
else
{
lean_dec(v___x_2885_);
lean_dec(v___x_2884_);
return v_pos_2881_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1___boxed(lean_object* v_s_2909_, lean_object* v_pos_2910_){
_start:
{
lean_object* v_res_2911_; 
v_res_2911_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v_s_2909_, v_pos_2910_);
lean_dec_ref(v_s_2909_);
return v_res_2911_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAscii(lean_object* v_s_2912_){
_start:
{
lean_object* v_str_2913_; lean_object* v_startInclusive_2914_; lean_object* v_endExclusive_2915_; lean_object* v___x_2916_; lean_object* v___x_2917_; lean_object* v___x_2919_; uint8_t v_isShared_2920_; uint8_t v_isSharedCheck_2929_; 
v_str_2913_ = lean_ctor_get(v_s_2912_, 0);
lean_inc_ref(v_str_2913_);
v_startInclusive_2914_ = lean_ctor_get(v_s_2912_, 1);
lean_inc(v_startInclusive_2914_);
v_endExclusive_2915_ = lean_ctor_get(v_s_2912_, 2);
lean_inc(v_endExclusive_2915_);
v___x_2916_ = lean_unsigned_to_nat(0u);
v___x_2917_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2912_, v___x_2916_);
v_isSharedCheck_2929_ = !lean_is_exclusive(v_s_2912_);
if (v_isSharedCheck_2929_ == 0)
{
lean_object* v_unused_2930_; lean_object* v_unused_2931_; lean_object* v_unused_2932_; 
v_unused_2930_ = lean_ctor_get(v_s_2912_, 2);
lean_dec(v_unused_2930_);
v_unused_2931_ = lean_ctor_get(v_s_2912_, 1);
lean_dec(v_unused_2931_);
v_unused_2932_ = lean_ctor_get(v_s_2912_, 0);
lean_dec(v_unused_2932_);
v___x_2919_ = v_s_2912_;
v_isShared_2920_ = v_isSharedCheck_2929_;
goto v_resetjp_2918_;
}
else
{
lean_dec(v_s_2912_);
v___x_2919_ = lean_box(0);
v_isShared_2920_ = v_isSharedCheck_2929_;
goto v_resetjp_2918_;
}
v_resetjp_2918_:
{
lean_object* v___x_2921_; lean_object* v___x_2923_; 
v___x_2921_ = lean_nat_add(v_startInclusive_2914_, v___x_2917_);
lean_dec(v___x_2917_);
lean_dec(v_startInclusive_2914_);
lean_inc(v_endExclusive_2915_);
lean_inc(v___x_2921_);
lean_inc_ref(v_str_2913_);
if (v_isShared_2920_ == 0)
{
lean_ctor_set(v___x_2919_, 1, v___x_2921_);
v___x_2923_ = v___x_2919_;
goto v_reusejp_2922_;
}
else
{
lean_object* v_reuseFailAlloc_2928_; 
v_reuseFailAlloc_2928_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2928_, 0, v_str_2913_);
lean_ctor_set(v_reuseFailAlloc_2928_, 1, v___x_2921_);
lean_ctor_set(v_reuseFailAlloc_2928_, 2, v_endExclusive_2915_);
v___x_2923_ = v_reuseFailAlloc_2928_;
goto v_reusejp_2922_;
}
v_reusejp_2922_:
{
lean_object* v___x_2924_; lean_object* v___x_2925_; lean_object* v___x_2926_; lean_object* v___x_2927_; 
v___x_2924_ = lean_nat_sub(v_endExclusive_2915_, v___x_2921_);
lean_dec(v_endExclusive_2915_);
v___x_2925_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v___x_2923_, v___x_2924_);
lean_dec_ref(v___x_2923_);
v___x_2926_ = lean_nat_add(v___x_2921_, v___x_2925_);
lean_dec(v___x_2925_);
v___x_2927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2927_, 0, v_str_2913_);
lean_ctor_set(v___x_2927_, 1, v___x_2921_);
lean_ctor_set(v___x_2927_, 2, v___x_2926_);
return v___x_2927_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(lean_object* v_s1_2933_, lean_object* v_s1Curr_2934_, lean_object* v_s2_2935_, lean_object* v_s2Curr_2936_){
_start:
{
uint8_t v___y_2938_; uint8_t v___y_2939_; uint8_t v___y_2946_; uint8_t v___y_2947_; uint8_t v___y_2948_; lean_object* v_str_2951_; lean_object* v_startInclusive_2952_; lean_object* v_endExclusive_2953_; lean_object* v___x_2954_; uint8_t v___x_2961_; 
v_str_2951_ = lean_ctor_get(v_s1_2933_, 0);
v_startInclusive_2952_ = lean_ctor_get(v_s1_2933_, 1);
v_endExclusive_2953_ = lean_ctor_get(v_s1_2933_, 2);
v___x_2954_ = lean_nat_sub(v_endExclusive_2953_, v_startInclusive_2952_);
v___x_2961_ = l_String_instDecidableLtRaw___aux__1(v_s1Curr_2934_, v___x_2954_);
if (v___x_2961_ == 0)
{
goto v___jp_2955_;
}
else
{
lean_object* v_str_2962_; lean_object* v_startInclusive_2963_; lean_object* v_endExclusive_2964_; uint8_t v___y_2966_; lean_object* v___x_2973_; uint8_t v___x_2974_; 
v_str_2962_ = lean_ctor_get(v_s2_2935_, 0);
v_startInclusive_2963_ = lean_ctor_get(v_s2_2935_, 1);
v_endExclusive_2964_ = lean_ctor_get(v_s2_2935_, 2);
v___x_2973_ = lean_nat_sub(v_endExclusive_2964_, v_startInclusive_2963_);
v___x_2974_ = l_String_instDecidableLtRaw___aux__1(v_s2Curr_2936_, v___x_2973_);
lean_dec(v___x_2973_);
if (v___x_2974_ == 0)
{
goto v___jp_2955_;
}
else
{
lean_object* v___x_2975_; uint8_t v___x_2976_; uint8_t v___y_2978_; uint8_t v___x_2981_; uint8_t v___x_2982_; 
lean_dec(v___x_2954_);
v___x_2975_ = lean_nat_add(v_startInclusive_2952_, v_s1Curr_2934_);
v___x_2976_ = lean_string_get_byte_fast(v_str_2951_, v___x_2975_);
v___x_2981_ = 65;
v___x_2982_ = lean_uint8_dec_le(v___x_2981_, v___x_2976_);
if (v___x_2982_ == 0)
{
v___y_2978_ = v___x_2982_;
goto v___jp_2977_;
}
else
{
uint8_t v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = 90;
v___x_2984_ = lean_uint8_dec_le(v___x_2976_, v___x_2983_);
v___y_2978_ = v___x_2984_;
goto v___jp_2977_;
}
v___jp_2977_:
{
if (v___y_2978_ == 0)
{
v___y_2966_ = v___x_2976_;
goto v___jp_2965_;
}
else
{
uint8_t v___x_2979_; uint8_t v___x_2980_; 
v___x_2979_ = 32;
v___x_2980_ = lean_uint8_add(v___x_2976_, v___x_2979_);
v___y_2966_ = v___x_2980_;
goto v___jp_2965_;
}
}
}
v___jp_2965_:
{
lean_object* v___x_2967_; uint8_t v___x_2968_; uint8_t v___x_2969_; uint8_t v___x_2970_; 
v___x_2967_ = lean_nat_add(v_startInclusive_2963_, v_s2Curr_2936_);
v___x_2968_ = lean_string_get_byte_fast(v_str_2962_, v___x_2967_);
v___x_2969_ = 65;
v___x_2970_ = lean_uint8_dec_le(v___x_2969_, v___x_2968_);
if (v___x_2970_ == 0)
{
v___y_2946_ = v___y_2966_;
v___y_2947_ = v___x_2968_;
v___y_2948_ = v___x_2970_;
goto v___jp_2945_;
}
else
{
uint8_t v___x_2971_; uint8_t v___x_2972_; 
v___x_2971_ = 90;
v___x_2972_ = lean_uint8_dec_le(v___x_2968_, v___x_2971_);
v___y_2946_ = v___y_2966_;
v___y_2947_ = v___x_2968_;
v___y_2948_ = v___x_2972_;
goto v___jp_2945_;
}
}
}
v___jp_2937_:
{
uint8_t v___x_2940_; 
v___x_2940_ = lean_uint8_dec_eq(v___y_2938_, v___y_2939_);
if (v___x_2940_ == 0)
{
lean_dec(v_s2Curr_2936_);
lean_dec(v_s1Curr_2934_);
return v___x_2940_;
}
else
{
lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; 
v___x_2941_ = lean_unsigned_to_nat(1u);
v___x_2942_ = lean_nat_add(v_s1Curr_2934_, v___x_2941_);
lean_dec(v_s1Curr_2934_);
v___x_2943_ = lean_nat_add(v_s2Curr_2936_, v___x_2941_);
lean_dec(v_s2Curr_2936_);
v_s1Curr_2934_ = v___x_2942_;
v_s2Curr_2936_ = v___x_2943_;
goto _start;
}
}
v___jp_2945_:
{
if (v___y_2948_ == 0)
{
v___y_2938_ = v___y_2946_;
v___y_2939_ = v___y_2947_;
goto v___jp_2937_;
}
else
{
uint8_t v___x_2949_; uint8_t v___x_2950_; 
v___x_2949_ = 32;
v___x_2950_ = lean_uint8_add(v___y_2947_, v___x_2949_);
v___y_2938_ = v___y_2946_;
v___y_2939_ = v___x_2950_;
goto v___jp_2937_;
}
}
v___jp_2955_:
{
uint8_t v___x_2956_; 
v___x_2956_ = lean_nat_dec_eq(v_s1Curr_2934_, v___x_2954_);
lean_dec(v___x_2954_);
lean_dec(v_s1Curr_2934_);
if (v___x_2956_ == 0)
{
lean_dec(v_s2Curr_2936_);
return v___x_2956_;
}
else
{
lean_object* v_startInclusive_2957_; lean_object* v_endExclusive_2958_; lean_object* v___x_2959_; uint8_t v___x_2960_; 
v_startInclusive_2957_ = lean_ctor_get(v_s2_2935_, 1);
v_endExclusive_2958_ = lean_ctor_get(v_s2_2935_, 2);
v___x_2959_ = lean_nat_sub(v_endExclusive_2958_, v_startInclusive_2957_);
v___x_2960_ = lean_nat_dec_eq(v_s2Curr_2936_, v___x_2959_);
lean_dec(v___x_2959_);
lean_dec(v_s2Curr_2936_);
return v___x_2960_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object* v_s1_2985_, lean_object* v_s1Curr_2986_, lean_object* v_s2_2987_, lean_object* v_s2Curr_2988_){
_start:
{
uint8_t v_res_2989_; lean_object* v_r_2990_; 
v_res_2989_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_2985_, v_s1Curr_2986_, v_s2_2987_, v_s2Curr_2988_);
lean_dec_ref(v_s2_2987_);
lean_dec_ref(v_s1_2985_);
v_r_2990_ = lean_box(v_res_2989_);
return v_r_2990_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object* v_s1_2991_, lean_object* v_s2_2992_){
_start:
{
lean_object* v_startInclusive_2993_; lean_object* v_endExclusive_2994_; lean_object* v_startInclusive_2995_; lean_object* v_endExclusive_2996_; lean_object* v___x_2997_; lean_object* v___x_2998_; uint8_t v___x_2999_; 
v_startInclusive_2993_ = lean_ctor_get(v_s1_2991_, 1);
v_endExclusive_2994_ = lean_ctor_get(v_s1_2991_, 2);
v_startInclusive_2995_ = lean_ctor_get(v_s2_2992_, 1);
v_endExclusive_2996_ = lean_ctor_get(v_s2_2992_, 2);
v___x_2997_ = lean_nat_sub(v_endExclusive_2994_, v_startInclusive_2993_);
v___x_2998_ = lean_nat_sub(v_endExclusive_2996_, v_startInclusive_2995_);
v___x_2999_ = lean_nat_dec_eq(v___x_2997_, v___x_2998_);
lean_dec(v___x_2998_);
lean_dec(v___x_2997_);
if (v___x_2999_ == 0)
{
return v___x_2999_;
}
else
{
lean_object* v___x_3000_; uint8_t v___x_3001_; 
v___x_3000_ = lean_unsigned_to_nat(0u);
v___x_3001_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_2991_, v___x_3000_, v_s2_2992_, v___x_3000_);
return v___x_3001_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object* v_s1_3002_, lean_object* v_s2_3003_){
_start:
{
uint8_t v_res_3004_; lean_object* v_r_3005_; 
v_res_3004_ = l_String_Slice_eqIgnoreAsciiCase(v_s1_3002_, v_s2_3003_);
lean_dec_ref(v_s2_3003_);
lean_dec_ref(v_s1_3002_);
v_r_3005_ = lean_box(v_res_3004_);
return v_r_3005_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines_lineMap(lean_object* v_s_3006_){
_start:
{
lean_object* v_str_3007_; lean_object* v_startInclusive_3008_; lean_object* v_endExclusive_3009_; lean_object* v___x_3010_; lean_object* v___x_3011_; uint8_t v___x_3012_; 
v_str_3007_ = lean_ctor_get(v_s_3006_, 0);
v_startInclusive_3008_ = lean_ctor_get(v_s_3006_, 1);
v_endExclusive_3009_ = lean_ctor_get(v_s_3006_, 2);
v___x_3010_ = lean_nat_sub(v_endExclusive_3009_, v_startInclusive_3008_);
v___x_3011_ = lean_unsigned_to_nat(0u);
v___x_3012_ = lean_nat_dec_eq(v___x_3010_, v___x_3011_);
if (v___x_3012_ == 0)
{
uint32_t v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; uint32_t v___x_3018_; uint8_t v___x_3019_; 
v___x_3013_ = 10;
v___x_3014_ = lean_unsigned_to_nat(1u);
v___x_3015_ = lean_nat_sub(v___x_3010_, v___x_3014_);
lean_dec(v___x_3010_);
v___x_3016_ = l_String_Slice_posLE(v_s_3006_, v___x_3015_);
v___x_3017_ = lean_nat_add(v_startInclusive_3008_, v___x_3016_);
lean_dec(v___x_3016_);
v___x_3018_ = lean_string_utf8_get_fast(v_str_3007_, v___x_3017_);
v___x_3019_ = lean_uint32_dec_eq(v___x_3018_, v___x_3013_);
if (v___x_3019_ == 0)
{
lean_dec(v___x_3017_);
return v_s_3006_;
}
else
{
lean_object* v___x_3021_; uint8_t v_isShared_3022_; uint8_t v_isSharedCheck_3035_; 
lean_inc(v_startInclusive_3008_);
lean_inc_ref(v_str_3007_);
v_isSharedCheck_3035_ = !lean_is_exclusive(v_s_3006_);
if (v_isSharedCheck_3035_ == 0)
{
lean_object* v_unused_3036_; lean_object* v_unused_3037_; lean_object* v_unused_3038_; 
v_unused_3036_ = lean_ctor_get(v_s_3006_, 2);
lean_dec(v_unused_3036_);
v_unused_3037_ = lean_ctor_get(v_s_3006_, 1);
lean_dec(v_unused_3037_);
v_unused_3038_ = lean_ctor_get(v_s_3006_, 0);
lean_dec(v_unused_3038_);
v___x_3021_ = v_s_3006_;
v_isShared_3022_ = v_isSharedCheck_3035_;
goto v_resetjp_3020_;
}
else
{
lean_dec(v_s_3006_);
v___x_3021_ = lean_box(0);
v_isShared_3022_ = v_isSharedCheck_3035_;
goto v_resetjp_3020_;
}
v_resetjp_3020_:
{
lean_object* v___x_3024_; 
lean_inc(v___x_3017_);
lean_inc(v_startInclusive_3008_);
lean_inc_ref(v_str_3007_);
if (v_isShared_3022_ == 0)
{
lean_ctor_set(v___x_3021_, 2, v___x_3017_);
v___x_3024_ = v___x_3021_;
goto v_reusejp_3023_;
}
else
{
lean_object* v_reuseFailAlloc_3034_; 
v_reuseFailAlloc_3034_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3034_, 0, v_str_3007_);
lean_ctor_set(v_reuseFailAlloc_3034_, 1, v_startInclusive_3008_);
lean_ctor_set(v_reuseFailAlloc_3034_, 2, v___x_3017_);
v___x_3024_ = v_reuseFailAlloc_3034_;
goto v_reusejp_3023_;
}
v_reusejp_3023_:
{
lean_object* v___x_3025_; uint8_t v___x_3026_; 
v___x_3025_ = lean_nat_sub(v___x_3017_, v_startInclusive_3008_);
lean_dec(v___x_3017_);
v___x_3026_ = lean_nat_dec_eq(v___x_3025_, v___x_3011_);
if (v___x_3026_ == 0)
{
uint32_t v___x_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; lean_object* v___x_3030_; uint32_t v___x_3031_; uint8_t v___x_3032_; 
v___x_3027_ = 13;
v___x_3028_ = lean_nat_sub(v___x_3025_, v___x_3014_);
lean_dec(v___x_3025_);
v___x_3029_ = l_String_Slice_posLE(v___x_3024_, v___x_3028_);
v___x_3030_ = lean_nat_add(v_startInclusive_3008_, v___x_3029_);
lean_dec(v___x_3029_);
v___x_3031_ = lean_string_utf8_get_fast(v_str_3007_, v___x_3030_);
v___x_3032_ = lean_uint32_dec_eq(v___x_3031_, v___x_3027_);
if (v___x_3032_ == 0)
{
lean_dec(v___x_3030_);
lean_dec(v_startInclusive_3008_);
lean_dec_ref(v_str_3007_);
return v___x_3024_;
}
else
{
lean_object* v___x_3033_; 
lean_dec_ref(v___x_3024_);
v___x_3033_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3033_, 0, v_str_3007_);
lean_ctor_set(v___x_3033_, 1, v_startInclusive_3008_);
lean_ctor_set(v___x_3033_, 2, v___x_3030_);
return v___x_3033_;
}
}
else
{
lean_dec(v___x_3025_);
lean_dec(v_startInclusive_3008_);
lean_dec_ref(v_str_3007_);
return v___x_3024_;
}
}
}
}
}
else
{
lean_dec(v___x_3010_);
return v_s_3006_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(lean_object* v_s_3041_){
_start:
{
lean_object* v___x_3042_; 
v___x_3042_ = ((lean_object*)(l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0));
return v___x_3042_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(lean_object* v_s_3043_){
_start:
{
lean_object* v_res_3044_; 
v_res_3044_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_3043_);
lean_dec_ref(v_s_3043_);
return v_res_3044_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines(lean_object* v_s_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_3045_);
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines___boxed(lean_object* v_s_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_String_Slice_lines(v_s_3047_);
lean_dec_ref(v_s_3047_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(lean_object* v_s_3049_, lean_object* v_a_3050_, lean_object* v_b_3051_){
_start:
{
lean_object* v_str_3052_; lean_object* v_startInclusive_3053_; lean_object* v_endExclusive_3054_; lean_object* v___x_3055_; uint8_t v_lastWasDigit_3056_; 
v_str_3052_ = lean_ctor_get(v_s_3049_, 0);
v_startInclusive_3053_ = lean_ctor_get(v_s_3049_, 1);
v_endExclusive_3054_ = lean_ctor_get(v_s_3049_, 2);
v___x_3055_ = lean_nat_sub(v_endExclusive_3054_, v_startInclusive_3053_);
v_lastWasDigit_3056_ = lean_nat_dec_eq(v_a_3050_, v___x_3055_);
lean_dec(v___x_3055_);
if (v_lastWasDigit_3056_ == 0)
{
lean_object* v_snd_3057_; lean_object* v___x_3059_; uint8_t v_isShared_3060_; uint8_t v_isSharedCheck_3091_; 
v_snd_3057_ = lean_ctor_get(v_b_3051_, 1);
v_isSharedCheck_3091_ = !lean_is_exclusive(v_b_3051_);
if (v_isSharedCheck_3091_ == 0)
{
lean_object* v_unused_3092_; 
v_unused_3092_ = lean_ctor_get(v_b_3051_, 0);
lean_dec(v_unused_3092_);
v___x_3059_ = v_b_3051_;
v_isShared_3060_ = v_isSharedCheck_3091_;
goto v_resetjp_3058_;
}
else
{
lean_inc(v_snd_3057_);
lean_dec(v_b_3051_);
v___x_3059_ = lean_box(0);
v_isShared_3060_ = v_isSharedCheck_3091_;
goto v_resetjp_3058_;
}
v_resetjp_3058_:
{
lean_object* v___x_3061_; lean_object* v___x_3062_; lean_object* v___x_3063_; lean_object* v___x_3064_; uint8_t v___y_3066_; uint32_t v___x_3077_; uint32_t v___x_3078_; uint8_t v___x_3079_; 
v___x_3061_ = lean_box(0);
v___x_3062_ = lean_nat_add(v_startInclusive_3053_, v_a_3050_);
lean_dec(v_a_3050_);
v___x_3063_ = lean_string_utf8_next_fast(v_str_3052_, v___x_3062_);
v___x_3064_ = lean_nat_sub(v___x_3063_, v_startInclusive_3053_);
v___x_3077_ = lean_string_utf8_get_fast(v_str_3052_, v___x_3062_);
lean_dec(v___x_3062_);
v___x_3078_ = 95;
v___x_3079_ = lean_uint32_dec_eq(v___x_3077_, v___x_3078_);
if (v___x_3079_ == 0)
{
uint32_t v___x_3080_; uint8_t v___x_3081_; 
v___x_3080_ = 48;
v___x_3081_ = lean_uint32_dec_le(v___x_3080_, v___x_3077_);
if (v___x_3081_ == 0)
{
v___y_3066_ = v___x_3081_;
goto v___jp_3065_;
}
else
{
uint32_t v___x_3082_; uint8_t v___x_3083_; 
v___x_3082_ = 57;
v___x_3083_ = lean_uint32_dec_le(v___x_3077_, v___x_3082_);
v___y_3066_ = v___x_3083_;
goto v___jp_3065_;
}
}
else
{
uint8_t v___x_3084_; 
lean_del_object(v___x_3059_);
v___x_3084_ = lean_unbox(v_snd_3057_);
if (v___x_3084_ == 0)
{
lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; 
lean_dec(v___x_3064_);
v___x_3085_ = lean_box(v_lastWasDigit_3056_);
v___x_3086_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3086_, 0, v___x_3085_);
v___x_3087_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3087_, 0, v___x_3086_);
lean_ctor_set(v___x_3087_, 1, v_snd_3057_);
return v___x_3087_;
}
else
{
lean_object* v___x_3088_; lean_object* v___x_3089_; 
lean_dec(v_snd_3057_);
v___x_3088_ = lean_box(v_lastWasDigit_3056_);
v___x_3089_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3089_, 0, v___x_3061_);
lean_ctor_set(v___x_3089_, 1, v___x_3088_);
v_a_3050_ = v___x_3064_;
v_b_3051_ = v___x_3089_;
goto _start;
}
}
v___jp_3065_:
{
if (v___y_3066_ == 0)
{
lean_object* v___x_3067_; lean_object* v___x_3068_; lean_object* v___x_3070_; 
lean_dec(v___x_3064_);
v___x_3067_ = lean_box(v_lastWasDigit_3056_);
v___x_3068_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3068_, 0, v___x_3067_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 0, v___x_3068_);
v___x_3070_ = v___x_3059_;
goto v_reusejp_3069_;
}
else
{
lean_object* v_reuseFailAlloc_3071_; 
v_reuseFailAlloc_3071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3071_, 0, v___x_3068_);
lean_ctor_set(v_reuseFailAlloc_3071_, 1, v_snd_3057_);
v___x_3070_ = v_reuseFailAlloc_3071_;
goto v_reusejp_3069_;
}
v_reusejp_3069_:
{
return v___x_3070_;
}
}
else
{
lean_object* v___x_3072_; lean_object* v___x_3074_; 
lean_dec(v_snd_3057_);
v___x_3072_ = lean_box(v___y_3066_);
if (v_isShared_3060_ == 0)
{
lean_ctor_set(v___x_3059_, 1, v___x_3072_);
lean_ctor_set(v___x_3059_, 0, v___x_3061_);
v___x_3074_ = v___x_3059_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3076_; 
v_reuseFailAlloc_3076_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3076_, 0, v___x_3061_);
lean_ctor_set(v_reuseFailAlloc_3076_, 1, v___x_3072_);
v___x_3074_ = v_reuseFailAlloc_3076_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
v_a_3050_ = v___x_3064_;
v_b_3051_ = v___x_3074_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_3050_);
return v_b_3051_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg___boxed(lean_object* v_s_3093_, lean_object* v_a_3094_, lean_object* v_b_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3093_, v_a_3094_, v_b_3095_);
lean_dec_ref(v_s_3093_);
return v_res_3096_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isNat(lean_object* v_s_3101_){
_start:
{
lean_object* v___x_3102_; lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v_fst_3105_; 
v___x_3102_ = ((lean_object*)(l_String_Slice_isNat___closed__0));
v___x_3103_ = l_String_Slice_positions(v_s_3101_);
v___x_3104_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3101_, v___x_3103_, v___x_3102_);
v_fst_3105_ = lean_ctor_get(v___x_3104_, 0);
lean_inc(v_fst_3105_);
if (lean_obj_tag(v_fst_3105_) == 0)
{
lean_object* v_snd_3106_; uint8_t v___x_3107_; 
v_snd_3106_ = lean_ctor_get(v___x_3104_, 1);
lean_inc(v_snd_3106_);
lean_dec_ref(v___x_3104_);
v___x_3107_ = lean_unbox(v_snd_3106_);
lean_dec(v_snd_3106_);
return v___x_3107_;
}
else
{
lean_object* v_val_3108_; uint8_t v___x_3109_; 
lean_dec_ref(v___x_3104_);
v_val_3108_ = lean_ctor_get(v_fst_3105_, 0);
lean_inc(v_val_3108_);
lean_dec_ref(v_fst_3105_);
v___x_3109_ = lean_unbox(v_val_3108_);
lean_dec(v_val_3108_);
return v___x_3109_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object* v_s_3110_){
_start:
{
uint8_t v_res_3111_; lean_object* v_r_3112_; 
v_res_3111_ = l_String_Slice_isNat(v_s_3110_);
lean_dec_ref(v_s_3110_);
v_r_3112_ = lean_box(v_res_3111_);
return v_r_3112_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(lean_object* v_s_3113_, lean_object* v_inst_3114_, lean_object* v_R_3115_, lean_object* v_a_3116_, lean_object* v_b_3117_, lean_object* v_c_3118_){
_start:
{
lean_object* v___x_3119_; 
v___x_3119_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3113_, v_a_3116_, v_b_3117_);
return v___x_3119_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___boxed(lean_object* v_s_3120_, lean_object* v_inst_3121_, lean_object* v_R_3122_, lean_object* v_a_3123_, lean_object* v_b_3124_, lean_object* v_c_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(v_s_3120_, v_inst_3121_, v_R_3122_, v_a_3123_, v_b_3124_, v_c_3125_);
lean_dec_ref(v_s_3120_);
return v_res_3126_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object* v_s_3127_, lean_object* v_a_3128_, lean_object* v_b_3129_){
_start:
{
lean_object* v_str_3130_; lean_object* v_startInclusive_3131_; lean_object* v_endExclusive_3132_; lean_object* v___x_3133_; uint8_t v___x_3134_; 
v_str_3130_ = lean_ctor_get(v_s_3127_, 0);
v_startInclusive_3131_ = lean_ctor_get(v_s_3127_, 1);
v_endExclusive_3132_ = lean_ctor_get(v_s_3127_, 2);
v___x_3133_ = lean_nat_sub(v_endExclusive_3132_, v_startInclusive_3131_);
v___x_3134_ = lean_nat_dec_eq(v_a_3128_, v___x_3133_);
lean_dec(v___x_3133_);
if (v___x_3134_ == 0)
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; uint32_t v___x_3138_; uint32_t v___x_3139_; uint8_t v___x_3140_; 
v___x_3135_ = lean_nat_add(v_startInclusive_3131_, v_a_3128_);
lean_dec(v_a_3128_);
v___x_3136_ = lean_string_utf8_next_fast(v_str_3130_, v___x_3135_);
v___x_3137_ = lean_nat_sub(v___x_3136_, v_startInclusive_3131_);
v___x_3138_ = lean_string_utf8_get_fast(v_str_3130_, v___x_3135_);
lean_dec(v___x_3135_);
v___x_3139_ = 95;
v___x_3140_ = lean_uint32_dec_eq(v___x_3138_, v___x_3139_);
if (v___x_3140_ == 0)
{
lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; 
v___x_3141_ = lean_unsigned_to_nat(10u);
v___x_3142_ = lean_nat_mul(v_b_3129_, v___x_3141_);
lean_dec(v_b_3129_);
v___x_3143_ = lean_uint32_to_nat(v___x_3138_);
v___x_3144_ = lean_unsigned_to_nat(48u);
v___x_3145_ = lean_nat_sub(v___x_3143_, v___x_3144_);
lean_dec(v___x_3143_);
v___x_3146_ = lean_nat_add(v___x_3142_, v___x_3145_);
lean_dec(v___x_3145_);
lean_dec(v___x_3142_);
v_a_3128_ = v___x_3137_;
v_b_3129_ = v___x_3146_;
goto _start;
}
else
{
v_a_3128_ = v___x_3137_;
goto _start;
}
}
else
{
lean_dec(v_a_3128_);
return v_b_3129_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object* v_s_3149_, lean_object* v_a_3150_, lean_object* v_b_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3149_, v_a_3150_, v_b_3151_);
lean_dec_ref(v_s_3149_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object* v_s_3153_){
_start:
{
uint8_t v___x_3154_; 
v___x_3154_ = l_String_Slice_isNat(v_s_3153_);
if (v___x_3154_ == 0)
{
lean_object* v___x_3155_; 
v___x_3155_ = lean_box(0);
return v___x_3155_;
}
else
{
lean_object* v___x_3156_; lean_object* v___x_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; 
v___x_3156_ = lean_unsigned_to_nat(0u);
v___x_3157_ = l_String_Slice_positions(v_s_3153_);
v___x_3158_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3153_, v___x_3157_, v___x_3156_);
v___x_3159_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3159_, 0, v___x_3158_);
return v___x_3159_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object* v_s_3160_){
_start:
{
lean_object* v_res_3161_; 
v_res_3161_ = l_String_Slice_toNat_x3f(v_s_3160_);
lean_dec_ref(v_s_3160_);
return v_res_3161_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object* v_s_3162_, lean_object* v_inst_3163_, lean_object* v_R_3164_, lean_object* v_a_3165_, lean_object* v_b_3166_, lean_object* v_c_3167_){
_start:
{
lean_object* v___x_3168_; 
v___x_3168_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3162_, v_a_3165_, v_b_3166_);
return v___x_3168_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object* v_s_3169_, lean_object* v_inst_3170_, lean_object* v_R_3171_, lean_object* v_a_3172_, lean_object* v_b_3173_, lean_object* v_c_3174_){
_start:
{
lean_object* v_res_3175_; 
v_res_3175_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(v_s_3169_, v_inst_3170_, v_R_3171_, v_a_3172_, v_b_3173_, v_c_3174_);
lean_dec_ref(v_s_3169_);
return v_res_3175_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_toNat_x21_spec__0(lean_object* v_msg_3176_){
_start:
{
lean_object* v___x_3177_; lean_object* v___x_3178_; 
v___x_3177_ = lean_unsigned_to_nat(0u);
v___x_3178_ = lean_panic_fn(v___x_3177_, v_msg_3176_);
return v___x_3178_;
}
}
static lean_object* _init_l_String_Slice_toNat_x21___closed__3(void){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; lean_object* v___x_3186_; lean_object* v___x_3187_; 
v___x_3182_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__2));
v___x_3183_ = lean_unsigned_to_nat(4u);
v___x_3184_ = lean_unsigned_to_nat(1013u);
v___x_3185_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__1));
v___x_3186_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__0));
v___x_3187_ = l_mkPanicMessageWithDecl(v___x_3186_, v___x_3185_, v___x_3184_, v___x_3183_, v___x_3182_);
return v___x_3187_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21(lean_object* v_s_3188_){
_start:
{
uint8_t v___x_3189_; 
v___x_3189_ = l_String_Slice_isNat(v_s_3188_);
if (v___x_3189_ == 0)
{
lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_obj_once(&l_String_Slice_toNat_x21___closed__3, &l_String_Slice_toNat_x21___closed__3_once, _init_l_String_Slice_toNat_x21___closed__3);
v___x_3191_ = l_panic___at___00String_Slice_toNat_x21_spec__0(v___x_3190_);
return v___x_3191_;
}
else
{
lean_object* v___x_3192_; lean_object* v___x_3193_; lean_object* v___x_3194_; 
v___x_3192_ = lean_unsigned_to_nat(0u);
v___x_3193_ = l_String_Slice_positions(v_s_3188_);
v___x_3194_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3188_, v___x_3193_, v___x_3192_);
return v___x_3194_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21___boxed(lean_object* v_s_3195_){
_start:
{
lean_object* v_res_3196_; 
v_res_3196_ = l_String_Slice_toNat_x21(v_s_3195_);
lean_dec_ref(v_s_3195_);
return v_res_3196_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object* v_s_3197_){
_start:
{
lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3198_ = lean_unsigned_to_nat(0u);
v___x_3199_ = l_String_Slice_Pos_get_x3f(v_s_3197_, v___x_3198_);
return v___x_3199_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object* v_s_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_String_Slice_front_x3f(v_s_3200_);
lean_dec_ref(v_s_3200_);
return v_res_3201_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_front(lean_object* v_s_3202_){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = lean_unsigned_to_nat(0u);
v___x_3204_ = l_String_Slice_Pos_get_x3f(v_s_3202_, v___x_3203_);
if (lean_obj_tag(v___x_3204_) == 0)
{
uint32_t v___x_3205_; 
v___x_3205_ = 65;
return v___x_3205_;
}
else
{
lean_object* v_val_3206_; uint32_t v___x_3207_; 
v_val_3206_ = lean_ctor_get(v___x_3204_, 0);
lean_inc(v_val_3206_);
lean_dec_ref(v___x_3204_);
v___x_3207_ = lean_unbox_uint32(v_val_3206_);
lean_dec(v_val_3206_);
return v___x_3207_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object* v_s_3208_){
_start:
{
uint32_t v_res_3209_; lean_object* v_r_3210_; 
v_res_3209_ = l_String_Slice_front(v_s_3208_);
lean_dec_ref(v_s_3208_);
v_r_3210_ = lean_box_uint32(v_res_3209_);
return v_r_3210_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isInt(lean_object* v_s_3211_){
_start:
{
lean_object* v_str_3212_; lean_object* v_startInclusive_3213_; lean_object* v_endExclusive_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; uint8_t v___x_3217_; 
v_str_3212_ = lean_ctor_get(v_s_3211_, 0);
v_startInclusive_3213_ = lean_ctor_get(v_s_3211_, 1);
v_endExclusive_3214_ = lean_ctor_get(v_s_3211_, 2);
v___x_3215_ = lean_unsigned_to_nat(0u);
v___x_3216_ = lean_nat_sub(v_endExclusive_3214_, v_startInclusive_3213_);
v___x_3217_ = lean_nat_dec_eq(v___x_3215_, v___x_3216_);
lean_dec(v___x_3216_);
if (v___x_3217_ == 0)
{
uint32_t v___x_3218_; uint32_t v___x_3219_; uint8_t v___x_3220_; 
v___x_3218_ = 45;
v___x_3219_ = lean_string_utf8_get_fast(v_str_3212_, v_startInclusive_3213_);
v___x_3220_ = lean_uint32_dec_eq(v___x_3219_, v___x_3218_);
if (v___x_3220_ == 0)
{
uint8_t v___x_3221_; 
v___x_3221_ = l_String_Slice_isNat(v_s_3211_);
lean_dec_ref(v_s_3211_);
return v___x_3221_;
}
else
{
lean_object* v___x_3223_; uint8_t v_isShared_3224_; uint8_t v_isSharedCheck_3232_; 
lean_inc(v_endExclusive_3214_);
lean_inc(v_startInclusive_3213_);
lean_inc_ref(v_str_3212_);
v_isSharedCheck_3232_ = !lean_is_exclusive(v_s_3211_);
if (v_isSharedCheck_3232_ == 0)
{
lean_object* v_unused_3233_; lean_object* v_unused_3234_; lean_object* v_unused_3235_; 
v_unused_3233_ = lean_ctor_get(v_s_3211_, 2);
lean_dec(v_unused_3233_);
v_unused_3234_ = lean_ctor_get(v_s_3211_, 1);
lean_dec(v_unused_3234_);
v_unused_3235_ = lean_ctor_get(v_s_3211_, 0);
lean_dec(v_unused_3235_);
v___x_3223_ = v_s_3211_;
v_isShared_3224_ = v_isSharedCheck_3232_;
goto v_resetjp_3222_;
}
else
{
lean_dec(v_s_3211_);
v___x_3223_ = lean_box(0);
v_isShared_3224_ = v_isSharedCheck_3232_;
goto v_resetjp_3222_;
}
v_resetjp_3222_:
{
lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v___x_3229_; 
v___x_3225_ = lean_string_utf8_next_fast(v_str_3212_, v_startInclusive_3213_);
v___x_3226_ = lean_nat_sub(v___x_3225_, v_startInclusive_3213_);
v___x_3227_ = lean_nat_add(v_startInclusive_3213_, v___x_3226_);
lean_dec(v___x_3226_);
lean_dec(v_startInclusive_3213_);
if (v_isShared_3224_ == 0)
{
lean_ctor_set(v___x_3223_, 1, v___x_3227_);
v___x_3229_ = v___x_3223_;
goto v_reusejp_3228_;
}
else
{
lean_object* v_reuseFailAlloc_3231_; 
v_reuseFailAlloc_3231_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3231_, 0, v_str_3212_);
lean_ctor_set(v_reuseFailAlloc_3231_, 1, v___x_3227_);
lean_ctor_set(v_reuseFailAlloc_3231_, 2, v_endExclusive_3214_);
v___x_3229_ = v_reuseFailAlloc_3231_;
goto v_reusejp_3228_;
}
v_reusejp_3228_:
{
uint8_t v___x_3230_; 
v___x_3230_ = l_String_Slice_isNat(v___x_3229_);
lean_dec_ref(v___x_3229_);
return v___x_3230_;
}
}
}
}
else
{
uint8_t v___x_3236_; 
v___x_3236_ = l_String_Slice_isNat(v_s_3211_);
lean_dec_ref(v_s_3211_);
return v___x_3236_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object* v_s_3237_){
_start:
{
uint8_t v_res_3238_; lean_object* v_r_3239_; 
v_res_3238_ = l_String_Slice_isInt(v_s_3237_);
v_r_3239_ = lean_box(v_res_3238_);
return v_r_3239_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x3f(lean_object* v_s_3240_){
_start:
{
lean_object* v_str_3253_; lean_object* v_startInclusive_3254_; lean_object* v_endExclusive_3255_; lean_object* v___x_3256_; lean_object* v___x_3257_; uint8_t v___x_3258_; 
v_str_3253_ = lean_ctor_get(v_s_3240_, 0);
v_startInclusive_3254_ = lean_ctor_get(v_s_3240_, 1);
v_endExclusive_3255_ = lean_ctor_get(v_s_3240_, 2);
v___x_3256_ = lean_unsigned_to_nat(0u);
v___x_3257_ = lean_nat_sub(v_endExclusive_3255_, v_startInclusive_3254_);
v___x_3258_ = lean_nat_dec_eq(v___x_3256_, v___x_3257_);
lean_dec(v___x_3257_);
if (v___x_3258_ == 0)
{
uint32_t v___x_3259_; uint32_t v___x_3260_; uint8_t v___x_3261_; 
v___x_3259_ = 45;
v___x_3260_ = lean_string_utf8_get_fast(v_str_3253_, v_startInclusive_3254_);
v___x_3261_ = lean_uint32_dec_eq(v___x_3260_, v___x_3259_);
if (v___x_3261_ == 0)
{
goto v___jp_3241_;
}
else
{
lean_object* v___x_3263_; uint8_t v_isShared_3264_; uint8_t v_isSharedCheck_3282_; 
lean_inc(v_endExclusive_3255_);
lean_inc(v_startInclusive_3254_);
lean_inc_ref(v_str_3253_);
v_isSharedCheck_3282_ = !lean_is_exclusive(v_s_3240_);
if (v_isSharedCheck_3282_ == 0)
{
lean_object* v_unused_3283_; lean_object* v_unused_3284_; lean_object* v_unused_3285_; 
v_unused_3283_ = lean_ctor_get(v_s_3240_, 2);
lean_dec(v_unused_3283_);
v_unused_3284_ = lean_ctor_get(v_s_3240_, 1);
lean_dec(v_unused_3284_);
v_unused_3285_ = lean_ctor_get(v_s_3240_, 0);
lean_dec(v_unused_3285_);
v___x_3263_ = v_s_3240_;
v_isShared_3264_ = v_isSharedCheck_3282_;
goto v_resetjp_3262_;
}
else
{
lean_dec(v_s_3240_);
v___x_3263_ = lean_box(0);
v_isShared_3264_ = v_isSharedCheck_3282_;
goto v_resetjp_3262_;
}
v_resetjp_3262_:
{
lean_object* v___x_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; lean_object* v___x_3269_; 
v___x_3265_ = lean_string_utf8_next_fast(v_str_3253_, v_startInclusive_3254_);
v___x_3266_ = lean_nat_sub(v___x_3265_, v_startInclusive_3254_);
v___x_3267_ = lean_nat_add(v_startInclusive_3254_, v___x_3266_);
lean_dec(v___x_3266_);
lean_dec(v_startInclusive_3254_);
if (v_isShared_3264_ == 0)
{
lean_ctor_set(v___x_3263_, 1, v___x_3267_);
v___x_3269_ = v___x_3263_;
goto v_reusejp_3268_;
}
else
{
lean_object* v_reuseFailAlloc_3281_; 
v_reuseFailAlloc_3281_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3281_, 0, v_str_3253_);
lean_ctor_set(v_reuseFailAlloc_3281_, 1, v___x_3267_);
lean_ctor_set(v_reuseFailAlloc_3281_, 2, v_endExclusive_3255_);
v___x_3269_ = v_reuseFailAlloc_3281_;
goto v_reusejp_3268_;
}
v_reusejp_3268_:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_String_Slice_toNat_x3f(v___x_3269_);
lean_dec_ref(v___x_3269_);
if (lean_obj_tag(v___x_3270_) == 0)
{
lean_object* v___x_3271_; 
v___x_3271_ = lean_box(0);
return v___x_3271_;
}
else
{
lean_object* v_val_3272_; lean_object* v___x_3274_; uint8_t v_isShared_3275_; uint8_t v_isSharedCheck_3280_; 
v_val_3272_ = lean_ctor_get(v___x_3270_, 0);
v_isSharedCheck_3280_ = !lean_is_exclusive(v___x_3270_);
if (v_isSharedCheck_3280_ == 0)
{
v___x_3274_ = v___x_3270_;
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
else
{
lean_inc(v_val_3272_);
lean_dec(v___x_3270_);
v___x_3274_ = lean_box(0);
v_isShared_3275_ = v_isSharedCheck_3280_;
goto v_resetjp_3273_;
}
v_resetjp_3273_:
{
lean_object* v___x_3276_; lean_object* v___x_3278_; 
v___x_3276_ = l_Int_negOfNat(v_val_3272_);
lean_dec(v_val_3272_);
if (v_isShared_3275_ == 0)
{
lean_ctor_set(v___x_3274_, 0, v___x_3276_);
v___x_3278_ = v___x_3274_;
goto v_reusejp_3277_;
}
else
{
lean_object* v_reuseFailAlloc_3279_; 
v_reuseFailAlloc_3279_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3279_, 0, v___x_3276_);
v___x_3278_ = v_reuseFailAlloc_3279_;
goto v_reusejp_3277_;
}
v_reusejp_3277_:
{
return v___x_3278_;
}
}
}
}
}
}
}
else
{
goto v___jp_3241_;
}
v___jp_3241_:
{
lean_object* v___x_3242_; 
v___x_3242_ = l_String_Slice_toNat_x3f(v_s_3240_);
lean_dec_ref(v_s_3240_);
if (lean_obj_tag(v___x_3242_) == 0)
{
lean_object* v___x_3243_; 
v___x_3243_ = lean_box(0);
return v___x_3243_;
}
else
{
lean_object* v_val_3244_; lean_object* v___x_3246_; uint8_t v_isShared_3247_; uint8_t v_isSharedCheck_3252_; 
v_val_3244_ = lean_ctor_get(v___x_3242_, 0);
v_isSharedCheck_3252_ = !lean_is_exclusive(v___x_3242_);
if (v_isSharedCheck_3252_ == 0)
{
v___x_3246_ = v___x_3242_;
v_isShared_3247_ = v_isSharedCheck_3252_;
goto v_resetjp_3245_;
}
else
{
lean_inc(v_val_3244_);
lean_dec(v___x_3242_);
v___x_3246_ = lean_box(0);
v_isShared_3247_ = v_isSharedCheck_3252_;
goto v_resetjp_3245_;
}
v_resetjp_3245_:
{
lean_object* v___x_3248_; lean_object* v___x_3250_; 
v___x_3248_ = lean_nat_to_int(v_val_3244_);
if (v_isShared_3247_ == 0)
{
lean_ctor_set(v___x_3246_, 0, v___x_3248_);
v___x_3250_ = v___x_3246_;
goto v_reusejp_3249_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v___x_3248_);
v___x_3250_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3249_;
}
v_reusejp_3249_:
{
return v___x_3250_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x21(lean_object* v_s_3287_){
_start:
{
lean_object* v___x_3288_; 
v___x_3288_ = l_String_Slice_toInt_x3f(v_s_3287_);
if (lean_obj_tag(v___x_3288_) == 0)
{
lean_object* v___x_3289_; lean_object* v___x_3290_; lean_object* v___x_3291_; 
v___x_3289_ = l_Int_instInhabited;
v___x_3290_ = ((lean_object*)(l_String_Slice_toInt_x21___closed__0));
v___x_3291_ = l_panic___redArg(v___x_3289_, v___x_3290_);
return v___x_3291_;
}
else
{
lean_object* v_val_3292_; 
v_val_3292_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_val_3292_);
lean_dec_ref(v___x_3288_);
return v_val_3292_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object* v_s_3293_){
_start:
{
lean_object* v_startInclusive_3294_; lean_object* v_endExclusive_3295_; lean_object* v___x_3296_; lean_object* v___x_3297_; 
v_startInclusive_3294_ = lean_ctor_get(v_s_3293_, 1);
v_endExclusive_3295_ = lean_ctor_get(v_s_3293_, 2);
v___x_3296_ = lean_nat_sub(v_endExclusive_3295_, v_startInclusive_3294_);
v___x_3297_ = l_String_Slice_Pos_prev_x3f(v_s_3293_, v___x_3296_);
lean_dec(v___x_3296_);
if (lean_obj_tag(v___x_3297_) == 0)
{
lean_object* v___x_3298_; 
v___x_3298_ = lean_box(0);
return v___x_3298_;
}
else
{
lean_object* v_val_3299_; lean_object* v___x_3300_; 
v_val_3299_ = lean_ctor_get(v___x_3297_, 0);
lean_inc(v_val_3299_);
lean_dec_ref(v___x_3297_);
v___x_3300_ = l_String_Slice_Pos_get_x3f(v_s_3293_, v_val_3299_);
lean_dec(v_val_3299_);
return v___x_3300_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object* v_s_3301_){
_start:
{
lean_object* v_res_3302_; 
v_res_3302_ = l_String_Slice_back_x3f(v_s_3301_);
lean_dec_ref(v_s_3301_);
return v_res_3302_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_back(lean_object* v_s_3303_){
_start:
{
lean_object* v_startInclusive_3304_; lean_object* v_endExclusive_3305_; lean_object* v___x_3306_; lean_object* v___x_3307_; 
v_startInclusive_3304_ = lean_ctor_get(v_s_3303_, 1);
v_endExclusive_3305_ = lean_ctor_get(v_s_3303_, 2);
v___x_3306_ = lean_nat_sub(v_endExclusive_3305_, v_startInclusive_3304_);
v___x_3307_ = l_String_Slice_Pos_prev_x3f(v_s_3303_, v___x_3306_);
lean_dec(v___x_3306_);
if (lean_obj_tag(v___x_3307_) == 0)
{
uint32_t v___x_3308_; 
v___x_3308_ = 65;
return v___x_3308_;
}
else
{
lean_object* v_val_3309_; lean_object* v___x_3310_; 
v_val_3309_ = lean_ctor_get(v___x_3307_, 0);
lean_inc(v_val_3309_);
lean_dec_ref(v___x_3307_);
v___x_3310_ = l_String_Slice_Pos_get_x3f(v_s_3303_, v_val_3309_);
lean_dec(v_val_3309_);
if (lean_obj_tag(v___x_3310_) == 0)
{
uint32_t v___x_3311_; 
v___x_3311_ = 65;
return v___x_3311_;
}
else
{
lean_object* v_val_3312_; uint32_t v___x_3313_; 
v_val_3312_ = lean_ctor_get(v___x_3310_, 0);
lean_inc(v_val_3312_);
lean_dec_ref(v___x_3310_);
v___x_3313_ = lean_unbox_uint32(v_val_3312_);
lean_dec(v_val_3312_);
return v___x_3313_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object* v_s_3314_){
_start:
{
uint32_t v_res_3315_; lean_object* v_r_3316_; 
v_res_3315_ = l_String_Slice_back(v_s_3314_);
lean_dec_ref(v_s_3314_);
v_r_3316_ = lean_box_uint32(v_res_3315_);
return v_r_3316_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(lean_object* v_acc_3317_, lean_object* v_s_3318_, lean_object* v_a_3319_){
_start:
{
if (lean_obj_tag(v_a_3319_) == 0)
{
return v_acc_3317_;
}
else
{
lean_object* v_head_3320_; lean_object* v_tail_3321_; lean_object* v_str_3322_; lean_object* v_startInclusive_3323_; lean_object* v_endExclusive_3324_; lean_object* v_str_3325_; lean_object* v_startInclusive_3326_; lean_object* v_endExclusive_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; lean_object* v___x_3330_; lean_object* v___x_3331_; 
v_head_3320_ = lean_ctor_get(v_a_3319_, 0);
v_tail_3321_ = lean_ctor_get(v_a_3319_, 1);
v_str_3322_ = lean_ctor_get(v_s_3318_, 0);
v_startInclusive_3323_ = lean_ctor_get(v_s_3318_, 1);
v_endExclusive_3324_ = lean_ctor_get(v_s_3318_, 2);
v_str_3325_ = lean_ctor_get(v_head_3320_, 0);
v_startInclusive_3326_ = lean_ctor_get(v_head_3320_, 1);
v_endExclusive_3327_ = lean_ctor_get(v_head_3320_, 2);
v___x_3328_ = lean_string_utf8_extract(v_str_3322_, v_startInclusive_3323_, v_endExclusive_3324_);
v___x_3329_ = lean_string_append(v_acc_3317_, v___x_3328_);
lean_dec_ref(v___x_3328_);
v___x_3330_ = lean_string_utf8_extract(v_str_3325_, v_startInclusive_3326_, v_endExclusive_3327_);
v___x_3331_ = lean_string_append(v___x_3329_, v___x_3330_);
lean_dec_ref(v___x_3330_);
v_acc_3317_ = v___x_3331_;
v_a_3319_ = v_tail_3321_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go___boxed(lean_object* v_acc_3333_, lean_object* v_s_3334_, lean_object* v_a_3335_){
_start:
{
lean_object* v_res_3336_; 
v_res_3336_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v_acc_3333_, v_s_3334_, v_a_3335_);
lean_dec(v_a_3335_);
lean_dec_ref(v_s_3334_);
return v_res_3336_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object* v_s_3337_, lean_object* v_x_3338_){
_start:
{
if (lean_obj_tag(v_x_3338_) == 0)
{
lean_object* v___x_3339_; 
v___x_3339_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
return v___x_3339_;
}
else
{
lean_object* v_head_3340_; lean_object* v_tail_3341_; lean_object* v_str_3342_; lean_object* v_startInclusive_3343_; lean_object* v_endExclusive_3344_; lean_object* v___x_3345_; lean_object* v___x_3346_; 
v_head_3340_ = lean_ctor_get(v_x_3338_, 0);
v_tail_3341_ = lean_ctor_get(v_x_3338_, 1);
v_str_3342_ = lean_ctor_get(v_head_3340_, 0);
v_startInclusive_3343_ = lean_ctor_get(v_head_3340_, 1);
v_endExclusive_3344_ = lean_ctor_get(v_head_3340_, 2);
v___x_3345_ = lean_string_utf8_extract(v_str_3342_, v_startInclusive_3343_, v_endExclusive_3344_);
v___x_3346_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v___x_3345_, v_s_3337_, v_tail_3341_);
return v___x_3346_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object* v_s_3347_, lean_object* v_x_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_String_Slice_intercalate(v_s_3347_, v_x_3348_);
lean_dec(v_x_3348_);
lean_dec_ref(v_s_3347_);
return v_res_3349_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0(lean_object* v_x_3350_, lean_object* v_x_3351_){
_start:
{
if (lean_obj_tag(v_x_3351_) == 0)
{
return v_x_3350_;
}
else
{
lean_object* v_head_3352_; lean_object* v_tail_3353_; lean_object* v_str_3354_; lean_object* v_startInclusive_3355_; lean_object* v_endExclusive_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; 
v_head_3352_ = lean_ctor_get(v_x_3351_, 0);
v_tail_3353_ = lean_ctor_get(v_x_3351_, 1);
v_str_3354_ = lean_ctor_get(v_head_3352_, 0);
v_startInclusive_3355_ = lean_ctor_get(v_head_3352_, 1);
v_endExclusive_3356_ = lean_ctor_get(v_head_3352_, 2);
v___x_3357_ = lean_string_utf8_extract(v_str_3354_, v_startInclusive_3355_, v_endExclusive_3356_);
v___x_3358_ = lean_string_append(v_x_3350_, v___x_3357_);
lean_dec_ref(v___x_3357_);
v_x_3350_ = v___x_3358_;
v_x_3351_ = v_tail_3353_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0___boxed(lean_object* v_x_3360_, lean_object* v_x_3361_){
_start:
{
lean_object* v_res_3362_; 
v_res_3362_ = l_List_foldl___at___00String_Slice_join_spec__0(v_x_3360_, v_x_3361_);
lean_dec(v_x_3361_);
return v_res_3362_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join(lean_object* v_l_3363_){
_start:
{
lean_object* v___x_3364_; lean_object* v___x_3365_; 
v___x_3364_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
v___x_3365_ = l_List_foldl___at___00String_Slice_join_spec__0(v___x_3364_, v_l_3363_);
return v___x_3365_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join___boxed(lean_object* v_l_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_String_Slice_join(v_l_3366_);
lean_dec(v_l_3366_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object* v_s_3368_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = l_String_Slice_toString(v_s_3368_);
v___x_3370_ = l_String_toName(v___x_3369_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object* v_s_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_String_Slice_toName(v_s_3371_);
lean_dec_ref(v_s_3371_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object* v_s_3373_){
_start:
{
lean_object* v_str_3374_; lean_object* v_startInclusive_3375_; lean_object* v_endExclusive_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_str_3374_ = lean_ctor_get(v_s_3373_, 0);
v_startInclusive_3375_ = lean_ctor_get(v_s_3373_, 1);
v_endExclusive_3376_ = lean_ctor_get(v_s_3373_, 2);
v___x_3377_ = lean_string_utf8_extract(v_str_3374_, v_startInclusive_3375_, v_endExclusive_3376_);
v___x_3378_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3378_, 0, v___x_3377_);
return v___x_3378_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object* v_s_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_String_Slice_instToFormat___lam__0(v_s_3379_);
lean_dec_ref(v_s_3379_);
return v_res_3380_;
}
}
lean_object* runtime_initialize_Init_Data_String_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_ToSlice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iter_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* runtime_initialize_Init_Omega(uint8_t builtin);
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
res = runtime_initialize_Init_Data_String_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_ToSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Iterate(builtin);
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
res = runtime_initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
l_String_Slice_instLT = _init_l_String_Slice_instLT();
lean_mark_persistent(l_String_Slice_instLT);
l_String_Slice_instLE = _init_l_String_Slice_instLE();
lean_mark_persistent(l_String_Slice_instLE);
return lean_io_result_mk_ok(lean_box(0));
}
static bool _G_meta_initialized = false;
LEAN_EXPORT lean_object* meta_initialize_Init_Data_String_Slice(uint8_t builtin) {
lean_object * res;
if (_G_meta_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_meta_initialized = true;
return lean_io_result_mk_ok(lean_box(0));
}
lean_object* initialize_Init_Data_String_Pattern(uint8_t builtin);
lean_object* initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* initialize_Init_Data_String_ToSlice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iter_Basic(uint8_t builtin);
lean_object* initialize_Init_Data_String_Iterate(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Collect(uint8_t builtin);
lean_object* initialize_Init_Data_Iterators_Consumers_Loop(uint8_t builtin);
lean_object* initialize_Init_Data_Option_Lemmas(uint8_t builtin);
lean_object* initialize_Init_Data_String_Termination(uint8_t builtin);
lean_object* initialize_Init_Omega(uint8_t builtin);
static bool _G_initialized = false;
LEAN_EXPORT lean_object* initialize_Init_Data_String_Slice(uint8_t builtin) {
lean_object * res;
if (_G_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_initialized = true;
res = initialize_Init_Data_String_Pattern(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Ord_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_Iterators_Combinators_FilterMap(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_ToSlice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Subslice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iter_Basic(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = initialize_Init_Data_String_Iterate(builtin);
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
res = initialize_Init_Omega(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = runtime_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
res = meta_initialize_Init_Data_String_Slice(builtin);
if (lean_io_result_is_error(res)) return res;
lean_dec_ref(res);
return initialize_Init_Data_String_Slice(builtin);
}
#ifdef __cplusplus
}
#endif
