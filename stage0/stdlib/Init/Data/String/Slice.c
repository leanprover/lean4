// Lean compiler output
// Module: Init.Data.String.Slice
// Imports: public import Init.Data.String.Pattern public import Init.Data.Ord.Basic public import Init.Data.Iterators.Combinators.FilterMap public import Init.Data.String.ToSlice public import Init.Data.String.Subslice public import Init.Data.String.Iter public import Init.Data.String.Iterate import Init.Data.Iterators.Consumers.Collect import Init.Data.Iterators.Consumers.Loop import Init.Data.Option.Lemmas import Init.Data.String.Termination import Init.Omega
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
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* l_String_Slice_positions(lean_object*);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
lean_object* l_String_Slice_Pos_nextn(lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
lean_object* l_String_Slice_posLE(lean_object*, lean_object*);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_dec_le(uint8_t, uint8_t);
lean_object* l_mkPanicMessageWithDecl(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_panic_fn(lean_object*, lean_object*);
lean_object* l_String_Slice_Pos_prevn(lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_to_int(lean_object*);
lean_object* l_Int_negOfNat(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(lean_object*);
extern lean_object* l_Int_instInhabited;
lean_object* l_panic___redArg(lean_object*, lean_object*);
lean_object* l_String_toName(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_closure_object l_String_Slice_trimAsciiStart___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_closure_object) + sizeof(void*)*0, .m_other = 0, .m_tag = 245}, .m_fun = (void*)l_Char_isWhitespace___boxed, .m_arity = 1, .m_num_fixed = 0, .m_objs = {} };
static const lean_object* l_String_Slice_trimAsciiStart___closed__0 = (const lean_object*)&l_String_Slice_trimAsciiStart___closed__0_value;
static lean_once_cell_t l_String_Slice_trimAsciiStart___closed__1_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_trimAsciiStart___closed__1;
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go_match__1_splitter___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
static lean_once_cell_t l_String_Slice_trimAsciiEnd___closed__0_once = LEAN_ONCE_CELL_INITIALIZER;
static lean_object* l_String_Slice_trimAsciiEnd___closed__0;
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___redArg(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___boxed(lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_Slice_trimAscii_spec__0(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_Slice_trimAscii_spec__0___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_Slice_trimAscii_spec__1(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_Slice_trimAscii_spec__1___boxed(lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimAscii(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_trimAscii___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_isNat___lam__0(lean_object*, lean_object*, lean_object*, uint8_t, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_isNat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_isNat(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_isInt(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_object* v___x_321_; 
v___x_321_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___redArg(v_x_318_, v_h__1_319_, v_h__2_320_);
return v___x_321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___boxed(lean_object* v_00_u03c1_322_, lean_object* v_00_u03c3_323_, lean_object* v_pat_324_, lean_object* v_inst_325_, lean_object* v_s_326_, lean_object* v_motive_327_, lean_object* v_x_328_, lean_object* v_h__1_329_, lean_object* v_h__2_330_){
_start:
{
lean_object* v_res_331_; 
v_res_331_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(v_00_u03c1_322_, v_00_u03c3_323_, v_pat_324_, v_inst_325_, v_s_326_, v_motive_327_, v_x_328_, v_h__1_329_, v_h__2_330_);
lean_dec_ref(v_s_326_);
lean_dec(v_inst_325_);
lean_dec(v_pat_324_);
return v_res_331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object* v_x_332_, lean_object* v_h__1_333_, lean_object* v_h__2_334_, lean_object* v_h__3_335_, lean_object* v_h__4_336_){
_start:
{
switch(lean_obj_tag(v_x_332_))
{
case 0:
{
lean_object* v_out_337_; 
lean_dec(v_h__4_336_);
lean_dec(v_h__3_335_);
v_out_337_ = lean_ctor_get(v_x_332_, 1);
lean_inc(v_out_337_);
if (lean_obj_tag(v_out_337_) == 0)
{
lean_object* v_it_338_; lean_object* v_startPos_339_; lean_object* v_endPos_340_; lean_object* v___x_341_; 
lean_dec(v_h__1_333_);
v_it_338_ = lean_ctor_get(v_x_332_, 0);
lean_inc(v_it_338_);
lean_dec_ref(v_x_332_);
v_startPos_339_ = lean_ctor_get(v_out_337_, 0);
lean_inc(v_startPos_339_);
v_endPos_340_ = lean_ctor_get(v_out_337_, 1);
lean_inc(v_endPos_340_);
lean_dec_ref(v_out_337_);
v___x_341_ = lean_apply_5(v_h__2_334_, v_it_338_, v_startPos_339_, v_endPos_340_, lean_box(0), lean_box(0));
return v___x_341_;
}
else
{
lean_object* v_it_342_; lean_object* v_startPos_343_; lean_object* v_endPos_344_; lean_object* v___x_345_; 
lean_dec(v_h__2_334_);
v_it_342_ = lean_ctor_get(v_x_332_, 0);
lean_inc(v_it_342_);
lean_dec_ref(v_x_332_);
v_startPos_343_ = lean_ctor_get(v_out_337_, 0);
lean_inc(v_startPos_343_);
v_endPos_344_ = lean_ctor_get(v_out_337_, 1);
lean_inc(v_endPos_344_);
lean_dec_ref(v_out_337_);
v___x_345_ = lean_apply_5(v_h__1_333_, v_it_342_, v_startPos_343_, v_endPos_344_, lean_box(0), lean_box(0));
return v___x_345_;
}
}
case 1:
{
lean_object* v_it_346_; lean_object* v___x_347_; 
lean_dec(v_h__4_336_);
lean_dec(v_h__2_334_);
lean_dec(v_h__1_333_);
v_it_346_ = lean_ctor_get(v_x_332_, 0);
lean_inc(v_it_346_);
lean_dec_ref(v_x_332_);
v___x_347_ = lean_apply_3(v_h__3_335_, v_it_346_, lean_box(0), lean_box(0));
return v___x_347_;
}
default: 
{
lean_object* v___x_348_; 
lean_dec(v_h__3_335_);
lean_dec(v_h__2_334_);
lean_dec(v_h__1_333_);
v___x_348_ = lean_apply_2(v_h__4_336_, lean_box(0), lean_box(0));
return v___x_348_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object* v_00_u03c3_349_, lean_object* v_inst_350_, lean_object* v_s_351_, lean_object* v_searcher_352_, lean_object* v_motive_353_, lean_object* v_x_354_, lean_object* v_h__1_355_, lean_object* v_h__2_356_, lean_object* v_h__3_357_, lean_object* v_h__4_358_){
_start:
{
lean_object* v___x_359_; 
v___x_359_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(v_x_354_, v_h__1_355_, v_h__2_356_, v_h__3_357_, v_h__4_358_);
return v___x_359_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object* v_00_u03c3_360_, lean_object* v_inst_361_, lean_object* v_s_362_, lean_object* v_searcher_363_, lean_object* v_motive_364_, lean_object* v_x_365_, lean_object* v_h__1_366_, lean_object* v_h__2_367_, lean_object* v_h__3_368_, lean_object* v_h__4_369_){
_start:
{
lean_object* v_res_370_; 
v_res_370_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(v_00_u03c3_360_, v_inst_361_, v_s_362_, v_searcher_363_, v_motive_364_, v_x_365_, v_h__1_366_, v_h__2_367_, v_h__3_368_, v_h__4_369_);
lean_dec(v_searcher_363_);
lean_dec_ref(v_s_362_);
lean_dec(v_inst_361_);
return v_res_370_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___redArg(lean_object* v_x_371_, lean_object* v_x_372_, lean_object* v_h__1_373_, lean_object* v_h__2_374_, lean_object* v_h__3_375_, lean_object* v_h__4_376_, lean_object* v_h__5_377_, lean_object* v_h__6_378_, lean_object* v_h__7_379_, lean_object* v_h__8_380_){
_start:
{
if (lean_obj_tag(v_x_371_) == 0)
{
lean_dec(v_h__8_380_);
lean_dec(v_h__7_379_);
lean_dec(v_h__6_378_);
switch(lean_obj_tag(v_x_372_))
{
case 0:
{
lean_object* v_it_381_; 
lean_dec(v_h__5_377_);
lean_dec(v_h__4_376_);
lean_dec(v_h__3_375_);
v_it_381_ = lean_ctor_get(v_x_372_, 0);
if (lean_obj_tag(v_it_381_) == 0)
{
lean_object* v_currPos_382_; lean_object* v_searcher_383_; lean_object* v_out_384_; lean_object* v_currPos_385_; lean_object* v_searcher_386_; lean_object* v___x_387_; 
lean_inc_ref(v_it_381_);
lean_dec(v_h__2_374_);
v_currPos_382_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_currPos_382_);
v_searcher_383_ = lean_ctor_get(v_x_371_, 1);
lean_inc(v_searcher_383_);
lean_dec_ref(v_x_371_);
v_out_384_ = lean_ctor_get(v_x_372_, 1);
lean_inc(v_out_384_);
lean_dec_ref(v_x_372_);
v_currPos_385_ = lean_ctor_get(v_it_381_, 0);
lean_inc(v_currPos_385_);
v_searcher_386_ = lean_ctor_get(v_it_381_, 1);
lean_inc(v_searcher_386_);
lean_dec_ref(v_it_381_);
v___x_387_ = lean_apply_5(v_h__1_373_, v_currPos_382_, v_searcher_383_, v_currPos_385_, v_searcher_386_, v_out_384_);
return v___x_387_;
}
else
{
lean_object* v_currPos_388_; lean_object* v_searcher_389_; lean_object* v_out_390_; lean_object* v___x_391_; 
lean_dec(v_h__1_373_);
v_currPos_388_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_currPos_388_);
v_searcher_389_ = lean_ctor_get(v_x_371_, 1);
lean_inc(v_searcher_389_);
lean_dec_ref(v_x_371_);
v_out_390_ = lean_ctor_get(v_x_372_, 1);
lean_inc(v_out_390_);
lean_dec_ref(v_x_372_);
v___x_391_ = lean_apply_3(v_h__2_374_, v_currPos_388_, v_searcher_389_, v_out_390_);
return v___x_391_;
}
}
case 1:
{
lean_object* v_it_392_; 
lean_dec(v_h__5_377_);
lean_dec(v_h__2_374_);
lean_dec(v_h__1_373_);
v_it_392_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_it_392_);
lean_dec_ref(v_x_372_);
if (lean_obj_tag(v_it_392_) == 0)
{
lean_object* v_currPos_393_; lean_object* v_searcher_394_; lean_object* v_currPos_395_; lean_object* v_searcher_396_; lean_object* v___x_397_; 
lean_dec(v_h__4_376_);
v_currPos_393_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_currPos_393_);
v_searcher_394_ = lean_ctor_get(v_x_371_, 1);
lean_inc(v_searcher_394_);
lean_dec_ref(v_x_371_);
v_currPos_395_ = lean_ctor_get(v_it_392_, 0);
lean_inc(v_currPos_395_);
v_searcher_396_ = lean_ctor_get(v_it_392_, 1);
lean_inc(v_searcher_396_);
lean_dec_ref(v_it_392_);
v___x_397_ = lean_apply_4(v_h__3_375_, v_currPos_393_, v_searcher_394_, v_currPos_395_, v_searcher_396_);
return v___x_397_;
}
else
{
lean_object* v_currPos_398_; lean_object* v_searcher_399_; lean_object* v___x_400_; 
lean_dec(v_h__3_375_);
v_currPos_398_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_currPos_398_);
v_searcher_399_ = lean_ctor_get(v_x_371_, 1);
lean_inc(v_searcher_399_);
lean_dec_ref(v_x_371_);
v___x_400_ = lean_apply_2(v_h__4_376_, v_currPos_398_, v_searcher_399_);
return v___x_400_;
}
}
default: 
{
lean_object* v_currPos_401_; lean_object* v_searcher_402_; lean_object* v___x_403_; 
lean_dec(v_h__4_376_);
lean_dec(v_h__3_375_);
lean_dec(v_h__2_374_);
lean_dec(v_h__1_373_);
v_currPos_401_ = lean_ctor_get(v_x_371_, 0);
lean_inc(v_currPos_401_);
v_searcher_402_ = lean_ctor_get(v_x_371_, 1);
lean_inc(v_searcher_402_);
lean_dec_ref(v_x_371_);
v___x_403_ = lean_apply_2(v_h__5_377_, v_currPos_401_, v_searcher_402_);
return v___x_403_;
}
}
}
else
{
lean_dec(v_h__5_377_);
lean_dec(v_h__4_376_);
lean_dec(v_h__3_375_);
lean_dec(v_h__2_374_);
lean_dec(v_h__1_373_);
switch(lean_obj_tag(v_x_372_))
{
case 0:
{
lean_object* v_it_404_; lean_object* v_out_405_; lean_object* v___x_406_; 
lean_dec(v_h__8_380_);
lean_dec(v_h__7_379_);
v_it_404_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_it_404_);
v_out_405_ = lean_ctor_get(v_x_372_, 1);
lean_inc(v_out_405_);
lean_dec_ref(v_x_372_);
v___x_406_ = lean_apply_2(v_h__6_378_, v_it_404_, v_out_405_);
return v___x_406_;
}
case 1:
{
lean_object* v_it_407_; lean_object* v___x_408_; 
lean_dec(v_h__8_380_);
lean_dec(v_h__6_378_);
v_it_407_ = lean_ctor_get(v_x_372_, 0);
lean_inc(v_it_407_);
lean_dec_ref(v_x_372_);
v___x_408_ = lean_apply_1(v_h__7_379_, v_it_407_);
return v___x_408_;
}
default: 
{
lean_object* v___x_409_; lean_object* v___x_410_; 
lean_dec(v_h__7_379_);
lean_dec(v_h__6_378_);
v___x_409_ = lean_box(0);
v___x_410_ = lean_apply_1(v_h__8_380_, v___x_409_);
return v___x_410_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(lean_object* v_00_u03c1_411_, lean_object* v_00_u03c3_412_, lean_object* v_pat_413_, lean_object* v_inst_414_, lean_object* v_s_415_, lean_object* v_motive_416_, lean_object* v_x_417_, lean_object* v_x_418_, lean_object* v_h__1_419_, lean_object* v_h__2_420_, lean_object* v_h__3_421_, lean_object* v_h__4_422_, lean_object* v_h__5_423_, lean_object* v_h__6_424_, lean_object* v_h__7_425_, lean_object* v_h__8_426_){
_start:
{
lean_object* v___x_427_; 
v___x_427_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___redArg(v_x_417_, v_x_418_, v_h__1_419_, v_h__2_420_, v_h__3_421_, v_h__4_422_, v_h__5_423_, v_h__6_424_, v_h__7_425_, v_h__8_426_);
return v___x_427_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___boxed(lean_object* v_00_u03c1_428_, lean_object* v_00_u03c3_429_, lean_object* v_pat_430_, lean_object* v_inst_431_, lean_object* v_s_432_, lean_object* v_motive_433_, lean_object* v_x_434_, lean_object* v_x_435_, lean_object* v_h__1_436_, lean_object* v_h__2_437_, lean_object* v_h__3_438_, lean_object* v_h__4_439_, lean_object* v_h__5_440_, lean_object* v_h__6_441_, lean_object* v_h__7_442_, lean_object* v_h__8_443_){
_start:
{
lean_object* v_res_444_; 
v_res_444_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(v_00_u03c1_428_, v_00_u03c3_429_, v_pat_430_, v_inst_431_, v_s_432_, v_motive_433_, v_x_434_, v_x_435_, v_h__1_436_, v_h__2_437_, v_h__3_438_, v_h__4_439_, v_h__5_440_, v_h__6_441_, v_h__7_442_, v_h__8_443_);
lean_dec_ref(v_s_432_);
lean_dec(v_inst_431_);
lean_dec(v_pat_430_);
return v_res_444_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___redArg(lean_object* v_x_445_, lean_object* v_h__1_446_, lean_object* v_h__2_447_){
_start:
{
if (lean_obj_tag(v_x_445_) == 0)
{
lean_object* v_currPos_448_; lean_object* v_searcher_449_; lean_object* v___x_450_; 
lean_dec(v_h__2_447_);
v_currPos_448_ = lean_ctor_get(v_x_445_, 0);
lean_inc(v_currPos_448_);
v_searcher_449_ = lean_ctor_get(v_x_445_, 1);
lean_inc(v_searcher_449_);
lean_dec_ref(v_x_445_);
v___x_450_ = lean_apply_2(v_h__1_446_, v_currPos_448_, v_searcher_449_);
return v___x_450_;
}
else
{
lean_object* v___x_451_; lean_object* v___x_452_; 
lean_dec(v_h__1_446_);
v___x_451_ = lean_box(0);
v___x_452_ = lean_apply_1(v_h__2_447_, v___x_451_);
return v___x_452_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_453_, lean_object* v_00_u03c3_454_, lean_object* v_pat_455_, lean_object* v_inst_456_, lean_object* v_s_457_, lean_object* v_motive_458_, lean_object* v_x_459_, lean_object* v_h__1_460_, lean_object* v_h__2_461_){
_start:
{
lean_object* v___x_462_; 
v___x_462_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___redArg(v_x_459_, v_h__1_460_, v_h__2_461_);
return v___x_462_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_463_, lean_object* v_00_u03c3_464_, lean_object* v_pat_465_, lean_object* v_inst_466_, lean_object* v_s_467_, lean_object* v_motive_468_, lean_object* v_x_469_, lean_object* v_h__1_470_, lean_object* v_h__2_471_){
_start:
{
lean_object* v_res_472_; 
v_res_472_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter(v_00_u03c1_463_, v_00_u03c3_464_, v_pat_465_, v_inst_466_, v_s_467_, v_motive_468_, v_x_469_, v_h__1_470_, v_h__2_471_);
lean_dec_ref(v_s_467_);
lean_dec(v_inst_466_);
lean_dec(v_pat_465_);
return v_res_472_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(lean_object* v_00_u03c1_473_, lean_object* v_00_u03c3_474_, lean_object* v_inst_475_, lean_object* v_pat_476_, lean_object* v_inst_477_, lean_object* v_s_478_, lean_object* v_inst_479_){
_start:
{
lean_object* v___x_480_; 
v___x_480_ = lean_box(0);
return v___x_480_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_481_, lean_object* v_00_u03c3_482_, lean_object* v_inst_483_, lean_object* v_pat_484_, lean_object* v_inst_485_, lean_object* v_s_486_, lean_object* v_inst_487_){
_start:
{
lean_object* v_res_488_; 
v_res_488_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(v_00_u03c1_481_, v_00_u03c3_482_, v_inst_483_, v_pat_484_, v_inst_485_, v_s_486_, v_inst_487_);
lean_dec_ref(v_s_486_);
lean_dec(v_inst_485_);
lean_dec(v_pat_484_);
lean_dec(v_inst_483_);
return v_res_488_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0(lean_object* v_toPure_489_, lean_object* v_recur_490_, lean_object* v_it_491_, lean_object* v_____do__lift_492_){
_start:
{
if (lean_obj_tag(v_____do__lift_492_) == 0)
{
lean_object* v_a_493_; lean_object* v___x_494_; 
lean_dec(v_it_491_);
lean_dec(v_recur_490_);
v_a_493_ = lean_ctor_get(v_____do__lift_492_, 0);
lean_inc(v_a_493_);
lean_dec_ref(v_____do__lift_492_);
v___x_494_ = lean_apply_2(v_toPure_489_, lean_box(0), v_a_493_);
return v___x_494_;
}
else
{
lean_object* v_a_495_; lean_object* v___x_496_; 
lean_dec(v_toPure_489_);
v_a_495_ = lean_ctor_get(v_____do__lift_492_, 0);
lean_inc(v_a_495_);
lean_dec_ref(v_____do__lift_492_);
v___x_496_ = lean_apply_4(v_recur_490_, v_it_491_, v_a_495_, lean_box(0), lean_box(0));
return v___x_496_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1(lean_object* v_toPure_497_, lean_object* v_recur_498_, lean_object* v___y_499_, lean_object* v_acc_500_, lean_object* v_toBind_501_, lean_object* v_s_502_){
_start:
{
switch(lean_obj_tag(v_s_502_))
{
case 0:
{
lean_object* v_it_503_; lean_object* v_out_504_; lean_object* v___f_505_; lean_object* v___x_506_; lean_object* v___x_507_; 
v_it_503_ = lean_ctor_get(v_s_502_, 0);
lean_inc(v_it_503_);
v_out_504_ = lean_ctor_get(v_s_502_, 1);
lean_inc(v_out_504_);
lean_dec_ref(v_s_502_);
v___f_505_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_505_, 0, v_toPure_497_);
lean_closure_set(v___f_505_, 1, v_recur_498_);
lean_closure_set(v___f_505_, 2, v_it_503_);
v___x_506_ = lean_apply_3(v___y_499_, v_out_504_, lean_box(0), v_acc_500_);
v___x_507_ = lean_apply_4(v_toBind_501_, lean_box(0), lean_box(0), v___x_506_, v___f_505_);
return v___x_507_;
}
case 1:
{
lean_object* v_it_508_; lean_object* v___x_509_; 
lean_dec(v_toBind_501_);
lean_dec(v___y_499_);
lean_dec(v_toPure_497_);
v_it_508_ = lean_ctor_get(v_s_502_, 0);
lean_inc(v_it_508_);
lean_dec_ref(v_s_502_);
v___x_509_ = lean_apply_4(v_recur_498_, v_it_508_, v_acc_500_, lean_box(0), lean_box(0));
return v___x_509_;
}
default: 
{
lean_object* v___x_510_; 
lean_dec(v_toBind_501_);
lean_dec(v___y_499_);
lean_dec(v_recur_498_);
v___x_510_ = lean_apply_2(v_toPure_497_, lean_box(0), v_acc_500_);
return v___x_510_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2(lean_object* v_toPure_511_, lean_object* v___y_512_, lean_object* v_toBind_513_, lean_object* v_inst_514_, lean_object* v_s_515_, lean_object* v_lift_516_, lean_object* v_it_517_, lean_object* v_acc_518_, lean_object* v_hP_519_, lean_object* v_recur_520_){
_start:
{
lean_object* v___f_521_; 
v___f_521_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_521_, 0, v_toPure_511_);
lean_closure_set(v___f_521_, 1, v_recur_520_);
lean_closure_set(v___f_521_, 2, v___y_512_);
lean_closure_set(v___f_521_, 3, v_acc_518_);
lean_closure_set(v___f_521_, 4, v_toBind_513_);
if (lean_obj_tag(v_it_517_) == 0)
{
lean_object* v_currPos_522_; lean_object* v_searcher_523_; lean_object* v___x_525_; uint8_t v_isShared_526_; uint8_t v_isSharedCheck_570_; 
v_currPos_522_ = lean_ctor_get(v_it_517_, 0);
v_searcher_523_ = lean_ctor_get(v_it_517_, 1);
v_isSharedCheck_570_ = !lean_is_exclusive(v_it_517_);
if (v_isSharedCheck_570_ == 0)
{
v___x_525_ = v_it_517_;
v_isShared_526_ = v_isSharedCheck_570_;
goto v_resetjp_524_;
}
else
{
lean_inc(v_searcher_523_);
lean_inc(v_currPos_522_);
lean_dec(v_it_517_);
v___x_525_ = lean_box(0);
v_isShared_526_ = v_isSharedCheck_570_;
goto v_resetjp_524_;
}
v_resetjp_524_:
{
lean_object* v___x_527_; 
lean_inc_ref(v_s_515_);
v___x_527_ = lean_apply_2(v_inst_514_, v_s_515_, v_searcher_523_);
switch(lean_obj_tag(v___x_527_))
{
case 0:
{
lean_object* v_out_528_; 
v_out_528_ = lean_ctor_get(v___x_527_, 1);
lean_inc(v_out_528_);
if (lean_obj_tag(v_out_528_) == 0)
{
lean_object* v_it_529_; lean_object* v___x_531_; 
lean_dec_ref(v_out_528_);
lean_dec_ref(v_s_515_);
v_it_529_ = lean_ctor_get(v___x_527_, 0);
lean_inc(v_it_529_);
lean_dec_ref(v___x_527_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_it_529_);
v___x_531_ = v___x_525_;
goto v_reusejp_530_;
}
else
{
lean_object* v_reuseFailAlloc_534_; 
v_reuseFailAlloc_534_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_534_, 0, v_currPos_522_);
lean_ctor_set(v_reuseFailAlloc_534_, 1, v_it_529_);
v___x_531_ = v_reuseFailAlloc_534_;
goto v_reusejp_530_;
}
v_reusejp_530_:
{
lean_object* v___x_532_; lean_object* v___x_533_; 
v___x_532_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_532_, 0, v___x_531_);
v___x_533_ = lean_apply_4(v_lift_516_, lean_box(0), lean_box(0), v___f_521_, v___x_532_);
return v___x_533_;
}
}
else
{
lean_object* v_it_535_; lean_object* v___x_537_; uint8_t v_isShared_538_; uint8_t v_isSharedCheck_549_; 
v_it_535_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_549_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_549_ == 0)
{
lean_object* v_unused_550_; 
v_unused_550_ = lean_ctor_get(v___x_527_, 1);
lean_dec(v_unused_550_);
v___x_537_ = v___x_527_;
v_isShared_538_ = v_isSharedCheck_549_;
goto v_resetjp_536_;
}
else
{
lean_inc(v_it_535_);
lean_dec(v___x_527_);
v___x_537_ = lean_box(0);
v_isShared_538_ = v_isSharedCheck_549_;
goto v_resetjp_536_;
}
v_resetjp_536_:
{
lean_object* v_startPos_539_; lean_object* v_endPos_540_; lean_object* v_slice_541_; lean_object* v_nextIt_543_; 
v_startPos_539_ = lean_ctor_get(v_out_528_, 0);
lean_inc(v_startPos_539_);
v_endPos_540_ = lean_ctor_get(v_out_528_, 1);
lean_inc(v_endPos_540_);
lean_dec_ref(v_out_528_);
v_slice_541_ = l_String_Slice_subslice_x21(v_s_515_, v_currPos_522_, v_startPos_539_);
lean_dec_ref(v_s_515_);
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_it_535_);
lean_ctor_set(v___x_525_, 0, v_endPos_540_);
v_nextIt_543_ = v___x_525_;
goto v_reusejp_542_;
}
else
{
lean_object* v_reuseFailAlloc_548_; 
v_reuseFailAlloc_548_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_548_, 0, v_endPos_540_);
lean_ctor_set(v_reuseFailAlloc_548_, 1, v_it_535_);
v_nextIt_543_ = v_reuseFailAlloc_548_;
goto v_reusejp_542_;
}
v_reusejp_542_:
{
lean_object* v___x_545_; 
if (v_isShared_538_ == 0)
{
lean_ctor_set(v___x_537_, 1, v_slice_541_);
lean_ctor_set(v___x_537_, 0, v_nextIt_543_);
v___x_545_ = v___x_537_;
goto v_reusejp_544_;
}
else
{
lean_object* v_reuseFailAlloc_547_; 
v_reuseFailAlloc_547_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_547_, 0, v_nextIt_543_);
lean_ctor_set(v_reuseFailAlloc_547_, 1, v_slice_541_);
v___x_545_ = v_reuseFailAlloc_547_;
goto v_reusejp_544_;
}
v_reusejp_544_:
{
lean_object* v___x_546_; 
v___x_546_ = lean_apply_4(v_lift_516_, lean_box(0), lean_box(0), v___f_521_, v___x_545_);
return v___x_546_;
}
}
}
}
}
case 1:
{
lean_object* v_it_551_; lean_object* v___x_553_; uint8_t v_isShared_554_; uint8_t v_isSharedCheck_562_; 
lean_dec_ref(v_s_515_);
v_it_551_ = lean_ctor_get(v___x_527_, 0);
v_isSharedCheck_562_ = !lean_is_exclusive(v___x_527_);
if (v_isSharedCheck_562_ == 0)
{
v___x_553_ = v___x_527_;
v_isShared_554_ = v_isSharedCheck_562_;
goto v_resetjp_552_;
}
else
{
lean_inc(v_it_551_);
lean_dec(v___x_527_);
v___x_553_ = lean_box(0);
v_isShared_554_ = v_isSharedCheck_562_;
goto v_resetjp_552_;
}
v_resetjp_552_:
{
lean_object* v___x_556_; 
if (v_isShared_526_ == 0)
{
lean_ctor_set(v___x_525_, 1, v_it_551_);
v___x_556_ = v___x_525_;
goto v_reusejp_555_;
}
else
{
lean_object* v_reuseFailAlloc_561_; 
v_reuseFailAlloc_561_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_561_, 0, v_currPos_522_);
lean_ctor_set(v_reuseFailAlloc_561_, 1, v_it_551_);
v___x_556_ = v_reuseFailAlloc_561_;
goto v_reusejp_555_;
}
v_reusejp_555_:
{
lean_object* v___x_558_; 
if (v_isShared_554_ == 0)
{
lean_ctor_set(v___x_553_, 0, v___x_556_);
v___x_558_ = v___x_553_;
goto v_reusejp_557_;
}
else
{
lean_object* v_reuseFailAlloc_560_; 
v_reuseFailAlloc_560_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_560_, 0, v___x_556_);
v___x_558_ = v_reuseFailAlloc_560_;
goto v_reusejp_557_;
}
v_reusejp_557_:
{
lean_object* v___x_559_; 
v___x_559_ = lean_apply_4(v_lift_516_, lean_box(0), lean_box(0), v___f_521_, v___x_558_);
return v___x_559_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_563_; lean_object* v_endExclusive_564_; lean_object* v___x_565_; lean_object* v_slice_566_; lean_object* v___x_567_; lean_object* v___x_568_; lean_object* v___x_569_; 
lean_del_object(v___x_525_);
v_startInclusive_563_ = lean_ctor_get(v_s_515_, 1);
lean_inc(v_startInclusive_563_);
v_endExclusive_564_ = lean_ctor_get(v_s_515_, 2);
lean_inc(v_endExclusive_564_);
lean_dec_ref(v_s_515_);
v___x_565_ = lean_nat_sub(v_endExclusive_564_, v_startInclusive_563_);
lean_dec(v_startInclusive_563_);
lean_dec(v_endExclusive_564_);
v_slice_566_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_566_, 0, v_currPos_522_);
lean_ctor_set(v_slice_566_, 1, v___x_565_);
v___x_567_ = lean_box(1);
v___x_568_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_568_, 0, v___x_567_);
lean_ctor_set(v___x_568_, 1, v_slice_566_);
v___x_569_ = lean_apply_4(v_lift_516_, lean_box(0), lean_box(0), v___f_521_, v___x_568_);
return v___x_569_;
}
}
}
}
else
{
lean_object* v___x_571_; lean_object* v___x_572_; 
lean_dec_ref(v_s_515_);
lean_dec(v_inst_514_);
v___x_571_ = lean_box(2);
v___x_572_ = lean_apply_4(v_lift_516_, lean_box(0), lean_box(0), v___f_521_, v___x_571_);
return v___x_572_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3(lean_object* v_inst_573_, lean_object* v_inst_574_, lean_object* v_s_575_, lean_object* v_lift_576_, lean_object* v_00_u03b3_577_, lean_object* v_Pl_578_, lean_object* v_it_579_, lean_object* v_init_580_, lean_object* v___y_581_){
_start:
{
lean_object* v_toApplicative_582_; lean_object* v_toBind_583_; lean_object* v_toPure_584_; lean_object* v___f_585_; lean_object* v___x_586_; 
v_toApplicative_582_ = lean_ctor_get(v_inst_573_, 0);
lean_inc_ref(v_toApplicative_582_);
v_toBind_583_ = lean_ctor_get(v_inst_573_, 1);
lean_inc(v_toBind_583_);
lean_dec_ref(v_inst_573_);
v_toPure_584_ = lean_ctor_get(v_toApplicative_582_, 1);
lean_inc(v_toPure_584_);
lean_dec_ref(v_toApplicative_582_);
v___f_585_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_585_, 0, v_toPure_584_);
lean_closure_set(v___f_585_, 1, v___y_581_);
lean_closure_set(v___f_585_, 2, v_toBind_583_);
lean_closure_set(v___f_585_, 3, v_inst_574_);
lean_closure_set(v___f_585_, 4, v_s_575_);
lean_closure_set(v___f_585_, 5, v_lift_576_);
v___x_586_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_585_, v_it_579_, v_init_580_, lean_box(0));
return v___x_586_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg(lean_object* v_inst_587_, lean_object* v_s_588_, lean_object* v_inst_589_){
_start:
{
lean_object* v___f_590_; 
v___f_590_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_590_, 0, v_inst_589_);
lean_closure_set(v___f_590_, 1, v_inst_587_);
lean_closure_set(v___f_590_, 2, v_s_588_);
return v___f_590_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(lean_object* v_00_u03c1_591_, lean_object* v_00_u03c3_592_, lean_object* v_inst_593_, lean_object* v_pat_594_, lean_object* v_inst_595_, lean_object* v_n_596_, lean_object* v_s_597_, lean_object* v_inst_598_){
_start:
{
lean_object* v___f_599_; 
v___f_599_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_599_, 0, v_inst_598_);
lean_closure_set(v___f_599_, 1, v_inst_593_);
lean_closure_set(v___f_599_, 2, v_s_597_);
return v___f_599_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___boxed(lean_object* v_00_u03c1_600_, lean_object* v_00_u03c3_601_, lean_object* v_inst_602_, lean_object* v_pat_603_, lean_object* v_inst_604_, lean_object* v_n_605_, lean_object* v_s_606_, lean_object* v_inst_607_){
_start:
{
lean_object* v_res_608_; 
v_res_608_ = l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(v_00_u03c1_600_, v_00_u03c3_601_, v_inst_602_, v_pat_603_, v_inst_604_, v_n_605_, v_s_606_, v_inst_607_);
lean_dec(v_inst_604_);
lean_dec(v_pat_603_);
return v_res_608_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___redArg(lean_object* v_s_609_, lean_object* v_inst_610_){
_start:
{
lean_object* v___x_611_; lean_object* v___x_612_; lean_object* v___x_613_; 
v___x_611_ = lean_unsigned_to_nat(0u);
v___x_612_ = lean_apply_1(v_inst_610_, v_s_609_);
v___x_613_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_613_, 0, v___x_611_);
lean_ctor_set(v___x_613_, 1, v___x_612_);
return v___x_613_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice(lean_object* v_00_u03c1_614_, lean_object* v_00_u03c3_615_, lean_object* v_s_616_, lean_object* v_pat_617_, lean_object* v_inst_618_){
_start:
{
lean_object* v___x_619_; 
v___x_619_ = l_String_Slice_splitToSubslice___redArg(v_s_616_, v_inst_618_);
return v___x_619_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___boxed(lean_object* v_00_u03c1_620_, lean_object* v_00_u03c3_621_, lean_object* v_s_622_, lean_object* v_pat_623_, lean_object* v_inst_624_){
_start:
{
lean_object* v_res_625_; 
v_res_625_ = l_String_Slice_splitToSubslice(v_00_u03c1_620_, v_00_u03c3_621_, v_s_622_, v_pat_623_, v_inst_624_);
lean_dec(v_pat_623_);
return v_res_625_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___redArg(lean_object* v_s_626_, lean_object* v_inst_627_){
_start:
{
lean_object* v___x_628_; 
v___x_628_ = l_String_Slice_splitToSubslice___redArg(v_s_626_, v_inst_627_);
return v___x_628_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split(lean_object* v_00_u03c1_629_, lean_object* v_00_u03c3_630_, lean_object* v_inst_631_, lean_object* v_s_632_, lean_object* v_pat_633_, lean_object* v_inst_634_){
_start:
{
lean_object* v___x_635_; 
v___x_635_ = l_String_Slice_splitToSubslice___redArg(v_s_632_, v_inst_634_);
return v___x_635_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___boxed(lean_object* v_00_u03c1_636_, lean_object* v_00_u03c3_637_, lean_object* v_inst_638_, lean_object* v_s_639_, lean_object* v_pat_640_, lean_object* v_inst_641_){
_start:
{
lean_object* v_res_642_; 
v_res_642_ = l_String_Slice_split(v_00_u03c1_636_, v_00_u03c3_637_, v_inst_638_, v_s_639_, v_pat_640_, v_inst_641_);
lean_dec(v_pat_640_);
lean_dec(v_inst_638_);
return v_res_642_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(lean_object* v_x_643_){
_start:
{
if (lean_obj_tag(v_x_643_) == 0)
{
lean_object* v___x_644_; 
v___x_644_ = lean_unsigned_to_nat(0u);
return v___x_644_;
}
else
{
lean_object* v___x_645_; 
v___x_645_ = lean_unsigned_to_nat(1u);
return v___x_645_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg___boxed(lean_object* v_x_646_){
_start:
{
lean_object* v_res_647_; 
v_res_647_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(v_x_646_);
lean_dec(v_x_646_);
return v_res_647_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx(lean_object* v_00_u03c3_648_, lean_object* v_00_u03c1_649_, lean_object* v_pat_650_, lean_object* v_s_651_, lean_object* v_inst_652_, lean_object* v_x_653_){
_start:
{
lean_object* v___x_654_; 
v___x_654_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(v_x_653_);
return v___x_654_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___boxed(lean_object* v_00_u03c3_655_, lean_object* v_00_u03c1_656_, lean_object* v_pat_657_, lean_object* v_s_658_, lean_object* v_inst_659_, lean_object* v_x_660_){
_start:
{
lean_object* v_res_661_; 
v_res_661_ = l_String_Slice_SplitInclusiveIterator_ctorIdx(v_00_u03c3_655_, v_00_u03c1_656_, v_pat_657_, v_s_658_, v_inst_659_, v_x_660_);
lean_dec(v_x_660_);
lean_dec(v_inst_659_);
lean_dec_ref(v_s_658_);
lean_dec(v_pat_657_);
return v_res_661_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(lean_object* v_t_662_, lean_object* v_k_663_){
_start:
{
if (lean_obj_tag(v_t_662_) == 0)
{
lean_object* v_currPos_664_; lean_object* v_searcher_665_; lean_object* v___x_666_; 
v_currPos_664_ = lean_ctor_get(v_t_662_, 0);
lean_inc(v_currPos_664_);
v_searcher_665_ = lean_ctor_get(v_t_662_, 1);
lean_inc(v_searcher_665_);
lean_dec_ref(v_t_662_);
v___x_666_ = lean_apply_2(v_k_663_, v_currPos_664_, v_searcher_665_);
return v___x_666_;
}
else
{
return v_k_663_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim(lean_object* v_00_u03c3_667_, lean_object* v_00_u03c1_668_, lean_object* v_pat_669_, lean_object* v_s_670_, lean_object* v_inst_671_, lean_object* v_motive_672_, lean_object* v_ctorIdx_673_, lean_object* v_t_674_, lean_object* v_h_675_, lean_object* v_k_676_){
_start:
{
lean_object* v___x_677_; 
v___x_677_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_674_, v_k_676_);
return v___x_677_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___boxed(lean_object* v_00_u03c3_678_, lean_object* v_00_u03c1_679_, lean_object* v_pat_680_, lean_object* v_s_681_, lean_object* v_inst_682_, lean_object* v_motive_683_, lean_object* v_ctorIdx_684_, lean_object* v_t_685_, lean_object* v_h_686_, lean_object* v_k_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_String_Slice_SplitInclusiveIterator_ctorElim(v_00_u03c3_678_, v_00_u03c1_679_, v_pat_680_, v_s_681_, v_inst_682_, v_motive_683_, v_ctorIdx_684_, v_t_685_, v_h_686_, v_k_687_);
lean_dec(v_ctorIdx_684_);
lean_dec(v_inst_682_);
lean_dec_ref(v_s_681_);
lean_dec(v_pat_680_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___redArg(lean_object* v_t_689_, lean_object* v_operating_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_689_, v_operating_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim(lean_object* v_00_u03c3_692_, lean_object* v_00_u03c1_693_, lean_object* v_pat_694_, lean_object* v_s_695_, lean_object* v_inst_696_, lean_object* v_motive_697_, lean_object* v_t_698_, lean_object* v_h_699_, lean_object* v_operating_700_){
_start:
{
lean_object* v___x_701_; 
v___x_701_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_698_, v_operating_700_);
return v___x_701_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___boxed(lean_object* v_00_u03c3_702_, lean_object* v_00_u03c1_703_, lean_object* v_pat_704_, lean_object* v_s_705_, lean_object* v_inst_706_, lean_object* v_motive_707_, lean_object* v_t_708_, lean_object* v_h_709_, lean_object* v_operating_710_){
_start:
{
lean_object* v_res_711_; 
v_res_711_ = l_String_Slice_SplitInclusiveIterator_operating_elim(v_00_u03c3_702_, v_00_u03c1_703_, v_pat_704_, v_s_705_, v_inst_706_, v_motive_707_, v_t_708_, v_h_709_, v_operating_710_);
lean_dec(v_inst_706_);
lean_dec_ref(v_s_705_);
lean_dec(v_pat_704_);
return v_res_711_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___redArg(lean_object* v_t_712_, lean_object* v_atEnd_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_712_, v_atEnd_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim(lean_object* v_00_u03c3_715_, lean_object* v_00_u03c1_716_, lean_object* v_pat_717_, lean_object* v_s_718_, lean_object* v_inst_719_, lean_object* v_motive_720_, lean_object* v_t_721_, lean_object* v_h_722_, lean_object* v_atEnd_723_){
_start:
{
lean_object* v___x_724_; 
v___x_724_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_721_, v_atEnd_723_);
return v___x_724_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_725_, lean_object* v_00_u03c1_726_, lean_object* v_pat_727_, lean_object* v_s_728_, lean_object* v_inst_729_, lean_object* v_motive_730_, lean_object* v_t_731_, lean_object* v_h_732_, lean_object* v_atEnd_733_){
_start:
{
lean_object* v_res_734_; 
v_res_734_ = l_String_Slice_SplitInclusiveIterator_atEnd_elim(v_00_u03c3_725_, v_00_u03c1_726_, v_pat_727_, v_s_728_, v_inst_729_, v_motive_730_, v_t_731_, v_h_732_, v_atEnd_733_);
lean_dec(v_inst_729_);
lean_dec_ref(v_s_728_);
lean_dec(v_pat_727_);
return v_res_734_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default(lean_object* v_a_735_, lean_object* v_a_736_, lean_object* v_a_737_, lean_object* v_a_738_, lean_object* v_a_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = lean_box(1);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___boxed(lean_object* v_a_741_, lean_object* v_a_742_, lean_object* v_a_743_, lean_object* v_a_744_, lean_object* v_a_745_){
_start:
{
lean_object* v_res_746_; 
v_res_746_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default(v_a_741_, v_a_742_, v_a_743_, v_a_744_, v_a_745_);
lean_dec(v_a_745_);
lean_dec_ref(v_a_744_);
lean_dec(v_a_743_);
return v_res_746_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator(lean_object* v_a_747_, lean_object* v_a_748_, lean_object* v_a_749_, lean_object* v_a_750_, lean_object* v_a_751_){
_start:
{
lean_object* v___x_752_; 
v___x_752_ = lean_box(1);
return v___x_752_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___boxed(lean_object* v_a_753_, lean_object* v_a_754_, lean_object* v_a_755_, lean_object* v_a_756_, lean_object* v_a_757_){
_start:
{
lean_object* v_res_758_; 
v_res_758_ = l_String_Slice_instInhabitedSplitInclusiveIterator(v_a_753_, v_a_754_, v_a_755_, v_a_756_, v_a_757_);
lean_dec(v_a_757_);
lean_dec_ref(v_a_756_);
lean_dec(v_a_755_);
return v_res_758_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0(lean_object* v_inst_759_, lean_object* v_s_760_, lean_object* v_x_761_){
_start:
{
if (lean_obj_tag(v_x_761_) == 0)
{
lean_object* v_currPos_762_; lean_object* v_searcher_763_; lean_object* v___x_765_; uint8_t v_isShared_766_; uint8_t v_isSharedCheck_815_; 
v_currPos_762_ = lean_ctor_get(v_x_761_, 0);
v_searcher_763_ = lean_ctor_get(v_x_761_, 1);
v_isSharedCheck_815_ = !lean_is_exclusive(v_x_761_);
if (v_isSharedCheck_815_ == 0)
{
v___x_765_ = v_x_761_;
v_isShared_766_ = v_isSharedCheck_815_;
goto v_resetjp_764_;
}
else
{
lean_inc(v_searcher_763_);
lean_inc(v_currPos_762_);
lean_dec(v_x_761_);
v___x_765_ = lean_box(0);
v_isShared_766_ = v_isSharedCheck_815_;
goto v_resetjp_764_;
}
v_resetjp_764_:
{
lean_object* v___x_767_; 
lean_inc_ref(v_s_760_);
v___x_767_ = lean_apply_2(v_inst_759_, v_s_760_, v_searcher_763_);
switch(lean_obj_tag(v___x_767_))
{
case 0:
{
lean_object* v_out_768_; 
v_out_768_ = lean_ctor_get(v___x_767_, 1);
lean_inc(v_out_768_);
if (lean_obj_tag(v_out_768_) == 0)
{
lean_object* v_it_769_; lean_object* v___x_771_; 
lean_dec_ref(v_out_768_);
lean_dec_ref(v_s_760_);
v_it_769_ = lean_ctor_get(v___x_767_, 0);
lean_inc(v_it_769_);
lean_dec_ref(v___x_767_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_it_769_);
v___x_771_ = v___x_765_;
goto v_reusejp_770_;
}
else
{
lean_object* v_reuseFailAlloc_773_; 
v_reuseFailAlloc_773_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_773_, 0, v_currPos_762_);
lean_ctor_set(v_reuseFailAlloc_773_, 1, v_it_769_);
v___x_771_ = v_reuseFailAlloc_773_;
goto v_reusejp_770_;
}
v_reusejp_770_:
{
lean_object* v___x_772_; 
v___x_772_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_772_, 0, v___x_771_);
return v___x_772_;
}
}
else
{
lean_object* v_it_774_; lean_object* v___x_776_; uint8_t v_isShared_777_; uint8_t v_isSharedCheck_786_; 
v_it_774_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_786_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_786_ == 0)
{
lean_object* v_unused_787_; 
v_unused_787_ = lean_ctor_get(v___x_767_, 1);
lean_dec(v_unused_787_);
v___x_776_ = v___x_767_;
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
else
{
lean_inc(v_it_774_);
lean_dec(v___x_767_);
v___x_776_ = lean_box(0);
v_isShared_777_ = v_isSharedCheck_786_;
goto v_resetjp_775_;
}
v_resetjp_775_:
{
lean_object* v_endPos_778_; lean_object* v_slice_779_; lean_object* v_nextIt_781_; 
v_endPos_778_ = lean_ctor_get(v_out_768_, 1);
lean_inc(v_endPos_778_);
lean_dec_ref(v_out_768_);
v_slice_779_ = l_String_Slice_slice_x21(v_s_760_, v_currPos_762_, v_endPos_778_);
lean_dec(v_currPos_762_);
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_it_774_);
lean_ctor_set(v___x_765_, 0, v_endPos_778_);
v_nextIt_781_ = v___x_765_;
goto v_reusejp_780_;
}
else
{
lean_object* v_reuseFailAlloc_785_; 
v_reuseFailAlloc_785_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_785_, 0, v_endPos_778_);
lean_ctor_set(v_reuseFailAlloc_785_, 1, v_it_774_);
v_nextIt_781_ = v_reuseFailAlloc_785_;
goto v_reusejp_780_;
}
v_reusejp_780_:
{
lean_object* v___x_783_; 
if (v_isShared_777_ == 0)
{
lean_ctor_set(v___x_776_, 1, v_slice_779_);
lean_ctor_set(v___x_776_, 0, v_nextIt_781_);
v___x_783_ = v___x_776_;
goto v_reusejp_782_;
}
else
{
lean_object* v_reuseFailAlloc_784_; 
v_reuseFailAlloc_784_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_784_, 0, v_nextIt_781_);
lean_ctor_set(v_reuseFailAlloc_784_, 1, v_slice_779_);
v___x_783_ = v_reuseFailAlloc_784_;
goto v_reusejp_782_;
}
v_reusejp_782_:
{
return v___x_783_;
}
}
}
}
}
case 1:
{
lean_object* v_it_788_; lean_object* v___x_790_; uint8_t v_isShared_791_; uint8_t v_isSharedCheck_798_; 
lean_dec_ref(v_s_760_);
v_it_788_ = lean_ctor_get(v___x_767_, 0);
v_isSharedCheck_798_ = !lean_is_exclusive(v___x_767_);
if (v_isSharedCheck_798_ == 0)
{
v___x_790_ = v___x_767_;
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
else
{
lean_inc(v_it_788_);
lean_dec(v___x_767_);
v___x_790_ = lean_box(0);
v_isShared_791_ = v_isSharedCheck_798_;
goto v_resetjp_789_;
}
v_resetjp_789_:
{
lean_object* v___x_793_; 
if (v_isShared_766_ == 0)
{
lean_ctor_set(v___x_765_, 1, v_it_788_);
v___x_793_ = v___x_765_;
goto v_reusejp_792_;
}
else
{
lean_object* v_reuseFailAlloc_797_; 
v_reuseFailAlloc_797_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_797_, 0, v_currPos_762_);
lean_ctor_set(v_reuseFailAlloc_797_, 1, v_it_788_);
v___x_793_ = v_reuseFailAlloc_797_;
goto v_reusejp_792_;
}
v_reusejp_792_:
{
lean_object* v___x_795_; 
if (v_isShared_791_ == 0)
{
lean_ctor_set(v___x_790_, 0, v___x_793_);
v___x_795_ = v___x_790_;
goto v_reusejp_794_;
}
else
{
lean_object* v_reuseFailAlloc_796_; 
v_reuseFailAlloc_796_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_796_, 0, v___x_793_);
v___x_795_ = v_reuseFailAlloc_796_;
goto v_reusejp_794_;
}
v_reusejp_794_:
{
return v___x_795_;
}
}
}
}
default: 
{
lean_object* v_str_799_; lean_object* v_startInclusive_800_; lean_object* v_endExclusive_801_; lean_object* v___x_803_; uint8_t v_isShared_804_; uint8_t v_isSharedCheck_814_; 
lean_del_object(v___x_765_);
v_str_799_ = lean_ctor_get(v_s_760_, 0);
v_startInclusive_800_ = lean_ctor_get(v_s_760_, 1);
v_endExclusive_801_ = lean_ctor_get(v_s_760_, 2);
v_isSharedCheck_814_ = !lean_is_exclusive(v_s_760_);
if (v_isSharedCheck_814_ == 0)
{
v___x_803_ = v_s_760_;
v_isShared_804_ = v_isSharedCheck_814_;
goto v_resetjp_802_;
}
else
{
lean_inc(v_endExclusive_801_);
lean_inc(v_startInclusive_800_);
lean_inc(v_str_799_);
lean_dec(v_s_760_);
v___x_803_ = lean_box(0);
v_isShared_804_ = v_isSharedCheck_814_;
goto v_resetjp_802_;
}
v_resetjp_802_:
{
lean_object* v___x_805_; uint8_t v___x_806_; 
v___x_805_ = lean_nat_sub(v_endExclusive_801_, v_startInclusive_800_);
v___x_806_ = lean_nat_dec_eq(v_currPos_762_, v___x_805_);
lean_dec(v___x_805_);
if (v___x_806_ == 0)
{
lean_object* v___x_807_; lean_object* v_slice_809_; 
v___x_807_ = lean_nat_add(v_startInclusive_800_, v_currPos_762_);
lean_dec(v_currPos_762_);
lean_dec(v_startInclusive_800_);
if (v_isShared_804_ == 0)
{
lean_ctor_set(v___x_803_, 1, v___x_807_);
v_slice_809_ = v___x_803_;
goto v_reusejp_808_;
}
else
{
lean_object* v_reuseFailAlloc_812_; 
v_reuseFailAlloc_812_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_812_, 0, v_str_799_);
lean_ctor_set(v_reuseFailAlloc_812_, 1, v___x_807_);
lean_ctor_set(v_reuseFailAlloc_812_, 2, v_endExclusive_801_);
v_slice_809_ = v_reuseFailAlloc_812_;
goto v_reusejp_808_;
}
v_reusejp_808_:
{
lean_object* v___x_810_; lean_object* v___x_811_; 
v___x_810_ = lean_box(1);
v___x_811_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_811_, 0, v___x_810_);
lean_ctor_set(v___x_811_, 1, v_slice_809_);
return v___x_811_;
}
}
else
{
lean_object* v___x_813_; 
lean_del_object(v___x_803_);
lean_dec(v_endExclusive_801_);
lean_dec(v_startInclusive_800_);
lean_dec_ref(v_str_799_);
lean_dec(v_currPos_762_);
v___x_813_ = lean_box(2);
return v___x_813_;
}
}
}
}
}
}
else
{
lean_object* v___x_816_; 
lean_dec_ref(v_s_760_);
lean_dec(v_inst_759_);
v___x_816_ = lean_box(2);
return v___x_816_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg(lean_object* v_inst_817_, lean_object* v_s_818_){
_start:
{
lean_object* v___f_819_; 
v___f_819_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_819_, 0, v_inst_817_);
lean_closure_set(v___f_819_, 1, v_s_818_);
return v___f_819_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId(lean_object* v_00_u03c1_820_, lean_object* v_00_u03c3_821_, lean_object* v_inst_822_, lean_object* v_pat_823_, lean_object* v_inst_824_, lean_object* v_s_825_){
_start:
{
lean_object* v___f_826_; 
v___f_826_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_826_, 0, v_inst_822_);
lean_closure_set(v___f_826_, 1, v_s_825_);
return v___f_826_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___boxed(lean_object* v_00_u03c1_827_, lean_object* v_00_u03c3_828_, lean_object* v_inst_829_, lean_object* v_pat_830_, lean_object* v_inst_831_, lean_object* v_s_832_){
_start:
{
lean_object* v_res_833_; 
v_res_833_ = l_String_Slice_SplitInclusiveIterator_instIteratorId(v_00_u03c1_827_, v_00_u03c3_828_, v_inst_829_, v_pat_830_, v_inst_831_, v_s_832_);
lean_dec(v_inst_831_);
lean_dec(v_pat_830_);
return v_res_833_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(lean_object* v_x_834_){
_start:
{
if (lean_obj_tag(v_x_834_) == 0)
{
lean_object* v_searcher_835_; lean_object* v___x_836_; 
v_searcher_835_ = lean_ctor_get(v_x_834_, 1);
lean_inc(v_searcher_835_);
v___x_836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_836_, 0, v_searcher_835_);
return v___x_836_;
}
else
{
lean_object* v___x_837_; 
v___x_837_ = lean_box(0);
return v___x_837_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg___boxed(lean_object* v_x_838_){
_start:
{
lean_object* v_res_839_; 
v_res_839_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_838_);
lean_dec(v_x_838_);
return v_res_839_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(lean_object* v_00_u03c1_840_, lean_object* v_00_u03c3_841_, lean_object* v_pat_842_, lean_object* v_inst_843_, lean_object* v_s_844_, lean_object* v_x_845_){
_start:
{
lean_object* v___x_846_; 
v___x_846_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_845_);
return v___x_846_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___boxed(lean_object* v_00_u03c1_847_, lean_object* v_00_u03c3_848_, lean_object* v_pat_849_, lean_object* v_inst_850_, lean_object* v_s_851_, lean_object* v_x_852_){
_start:
{
lean_object* v_res_853_; 
v_res_853_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(v_00_u03c1_847_, v_00_u03c3_848_, v_pat_849_, v_inst_850_, v_s_851_, v_x_852_);
lean_dec(v_x_852_);
lean_dec_ref(v_s_851_);
lean_dec(v_inst_850_);
lean_dec(v_pat_849_);
return v_res_853_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___redArg(lean_object* v_x_854_, lean_object* v_h__1_855_, lean_object* v_h__2_856_){
_start:
{
if (lean_obj_tag(v_x_854_) == 0)
{
lean_object* v_currPos_857_; lean_object* v_searcher_858_; lean_object* v___x_859_; 
lean_dec(v_h__2_856_);
v_currPos_857_ = lean_ctor_get(v_x_854_, 0);
lean_inc(v_currPos_857_);
v_searcher_858_ = lean_ctor_get(v_x_854_, 1);
lean_inc(v_searcher_858_);
lean_dec_ref(v_x_854_);
v___x_859_ = lean_apply_2(v_h__1_855_, v_currPos_857_, v_searcher_858_);
return v___x_859_;
}
else
{
lean_object* v___x_860_; lean_object* v___x_861_; 
lean_dec(v_h__1_855_);
v___x_860_ = lean_box(0);
v___x_861_ = lean_apply_1(v_h__2_856_, v___x_860_);
return v___x_861_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(lean_object* v_00_u03c1_862_, lean_object* v_00_u03c3_863_, lean_object* v_pat_864_, lean_object* v_inst_865_, lean_object* v_s_866_, lean_object* v_motive_867_, lean_object* v_x_868_, lean_object* v_h__1_869_, lean_object* v_h__2_870_){
_start:
{
lean_object* v___x_871_; 
v___x_871_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___redArg(v_x_868_, v_h__1_869_, v_h__2_870_);
return v___x_871_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___boxed(lean_object* v_00_u03c1_872_, lean_object* v_00_u03c3_873_, lean_object* v_pat_874_, lean_object* v_inst_875_, lean_object* v_s_876_, lean_object* v_motive_877_, lean_object* v_x_878_, lean_object* v_h__1_879_, lean_object* v_h__2_880_){
_start:
{
lean_object* v_res_881_; 
v_res_881_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(v_00_u03c1_872_, v_00_u03c3_873_, v_pat_874_, v_inst_875_, v_s_876_, v_motive_877_, v_x_878_, v_h__1_879_, v_h__2_880_);
lean_dec_ref(v_s_876_);
lean_dec(v_inst_875_);
lean_dec(v_pat_874_);
return v_res_881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___redArg(lean_object* v_x_882_, lean_object* v_x_883_, lean_object* v_h__1_884_, lean_object* v_h__2_885_, lean_object* v_h__3_886_, lean_object* v_h__4_887_, lean_object* v_h__5_888_, lean_object* v_h__6_889_, lean_object* v_h__7_890_, lean_object* v_h__8_891_){
_start:
{
if (lean_obj_tag(v_x_882_) == 0)
{
lean_dec(v_h__8_891_);
lean_dec(v_h__7_890_);
lean_dec(v_h__6_889_);
switch(lean_obj_tag(v_x_883_))
{
case 0:
{
lean_object* v_it_892_; 
lean_dec(v_h__5_888_);
lean_dec(v_h__4_887_);
lean_dec(v_h__3_886_);
v_it_892_ = lean_ctor_get(v_x_883_, 0);
if (lean_obj_tag(v_it_892_) == 0)
{
lean_object* v_currPos_893_; lean_object* v_searcher_894_; lean_object* v_out_895_; lean_object* v_currPos_896_; lean_object* v_searcher_897_; lean_object* v___x_898_; 
lean_inc_ref(v_it_892_);
lean_dec(v_h__2_885_);
v_currPos_893_ = lean_ctor_get(v_x_882_, 0);
lean_inc(v_currPos_893_);
v_searcher_894_ = lean_ctor_get(v_x_882_, 1);
lean_inc(v_searcher_894_);
lean_dec_ref(v_x_882_);
v_out_895_ = lean_ctor_get(v_x_883_, 1);
lean_inc(v_out_895_);
lean_dec_ref(v_x_883_);
v_currPos_896_ = lean_ctor_get(v_it_892_, 0);
lean_inc(v_currPos_896_);
v_searcher_897_ = lean_ctor_get(v_it_892_, 1);
lean_inc(v_searcher_897_);
lean_dec_ref(v_it_892_);
v___x_898_ = lean_apply_5(v_h__1_884_, v_currPos_893_, v_searcher_894_, v_currPos_896_, v_searcher_897_, v_out_895_);
return v___x_898_;
}
else
{
lean_object* v_currPos_899_; lean_object* v_searcher_900_; lean_object* v_out_901_; lean_object* v___x_902_; 
lean_dec(v_h__1_884_);
v_currPos_899_ = lean_ctor_get(v_x_882_, 0);
lean_inc(v_currPos_899_);
v_searcher_900_ = lean_ctor_get(v_x_882_, 1);
lean_inc(v_searcher_900_);
lean_dec_ref(v_x_882_);
v_out_901_ = lean_ctor_get(v_x_883_, 1);
lean_inc(v_out_901_);
lean_dec_ref(v_x_883_);
v___x_902_ = lean_apply_3(v_h__2_885_, v_currPos_899_, v_searcher_900_, v_out_901_);
return v___x_902_;
}
}
case 1:
{
lean_object* v_it_903_; 
lean_dec(v_h__5_888_);
lean_dec(v_h__2_885_);
lean_dec(v_h__1_884_);
v_it_903_ = lean_ctor_get(v_x_883_, 0);
lean_inc(v_it_903_);
lean_dec_ref(v_x_883_);
if (lean_obj_tag(v_it_903_) == 0)
{
lean_object* v_currPos_904_; lean_object* v_searcher_905_; lean_object* v_currPos_906_; lean_object* v_searcher_907_; lean_object* v___x_908_; 
lean_dec(v_h__4_887_);
v_currPos_904_ = lean_ctor_get(v_x_882_, 0);
lean_inc(v_currPos_904_);
v_searcher_905_ = lean_ctor_get(v_x_882_, 1);
lean_inc(v_searcher_905_);
lean_dec_ref(v_x_882_);
v_currPos_906_ = lean_ctor_get(v_it_903_, 0);
lean_inc(v_currPos_906_);
v_searcher_907_ = lean_ctor_get(v_it_903_, 1);
lean_inc(v_searcher_907_);
lean_dec_ref(v_it_903_);
v___x_908_ = lean_apply_4(v_h__3_886_, v_currPos_904_, v_searcher_905_, v_currPos_906_, v_searcher_907_);
return v___x_908_;
}
else
{
lean_object* v_currPos_909_; lean_object* v_searcher_910_; lean_object* v___x_911_; 
lean_dec(v_h__3_886_);
v_currPos_909_ = lean_ctor_get(v_x_882_, 0);
lean_inc(v_currPos_909_);
v_searcher_910_ = lean_ctor_get(v_x_882_, 1);
lean_inc(v_searcher_910_);
lean_dec_ref(v_x_882_);
v___x_911_ = lean_apply_2(v_h__4_887_, v_currPos_909_, v_searcher_910_);
return v___x_911_;
}
}
default: 
{
lean_object* v_currPos_912_; lean_object* v_searcher_913_; lean_object* v___x_914_; 
lean_dec(v_h__4_887_);
lean_dec(v_h__3_886_);
lean_dec(v_h__2_885_);
lean_dec(v_h__1_884_);
v_currPos_912_ = lean_ctor_get(v_x_882_, 0);
lean_inc(v_currPos_912_);
v_searcher_913_ = lean_ctor_get(v_x_882_, 1);
lean_inc(v_searcher_913_);
lean_dec_ref(v_x_882_);
v___x_914_ = lean_apply_2(v_h__5_888_, v_currPos_912_, v_searcher_913_);
return v___x_914_;
}
}
}
else
{
lean_dec(v_h__5_888_);
lean_dec(v_h__4_887_);
lean_dec(v_h__3_886_);
lean_dec(v_h__2_885_);
lean_dec(v_h__1_884_);
switch(lean_obj_tag(v_x_883_))
{
case 0:
{
lean_object* v_it_915_; lean_object* v_out_916_; lean_object* v___x_917_; 
lean_dec(v_h__8_891_);
lean_dec(v_h__7_890_);
v_it_915_ = lean_ctor_get(v_x_883_, 0);
lean_inc(v_it_915_);
v_out_916_ = lean_ctor_get(v_x_883_, 1);
lean_inc(v_out_916_);
lean_dec_ref(v_x_883_);
v___x_917_ = lean_apply_2(v_h__6_889_, v_it_915_, v_out_916_);
return v___x_917_;
}
case 1:
{
lean_object* v_it_918_; lean_object* v___x_919_; 
lean_dec(v_h__8_891_);
lean_dec(v_h__6_889_);
v_it_918_ = lean_ctor_get(v_x_883_, 0);
lean_inc(v_it_918_);
lean_dec_ref(v_x_883_);
v___x_919_ = lean_apply_1(v_h__7_890_, v_it_918_);
return v___x_919_;
}
default: 
{
lean_object* v___x_920_; lean_object* v___x_921_; 
lean_dec(v_h__7_890_);
lean_dec(v_h__6_889_);
v___x_920_ = lean_box(0);
v___x_921_ = lean_apply_1(v_h__8_891_, v___x_920_);
return v___x_921_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(lean_object* v_00_u03c1_922_, lean_object* v_00_u03c3_923_, lean_object* v_pat_924_, lean_object* v_inst_925_, lean_object* v_s_926_, lean_object* v_motive_927_, lean_object* v_x_928_, lean_object* v_x_929_, lean_object* v_h__1_930_, lean_object* v_h__2_931_, lean_object* v_h__3_932_, lean_object* v_h__4_933_, lean_object* v_h__5_934_, lean_object* v_h__6_935_, lean_object* v_h__7_936_, lean_object* v_h__8_937_){
_start:
{
lean_object* v___x_938_; 
v___x_938_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___redArg(v_x_928_, v_x_929_, v_h__1_930_, v_h__2_931_, v_h__3_932_, v_h__4_933_, v_h__5_934_, v_h__6_935_, v_h__7_936_, v_h__8_937_);
return v___x_938_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___boxed(lean_object* v_00_u03c1_939_, lean_object* v_00_u03c3_940_, lean_object* v_pat_941_, lean_object* v_inst_942_, lean_object* v_s_943_, lean_object* v_motive_944_, lean_object* v_x_945_, lean_object* v_x_946_, lean_object* v_h__1_947_, lean_object* v_h__2_948_, lean_object* v_h__3_949_, lean_object* v_h__4_950_, lean_object* v_h__5_951_, lean_object* v_h__6_952_, lean_object* v_h__7_953_, lean_object* v_h__8_954_){
_start:
{
lean_object* v_res_955_; 
v_res_955_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(v_00_u03c1_939_, v_00_u03c3_940_, v_pat_941_, v_inst_942_, v_s_943_, v_motive_944_, v_x_945_, v_x_946_, v_h__1_947_, v_h__2_948_, v_h__3_949_, v_h__4_950_, v_h__5_951_, v_h__6_952_, v_h__7_953_, v_h__8_954_);
lean_dec_ref(v_s_943_);
lean_dec(v_inst_942_);
lean_dec(v_pat_941_);
return v_res_955_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___redArg(lean_object* v_x_956_, lean_object* v_h__1_957_, lean_object* v_h__2_958_){
_start:
{
if (lean_obj_tag(v_x_956_) == 0)
{
lean_object* v_currPos_959_; lean_object* v_searcher_960_; lean_object* v___x_961_; 
lean_dec(v_h__2_958_);
v_currPos_959_ = lean_ctor_get(v_x_956_, 0);
lean_inc(v_currPos_959_);
v_searcher_960_ = lean_ctor_get(v_x_956_, 1);
lean_inc(v_searcher_960_);
lean_dec_ref(v_x_956_);
v___x_961_ = lean_apply_2(v_h__1_957_, v_currPos_959_, v_searcher_960_);
return v___x_961_;
}
else
{
lean_object* v___x_962_; lean_object* v___x_963_; 
lean_dec(v_h__1_957_);
v___x_962_ = lean_box(0);
v___x_963_ = lean_apply_1(v_h__2_958_, v___x_962_);
return v___x_963_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_964_, lean_object* v_00_u03c3_965_, lean_object* v_pat_966_, lean_object* v_inst_967_, lean_object* v_s_968_, lean_object* v_motive_969_, lean_object* v_x_970_, lean_object* v_h__1_971_, lean_object* v_h__2_972_){
_start:
{
lean_object* v___x_973_; 
v___x_973_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___redArg(v_x_970_, v_h__1_971_, v_h__2_972_);
return v___x_973_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_974_, lean_object* v_00_u03c3_975_, lean_object* v_pat_976_, lean_object* v_inst_977_, lean_object* v_s_978_, lean_object* v_motive_979_, lean_object* v_x_980_, lean_object* v_h__1_981_, lean_object* v_h__2_982_){
_start:
{
lean_object* v_res_983_; 
v_res_983_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(v_00_u03c1_974_, v_00_u03c3_975_, v_pat_976_, v_inst_977_, v_s_978_, v_motive_979_, v_x_980_, v_h__1_981_, v_h__2_982_);
lean_dec_ref(v_s_978_);
lean_dec(v_inst_977_);
lean_dec(v_pat_976_);
return v_res_983_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(lean_object* v_00_u03c1_984_, lean_object* v_00_u03c3_985_, lean_object* v_inst_986_, lean_object* v_pat_987_, lean_object* v_inst_988_, lean_object* v_s_989_, lean_object* v_inst_990_){
_start:
{
lean_object* v___x_991_; 
v___x_991_ = lean_box(0);
return v___x_991_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_992_, lean_object* v_00_u03c3_993_, lean_object* v_inst_994_, lean_object* v_pat_995_, lean_object* v_inst_996_, lean_object* v_s_997_, lean_object* v_inst_998_){
_start:
{
lean_object* v_res_999_; 
v_res_999_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(v_00_u03c1_992_, v_00_u03c3_993_, v_inst_994_, v_pat_995_, v_inst_996_, v_s_997_, v_inst_998_);
lean_dec_ref(v_s_997_);
lean_dec(v_inst_996_);
lean_dec(v_pat_995_);
lean_dec(v_inst_994_);
return v_res_999_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0(lean_object* v_toPure_1000_, lean_object* v_recur_1001_, lean_object* v_it_1002_, lean_object* v_____do__lift_1003_){
_start:
{
if (lean_obj_tag(v_____do__lift_1003_) == 0)
{
lean_object* v_a_1004_; lean_object* v___x_1005_; 
lean_dec(v_it_1002_);
lean_dec(v_recur_1001_);
v_a_1004_ = lean_ctor_get(v_____do__lift_1003_, 0);
lean_inc(v_a_1004_);
lean_dec_ref(v_____do__lift_1003_);
v___x_1005_ = lean_apply_2(v_toPure_1000_, lean_box(0), v_a_1004_);
return v___x_1005_;
}
else
{
lean_object* v_a_1006_; lean_object* v___x_1007_; 
lean_dec(v_toPure_1000_);
v_a_1006_ = lean_ctor_get(v_____do__lift_1003_, 0);
lean_inc(v_a_1006_);
lean_dec_ref(v_____do__lift_1003_);
v___x_1007_ = lean_apply_4(v_recur_1001_, v_it_1002_, v_a_1006_, lean_box(0), lean_box(0));
return v___x_1007_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1(lean_object* v_toPure_1008_, lean_object* v_recur_1009_, lean_object* v___y_1010_, lean_object* v_acc_1011_, lean_object* v_toBind_1012_, lean_object* v_s_1013_){
_start:
{
switch(lean_obj_tag(v_s_1013_))
{
case 0:
{
lean_object* v_it_1014_; lean_object* v_out_1015_; lean_object* v___f_1016_; lean_object* v___x_1017_; lean_object* v___x_1018_; 
v_it_1014_ = lean_ctor_get(v_s_1013_, 0);
lean_inc(v_it_1014_);
v_out_1015_ = lean_ctor_get(v_s_1013_, 1);
lean_inc(v_out_1015_);
lean_dec_ref(v_s_1013_);
v___f_1016_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1016_, 0, v_toPure_1008_);
lean_closure_set(v___f_1016_, 1, v_recur_1009_);
lean_closure_set(v___f_1016_, 2, v_it_1014_);
v___x_1017_ = lean_apply_3(v___y_1010_, v_out_1015_, lean_box(0), v_acc_1011_);
v___x_1018_ = lean_apply_4(v_toBind_1012_, lean_box(0), lean_box(0), v___x_1017_, v___f_1016_);
return v___x_1018_;
}
case 1:
{
lean_object* v_it_1019_; lean_object* v___x_1020_; 
lean_dec(v_toBind_1012_);
lean_dec(v___y_1010_);
lean_dec(v_toPure_1008_);
v_it_1019_ = lean_ctor_get(v_s_1013_, 0);
lean_inc(v_it_1019_);
lean_dec_ref(v_s_1013_);
v___x_1020_ = lean_apply_4(v_recur_1009_, v_it_1019_, v_acc_1011_, lean_box(0), lean_box(0));
return v___x_1020_;
}
default: 
{
lean_object* v___x_1021_; 
lean_dec(v_toBind_1012_);
lean_dec(v___y_1010_);
lean_dec(v_recur_1009_);
v___x_1021_ = lean_apply_2(v_toPure_1008_, lean_box(0), v_acc_1011_);
return v___x_1021_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2(lean_object* v_toPure_1022_, lean_object* v___y_1023_, lean_object* v_toBind_1024_, lean_object* v_inst_1025_, lean_object* v_s_1026_, lean_object* v_lift_1027_, lean_object* v_it_1028_, lean_object* v_acc_1029_, lean_object* v_hP_1030_, lean_object* v_recur_1031_){
_start:
{
lean_object* v___f_1032_; 
v___f_1032_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_1032_, 0, v_toPure_1022_);
lean_closure_set(v___f_1032_, 1, v_recur_1031_);
lean_closure_set(v___f_1032_, 2, v___y_1023_);
lean_closure_set(v___f_1032_, 3, v_acc_1029_);
lean_closure_set(v___f_1032_, 4, v_toBind_1024_);
if (lean_obj_tag(v_it_1028_) == 0)
{
lean_object* v_currPos_1033_; lean_object* v_searcher_1034_; lean_object* v___x_1036_; uint8_t v_isShared_1037_; uint8_t v_isSharedCheck_1091_; 
v_currPos_1033_ = lean_ctor_get(v_it_1028_, 0);
v_searcher_1034_ = lean_ctor_get(v_it_1028_, 1);
v_isSharedCheck_1091_ = !lean_is_exclusive(v_it_1028_);
if (v_isSharedCheck_1091_ == 0)
{
v___x_1036_ = v_it_1028_;
v_isShared_1037_ = v_isSharedCheck_1091_;
goto v_resetjp_1035_;
}
else
{
lean_inc(v_searcher_1034_);
lean_inc(v_currPos_1033_);
lean_dec(v_it_1028_);
v___x_1036_ = lean_box(0);
v_isShared_1037_ = v_isSharedCheck_1091_;
goto v_resetjp_1035_;
}
v_resetjp_1035_:
{
lean_object* v___x_1038_; 
lean_inc_ref(v_s_1026_);
v___x_1038_ = lean_apply_2(v_inst_1025_, v_s_1026_, v_searcher_1034_);
switch(lean_obj_tag(v___x_1038_))
{
case 0:
{
lean_object* v_out_1039_; 
v_out_1039_ = lean_ctor_get(v___x_1038_, 1);
lean_inc(v_out_1039_);
if (lean_obj_tag(v_out_1039_) == 0)
{
lean_object* v_it_1040_; lean_object* v___x_1042_; 
lean_dec_ref(v_out_1039_);
lean_dec_ref(v_s_1026_);
v_it_1040_ = lean_ctor_get(v___x_1038_, 0);
lean_inc(v_it_1040_);
lean_dec_ref(v___x_1038_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v_it_1040_);
v___x_1042_ = v___x_1036_;
goto v_reusejp_1041_;
}
else
{
lean_object* v_reuseFailAlloc_1045_; 
v_reuseFailAlloc_1045_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1045_, 0, v_currPos_1033_);
lean_ctor_set(v_reuseFailAlloc_1045_, 1, v_it_1040_);
v___x_1042_ = v_reuseFailAlloc_1045_;
goto v_reusejp_1041_;
}
v_reusejp_1041_:
{
lean_object* v___x_1043_; lean_object* v___x_1044_; 
v___x_1043_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1043_, 0, v___x_1042_);
v___x_1044_ = lean_apply_4(v_lift_1027_, lean_box(0), lean_box(0), v___f_1032_, v___x_1043_);
return v___x_1044_;
}
}
else
{
lean_object* v_it_1046_; lean_object* v___x_1048_; uint8_t v_isShared_1049_; uint8_t v_isSharedCheck_1059_; 
v_it_1046_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1059_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1059_ == 0)
{
lean_object* v_unused_1060_; 
v_unused_1060_ = lean_ctor_get(v___x_1038_, 1);
lean_dec(v_unused_1060_);
v___x_1048_ = v___x_1038_;
v_isShared_1049_ = v_isSharedCheck_1059_;
goto v_resetjp_1047_;
}
else
{
lean_inc(v_it_1046_);
lean_dec(v___x_1038_);
v___x_1048_ = lean_box(0);
v_isShared_1049_ = v_isSharedCheck_1059_;
goto v_resetjp_1047_;
}
v_resetjp_1047_:
{
lean_object* v_endPos_1050_; lean_object* v_slice_1051_; lean_object* v_nextIt_1053_; 
v_endPos_1050_ = lean_ctor_get(v_out_1039_, 1);
lean_inc(v_endPos_1050_);
lean_dec_ref(v_out_1039_);
v_slice_1051_ = l_String_Slice_slice_x21(v_s_1026_, v_currPos_1033_, v_endPos_1050_);
lean_dec(v_currPos_1033_);
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v_it_1046_);
lean_ctor_set(v___x_1036_, 0, v_endPos_1050_);
v_nextIt_1053_ = v___x_1036_;
goto v_reusejp_1052_;
}
else
{
lean_object* v_reuseFailAlloc_1058_; 
v_reuseFailAlloc_1058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1058_, 0, v_endPos_1050_);
lean_ctor_set(v_reuseFailAlloc_1058_, 1, v_it_1046_);
v_nextIt_1053_ = v_reuseFailAlloc_1058_;
goto v_reusejp_1052_;
}
v_reusejp_1052_:
{
lean_object* v___x_1055_; 
if (v_isShared_1049_ == 0)
{
lean_ctor_set(v___x_1048_, 1, v_slice_1051_);
lean_ctor_set(v___x_1048_, 0, v_nextIt_1053_);
v___x_1055_ = v___x_1048_;
goto v_reusejp_1054_;
}
else
{
lean_object* v_reuseFailAlloc_1057_; 
v_reuseFailAlloc_1057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1057_, 0, v_nextIt_1053_);
lean_ctor_set(v_reuseFailAlloc_1057_, 1, v_slice_1051_);
v___x_1055_ = v_reuseFailAlloc_1057_;
goto v_reusejp_1054_;
}
v_reusejp_1054_:
{
lean_object* v___x_1056_; 
v___x_1056_ = lean_apply_4(v_lift_1027_, lean_box(0), lean_box(0), v___f_1032_, v___x_1055_);
return v___x_1056_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1061_; lean_object* v___x_1063_; uint8_t v_isShared_1064_; uint8_t v_isSharedCheck_1072_; 
lean_dec_ref(v_s_1026_);
v_it_1061_ = lean_ctor_get(v___x_1038_, 0);
v_isSharedCheck_1072_ = !lean_is_exclusive(v___x_1038_);
if (v_isSharedCheck_1072_ == 0)
{
v___x_1063_ = v___x_1038_;
v_isShared_1064_ = v_isSharedCheck_1072_;
goto v_resetjp_1062_;
}
else
{
lean_inc(v_it_1061_);
lean_dec(v___x_1038_);
v___x_1063_ = lean_box(0);
v_isShared_1064_ = v_isSharedCheck_1072_;
goto v_resetjp_1062_;
}
v_resetjp_1062_:
{
lean_object* v___x_1066_; 
if (v_isShared_1037_ == 0)
{
lean_ctor_set(v___x_1036_, 1, v_it_1061_);
v___x_1066_ = v___x_1036_;
goto v_reusejp_1065_;
}
else
{
lean_object* v_reuseFailAlloc_1071_; 
v_reuseFailAlloc_1071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1071_, 0, v_currPos_1033_);
lean_ctor_set(v_reuseFailAlloc_1071_, 1, v_it_1061_);
v___x_1066_ = v_reuseFailAlloc_1071_;
goto v_reusejp_1065_;
}
v_reusejp_1065_:
{
lean_object* v___x_1068_; 
if (v_isShared_1064_ == 0)
{
lean_ctor_set(v___x_1063_, 0, v___x_1066_);
v___x_1068_ = v___x_1063_;
goto v_reusejp_1067_;
}
else
{
lean_object* v_reuseFailAlloc_1070_; 
v_reuseFailAlloc_1070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1070_, 0, v___x_1066_);
v___x_1068_ = v_reuseFailAlloc_1070_;
goto v_reusejp_1067_;
}
v_reusejp_1067_:
{
lean_object* v___x_1069_; 
v___x_1069_ = lean_apply_4(v_lift_1027_, lean_box(0), lean_box(0), v___f_1032_, v___x_1068_);
return v___x_1069_;
}
}
}
}
default: 
{
lean_object* v_str_1073_; lean_object* v_startInclusive_1074_; lean_object* v_endExclusive_1075_; lean_object* v___x_1077_; uint8_t v_isShared_1078_; uint8_t v_isSharedCheck_1090_; 
lean_del_object(v___x_1036_);
v_str_1073_ = lean_ctor_get(v_s_1026_, 0);
v_startInclusive_1074_ = lean_ctor_get(v_s_1026_, 1);
v_endExclusive_1075_ = lean_ctor_get(v_s_1026_, 2);
v_isSharedCheck_1090_ = !lean_is_exclusive(v_s_1026_);
if (v_isSharedCheck_1090_ == 0)
{
v___x_1077_ = v_s_1026_;
v_isShared_1078_ = v_isSharedCheck_1090_;
goto v_resetjp_1076_;
}
else
{
lean_inc(v_endExclusive_1075_);
lean_inc(v_startInclusive_1074_);
lean_inc(v_str_1073_);
lean_dec(v_s_1026_);
v___x_1077_ = lean_box(0);
v_isShared_1078_ = v_isSharedCheck_1090_;
goto v_resetjp_1076_;
}
v_resetjp_1076_:
{
lean_object* v___x_1079_; uint8_t v___x_1080_; 
v___x_1079_ = lean_nat_sub(v_endExclusive_1075_, v_startInclusive_1074_);
v___x_1080_ = lean_nat_dec_eq(v_currPos_1033_, v___x_1079_);
lean_dec(v___x_1079_);
if (v___x_1080_ == 0)
{
lean_object* v___x_1081_; lean_object* v_slice_1083_; 
v___x_1081_ = lean_nat_add(v_startInclusive_1074_, v_currPos_1033_);
lean_dec(v_currPos_1033_);
lean_dec(v_startInclusive_1074_);
if (v_isShared_1078_ == 0)
{
lean_ctor_set(v___x_1077_, 1, v___x_1081_);
v_slice_1083_ = v___x_1077_;
goto v_reusejp_1082_;
}
else
{
lean_object* v_reuseFailAlloc_1087_; 
v_reuseFailAlloc_1087_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1087_, 0, v_str_1073_);
lean_ctor_set(v_reuseFailAlloc_1087_, 1, v___x_1081_);
lean_ctor_set(v_reuseFailAlloc_1087_, 2, v_endExclusive_1075_);
v_slice_1083_ = v_reuseFailAlloc_1087_;
goto v_reusejp_1082_;
}
v_reusejp_1082_:
{
lean_object* v___x_1084_; lean_object* v___x_1085_; lean_object* v___x_1086_; 
v___x_1084_ = lean_box(1);
v___x_1085_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1085_, 0, v___x_1084_);
lean_ctor_set(v___x_1085_, 1, v_slice_1083_);
v___x_1086_ = lean_apply_4(v_lift_1027_, lean_box(0), lean_box(0), v___f_1032_, v___x_1085_);
return v___x_1086_;
}
}
else
{
lean_object* v___x_1088_; lean_object* v___x_1089_; 
lean_del_object(v___x_1077_);
lean_dec(v_endExclusive_1075_);
lean_dec(v_startInclusive_1074_);
lean_dec_ref(v_str_1073_);
lean_dec(v_currPos_1033_);
v___x_1088_ = lean_box(2);
v___x_1089_ = lean_apply_4(v_lift_1027_, lean_box(0), lean_box(0), v___f_1032_, v___x_1088_);
return v___x_1089_;
}
}
}
}
}
}
else
{
lean_object* v___x_1092_; lean_object* v___x_1093_; 
lean_dec_ref(v_s_1026_);
lean_dec(v_inst_1025_);
v___x_1092_ = lean_box(2);
v___x_1093_ = lean_apply_4(v_lift_1027_, lean_box(0), lean_box(0), v___f_1032_, v___x_1092_);
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3(lean_object* v_inst_1094_, lean_object* v_inst_1095_, lean_object* v_s_1096_, lean_object* v_lift_1097_, lean_object* v_00_u03b3_1098_, lean_object* v_Pl_1099_, lean_object* v_it_1100_, lean_object* v_init_1101_, lean_object* v___y_1102_){
_start:
{
lean_object* v_toApplicative_1103_; lean_object* v_toBind_1104_; lean_object* v_toPure_1105_; lean_object* v___f_1106_; lean_object* v___x_1107_; 
v_toApplicative_1103_ = lean_ctor_get(v_inst_1094_, 0);
lean_inc_ref(v_toApplicative_1103_);
v_toBind_1104_ = lean_ctor_get(v_inst_1094_, 1);
lean_inc(v_toBind_1104_);
lean_dec_ref(v_inst_1094_);
v_toPure_1105_ = lean_ctor_get(v_toApplicative_1103_, 1);
lean_inc(v_toPure_1105_);
lean_dec_ref(v_toApplicative_1103_);
v___f_1106_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_1106_, 0, v_toPure_1105_);
lean_closure_set(v___f_1106_, 1, v___y_1102_);
lean_closure_set(v___f_1106_, 2, v_toBind_1104_);
lean_closure_set(v___f_1106_, 3, v_inst_1095_);
lean_closure_set(v___f_1106_, 4, v_s_1096_);
lean_closure_set(v___f_1106_, 5, v_lift_1097_);
v___x_1107_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1106_, v_it_1100_, v_init_1101_, lean_box(0));
return v___x_1107_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg(lean_object* v_inst_1108_, lean_object* v_inst_1109_, lean_object* v_s_1110_){
_start:
{
lean_object* v___f_1111_; 
v___f_1111_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1111_, 0, v_inst_1109_);
lean_closure_set(v___f_1111_, 1, v_inst_1108_);
lean_closure_set(v___f_1111_, 2, v_s_1110_);
return v___f_1111_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(lean_object* v_00_u03c1_1112_, lean_object* v_00_u03c3_1113_, lean_object* v_inst_1114_, lean_object* v_pat_1115_, lean_object* v_inst_1116_, lean_object* v_n_1117_, lean_object* v_inst_1118_, lean_object* v_s_1119_){
_start:
{
lean_object* v___f_1120_; 
v___f_1120_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1120_, 0, v_inst_1118_);
lean_closure_set(v___f_1120_, 1, v_inst_1114_);
lean_closure_set(v___f_1120_, 2, v_s_1119_);
return v___f_1120_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___boxed(lean_object* v_00_u03c1_1121_, lean_object* v_00_u03c3_1122_, lean_object* v_inst_1123_, lean_object* v_pat_1124_, lean_object* v_inst_1125_, lean_object* v_n_1126_, lean_object* v_inst_1127_, lean_object* v_s_1128_){
_start:
{
lean_object* v_res_1129_; 
v_res_1129_ = l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(v_00_u03c1_1121_, v_00_u03c3_1122_, v_inst_1123_, v_pat_1124_, v_inst_1125_, v_n_1126_, v_inst_1127_, v_s_1128_);
lean_dec(v_inst_1125_);
lean_dec(v_pat_1124_);
return v_res_1129_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___redArg(lean_object* v_s_1130_, lean_object* v_inst_1131_){
_start:
{
lean_object* v___x_1132_; lean_object* v___x_1133_; lean_object* v___x_1134_; 
v___x_1132_ = lean_unsigned_to_nat(0u);
v___x_1133_ = lean_apply_1(v_inst_1131_, v_s_1130_);
v___x_1134_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1134_, 0, v___x_1132_);
lean_ctor_set(v___x_1134_, 1, v___x_1133_);
return v___x_1134_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive(lean_object* v_00_u03c1_1135_, lean_object* v_00_u03c3_1136_, lean_object* v_s_1137_, lean_object* v_pat_1138_, lean_object* v_inst_1139_){
_start:
{
lean_object* v___x_1140_; 
v___x_1140_ = l_String_Slice_splitInclusive___redArg(v_s_1137_, v_inst_1139_);
return v___x_1140_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___boxed(lean_object* v_00_u03c1_1141_, lean_object* v_00_u03c3_1142_, lean_object* v_s_1143_, lean_object* v_pat_1144_, lean_object* v_inst_1145_){
_start:
{
lean_object* v_res_1146_; 
v_res_1146_ = l_String_Slice_splitInclusive(v_00_u03c1_1141_, v_00_u03c3_1142_, v_s_1143_, v_pat_1144_, v_inst_1145_);
lean_dec(v_pat_1144_);
return v_res_1146_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___redArg(lean_object* v_s_1147_, lean_object* v_inst_1148_){
_start:
{
lean_object* v_dropPrefix_x3f_1149_; lean_object* v___x_1150_; 
v_dropPrefix_x3f_1149_ = lean_ctor_get(v_inst_1148_, 0);
lean_inc_ref(v_dropPrefix_x3f_1149_);
lean_dec_ref(v_inst_1148_);
lean_inc_ref(v_s_1147_);
v___x_1150_ = lean_apply_1(v_dropPrefix_x3f_1149_, v_s_1147_);
if (lean_obj_tag(v___x_1150_) == 0)
{
lean_object* v___x_1151_; 
lean_dec_ref(v_s_1147_);
v___x_1151_ = lean_box(0);
return v___x_1151_;
}
else
{
lean_object* v_val_1152_; lean_object* v___x_1154_; uint8_t v_isShared_1155_; uint8_t v_isSharedCheck_1170_; 
v_val_1152_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1170_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1170_ == 0)
{
v___x_1154_ = v___x_1150_;
v_isShared_1155_ = v_isSharedCheck_1170_;
goto v_resetjp_1153_;
}
else
{
lean_inc(v_val_1152_);
lean_dec(v___x_1150_);
v___x_1154_ = lean_box(0);
v_isShared_1155_ = v_isSharedCheck_1170_;
goto v_resetjp_1153_;
}
v_resetjp_1153_:
{
lean_object* v_str_1156_; lean_object* v_startInclusive_1157_; lean_object* v_endExclusive_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1169_; 
v_str_1156_ = lean_ctor_get(v_s_1147_, 0);
v_startInclusive_1157_ = lean_ctor_get(v_s_1147_, 1);
v_endExclusive_1158_ = lean_ctor_get(v_s_1147_, 2);
v_isSharedCheck_1169_ = !lean_is_exclusive(v_s_1147_);
if (v_isSharedCheck_1169_ == 0)
{
v___x_1160_ = v_s_1147_;
v_isShared_1161_ = v_isSharedCheck_1169_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_endExclusive_1158_);
lean_inc(v_startInclusive_1157_);
lean_inc(v_str_1156_);
lean_dec(v_s_1147_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1169_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v___x_1162_; lean_object* v___x_1164_; 
v___x_1162_ = lean_nat_add(v_startInclusive_1157_, v_val_1152_);
lean_dec(v_val_1152_);
lean_dec(v_startInclusive_1157_);
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v___x_1162_);
v___x_1164_ = v___x_1160_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1168_; 
v_reuseFailAlloc_1168_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1168_, 0, v_str_1156_);
lean_ctor_set(v_reuseFailAlloc_1168_, 1, v___x_1162_);
lean_ctor_set(v_reuseFailAlloc_1168_, 2, v_endExclusive_1158_);
v___x_1164_ = v_reuseFailAlloc_1168_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1166_; 
if (v_isShared_1155_ == 0)
{
lean_ctor_set(v___x_1154_, 0, v___x_1164_);
v___x_1166_ = v___x_1154_;
goto v_reusejp_1165_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v___x_1164_);
v___x_1166_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1165_;
}
v_reusejp_1165_:
{
return v___x_1166_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f(lean_object* v_00_u03c1_1171_, lean_object* v_s_1172_, lean_object* v_pat_1173_, lean_object* v_inst_1174_){
_start:
{
lean_object* v_dropPrefix_x3f_1175_; lean_object* v___x_1176_; 
v_dropPrefix_x3f_1175_ = lean_ctor_get(v_inst_1174_, 0);
lean_inc_ref(v_dropPrefix_x3f_1175_);
lean_dec_ref(v_inst_1174_);
lean_inc_ref(v_s_1172_);
v___x_1176_ = lean_apply_1(v_dropPrefix_x3f_1175_, v_s_1172_);
if (lean_obj_tag(v___x_1176_) == 0)
{
lean_object* v___x_1177_; 
lean_dec_ref(v_s_1172_);
v___x_1177_ = lean_box(0);
return v___x_1177_;
}
else
{
lean_object* v_val_1178_; lean_object* v___x_1180_; uint8_t v_isShared_1181_; uint8_t v_isSharedCheck_1196_; 
v_val_1178_ = lean_ctor_get(v___x_1176_, 0);
v_isSharedCheck_1196_ = !lean_is_exclusive(v___x_1176_);
if (v_isSharedCheck_1196_ == 0)
{
v___x_1180_ = v___x_1176_;
v_isShared_1181_ = v_isSharedCheck_1196_;
goto v_resetjp_1179_;
}
else
{
lean_inc(v_val_1178_);
lean_dec(v___x_1176_);
v___x_1180_ = lean_box(0);
v_isShared_1181_ = v_isSharedCheck_1196_;
goto v_resetjp_1179_;
}
v_resetjp_1179_:
{
lean_object* v_str_1182_; lean_object* v_startInclusive_1183_; lean_object* v_endExclusive_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1195_; 
v_str_1182_ = lean_ctor_get(v_s_1172_, 0);
v_startInclusive_1183_ = lean_ctor_get(v_s_1172_, 1);
v_endExclusive_1184_ = lean_ctor_get(v_s_1172_, 2);
v_isSharedCheck_1195_ = !lean_is_exclusive(v_s_1172_);
if (v_isSharedCheck_1195_ == 0)
{
v___x_1186_ = v_s_1172_;
v_isShared_1187_ = v_isSharedCheck_1195_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_endExclusive_1184_);
lean_inc(v_startInclusive_1183_);
lean_inc(v_str_1182_);
lean_dec(v_s_1172_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1195_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; lean_object* v___x_1190_; 
v___x_1188_ = lean_nat_add(v_startInclusive_1183_, v_val_1178_);
lean_dec(v_val_1178_);
lean_dec(v_startInclusive_1183_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___x_1188_);
v___x_1190_ = v___x_1186_;
goto v_reusejp_1189_;
}
else
{
lean_object* v_reuseFailAlloc_1194_; 
v_reuseFailAlloc_1194_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1194_, 0, v_str_1182_);
lean_ctor_set(v_reuseFailAlloc_1194_, 1, v___x_1188_);
lean_ctor_set(v_reuseFailAlloc_1194_, 2, v_endExclusive_1184_);
v___x_1190_ = v_reuseFailAlloc_1194_;
goto v_reusejp_1189_;
}
v_reusejp_1189_:
{
lean_object* v___x_1192_; 
if (v_isShared_1181_ == 0)
{
lean_ctor_set(v___x_1180_, 0, v___x_1190_);
v___x_1192_ = v___x_1180_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1193_; 
v_reuseFailAlloc_1193_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1193_, 0, v___x_1190_);
v___x_1192_ = v_reuseFailAlloc_1193_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
return v___x_1192_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_1197_, lean_object* v_s_1198_, lean_object* v_pat_1199_, lean_object* v_inst_1200_){
_start:
{
lean_object* v_res_1201_; 
v_res_1201_ = l_String_Slice_dropPrefix_x3f(v_00_u03c1_1197_, v_s_1198_, v_pat_1199_, v_inst_1200_);
lean_dec(v_pat_1199_);
return v_res_1201_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___redArg(lean_object* v_s_1202_, lean_object* v_inst_1203_){
_start:
{
lean_object* v_dropPrefix_x3f_1204_; lean_object* v___x_1205_; 
v_dropPrefix_x3f_1204_ = lean_ctor_get(v_inst_1203_, 0);
lean_inc_ref(v_dropPrefix_x3f_1204_);
lean_dec_ref(v_inst_1203_);
lean_inc_ref(v_s_1202_);
v___x_1205_ = lean_apply_1(v_dropPrefix_x3f_1204_, v_s_1202_);
if (lean_obj_tag(v___x_1205_) == 0)
{
return v_s_1202_;
}
else
{
lean_object* v_val_1206_; lean_object* v_str_1207_; lean_object* v_startInclusive_1208_; lean_object* v_endExclusive_1209_; lean_object* v___x_1211_; uint8_t v_isShared_1212_; uint8_t v_isSharedCheck_1217_; 
v_val_1206_ = lean_ctor_get(v___x_1205_, 0);
lean_inc(v_val_1206_);
lean_dec_ref(v___x_1205_);
v_str_1207_ = lean_ctor_get(v_s_1202_, 0);
v_startInclusive_1208_ = lean_ctor_get(v_s_1202_, 1);
v_endExclusive_1209_ = lean_ctor_get(v_s_1202_, 2);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_s_1202_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1211_ = v_s_1202_;
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
else
{
lean_inc(v_endExclusive_1209_);
lean_inc(v_startInclusive_1208_);
lean_inc(v_str_1207_);
lean_dec(v_s_1202_);
v___x_1211_ = lean_box(0);
v_isShared_1212_ = v_isSharedCheck_1217_;
goto v_resetjp_1210_;
}
v_resetjp_1210_:
{
lean_object* v___x_1213_; lean_object* v___x_1215_; 
v___x_1213_ = lean_nat_add(v_startInclusive_1208_, v_val_1206_);
lean_dec(v_val_1206_);
lean_dec(v_startInclusive_1208_);
if (v_isShared_1212_ == 0)
{
lean_ctor_set(v___x_1211_, 1, v___x_1213_);
v___x_1215_ = v___x_1211_;
goto v_reusejp_1214_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_str_1207_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1213_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_endExclusive_1209_);
v___x_1215_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1214_;
}
v_reusejp_1214_:
{
return v___x_1215_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix(lean_object* v_00_u03c1_1218_, lean_object* v_s_1219_, lean_object* v_pat_1220_, lean_object* v_inst_1221_){
_start:
{
lean_object* v___x_1222_; 
v___x_1222_ = l_String_Slice_dropPrefix___redArg(v_s_1219_, v_inst_1221_);
return v___x_1222_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___boxed(lean_object* v_00_u03c1_1223_, lean_object* v_s_1224_, lean_object* v_pat_1225_, lean_object* v_inst_1226_){
_start:
{
lean_object* v_res_1227_; 
v_res_1227_ = l_String_Slice_dropPrefix(v_00_u03c1_1223_, v_s_1224_, v_pat_1225_, v_inst_1226_);
lean_dec(v_pat_1225_);
return v_res_1227_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__0(lean_object* v_x_1228_, lean_object* v_x_1229_, lean_object* v_f_1230_, lean_object* v_c_1231_){
_start:
{
lean_object* v___x_1232_; 
v___x_1232_ = lean_apply_1(v_f_1230_, v_c_1231_);
return v___x_1232_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1(lean_object* v_s_1233_, lean_object* v_inst_1234_, lean_object* v_replacement_1235_, lean_object* v_x1_1236_, lean_object* v_x2_1237_, lean_object* v_x3_1238_){
_start:
{
if (lean_obj_tag(v_x1_1236_) == 0)
{
lean_object* v_startPos_1239_; lean_object* v_endPos_1240_; lean_object* v___x_1241_; lean_object* v_str_1242_; lean_object* v_startInclusive_1243_; lean_object* v_endExclusive_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; lean_object* v___x_1247_; 
lean_dec(v_replacement_1235_);
lean_dec_ref(v_inst_1234_);
v_startPos_1239_ = lean_ctor_get(v_x1_1236_, 0);
v_endPos_1240_ = lean_ctor_get(v_x1_1236_, 1);
v___x_1241_ = l_String_Slice_slice_x21(v_s_1233_, v_startPos_1239_, v_endPos_1240_);
v_str_1242_ = lean_ctor_get(v___x_1241_, 0);
lean_inc_ref(v_str_1242_);
v_startInclusive_1243_ = lean_ctor_get(v___x_1241_, 1);
lean_inc(v_startInclusive_1243_);
v_endExclusive_1244_ = lean_ctor_get(v___x_1241_, 2);
lean_inc(v_endExclusive_1244_);
lean_dec_ref(v___x_1241_);
v___x_1245_ = lean_string_utf8_extract(v_str_1242_, v_startInclusive_1243_, v_endExclusive_1244_);
lean_dec(v_endExclusive_1244_);
lean_dec(v_startInclusive_1243_);
lean_dec_ref(v_str_1242_);
v___x_1246_ = lean_string_append(v_x3_1238_, v___x_1245_);
lean_dec_ref(v___x_1245_);
v___x_1247_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1247_, 0, v___x_1246_);
return v___x_1247_;
}
else
{
lean_object* v___x_1248_; lean_object* v_str_1249_; lean_object* v_startInclusive_1250_; lean_object* v_endExclusive_1251_; lean_object* v___x_1252_; lean_object* v___x_1253_; lean_object* v___x_1254_; 
lean_dec_ref(v_s_1233_);
v___x_1248_ = lean_apply_1(v_inst_1234_, v_replacement_1235_);
v_str_1249_ = lean_ctor_get(v___x_1248_, 0);
lean_inc_ref(v_str_1249_);
v_startInclusive_1250_ = lean_ctor_get(v___x_1248_, 1);
lean_inc(v_startInclusive_1250_);
v_endExclusive_1251_ = lean_ctor_get(v___x_1248_, 2);
lean_inc(v_endExclusive_1251_);
lean_dec_ref(v___x_1248_);
v___x_1252_ = lean_string_utf8_extract(v_str_1249_, v_startInclusive_1250_, v_endExclusive_1251_);
lean_dec(v_endExclusive_1251_);
lean_dec(v_startInclusive_1250_);
lean_dec_ref(v_str_1249_);
v___x_1253_ = lean_string_append(v_x3_1238_, v___x_1252_);
lean_dec_ref(v___x_1252_);
v___x_1254_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1254_, 0, v___x_1253_);
return v___x_1254_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1___boxed(lean_object* v_s_1255_, lean_object* v_inst_1256_, lean_object* v_replacement_1257_, lean_object* v_x1_1258_, lean_object* v_x2_1259_, lean_object* v_x3_1260_){
_start:
{
lean_object* v_res_1261_; 
v_res_1261_ = l_String_Slice_replace___redArg___lam__1(v_s_1255_, v_inst_1256_, v_replacement_1257_, v_x1_1258_, v_x2_1259_, v_x3_1260_);
lean_dec_ref(v_x1_1258_);
return v_res_1261_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg(lean_object* v_inst_1264_, lean_object* v_inst_1265_, lean_object* v_s_1266_, lean_object* v_inst_1267_, lean_object* v_replacement_1268_){
_start:
{
lean_object* v___f_1269_; lean_object* v___f_1270_; lean_object* v___x_1271_; lean_object* v___x_1272_; lean_object* v___x_1273_; 
v___f_1269_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1266_);
v___f_1270_ = lean_alloc_closure((void*)(l_String_Slice_replace___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1270_, 0, v_s_1266_);
lean_closure_set(v___f_1270_, 1, v_inst_1265_);
lean_closure_set(v___f_1270_, 2, v_replacement_1268_);
v___x_1271_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
lean_inc_ref(v_s_1266_);
v___x_1272_ = lean_apply_1(v_inst_1267_, v_s_1266_);
v___x_1273_ = lean_apply_7(v_inst_1264_, v_s_1266_, v___f_1269_, lean_box(0), lean_box(0), v___x_1272_, v___x_1271_, v___f_1270_);
return v___x_1273_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace(lean_object* v_00_u03c1_1274_, lean_object* v_00_u03c3_1275_, lean_object* v_inst_1276_, lean_object* v_inst_1277_, lean_object* v_00_u03b1_1278_, lean_object* v_inst_1279_, lean_object* v_s_1280_, lean_object* v_pattern_1281_, lean_object* v_inst_1282_, lean_object* v_replacement_1283_){
_start:
{
lean_object* v___x_1284_; 
v___x_1284_ = l_String_Slice_replace___redArg(v_inst_1277_, v_inst_1279_, v_s_1280_, v_inst_1282_, v_replacement_1283_);
return v___x_1284_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___boxed(lean_object* v_00_u03c1_1285_, lean_object* v_00_u03c3_1286_, lean_object* v_inst_1287_, lean_object* v_inst_1288_, lean_object* v_00_u03b1_1289_, lean_object* v_inst_1290_, lean_object* v_s_1291_, lean_object* v_pattern_1292_, lean_object* v_inst_1293_, lean_object* v_replacement_1294_){
_start:
{
lean_object* v_res_1295_; 
v_res_1295_ = l_String_Slice_replace(v_00_u03c1_1285_, v_00_u03c3_1286_, v_inst_1287_, v_inst_1288_, v_00_u03b1_1289_, v_inst_1290_, v_s_1291_, v_pattern_1292_, v_inst_1293_, v_replacement_1294_);
lean_dec(v_pattern_1292_);
lean_dec(v_inst_1287_);
return v_res_1295_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object* v_s_1296_, lean_object* v_n_1297_){
_start:
{
lean_object* v_str_1298_; lean_object* v_startInclusive_1299_; lean_object* v_endExclusive_1300_; lean_object* v___x_1301_; lean_object* v___x_1302_; lean_object* v___x_1304_; uint8_t v_isShared_1305_; uint8_t v_isSharedCheck_1310_; 
v_str_1298_ = lean_ctor_get(v_s_1296_, 0);
lean_inc_ref(v_str_1298_);
v_startInclusive_1299_ = lean_ctor_get(v_s_1296_, 1);
lean_inc(v_startInclusive_1299_);
v_endExclusive_1300_ = lean_ctor_get(v_s_1296_, 2);
lean_inc(v_endExclusive_1300_);
v___x_1301_ = lean_unsigned_to_nat(0u);
v___x_1302_ = l_String_Slice_Pos_nextn(v_s_1296_, v___x_1301_, v_n_1297_);
v_isSharedCheck_1310_ = !lean_is_exclusive(v_s_1296_);
if (v_isSharedCheck_1310_ == 0)
{
lean_object* v_unused_1311_; lean_object* v_unused_1312_; lean_object* v_unused_1313_; 
v_unused_1311_ = lean_ctor_get(v_s_1296_, 2);
lean_dec(v_unused_1311_);
v_unused_1312_ = lean_ctor_get(v_s_1296_, 1);
lean_dec(v_unused_1312_);
v_unused_1313_ = lean_ctor_get(v_s_1296_, 0);
lean_dec(v_unused_1313_);
v___x_1304_ = v_s_1296_;
v_isShared_1305_ = v_isSharedCheck_1310_;
goto v_resetjp_1303_;
}
else
{
lean_dec(v_s_1296_);
v___x_1304_ = lean_box(0);
v_isShared_1305_ = v_isSharedCheck_1310_;
goto v_resetjp_1303_;
}
v_resetjp_1303_:
{
lean_object* v___x_1306_; lean_object* v___x_1308_; 
v___x_1306_ = lean_nat_add(v_startInclusive_1299_, v___x_1302_);
lean_dec(v___x_1302_);
lean_dec(v_startInclusive_1299_);
if (v_isShared_1305_ == 0)
{
lean_ctor_set(v___x_1304_, 1, v___x_1306_);
v___x_1308_ = v___x_1304_;
goto v_reusejp_1307_;
}
else
{
lean_object* v_reuseFailAlloc_1309_; 
v_reuseFailAlloc_1309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1309_, 0, v_str_1298_);
lean_ctor_set(v_reuseFailAlloc_1309_, 1, v___x_1306_);
lean_ctor_set(v_reuseFailAlloc_1309_, 2, v_endExclusive_1300_);
v___x_1308_ = v_reuseFailAlloc_1309_;
goto v_reusejp_1307_;
}
v_reusejp_1307_:
{
return v___x_1308_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___redArg(lean_object* v_s_1314_, lean_object* v_inst_1315_, lean_object* v_curr_1316_){
_start:
{
lean_object* v_dropPrefix_x3f_1317_; lean_object* v_str_1318_; lean_object* v_startInclusive_1319_; lean_object* v_endExclusive_1320_; lean_object* v___x_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; 
v_dropPrefix_x3f_1317_ = lean_ctor_get(v_inst_1315_, 0);
v_str_1318_ = lean_ctor_get(v_s_1314_, 0);
v_startInclusive_1319_ = lean_ctor_get(v_s_1314_, 1);
v_endExclusive_1320_ = lean_ctor_get(v_s_1314_, 2);
v___x_1321_ = lean_nat_add(v_startInclusive_1319_, v_curr_1316_);
lean_inc(v_endExclusive_1320_);
lean_inc_ref(v_str_1318_);
v___x_1322_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1322_, 0, v_str_1318_);
lean_ctor_set(v___x_1322_, 1, v___x_1321_);
lean_ctor_set(v___x_1322_, 2, v_endExclusive_1320_);
lean_inc_ref(v_dropPrefix_x3f_1317_);
lean_inc_ref(v___x_1322_);
v___x_1323_ = lean_apply_1(v_dropPrefix_x3f_1317_, v___x_1322_);
if (lean_obj_tag(v___x_1323_) == 1)
{
lean_object* v_val_1324_; lean_object* v___x_1325_; uint8_t v___x_1326_; 
v_val_1324_ = lean_ctor_get(v___x_1323_, 0);
lean_inc(v_val_1324_);
lean_dec_ref(v___x_1323_);
v___x_1325_ = lean_nat_add(v_curr_1316_, v_val_1324_);
lean_dec(v_val_1324_);
v___x_1326_ = lean_nat_dec_lt(v_curr_1316_, v___x_1325_);
lean_dec(v_curr_1316_);
if (v___x_1326_ == 0)
{
lean_dec(v___x_1325_);
lean_dec_ref(v_inst_1315_);
return v___x_1322_;
}
else
{
lean_dec_ref(v___x_1322_);
v_curr_1316_ = v___x_1325_;
goto _start;
}
}
else
{
lean_dec(v___x_1323_);
lean_dec(v_curr_1316_);
lean_dec_ref(v_inst_1315_);
return v___x_1322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___redArg___boxed(lean_object* v_s_1328_, lean_object* v_inst_1329_, lean_object* v_curr_1330_){
_start:
{
lean_object* v_res_1331_; 
v_res_1331_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___redArg(v_s_1328_, v_inst_1329_, v_curr_1330_);
lean_dec_ref(v_s_1328_);
return v_res_1331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(lean_object* v_00_u03c1_1332_, lean_object* v_s_1333_, lean_object* v_pat_1334_, lean_object* v_inst_1335_, lean_object* v_curr_1336_){
_start:
{
lean_object* v___x_1337_; 
v___x_1337_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___redArg(v_s_1333_, v_inst_1335_, v_curr_1336_);
return v___x_1337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___boxed(lean_object* v_00_u03c1_1338_, lean_object* v_s_1339_, lean_object* v_pat_1340_, lean_object* v_inst_1341_, lean_object* v_curr_1342_){
_start:
{
lean_object* v_res_1343_; 
v_res_1343_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go(v_00_u03c1_1338_, v_s_1339_, v_pat_1340_, v_inst_1341_, v_curr_1342_);
lean_dec(v_pat_1340_);
lean_dec_ref(v_s_1339_);
return v_res_1343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go_match__1_splitter___redArg(lean_object* v_x_1344_, lean_object* v_h__1_1345_, lean_object* v_h__2_1346_){
_start:
{
if (lean_obj_tag(v_x_1344_) == 1)
{
lean_object* v_val_1347_; lean_object* v___x_1348_; 
lean_dec(v_h__2_1346_);
v_val_1347_ = lean_ctor_get(v_x_1344_, 0);
lean_inc(v_val_1347_);
lean_dec_ref(v_x_1344_);
v___x_1348_ = lean_apply_1(v_h__1_1345_, v_val_1347_);
return v___x_1348_;
}
else
{
lean_object* v___x_1349_; 
lean_dec(v_h__1_1345_);
v___x_1349_ = lean_apply_2(v_h__2_1346_, v_x_1344_, lean_box(0));
return v___x_1349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go_match__1_splitter(lean_object* v_s_1350_, lean_object* v_curr_1351_, lean_object* v_motive_1352_, lean_object* v_x_1353_, lean_object* v_h__1_1354_, lean_object* v_h__2_1355_){
_start:
{
if (lean_obj_tag(v_x_1353_) == 1)
{
lean_object* v_val_1356_; lean_object* v___x_1357_; 
lean_dec(v_h__2_1355_);
v_val_1356_ = lean_ctor_get(v_x_1353_, 0);
lean_inc(v_val_1356_);
lean_dec_ref(v_x_1353_);
v___x_1357_ = lean_apply_1(v_h__1_1354_, v_val_1356_);
return v___x_1357_;
}
else
{
lean_object* v___x_1358_; 
lean_dec(v_h__1_1354_);
v___x_1358_ = lean_apply_2(v_h__2_1355_, v_x_1353_, lean_box(0));
return v___x_1358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go_match__1_splitter___boxed(lean_object* v_s_1359_, lean_object* v_curr_1360_, lean_object* v_motive_1361_, lean_object* v_x_1362_, lean_object* v_h__1_1363_, lean_object* v_h__2_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go_match__1_splitter(v_s_1359_, v_curr_1360_, v_motive_1361_, v_x_1362_, v_h__1_1363_, v_h__2_1364_);
lean_dec(v_curr_1360_);
lean_dec_ref(v_s_1359_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg(lean_object* v_s_1366_, lean_object* v_inst_1367_){
_start:
{
lean_object* v___x_1368_; lean_object* v___x_1369_; 
v___x_1368_ = lean_unsigned_to_nat(0u);
v___x_1369_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___redArg(v_s_1366_, v_inst_1367_, v___x_1368_);
return v___x_1369_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg___boxed(lean_object* v_s_1370_, lean_object* v_inst_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_String_Slice_dropWhile___redArg(v_s_1370_, v_inst_1371_);
lean_dec_ref(v_s_1370_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile(lean_object* v_00_u03c1_1373_, lean_object* v_s_1374_, lean_object* v_pat_1375_, lean_object* v_inst_1376_){
_start:
{
lean_object* v___x_1377_; lean_object* v___x_1378_; 
v___x_1377_ = lean_unsigned_to_nat(0u);
v___x_1378_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___redArg(v_s_1374_, v_inst_1376_, v___x_1377_);
return v___x_1378_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___boxed(lean_object* v_00_u03c1_1379_, lean_object* v_s_1380_, lean_object* v_pat_1381_, lean_object* v_inst_1382_){
_start:
{
lean_object* v_res_1383_; 
v_res_1383_ = l_String_Slice_dropWhile(v_00_u03c1_1379_, v_s_1380_, v_pat_1381_, v_inst_1382_);
lean_dec(v_pat_1381_);
lean_dec_ref(v_s_1380_);
return v_res_1383_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiStart___closed__1(void){
_start:
{
lean_object* v___x_1385_; lean_object* v___x_1386_; 
v___x_1385_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_1386_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart(lean_object* v_s_1387_){
_start:
{
lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
v___x_1388_ = lean_obj_once(&l_String_Slice_trimAsciiStart___closed__1, &l_String_Slice_trimAsciiStart___closed__1_once, _init_l_String_Slice_trimAsciiStart___closed__1);
v___x_1389_ = lean_unsigned_to_nat(0u);
v___x_1390_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___redArg(v_s_1387_, v___x_1388_, v___x_1389_);
return v___x_1390_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart___boxed(lean_object* v_s_1391_){
_start:
{
lean_object* v_res_1392_; 
v_res_1392_ = l_String_Slice_trimAsciiStart(v_s_1391_);
lean_dec_ref(v_s_1391_);
return v_res_1392_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object* v_s_1393_, lean_object* v_n_1394_){
_start:
{
lean_object* v_str_1395_; lean_object* v_startInclusive_1396_; lean_object* v___x_1397_; lean_object* v___x_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1406_; 
v_str_1395_ = lean_ctor_get(v_s_1393_, 0);
lean_inc_ref(v_str_1395_);
v_startInclusive_1396_ = lean_ctor_get(v_s_1393_, 1);
lean_inc(v_startInclusive_1396_);
v___x_1397_ = lean_unsigned_to_nat(0u);
v___x_1398_ = l_String_Slice_Pos_nextn(v_s_1393_, v___x_1397_, v_n_1394_);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_s_1393_);
if (v_isSharedCheck_1406_ == 0)
{
lean_object* v_unused_1407_; lean_object* v_unused_1408_; lean_object* v_unused_1409_; 
v_unused_1407_ = lean_ctor_get(v_s_1393_, 2);
lean_dec(v_unused_1407_);
v_unused_1408_ = lean_ctor_get(v_s_1393_, 1);
lean_dec(v_unused_1408_);
v_unused_1409_ = lean_ctor_get(v_s_1393_, 0);
lean_dec(v_unused_1409_);
v___x_1400_ = v_s_1393_;
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
else
{
lean_dec(v_s_1393_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_nat_add(v_startInclusive_1396_, v___x_1398_);
lean_dec(v___x_1398_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 2, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_str_1395_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v_startInclusive_1396_);
lean_ctor_set(v_reuseFailAlloc_1405_, 2, v___x_1402_);
v___x_1404_ = v_reuseFailAlloc_1405_;
goto v_reusejp_1403_;
}
v_reusejp_1403_:
{
return v___x_1404_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go___redArg(lean_object* v_s_1410_, lean_object* v_inst_1411_, lean_object* v_curr_1412_){
_start:
{
lean_object* v_dropPrefix_x3f_1413_; lean_object* v_str_1414_; lean_object* v_startInclusive_1415_; lean_object* v_endExclusive_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; lean_object* v___x_1419_; 
v_dropPrefix_x3f_1413_ = lean_ctor_get(v_inst_1411_, 0);
v_str_1414_ = lean_ctor_get(v_s_1410_, 0);
v_startInclusive_1415_ = lean_ctor_get(v_s_1410_, 1);
v_endExclusive_1416_ = lean_ctor_get(v_s_1410_, 2);
v___x_1417_ = lean_nat_add(v_startInclusive_1415_, v_curr_1412_);
lean_inc(v_endExclusive_1416_);
lean_inc(v___x_1417_);
lean_inc_ref(v_str_1414_);
v___x_1418_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1418_, 0, v_str_1414_);
lean_ctor_set(v___x_1418_, 1, v___x_1417_);
lean_ctor_set(v___x_1418_, 2, v_endExclusive_1416_);
lean_inc_ref(v_dropPrefix_x3f_1413_);
v___x_1419_ = lean_apply_1(v_dropPrefix_x3f_1413_, v___x_1418_);
if (lean_obj_tag(v___x_1419_) == 1)
{
lean_object* v_val_1420_; lean_object* v___x_1421_; uint8_t v___x_1422_; 
v_val_1420_ = lean_ctor_get(v___x_1419_, 0);
lean_inc(v_val_1420_);
lean_dec_ref(v___x_1419_);
v___x_1421_ = lean_nat_add(v_curr_1412_, v_val_1420_);
lean_dec(v_val_1420_);
v___x_1422_ = lean_nat_dec_lt(v_curr_1412_, v___x_1421_);
lean_dec(v_curr_1412_);
if (v___x_1422_ == 0)
{
lean_object* v___x_1424_; uint8_t v_isShared_1425_; uint8_t v_isSharedCheck_1429_; 
lean_inc(v_startInclusive_1415_);
lean_inc_ref(v_str_1414_);
lean_dec(v___x_1421_);
lean_dec_ref(v_inst_1411_);
v_isSharedCheck_1429_ = !lean_is_exclusive(v_s_1410_);
if (v_isSharedCheck_1429_ == 0)
{
lean_object* v_unused_1430_; lean_object* v_unused_1431_; lean_object* v_unused_1432_; 
v_unused_1430_ = lean_ctor_get(v_s_1410_, 2);
lean_dec(v_unused_1430_);
v_unused_1431_ = lean_ctor_get(v_s_1410_, 1);
lean_dec(v_unused_1431_);
v_unused_1432_ = lean_ctor_get(v_s_1410_, 0);
lean_dec(v_unused_1432_);
v___x_1424_ = v_s_1410_;
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
else
{
lean_dec(v_s_1410_);
v___x_1424_ = lean_box(0);
v_isShared_1425_ = v_isSharedCheck_1429_;
goto v_resetjp_1423_;
}
v_resetjp_1423_:
{
lean_object* v___x_1427_; 
if (v_isShared_1425_ == 0)
{
lean_ctor_set(v___x_1424_, 2, v___x_1417_);
v___x_1427_ = v___x_1424_;
goto v_reusejp_1426_;
}
else
{
lean_object* v_reuseFailAlloc_1428_; 
v_reuseFailAlloc_1428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1428_, 0, v_str_1414_);
lean_ctor_set(v_reuseFailAlloc_1428_, 1, v_startInclusive_1415_);
lean_ctor_set(v_reuseFailAlloc_1428_, 2, v___x_1417_);
v___x_1427_ = v_reuseFailAlloc_1428_;
goto v_reusejp_1426_;
}
v_reusejp_1426_:
{
return v___x_1427_;
}
}
}
else
{
lean_dec(v___x_1417_);
v_curr_1412_ = v___x_1421_;
goto _start;
}
}
else
{
lean_object* v___x_1435_; uint8_t v_isShared_1436_; uint8_t v_isSharedCheck_1440_; 
lean_inc(v_startInclusive_1415_);
lean_inc_ref(v_str_1414_);
lean_dec(v___x_1419_);
lean_dec(v_curr_1412_);
lean_dec_ref(v_inst_1411_);
v_isSharedCheck_1440_ = !lean_is_exclusive(v_s_1410_);
if (v_isSharedCheck_1440_ == 0)
{
lean_object* v_unused_1441_; lean_object* v_unused_1442_; lean_object* v_unused_1443_; 
v_unused_1441_ = lean_ctor_get(v_s_1410_, 2);
lean_dec(v_unused_1441_);
v_unused_1442_ = lean_ctor_get(v_s_1410_, 1);
lean_dec(v_unused_1442_);
v_unused_1443_ = lean_ctor_get(v_s_1410_, 0);
lean_dec(v_unused_1443_);
v___x_1435_ = v_s_1410_;
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
else
{
lean_dec(v_s_1410_);
v___x_1435_ = lean_box(0);
v_isShared_1436_ = v_isSharedCheck_1440_;
goto v_resetjp_1434_;
}
v_resetjp_1434_:
{
lean_object* v___x_1438_; 
if (v_isShared_1436_ == 0)
{
lean_ctor_set(v___x_1435_, 2, v___x_1417_);
v___x_1438_ = v___x_1435_;
goto v_reusejp_1437_;
}
else
{
lean_object* v_reuseFailAlloc_1439_; 
v_reuseFailAlloc_1439_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1439_, 0, v_str_1414_);
lean_ctor_set(v_reuseFailAlloc_1439_, 1, v_startInclusive_1415_);
lean_ctor_set(v_reuseFailAlloc_1439_, 2, v___x_1417_);
v___x_1438_ = v_reuseFailAlloc_1439_;
goto v_reusejp_1437_;
}
v_reusejp_1437_:
{
return v___x_1438_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go(lean_object* v_00_u03c1_1444_, lean_object* v_s_1445_, lean_object* v_pat_1446_, lean_object* v_inst_1447_, lean_object* v_curr_1448_){
_start:
{
lean_object* v___x_1449_; 
v___x_1449_ = l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go___redArg(v_s_1445_, v_inst_1447_, v_curr_1448_);
return v___x_1449_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go___boxed(lean_object* v_00_u03c1_1450_, lean_object* v_s_1451_, lean_object* v_pat_1452_, lean_object* v_inst_1453_, lean_object* v_curr_1454_){
_start:
{
lean_object* v_res_1455_; 
v_res_1455_ = l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go(v_00_u03c1_1450_, v_s_1451_, v_pat_1452_, v_inst_1453_, v_curr_1454_);
lean_dec(v_pat_1452_);
return v_res_1455_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___redArg(lean_object* v_s_1456_, lean_object* v_inst_1457_){
_start:
{
lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___x_1458_ = lean_unsigned_to_nat(0u);
v___x_1459_ = l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go___redArg(v_s_1456_, v_inst_1457_, v___x_1458_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile(lean_object* v_00_u03c1_1460_, lean_object* v_s_1461_, lean_object* v_pat_1462_, lean_object* v_inst_1463_){
_start:
{
lean_object* v___x_1464_; lean_object* v___x_1465_; 
v___x_1464_ = lean_unsigned_to_nat(0u);
v___x_1465_ = l___private_Init_Data_String_Slice_0__String_Slice_takeWhile_go___redArg(v_s_1461_, v_inst_1463_, v___x_1464_);
return v___x_1465_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___boxed(lean_object* v_00_u03c1_1466_, lean_object* v_s_1467_, lean_object* v_pat_1468_, lean_object* v_inst_1469_){
_start:
{
lean_object* v_res_1470_; 
v_res_1470_ = l_String_Slice_takeWhile(v_00_u03c1_1466_, v_s_1467_, v_pat_1468_, v_inst_1469_);
lean_dec(v_pat_1468_);
return v_res_1470_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1(lean_object* v___x_1471_, lean_object* v_x1_1472_, lean_object* v_x2_1473_, lean_object* v_x3_1474_){
_start:
{
if (lean_obj_tag(v_x1_1472_) == 0)
{
lean_object* v___x_1475_; 
v___x_1475_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1475_, 0, v___x_1471_);
return v___x_1475_;
}
else
{
lean_object* v_startPos_1476_; lean_object* v___x_1477_; lean_object* v___x_1478_; 
lean_dec(v___x_1471_);
v_startPos_1476_ = lean_ctor_get(v_x1_1472_, 0);
lean_inc(v_startPos_1476_);
v___x_1477_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1477_, 0, v_startPos_1476_);
v___x_1478_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1478_, 0, v___x_1477_);
return v___x_1478_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1___boxed(lean_object* v___x_1479_, lean_object* v_x1_1480_, lean_object* v_x2_1481_, lean_object* v_x3_1482_){
_start:
{
lean_object* v_res_1483_; 
v_res_1483_ = l_String_Slice_find_x3f___redArg___lam__1(v___x_1479_, v_x1_1480_, v_x2_1481_, v_x3_1482_);
lean_dec(v_x3_1482_);
lean_dec_ref(v_x1_1480_);
return v_res_1483_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg(lean_object* v_inst_1486_, lean_object* v_s_1487_, lean_object* v_inst_1488_){
_start:
{
lean_object* v___f_1489_; lean_object* v_searcher_1490_; lean_object* v___x_1491_; lean_object* v___f_1492_; lean_object* v___x_1493_; 
v___f_1489_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1487_);
v_searcher_1490_ = lean_apply_1(v_inst_1488_, v_s_1487_);
v___x_1491_ = lean_box(0);
v___f_1492_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1493_ = lean_apply_7(v_inst_1486_, v_s_1487_, v___f_1489_, lean_box(0), lean_box(0), v_searcher_1490_, v___x_1491_, v___f_1492_);
return v___x_1493_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f(lean_object* v_00_u03c1_1494_, lean_object* v_00_u03c3_1495_, lean_object* v_inst_1496_, lean_object* v_inst_1497_, lean_object* v_s_1498_, lean_object* v_pat_1499_, lean_object* v_inst_1500_){
_start:
{
lean_object* v___f_1501_; lean_object* v_searcher_1502_; lean_object* v___x_1503_; lean_object* v___f_1504_; lean_object* v___x_1505_; 
v___f_1501_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1498_);
v_searcher_1502_ = lean_apply_1(v_inst_1500_, v_s_1498_);
v___x_1503_ = lean_box(0);
v___f_1504_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1505_ = lean_apply_7(v_inst_1497_, v_s_1498_, v___f_1501_, lean_box(0), lean_box(0), v_searcher_1502_, v___x_1503_, v___f_1504_);
return v___x_1505_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___boxed(lean_object* v_00_u03c1_1506_, lean_object* v_00_u03c3_1507_, lean_object* v_inst_1508_, lean_object* v_inst_1509_, lean_object* v_s_1510_, lean_object* v_pat_1511_, lean_object* v_inst_1512_){
_start:
{
lean_object* v_res_1513_; 
v_res_1513_ = l_String_Slice_find_x3f(v_00_u03c1_1506_, v_00_u03c3_1507_, v_inst_1508_, v_inst_1509_, v_s_1510_, v_pat_1511_, v_inst_1512_);
lean_dec(v_pat_1511_);
lean_dec(v_inst_1508_);
return v_res_1513_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___redArg(lean_object* v_inst_1514_, lean_object* v_s_1515_, lean_object* v_inst_1516_){
_start:
{
lean_object* v___f_1517_; lean_object* v_searcher_1518_; lean_object* v___x_1519_; lean_object* v___f_1520_; lean_object* v___x_1521_; 
v___f_1517_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1515_);
v_searcher_1518_ = lean_apply_1(v_inst_1516_, v_s_1515_);
v___x_1519_ = lean_box(0);
v___f_1520_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
lean_inc_ref(v_s_1515_);
v___x_1521_ = lean_apply_7(v_inst_1514_, v_s_1515_, v___f_1517_, lean_box(0), lean_box(0), v_searcher_1518_, v___x_1519_, v___f_1520_);
if (lean_obj_tag(v___x_1521_) == 0)
{
lean_object* v_startInclusive_1522_; lean_object* v_endExclusive_1523_; lean_object* v___x_1524_; 
v_startInclusive_1522_ = lean_ctor_get(v_s_1515_, 1);
lean_inc(v_startInclusive_1522_);
v_endExclusive_1523_ = lean_ctor_get(v_s_1515_, 2);
lean_inc(v_endExclusive_1523_);
lean_dec_ref(v_s_1515_);
v___x_1524_ = lean_nat_sub(v_endExclusive_1523_, v_startInclusive_1522_);
lean_dec(v_startInclusive_1522_);
lean_dec(v_endExclusive_1523_);
return v___x_1524_;
}
else
{
lean_object* v_val_1525_; 
lean_dec_ref(v_s_1515_);
v_val_1525_ = lean_ctor_get(v___x_1521_, 0);
lean_inc(v_val_1525_);
lean_dec_ref(v___x_1521_);
return v_val_1525_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find(lean_object* v_00_u03c1_1526_, lean_object* v_00_u03c3_1527_, lean_object* v_inst_1528_, lean_object* v_inst_1529_, lean_object* v_s_1530_, lean_object* v_pat_1531_, lean_object* v_inst_1532_){
_start:
{
lean_object* v___f_1533_; lean_object* v_searcher_1534_; lean_object* v___x_1535_; lean_object* v___f_1536_; lean_object* v___x_1537_; 
v___f_1533_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1530_);
v_searcher_1534_ = lean_apply_1(v_inst_1532_, v_s_1530_);
v___x_1535_ = lean_box(0);
v___f_1536_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
lean_inc_ref(v_s_1530_);
v___x_1537_ = lean_apply_7(v_inst_1529_, v_s_1530_, v___f_1533_, lean_box(0), lean_box(0), v_searcher_1534_, v___x_1535_, v___f_1536_);
if (lean_obj_tag(v___x_1537_) == 0)
{
lean_object* v_startInclusive_1538_; lean_object* v_endExclusive_1539_; lean_object* v___x_1540_; 
v_startInclusive_1538_ = lean_ctor_get(v_s_1530_, 1);
lean_inc(v_startInclusive_1538_);
v_endExclusive_1539_ = lean_ctor_get(v_s_1530_, 2);
lean_inc(v_endExclusive_1539_);
lean_dec_ref(v_s_1530_);
v___x_1540_ = lean_nat_sub(v_endExclusive_1539_, v_startInclusive_1538_);
lean_dec(v_startInclusive_1538_);
lean_dec(v_endExclusive_1539_);
return v___x_1540_;
}
else
{
lean_object* v_val_1541_; 
lean_dec_ref(v_s_1530_);
v_val_1541_ = lean_ctor_get(v___x_1537_, 0);
lean_inc(v_val_1541_);
lean_dec_ref(v___x_1537_);
return v_val_1541_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___boxed(lean_object* v_00_u03c1_1542_, lean_object* v_00_u03c3_1543_, lean_object* v_inst_1544_, lean_object* v_inst_1545_, lean_object* v_s_1546_, lean_object* v_pat_1547_, lean_object* v_inst_1548_){
_start:
{
lean_object* v_res_1549_; 
v_res_1549_ = l_String_Slice_find(v_00_u03c1_1542_, v_00_u03c3_1543_, v_inst_1544_, v_inst_1545_, v_s_1546_, v_pat_1547_, v_inst_1548_);
lean_dec(v_pat_1547_);
lean_dec(v_inst_1544_);
return v_res_1549_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1(uint8_t v___x_1553_, lean_object* v_x1_1554_, lean_object* v_x2_1555_, uint8_t v_x3_1556_){
_start:
{
if (lean_obj_tag(v_x1_1554_) == 1)
{
lean_object* v___x_1557_; 
v___x_1557_ = ((lean_object*)(l_String_Slice_contains___redArg___lam__1___closed__0));
return v___x_1557_;
}
else
{
lean_object* v___x_1558_; lean_object* v___x_1559_; 
v___x_1558_ = lean_box(v___x_1553_);
v___x_1559_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1559_, 0, v___x_1558_);
return v___x_1559_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1___boxed(lean_object* v___x_1560_, lean_object* v_x1_1561_, lean_object* v_x2_1562_, lean_object* v_x3_1563_){
_start:
{
uint8_t v___x_86__boxed_1564_; uint8_t v_x3_89__boxed_1565_; lean_object* v_res_1566_; 
v___x_86__boxed_1564_ = lean_unbox(v___x_1560_);
v_x3_89__boxed_1565_ = lean_unbox(v_x3_1563_);
v_res_1566_ = l_String_Slice_contains___redArg___lam__1(v___x_86__boxed_1564_, v_x1_1561_, v_x2_1562_, v_x3_89__boxed_1565_);
lean_dec_ref(v_x1_1561_);
return v_res_1566_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___redArg(lean_object* v_inst_1570_, lean_object* v_s_1571_, lean_object* v_inst_1572_){
_start:
{
lean_object* v___f_1573_; lean_object* v_searcher_1574_; uint8_t v___x_1575_; lean_object* v___f_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; uint8_t v___x_1579_; 
v___f_1573_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1571_);
v_searcher_1574_ = lean_apply_1(v_inst_1572_, v_s_1571_);
v___x_1575_ = 0;
v___f_1576_ = ((lean_object*)(l_String_Slice_contains___redArg___closed__0));
v___x_1577_ = lean_box(v___x_1575_);
v___x_1578_ = lean_apply_7(v_inst_1570_, v_s_1571_, v___f_1573_, lean_box(0), lean_box(0), v_searcher_1574_, v___x_1577_, v___f_1576_);
v___x_1579_ = lean_unbox(v___x_1578_);
return v___x_1579_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___boxed(lean_object* v_inst_1580_, lean_object* v_s_1581_, lean_object* v_inst_1582_){
_start:
{
uint8_t v_res_1583_; lean_object* v_r_1584_; 
v_res_1583_ = l_String_Slice_contains___redArg(v_inst_1580_, v_s_1581_, v_inst_1582_);
v_r_1584_ = lean_box(v_res_1583_);
return v_r_1584_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains(lean_object* v_00_u03c1_1585_, lean_object* v_00_u03c3_1586_, lean_object* v_inst_1587_, lean_object* v_inst_1588_, lean_object* v_s_1589_, lean_object* v_pat_1590_, lean_object* v_inst_1591_){
_start:
{
uint8_t v___x_1592_; 
v___x_1592_ = l_String_Slice_contains___redArg(v_inst_1588_, v_s_1589_, v_inst_1591_);
return v___x_1592_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___boxed(lean_object* v_00_u03c1_1593_, lean_object* v_00_u03c3_1594_, lean_object* v_inst_1595_, lean_object* v_inst_1596_, lean_object* v_s_1597_, lean_object* v_pat_1598_, lean_object* v_inst_1599_){
_start:
{
uint8_t v_res_1600_; lean_object* v_r_1601_; 
v_res_1600_ = l_String_Slice_contains(v_00_u03c1_1593_, v_00_u03c3_1594_, v_inst_1595_, v_inst_1596_, v_s_1597_, v_pat_1598_, v_inst_1599_);
lean_dec(v_pat_1598_);
lean_dec(v_inst_1595_);
v_r_1601_ = lean_box(v_res_1600_);
return v_r_1601_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any___redArg(lean_object* v_inst_1602_, lean_object* v_s_1603_, lean_object* v_inst_1604_){
_start:
{
uint8_t v___x_1605_; 
v___x_1605_ = l_String_Slice_contains___redArg(v_inst_1602_, v_s_1603_, v_inst_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___redArg___boxed(lean_object* v_inst_1606_, lean_object* v_s_1607_, lean_object* v_inst_1608_){
_start:
{
uint8_t v_res_1609_; lean_object* v_r_1610_; 
v_res_1609_ = l_String_Slice_any___redArg(v_inst_1606_, v_s_1607_, v_inst_1608_);
v_r_1610_ = lean_box(v_res_1609_);
return v_r_1610_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any(lean_object* v_00_u03c1_1611_, lean_object* v_00_u03c3_1612_, lean_object* v_inst_1613_, lean_object* v_inst_1614_, lean_object* v_s_1615_, lean_object* v_pat_1616_, lean_object* v_inst_1617_){
_start:
{
uint8_t v___x_1618_; 
v___x_1618_ = l_String_Slice_contains___redArg(v_inst_1614_, v_s_1615_, v_inst_1617_);
return v___x_1618_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___boxed(lean_object* v_00_u03c1_1619_, lean_object* v_00_u03c3_1620_, lean_object* v_inst_1621_, lean_object* v_inst_1622_, lean_object* v_s_1623_, lean_object* v_pat_1624_, lean_object* v_inst_1625_){
_start:
{
uint8_t v_res_1626_; lean_object* v_r_1627_; 
v_res_1626_ = l_String_Slice_any(v_00_u03c1_1619_, v_00_u03c3_1620_, v_inst_1621_, v_inst_1622_, v_s_1623_, v_pat_1624_, v_inst_1625_);
lean_dec(v_pat_1624_);
lean_dec(v_inst_1621_);
v_r_1627_ = lean_box(v_res_1626_);
return v_r_1627_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all___redArg(lean_object* v_s_1628_, lean_object* v_inst_1629_){
_start:
{
lean_object* v___x_1630_; lean_object* v___x_1631_; lean_object* v_startInclusive_1632_; lean_object* v_endExclusive_1633_; lean_object* v___x_1634_; uint8_t v___x_1635_; 
v___x_1630_ = lean_unsigned_to_nat(0u);
v___x_1631_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___redArg(v_s_1628_, v_inst_1629_, v___x_1630_);
v_startInclusive_1632_ = lean_ctor_get(v___x_1631_, 1);
lean_inc(v_startInclusive_1632_);
v_endExclusive_1633_ = lean_ctor_get(v___x_1631_, 2);
lean_inc(v_endExclusive_1633_);
lean_dec_ref(v___x_1631_);
v___x_1634_ = lean_nat_sub(v_endExclusive_1633_, v_startInclusive_1632_);
lean_dec(v_startInclusive_1632_);
lean_dec(v_endExclusive_1633_);
v___x_1635_ = lean_nat_dec_eq(v___x_1634_, v___x_1630_);
lean_dec(v___x_1634_);
return v___x_1635_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___redArg___boxed(lean_object* v_s_1636_, lean_object* v_inst_1637_){
_start:
{
uint8_t v_res_1638_; lean_object* v_r_1639_; 
v_res_1638_ = l_String_Slice_all___redArg(v_s_1636_, v_inst_1637_);
lean_dec_ref(v_s_1636_);
v_r_1639_ = lean_box(v_res_1638_);
return v_r_1639_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all(lean_object* v_00_u03c1_1640_, lean_object* v_s_1641_, lean_object* v_pat_1642_, lean_object* v_inst_1643_){
_start:
{
lean_object* v___x_1644_; lean_object* v___x_1645_; lean_object* v_startInclusive_1646_; lean_object* v_endExclusive_1647_; lean_object* v___x_1648_; uint8_t v___x_1649_; 
v___x_1644_ = lean_unsigned_to_nat(0u);
v___x_1645_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___redArg(v_s_1641_, v_inst_1643_, v___x_1644_);
v_startInclusive_1646_ = lean_ctor_get(v___x_1645_, 1);
lean_inc(v_startInclusive_1646_);
v_endExclusive_1647_ = lean_ctor_get(v___x_1645_, 2);
lean_inc(v_endExclusive_1647_);
lean_dec_ref(v___x_1645_);
v___x_1648_ = lean_nat_sub(v_endExclusive_1647_, v_startInclusive_1646_);
lean_dec(v_startInclusive_1646_);
lean_dec(v_endExclusive_1647_);
v___x_1649_ = lean_nat_dec_eq(v___x_1648_, v___x_1644_);
lean_dec(v___x_1648_);
return v___x_1649_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___boxed(lean_object* v_00_u03c1_1650_, lean_object* v_s_1651_, lean_object* v_pat_1652_, lean_object* v_inst_1653_){
_start:
{
uint8_t v_res_1654_; lean_object* v_r_1655_; 
v_res_1654_ = l_String_Slice_all(v_00_u03c1_1650_, v_s_1651_, v_pat_1652_, v_inst_1653_);
lean_dec(v_pat_1652_);
lean_dec_ref(v_s_1651_);
v_r_1655_ = lean_box(v_res_1654_);
return v_r_1655_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith___redArg(lean_object* v_s_1656_, lean_object* v_inst_1657_){
_start:
{
lean_object* v_endsWith_1658_; lean_object* v___x_1659_; uint8_t v___x_1660_; 
v_endsWith_1658_ = lean_ctor_get(v_inst_1657_, 2);
lean_inc_ref(v_endsWith_1658_);
lean_dec_ref(v_inst_1657_);
v___x_1659_ = lean_apply_1(v_endsWith_1658_, v_s_1656_);
v___x_1660_ = lean_unbox(v___x_1659_);
return v___x_1660_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___redArg___boxed(lean_object* v_s_1661_, lean_object* v_inst_1662_){
_start:
{
uint8_t v_res_1663_; lean_object* v_r_1664_; 
v_res_1663_ = l_String_Slice_endsWith___redArg(v_s_1661_, v_inst_1662_);
v_r_1664_ = lean_box(v_res_1663_);
return v_r_1664_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith(lean_object* v_00_u03c1_1665_, lean_object* v_s_1666_, lean_object* v_pat_1667_, lean_object* v_inst_1668_){
_start:
{
lean_object* v_endsWith_1669_; lean_object* v___x_1670_; uint8_t v___x_1671_; 
v_endsWith_1669_ = lean_ctor_get(v_inst_1668_, 2);
lean_inc_ref(v_endsWith_1669_);
lean_dec_ref(v_inst_1668_);
v___x_1670_ = lean_apply_1(v_endsWith_1669_, v_s_1666_);
v___x_1671_ = lean_unbox(v___x_1670_);
return v___x_1671_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___boxed(lean_object* v_00_u03c1_1672_, lean_object* v_s_1673_, lean_object* v_pat_1674_, lean_object* v_inst_1675_){
_start:
{
uint8_t v_res_1676_; lean_object* v_r_1677_; 
v_res_1676_ = l_String_Slice_endsWith(v_00_u03c1_1672_, v_s_1673_, v_pat_1674_, v_inst_1675_);
lean_dec(v_pat_1674_);
v_r_1677_ = lean_box(v_res_1676_);
return v_r_1677_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___redArg(lean_object* v_x_1678_){
_start:
{
if (lean_obj_tag(v_x_1678_) == 0)
{
lean_object* v___x_1679_; 
v___x_1679_ = lean_unsigned_to_nat(0u);
return v___x_1679_;
}
else
{
lean_object* v___x_1680_; 
v___x_1680_ = lean_unsigned_to_nat(1u);
return v___x_1680_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___redArg___boxed(lean_object* v_x_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_String_Slice_RevSplitIterator_ctorIdx___redArg(v_x_1681_);
lean_dec(v_x_1681_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx(lean_object* v_00_u03c3_1683_, lean_object* v_00_u03c1_1684_, lean_object* v_pat_1685_, lean_object* v_s_1686_, lean_object* v_inst_1687_, lean_object* v_x_1688_){
_start:
{
lean_object* v___x_1689_; 
v___x_1689_ = l_String_Slice_RevSplitIterator_ctorIdx___redArg(v_x_1688_);
return v___x_1689_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___boxed(lean_object* v_00_u03c3_1690_, lean_object* v_00_u03c1_1691_, lean_object* v_pat_1692_, lean_object* v_s_1693_, lean_object* v_inst_1694_, lean_object* v_x_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_String_Slice_RevSplitIterator_ctorIdx(v_00_u03c3_1690_, v_00_u03c1_1691_, v_pat_1692_, v_s_1693_, v_inst_1694_, v_x_1695_);
lean_dec(v_x_1695_);
lean_dec(v_inst_1694_);
lean_dec_ref(v_s_1693_);
lean_dec(v_pat_1692_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___redArg(lean_object* v_t_1697_, lean_object* v_k_1698_){
_start:
{
if (lean_obj_tag(v_t_1697_) == 0)
{
lean_object* v_currPos_1699_; lean_object* v_searcher_1700_; lean_object* v___x_1701_; 
v_currPos_1699_ = lean_ctor_get(v_t_1697_, 0);
lean_inc(v_currPos_1699_);
v_searcher_1700_ = lean_ctor_get(v_t_1697_, 1);
lean_inc(v_searcher_1700_);
lean_dec_ref(v_t_1697_);
v___x_1701_ = lean_apply_2(v_k_1698_, v_currPos_1699_, v_searcher_1700_);
return v___x_1701_;
}
else
{
return v_k_1698_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim(lean_object* v_00_u03c3_1702_, lean_object* v_00_u03c1_1703_, lean_object* v_pat_1704_, lean_object* v_s_1705_, lean_object* v_inst_1706_, lean_object* v_motive_1707_, lean_object* v_ctorIdx_1708_, lean_object* v_t_1709_, lean_object* v_h_1710_, lean_object* v_k_1711_){
_start:
{
lean_object* v___x_1712_; 
v___x_1712_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1709_, v_k_1711_);
return v___x_1712_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_1713_, lean_object* v_00_u03c1_1714_, lean_object* v_pat_1715_, lean_object* v_s_1716_, lean_object* v_inst_1717_, lean_object* v_motive_1718_, lean_object* v_ctorIdx_1719_, lean_object* v_t_1720_, lean_object* v_h_1721_, lean_object* v_k_1722_){
_start:
{
lean_object* v_res_1723_; 
v_res_1723_ = l_String_Slice_RevSplitIterator_ctorElim(v_00_u03c3_1713_, v_00_u03c1_1714_, v_pat_1715_, v_s_1716_, v_inst_1717_, v_motive_1718_, v_ctorIdx_1719_, v_t_1720_, v_h_1721_, v_k_1722_);
lean_dec(v_ctorIdx_1719_);
lean_dec(v_inst_1717_);
lean_dec_ref(v_s_1716_);
lean_dec(v_pat_1715_);
return v_res_1723_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___redArg(lean_object* v_t_1724_, lean_object* v_operating_1725_){
_start:
{
lean_object* v___x_1726_; 
v___x_1726_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1724_, v_operating_1725_);
return v___x_1726_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim(lean_object* v_00_u03c3_1727_, lean_object* v_00_u03c1_1728_, lean_object* v_pat_1729_, lean_object* v_s_1730_, lean_object* v_inst_1731_, lean_object* v_motive_1732_, lean_object* v_t_1733_, lean_object* v_h_1734_, lean_object* v_operating_1735_){
_start:
{
lean_object* v___x_1736_; 
v___x_1736_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1733_, v_operating_1735_);
return v___x_1736_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_1737_, lean_object* v_00_u03c1_1738_, lean_object* v_pat_1739_, lean_object* v_s_1740_, lean_object* v_inst_1741_, lean_object* v_motive_1742_, lean_object* v_t_1743_, lean_object* v_h_1744_, lean_object* v_operating_1745_){
_start:
{
lean_object* v_res_1746_; 
v_res_1746_ = l_String_Slice_RevSplitIterator_operating_elim(v_00_u03c3_1737_, v_00_u03c1_1738_, v_pat_1739_, v_s_1740_, v_inst_1741_, v_motive_1742_, v_t_1743_, v_h_1744_, v_operating_1745_);
lean_dec(v_inst_1741_);
lean_dec_ref(v_s_1740_);
lean_dec(v_pat_1739_);
return v_res_1746_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___redArg(lean_object* v_t_1747_, lean_object* v_atEnd_1748_){
_start:
{
lean_object* v___x_1749_; 
v___x_1749_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1747_, v_atEnd_1748_);
return v___x_1749_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim(lean_object* v_00_u03c3_1750_, lean_object* v_00_u03c1_1751_, lean_object* v_pat_1752_, lean_object* v_s_1753_, lean_object* v_inst_1754_, lean_object* v_motive_1755_, lean_object* v_t_1756_, lean_object* v_h_1757_, lean_object* v_atEnd_1758_){
_start:
{
lean_object* v___x_1759_; 
v___x_1759_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1756_, v_atEnd_1758_);
return v___x_1759_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_1760_, lean_object* v_00_u03c1_1761_, lean_object* v_pat_1762_, lean_object* v_s_1763_, lean_object* v_inst_1764_, lean_object* v_motive_1765_, lean_object* v_t_1766_, lean_object* v_h_1767_, lean_object* v_atEnd_1768_){
_start:
{
lean_object* v_res_1769_; 
v_res_1769_ = l_String_Slice_RevSplitIterator_atEnd_elim(v_00_u03c3_1760_, v_00_u03c1_1761_, v_pat_1762_, v_s_1763_, v_inst_1764_, v_motive_1765_, v_t_1766_, v_h_1767_, v_atEnd_1768_);
lean_dec(v_inst_1764_);
lean_dec_ref(v_s_1763_);
lean_dec(v_pat_1762_);
return v_res_1769_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default(lean_object* v_a_1770_, lean_object* v_a_1771_, lean_object* v_a_1772_, lean_object* v_a_1773_, lean_object* v_a_1774_){
_start:
{
lean_object* v___x_1775_; 
v___x_1775_ = lean_box(1);
return v___x_1775_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___boxed(lean_object* v_a_1776_, lean_object* v_a_1777_, lean_object* v_a_1778_, lean_object* v_a_1779_, lean_object* v_a_1780_){
_start:
{
lean_object* v_res_1781_; 
v_res_1781_ = l_String_Slice_instInhabitedRevSplitIterator_default(v_a_1776_, v_a_1777_, v_a_1778_, v_a_1779_, v_a_1780_);
lean_dec(v_a_1780_);
lean_dec_ref(v_a_1779_);
lean_dec(v_a_1778_);
return v_res_1781_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator(lean_object* v_a_1782_, lean_object* v_a_1783_, lean_object* v_a_1784_, lean_object* v_a_1785_, lean_object* v_a_1786_){
_start:
{
lean_object* v___x_1787_; 
v___x_1787_ = lean_box(1);
return v___x_1787_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___boxed(lean_object* v_a_1788_, lean_object* v_a_1789_, lean_object* v_a_1790_, lean_object* v_a_1791_, lean_object* v_a_1792_){
_start:
{
lean_object* v_res_1793_; 
v_res_1793_ = l_String_Slice_instInhabitedRevSplitIterator(v_a_1788_, v_a_1789_, v_a_1790_, v_a_1791_, v_a_1792_);
lean_dec(v_a_1792_);
lean_dec_ref(v_a_1791_);
lean_dec(v_a_1790_);
return v_res_1793_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0(lean_object* v_inst_1794_, lean_object* v_s_1795_, lean_object* v_inst_1796_, lean_object* v_x_1797_){
_start:
{
if (lean_obj_tag(v_x_1797_) == 0)
{
lean_object* v_currPos_1798_; lean_object* v_searcher_1799_; lean_object* v___x_1801_; uint8_t v_isShared_1802_; uint8_t v_isSharedCheck_1857_; 
v_currPos_1798_ = lean_ctor_get(v_x_1797_, 0);
v_searcher_1799_ = lean_ctor_get(v_x_1797_, 1);
v_isSharedCheck_1857_ = !lean_is_exclusive(v_x_1797_);
if (v_isSharedCheck_1857_ == 0)
{
v___x_1801_ = v_x_1797_;
v_isShared_1802_ = v_isSharedCheck_1857_;
goto v_resetjp_1800_;
}
else
{
lean_inc(v_searcher_1799_);
lean_inc(v_currPos_1798_);
lean_dec(v_x_1797_);
v___x_1801_ = lean_box(0);
v_isShared_1802_ = v_isSharedCheck_1857_;
goto v_resetjp_1800_;
}
v_resetjp_1800_:
{
lean_object* v___x_1803_; 
lean_inc_ref(v_s_1795_);
v___x_1803_ = lean_apply_2(v_inst_1794_, v_s_1795_, v_searcher_1799_);
switch(lean_obj_tag(v___x_1803_))
{
case 0:
{
lean_object* v_out_1804_; 
v_out_1804_ = lean_ctor_get(v___x_1803_, 1);
lean_inc(v_out_1804_);
if (lean_obj_tag(v_out_1804_) == 0)
{
lean_object* v_it_1805_; lean_object* v___x_1807_; 
lean_dec_ref(v_out_1804_);
lean_dec_ref(v_s_1795_);
v_it_1805_ = lean_ctor_get(v___x_1803_, 0);
lean_inc(v_it_1805_);
lean_dec_ref(v___x_1803_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v_it_1805_);
v___x_1807_ = v___x_1801_;
goto v_reusejp_1806_;
}
else
{
lean_object* v_reuseFailAlloc_1810_; 
v_reuseFailAlloc_1810_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1810_, 0, v_currPos_1798_);
lean_ctor_set(v_reuseFailAlloc_1810_, 1, v_it_1805_);
v___x_1807_ = v_reuseFailAlloc_1810_;
goto v_reusejp_1806_;
}
v_reusejp_1806_:
{
lean_object* v___x_1808_; lean_object* v___x_1809_; 
v___x_1808_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1808_, 0, v___x_1807_);
v___x_1809_ = lean_apply_2(v_inst_1796_, lean_box(0), v___x_1808_);
return v___x_1809_;
}
}
else
{
lean_object* v_it_1811_; lean_object* v___x_1813_; uint8_t v_isShared_1814_; uint8_t v_isSharedCheck_1825_; 
v_it_1811_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1825_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1825_ == 0)
{
lean_object* v_unused_1826_; 
v_unused_1826_ = lean_ctor_get(v___x_1803_, 1);
lean_dec(v_unused_1826_);
v___x_1813_ = v___x_1803_;
v_isShared_1814_ = v_isSharedCheck_1825_;
goto v_resetjp_1812_;
}
else
{
lean_inc(v_it_1811_);
lean_dec(v___x_1803_);
v___x_1813_ = lean_box(0);
v_isShared_1814_ = v_isSharedCheck_1825_;
goto v_resetjp_1812_;
}
v_resetjp_1812_:
{
lean_object* v_startPos_1815_; lean_object* v_endPos_1816_; lean_object* v_slice_1817_; lean_object* v_nextIt_1819_; 
v_startPos_1815_ = lean_ctor_get(v_out_1804_, 0);
lean_inc(v_startPos_1815_);
v_endPos_1816_ = lean_ctor_get(v_out_1804_, 1);
lean_inc(v_endPos_1816_);
lean_dec_ref(v_out_1804_);
v_slice_1817_ = l_String_Slice_slice_x21(v_s_1795_, v_endPos_1816_, v_currPos_1798_);
lean_dec(v_currPos_1798_);
lean_dec(v_endPos_1816_);
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v_it_1811_);
lean_ctor_set(v___x_1801_, 0, v_startPos_1815_);
v_nextIt_1819_ = v___x_1801_;
goto v_reusejp_1818_;
}
else
{
lean_object* v_reuseFailAlloc_1824_; 
v_reuseFailAlloc_1824_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1824_, 0, v_startPos_1815_);
lean_ctor_set(v_reuseFailAlloc_1824_, 1, v_it_1811_);
v_nextIt_1819_ = v_reuseFailAlloc_1824_;
goto v_reusejp_1818_;
}
v_reusejp_1818_:
{
lean_object* v___x_1821_; 
if (v_isShared_1814_ == 0)
{
lean_ctor_set(v___x_1813_, 1, v_slice_1817_);
lean_ctor_set(v___x_1813_, 0, v_nextIt_1819_);
v___x_1821_ = v___x_1813_;
goto v_reusejp_1820_;
}
else
{
lean_object* v_reuseFailAlloc_1823_; 
v_reuseFailAlloc_1823_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1823_, 0, v_nextIt_1819_);
lean_ctor_set(v_reuseFailAlloc_1823_, 1, v_slice_1817_);
v___x_1821_ = v_reuseFailAlloc_1823_;
goto v_reusejp_1820_;
}
v_reusejp_1820_:
{
lean_object* v___x_1822_; 
v___x_1822_ = lean_apply_2(v_inst_1796_, lean_box(0), v___x_1821_);
return v___x_1822_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1827_; lean_object* v___x_1829_; uint8_t v_isShared_1830_; uint8_t v_isSharedCheck_1838_; 
lean_dec_ref(v_s_1795_);
v_it_1827_ = lean_ctor_get(v___x_1803_, 0);
v_isSharedCheck_1838_ = !lean_is_exclusive(v___x_1803_);
if (v_isSharedCheck_1838_ == 0)
{
v___x_1829_ = v___x_1803_;
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
else
{
lean_inc(v_it_1827_);
lean_dec(v___x_1803_);
v___x_1829_ = lean_box(0);
v_isShared_1830_ = v_isSharedCheck_1838_;
goto v_resetjp_1828_;
}
v_resetjp_1828_:
{
lean_object* v___x_1832_; 
if (v_isShared_1802_ == 0)
{
lean_ctor_set(v___x_1801_, 1, v_it_1827_);
v___x_1832_ = v___x_1801_;
goto v_reusejp_1831_;
}
else
{
lean_object* v_reuseFailAlloc_1837_; 
v_reuseFailAlloc_1837_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1837_, 0, v_currPos_1798_);
lean_ctor_set(v_reuseFailAlloc_1837_, 1, v_it_1827_);
v___x_1832_ = v_reuseFailAlloc_1837_;
goto v_reusejp_1831_;
}
v_reusejp_1831_:
{
lean_object* v___x_1834_; 
if (v_isShared_1830_ == 0)
{
lean_ctor_set(v___x_1829_, 0, v___x_1832_);
v___x_1834_ = v___x_1829_;
goto v_reusejp_1833_;
}
else
{
lean_object* v_reuseFailAlloc_1836_; 
v_reuseFailAlloc_1836_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1836_, 0, v___x_1832_);
v___x_1834_ = v_reuseFailAlloc_1836_;
goto v_reusejp_1833_;
}
v_reusejp_1833_:
{
lean_object* v___x_1835_; 
v___x_1835_ = lean_apply_2(v_inst_1796_, lean_box(0), v___x_1834_);
return v___x_1835_;
}
}
}
}
default: 
{
lean_object* v___x_1839_; uint8_t v___x_1840_; 
lean_del_object(v___x_1801_);
v___x_1839_ = lean_unsigned_to_nat(0u);
v___x_1840_ = lean_nat_dec_eq(v_currPos_1798_, v___x_1839_);
if (v___x_1840_ == 0)
{
lean_object* v_str_1841_; lean_object* v_startInclusive_1842_; lean_object* v___x_1844_; uint8_t v_isShared_1845_; uint8_t v_isSharedCheck_1853_; 
v_str_1841_ = lean_ctor_get(v_s_1795_, 0);
v_startInclusive_1842_ = lean_ctor_get(v_s_1795_, 1);
v_isSharedCheck_1853_ = !lean_is_exclusive(v_s_1795_);
if (v_isSharedCheck_1853_ == 0)
{
lean_object* v_unused_1854_; 
v_unused_1854_ = lean_ctor_get(v_s_1795_, 2);
lean_dec(v_unused_1854_);
v___x_1844_ = v_s_1795_;
v_isShared_1845_ = v_isSharedCheck_1853_;
goto v_resetjp_1843_;
}
else
{
lean_inc(v_startInclusive_1842_);
lean_inc(v_str_1841_);
lean_dec(v_s_1795_);
v___x_1844_ = lean_box(0);
v_isShared_1845_ = v_isSharedCheck_1853_;
goto v_resetjp_1843_;
}
v_resetjp_1843_:
{
lean_object* v___x_1846_; lean_object* v_slice_1848_; 
v___x_1846_ = lean_nat_add(v_startInclusive_1842_, v_currPos_1798_);
lean_dec(v_currPos_1798_);
if (v_isShared_1845_ == 0)
{
lean_ctor_set(v___x_1844_, 2, v___x_1846_);
v_slice_1848_ = v___x_1844_;
goto v_reusejp_1847_;
}
else
{
lean_object* v_reuseFailAlloc_1852_; 
v_reuseFailAlloc_1852_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1852_, 0, v_str_1841_);
lean_ctor_set(v_reuseFailAlloc_1852_, 1, v_startInclusive_1842_);
lean_ctor_set(v_reuseFailAlloc_1852_, 2, v___x_1846_);
v_slice_1848_ = v_reuseFailAlloc_1852_;
goto v_reusejp_1847_;
}
v_reusejp_1847_:
{
lean_object* v___x_1849_; lean_object* v___x_1850_; lean_object* v___x_1851_; 
v___x_1849_ = lean_box(1);
v___x_1850_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1850_, 0, v___x_1849_);
lean_ctor_set(v___x_1850_, 1, v_slice_1848_);
v___x_1851_ = lean_apply_2(v_inst_1796_, lean_box(0), v___x_1850_);
return v___x_1851_;
}
}
}
else
{
lean_object* v___x_1855_; lean_object* v___x_1856_; 
lean_dec(v_currPos_1798_);
lean_dec_ref(v_s_1795_);
v___x_1855_ = lean_box(2);
v___x_1856_ = lean_apply_2(v_inst_1796_, lean_box(0), v___x_1855_);
return v___x_1856_;
}
}
}
}
}
else
{
lean_object* v___x_1858_; lean_object* v___x_1859_; 
lean_dec_ref(v_s_1795_);
lean_dec(v_inst_1794_);
v___x_1858_ = lean_box(2);
v___x_1859_ = lean_apply_2(v_inst_1796_, lean_box(0), v___x_1858_);
return v___x_1859_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg(lean_object* v_inst_1860_, lean_object* v_s_1861_, lean_object* v_inst_1862_){
_start:
{
lean_object* v___f_1863_; 
v___f_1863_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1863_, 0, v_inst_1860_);
lean_closure_set(v___f_1863_, 1, v_s_1861_);
lean_closure_set(v___f_1863_, 2, v_inst_1862_);
return v___f_1863_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure(lean_object* v_00_u03c1_1864_, lean_object* v_00_u03c1_1865_, lean_object* v_00_u03c3_1866_, lean_object* v_inst_1867_, lean_object* v_inst_1868_, lean_object* v_m_1869_, lean_object* v_s_1870_, lean_object* v_inst_1871_){
_start:
{
lean_object* v___f_1872_; 
v___f_1872_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1872_, 0, v_inst_1867_);
lean_closure_set(v___f_1872_, 1, v_s_1870_);
lean_closure_set(v___f_1872_, 2, v_inst_1871_);
return v___f_1872_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___boxed(lean_object* v_00_u03c1_1873_, lean_object* v_00_u03c1_1874_, lean_object* v_00_u03c3_1875_, lean_object* v_inst_1876_, lean_object* v_inst_1877_, lean_object* v_m_1878_, lean_object* v_s_1879_, lean_object* v_inst_1880_){
_start:
{
lean_object* v_res_1881_; 
v_res_1881_ = l_String_Slice_RevSplitIterator_instIteratorOfPure(v_00_u03c1_1873_, v_00_u03c1_1874_, v_00_u03c3_1875_, v_inst_1876_, v_inst_1877_, v_m_1878_, v_s_1879_, v_inst_1880_);
lean_dec(v_inst_1877_);
lean_dec(v_00_u03c1_1874_);
return v_res_1881_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(lean_object* v_x_1882_){
_start:
{
if (lean_obj_tag(v_x_1882_) == 0)
{
lean_object* v_searcher_1883_; lean_object* v___x_1884_; 
v_searcher_1883_ = lean_ctor_get(v_x_1882_, 1);
lean_inc(v_searcher_1883_);
v___x_1884_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1884_, 0, v_searcher_1883_);
return v___x_1884_;
}
else
{
lean_object* v___x_1885_; 
v___x_1885_ = lean_box(0);
return v___x_1885_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg___boxed(lean_object* v_x_1886_){
_start:
{
lean_object* v_res_1887_; 
v_res_1887_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_1886_);
lean_dec(v_x_1886_);
return v_res_1887_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(lean_object* v_00_u03c1_1888_, lean_object* v_00_u03c1_1889_, lean_object* v_00_u03c3_1890_, lean_object* v_inst_1891_, lean_object* v_s_1892_, lean_object* v_x_1893_){
_start:
{
lean_object* v___x_1894_; 
v___x_1894_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___boxed(lean_object* v_00_u03c1_1895_, lean_object* v_00_u03c1_1896_, lean_object* v_00_u03c3_1897_, lean_object* v_inst_1898_, lean_object* v_s_1899_, lean_object* v_x_1900_){
_start:
{
lean_object* v_res_1901_; 
v_res_1901_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(v_00_u03c1_1895_, v_00_u03c1_1896_, v_00_u03c3_1897_, v_inst_1898_, v_s_1899_, v_x_1900_);
lean_dec(v_x_1900_);
lean_dec_ref(v_s_1899_);
lean_dec(v_inst_1898_);
lean_dec(v_00_u03c1_1896_);
return v_res_1901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(lean_object* v_x_1902_, lean_object* v_h__1_1903_, lean_object* v_h__2_1904_){
_start:
{
if (lean_obj_tag(v_x_1902_) == 0)
{
lean_object* v_currPos_1905_; lean_object* v_searcher_1906_; lean_object* v___x_1907_; 
lean_dec(v_h__2_1904_);
v_currPos_1905_ = lean_ctor_get(v_x_1902_, 0);
lean_inc(v_currPos_1905_);
v_searcher_1906_ = lean_ctor_get(v_x_1902_, 1);
lean_inc(v_searcher_1906_);
lean_dec_ref(v_x_1902_);
v___x_1907_ = lean_apply_2(v_h__1_1903_, v_currPos_1905_, v_searcher_1906_);
return v___x_1907_;
}
else
{
lean_object* v___x_1908_; lean_object* v___x_1909_; 
lean_dec(v_h__1_1903_);
v___x_1908_ = lean_box(0);
v___x_1909_ = lean_apply_1(v_h__2_1904_, v___x_1908_);
return v___x_1909_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(lean_object* v_00_u03c1_1910_, lean_object* v_00_u03c1_1911_, lean_object* v_00_u03c3_1912_, lean_object* v_inst_1913_, lean_object* v_m_1914_, lean_object* v_s_1915_, lean_object* v_motive_1916_, lean_object* v_x_1917_, lean_object* v_h__1_1918_, lean_object* v_h__2_1919_){
_start:
{
lean_object* v___x_1920_; 
v___x_1920_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(v_x_1917_, v_h__1_1918_, v_h__2_1919_);
return v___x_1920_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___boxed(lean_object* v_00_u03c1_1921_, lean_object* v_00_u03c1_1922_, lean_object* v_00_u03c3_1923_, lean_object* v_inst_1924_, lean_object* v_m_1925_, lean_object* v_s_1926_, lean_object* v_motive_1927_, lean_object* v_x_1928_, lean_object* v_h__1_1929_, lean_object* v_h__2_1930_){
_start:
{
lean_object* v_res_1931_; 
v_res_1931_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(v_00_u03c1_1921_, v_00_u03c1_1922_, v_00_u03c3_1923_, v_inst_1924_, v_m_1925_, v_s_1926_, v_motive_1927_, v_x_1928_, v_h__1_1929_, v_h__2_1930_);
lean_dec_ref(v_s_1926_);
lean_dec(v_inst_1924_);
lean_dec(v_00_u03c1_1922_);
return v_res_1931_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(lean_object* v_x_1932_, lean_object* v_x_1933_, lean_object* v_h__1_1934_, lean_object* v_h__2_1935_, lean_object* v_h__3_1936_, lean_object* v_h__4_1937_, lean_object* v_h__5_1938_, lean_object* v_h__6_1939_, lean_object* v_h__7_1940_, lean_object* v_h__8_1941_){
_start:
{
if (lean_obj_tag(v_x_1932_) == 0)
{
lean_dec(v_h__8_1941_);
lean_dec(v_h__7_1940_);
lean_dec(v_h__6_1939_);
switch(lean_obj_tag(v_x_1933_))
{
case 0:
{
lean_object* v_it_1942_; 
lean_dec(v_h__5_1938_);
lean_dec(v_h__4_1937_);
lean_dec(v_h__3_1936_);
v_it_1942_ = lean_ctor_get(v_x_1933_, 0);
if (lean_obj_tag(v_it_1942_) == 0)
{
lean_object* v_currPos_1943_; lean_object* v_searcher_1944_; lean_object* v_out_1945_; lean_object* v_currPos_1946_; lean_object* v_searcher_1947_; lean_object* v___x_1948_; 
lean_inc_ref(v_it_1942_);
lean_dec(v_h__2_1935_);
v_currPos_1943_ = lean_ctor_get(v_x_1932_, 0);
lean_inc(v_currPos_1943_);
v_searcher_1944_ = lean_ctor_get(v_x_1932_, 1);
lean_inc(v_searcher_1944_);
lean_dec_ref(v_x_1932_);
v_out_1945_ = lean_ctor_get(v_x_1933_, 1);
lean_inc(v_out_1945_);
lean_dec_ref(v_x_1933_);
v_currPos_1946_ = lean_ctor_get(v_it_1942_, 0);
lean_inc(v_currPos_1946_);
v_searcher_1947_ = lean_ctor_get(v_it_1942_, 1);
lean_inc(v_searcher_1947_);
lean_dec_ref(v_it_1942_);
v___x_1948_ = lean_apply_5(v_h__1_1934_, v_currPos_1943_, v_searcher_1944_, v_currPos_1946_, v_searcher_1947_, v_out_1945_);
return v___x_1948_;
}
else
{
lean_object* v_currPos_1949_; lean_object* v_searcher_1950_; lean_object* v_out_1951_; lean_object* v___x_1952_; 
lean_dec(v_h__1_1934_);
v_currPos_1949_ = lean_ctor_get(v_x_1932_, 0);
lean_inc(v_currPos_1949_);
v_searcher_1950_ = lean_ctor_get(v_x_1932_, 1);
lean_inc(v_searcher_1950_);
lean_dec_ref(v_x_1932_);
v_out_1951_ = lean_ctor_get(v_x_1933_, 1);
lean_inc(v_out_1951_);
lean_dec_ref(v_x_1933_);
v___x_1952_ = lean_apply_3(v_h__2_1935_, v_currPos_1949_, v_searcher_1950_, v_out_1951_);
return v___x_1952_;
}
}
case 1:
{
lean_object* v_it_1953_; 
lean_dec(v_h__5_1938_);
lean_dec(v_h__2_1935_);
lean_dec(v_h__1_1934_);
v_it_1953_ = lean_ctor_get(v_x_1933_, 0);
lean_inc(v_it_1953_);
lean_dec_ref(v_x_1933_);
if (lean_obj_tag(v_it_1953_) == 0)
{
lean_object* v_currPos_1954_; lean_object* v_searcher_1955_; lean_object* v_currPos_1956_; lean_object* v_searcher_1957_; lean_object* v___x_1958_; 
lean_dec(v_h__4_1937_);
v_currPos_1954_ = lean_ctor_get(v_x_1932_, 0);
lean_inc(v_currPos_1954_);
v_searcher_1955_ = lean_ctor_get(v_x_1932_, 1);
lean_inc(v_searcher_1955_);
lean_dec_ref(v_x_1932_);
v_currPos_1956_ = lean_ctor_get(v_it_1953_, 0);
lean_inc(v_currPos_1956_);
v_searcher_1957_ = lean_ctor_get(v_it_1953_, 1);
lean_inc(v_searcher_1957_);
lean_dec_ref(v_it_1953_);
v___x_1958_ = lean_apply_4(v_h__3_1936_, v_currPos_1954_, v_searcher_1955_, v_currPos_1956_, v_searcher_1957_);
return v___x_1958_;
}
else
{
lean_object* v_currPos_1959_; lean_object* v_searcher_1960_; lean_object* v___x_1961_; 
lean_dec(v_h__3_1936_);
v_currPos_1959_ = lean_ctor_get(v_x_1932_, 0);
lean_inc(v_currPos_1959_);
v_searcher_1960_ = lean_ctor_get(v_x_1932_, 1);
lean_inc(v_searcher_1960_);
lean_dec_ref(v_x_1932_);
v___x_1961_ = lean_apply_2(v_h__4_1937_, v_currPos_1959_, v_searcher_1960_);
return v___x_1961_;
}
}
default: 
{
lean_object* v_currPos_1962_; lean_object* v_searcher_1963_; lean_object* v___x_1964_; 
lean_dec(v_h__4_1937_);
lean_dec(v_h__3_1936_);
lean_dec(v_h__2_1935_);
lean_dec(v_h__1_1934_);
v_currPos_1962_ = lean_ctor_get(v_x_1932_, 0);
lean_inc(v_currPos_1962_);
v_searcher_1963_ = lean_ctor_get(v_x_1932_, 1);
lean_inc(v_searcher_1963_);
lean_dec_ref(v_x_1932_);
v___x_1964_ = lean_apply_2(v_h__5_1938_, v_currPos_1962_, v_searcher_1963_);
return v___x_1964_;
}
}
}
else
{
lean_dec(v_h__5_1938_);
lean_dec(v_h__4_1937_);
lean_dec(v_h__3_1936_);
lean_dec(v_h__2_1935_);
lean_dec(v_h__1_1934_);
switch(lean_obj_tag(v_x_1933_))
{
case 0:
{
lean_object* v_it_1965_; lean_object* v_out_1966_; lean_object* v___x_1967_; 
lean_dec(v_h__8_1941_);
lean_dec(v_h__7_1940_);
v_it_1965_ = lean_ctor_get(v_x_1933_, 0);
lean_inc(v_it_1965_);
v_out_1966_ = lean_ctor_get(v_x_1933_, 1);
lean_inc(v_out_1966_);
lean_dec_ref(v_x_1933_);
v___x_1967_ = lean_apply_2(v_h__6_1939_, v_it_1965_, v_out_1966_);
return v___x_1967_;
}
case 1:
{
lean_object* v_it_1968_; lean_object* v___x_1969_; 
lean_dec(v_h__8_1941_);
lean_dec(v_h__6_1939_);
v_it_1968_ = lean_ctor_get(v_x_1933_, 0);
lean_inc(v_it_1968_);
lean_dec_ref(v_x_1933_);
v___x_1969_ = lean_apply_1(v_h__7_1940_, v_it_1968_);
return v___x_1969_;
}
default: 
{
lean_object* v___x_1970_; lean_object* v___x_1971_; 
lean_dec(v_h__7_1940_);
lean_dec(v_h__6_1939_);
v___x_1970_ = lean_box(0);
v___x_1971_ = lean_apply_1(v_h__8_1941_, v___x_1970_);
return v___x_1971_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(lean_object* v_00_u03c1_1972_, lean_object* v_00_u03c1_1973_, lean_object* v_00_u03c3_1974_, lean_object* v_inst_1975_, lean_object* v_m_1976_, lean_object* v_s_1977_, lean_object* v_motive_1978_, lean_object* v_x_1979_, lean_object* v_x_1980_, lean_object* v_h__1_1981_, lean_object* v_h__2_1982_, lean_object* v_h__3_1983_, lean_object* v_h__4_1984_, lean_object* v_h__5_1985_, lean_object* v_h__6_1986_, lean_object* v_h__7_1987_, lean_object* v_h__8_1988_){
_start:
{
lean_object* v___x_1989_; 
v___x_1989_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(v_x_1979_, v_x_1980_, v_h__1_1981_, v_h__2_1982_, v_h__3_1983_, v_h__4_1984_, v_h__5_1985_, v_h__6_1986_, v_h__7_1987_, v_h__8_1988_);
return v___x_1989_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___boxed(lean_object** _args){
lean_object* v_00_u03c1_1990_ = _args[0];
lean_object* v_00_u03c1_1991_ = _args[1];
lean_object* v_00_u03c3_1992_ = _args[2];
lean_object* v_inst_1993_ = _args[3];
lean_object* v_m_1994_ = _args[4];
lean_object* v_s_1995_ = _args[5];
lean_object* v_motive_1996_ = _args[6];
lean_object* v_x_1997_ = _args[7];
lean_object* v_x_1998_ = _args[8];
lean_object* v_h__1_1999_ = _args[9];
lean_object* v_h__2_2000_ = _args[10];
lean_object* v_h__3_2001_ = _args[11];
lean_object* v_h__4_2002_ = _args[12];
lean_object* v_h__5_2003_ = _args[13];
lean_object* v_h__6_2004_ = _args[14];
lean_object* v_h__7_2005_ = _args[15];
lean_object* v_h__8_2006_ = _args[16];
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(v_00_u03c1_1990_, v_00_u03c1_1991_, v_00_u03c3_1992_, v_inst_1993_, v_m_1994_, v_s_1995_, v_motive_1996_, v_x_1997_, v_x_1998_, v_h__1_1999_, v_h__2_2000_, v_h__3_2001_, v_h__4_2002_, v_h__5_2003_, v_h__6_2004_, v_h__7_2005_, v_h__8_2006_);
lean_dec_ref(v_s_1995_);
lean_dec(v_inst_1993_);
lean_dec(v_00_u03c1_1991_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___redArg(lean_object* v_x_2008_, lean_object* v_h__1_2009_, lean_object* v_h__2_2010_){
_start:
{
if (lean_obj_tag(v_x_2008_) == 0)
{
lean_object* v_currPos_2011_; lean_object* v_searcher_2012_; lean_object* v___x_2013_; 
lean_dec(v_h__2_2010_);
v_currPos_2011_ = lean_ctor_get(v_x_2008_, 0);
lean_inc(v_currPos_2011_);
v_searcher_2012_ = lean_ctor_get(v_x_2008_, 1);
lean_inc(v_searcher_2012_);
lean_dec_ref(v_x_2008_);
v___x_2013_ = lean_apply_2(v_h__1_2009_, v_currPos_2011_, v_searcher_2012_);
return v___x_2013_;
}
else
{
lean_object* v___x_2014_; lean_object* v___x_2015_; 
lean_dec(v_h__1_2009_);
v___x_2014_ = lean_box(0);
v___x_2015_ = lean_apply_1(v_h__2_2010_, v___x_2014_);
return v___x_2015_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_2016_, lean_object* v_00_u03c1_2017_, lean_object* v_00_u03c3_2018_, lean_object* v_inst_2019_, lean_object* v_s_2020_, lean_object* v_motive_2021_, lean_object* v_x_2022_, lean_object* v_h__1_2023_, lean_object* v_h__2_2024_){
_start:
{
lean_object* v___x_2025_; 
v___x_2025_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___redArg(v_x_2022_, v_h__1_2023_, v_h__2_2024_);
return v___x_2025_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_2026_, lean_object* v_00_u03c1_2027_, lean_object* v_00_u03c3_2028_, lean_object* v_inst_2029_, lean_object* v_s_2030_, lean_object* v_motive_2031_, lean_object* v_x_2032_, lean_object* v_h__1_2033_, lean_object* v_h__2_2034_){
_start:
{
lean_object* v_res_2035_; 
v_res_2035_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(v_00_u03c1_2026_, v_00_u03c1_2027_, v_00_u03c3_2028_, v_inst_2029_, v_s_2030_, v_motive_2031_, v_x_2032_, v_h__1_2033_, v_h__2_2034_);
lean_dec_ref(v_s_2030_);
lean_dec(v_inst_2029_);
lean_dec(v_00_u03c1_2027_);
return v_res_2035_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(lean_object* v_00_u03c1_2036_, lean_object* v_00_u03c1_2037_, lean_object* v_00_u03c3_2038_, lean_object* v_inst_2039_, lean_object* v_inst_2040_, lean_object* v_s_2041_, lean_object* v_inst_2042_){
_start:
{
lean_object* v___x_2043_; 
v___x_2043_ = lean_box(0);
return v___x_2043_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_2044_, lean_object* v_00_u03c1_2045_, lean_object* v_00_u03c3_2046_, lean_object* v_inst_2047_, lean_object* v_inst_2048_, lean_object* v_s_2049_, lean_object* v_inst_2050_){
_start:
{
lean_object* v_res_2051_; 
v_res_2051_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(v_00_u03c1_2044_, v_00_u03c1_2045_, v_00_u03c3_2046_, v_inst_2047_, v_inst_2048_, v_s_2049_, v_inst_2050_);
lean_dec_ref(v_s_2049_);
lean_dec(v_inst_2048_);
lean_dec(v_inst_2047_);
lean_dec(v_00_u03c1_2045_);
return v_res_2051_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object* v_toPure_2052_, lean_object* v_recur_2053_, lean_object* v_it_2054_, lean_object* v_____do__lift_2055_){
_start:
{
if (lean_obj_tag(v_____do__lift_2055_) == 0)
{
lean_object* v_a_2056_; lean_object* v___x_2057_; 
lean_dec(v_it_2054_);
lean_dec(v_recur_2053_);
v_a_2056_ = lean_ctor_get(v_____do__lift_2055_, 0);
lean_inc(v_a_2056_);
lean_dec_ref(v_____do__lift_2055_);
v___x_2057_ = lean_apply_2(v_toPure_2052_, lean_box(0), v_a_2056_);
return v___x_2057_;
}
else
{
lean_object* v_a_2058_; lean_object* v___x_2059_; 
lean_dec(v_toPure_2052_);
v_a_2058_ = lean_ctor_get(v_____do__lift_2055_, 0);
lean_inc(v_a_2058_);
lean_dec_ref(v_____do__lift_2055_);
v___x_2059_ = lean_apply_4(v_recur_2053_, v_it_2054_, v_a_2058_, lean_box(0), lean_box(0));
return v___x_2059_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object* v_toPure_2060_, lean_object* v_recur_2061_, lean_object* v___y_2062_, lean_object* v_acc_2063_, lean_object* v_toBind_2064_, lean_object* v_s_2065_){
_start:
{
switch(lean_obj_tag(v_s_2065_))
{
case 0:
{
lean_object* v_it_2066_; lean_object* v_out_2067_; lean_object* v___f_2068_; lean_object* v___x_2069_; lean_object* v___x_2070_; 
v_it_2066_ = lean_ctor_get(v_s_2065_, 0);
lean_inc(v_it_2066_);
v_out_2067_ = lean_ctor_get(v_s_2065_, 1);
lean_inc(v_out_2067_);
lean_dec_ref(v_s_2065_);
v___f_2068_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2068_, 0, v_toPure_2060_);
lean_closure_set(v___f_2068_, 1, v_recur_2061_);
lean_closure_set(v___f_2068_, 2, v_it_2066_);
v___x_2069_ = lean_apply_3(v___y_2062_, v_out_2067_, lean_box(0), v_acc_2063_);
v___x_2070_ = lean_apply_4(v_toBind_2064_, lean_box(0), lean_box(0), v___x_2069_, v___f_2068_);
return v___x_2070_;
}
case 1:
{
lean_object* v_it_2071_; lean_object* v___x_2072_; 
lean_dec(v_toBind_2064_);
lean_dec(v___y_2062_);
lean_dec(v_toPure_2060_);
v_it_2071_ = lean_ctor_get(v_s_2065_, 0);
lean_inc(v_it_2071_);
lean_dec_ref(v_s_2065_);
v___x_2072_ = lean_apply_4(v_recur_2061_, v_it_2071_, v_acc_2063_, lean_box(0), lean_box(0));
return v___x_2072_;
}
default: 
{
lean_object* v___x_2073_; 
lean_dec(v_toBind_2064_);
lean_dec(v___y_2062_);
lean_dec(v_recur_2061_);
v___x_2073_ = lean_apply_2(v_toPure_2060_, lean_box(0), v_acc_2063_);
return v___x_2073_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object* v_toPure_2074_, lean_object* v___y_2075_, lean_object* v_toBind_2076_, lean_object* v_inst_2077_, lean_object* v_s_2078_, lean_object* v_toPure_2079_, lean_object* v_lift_2080_, lean_object* v_it_2081_, lean_object* v_acc_2082_, lean_object* v_hP_2083_, lean_object* v_recur_2084_){
_start:
{
lean_object* v___f_2085_; 
v___f_2085_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2085_, 0, v_toPure_2074_);
lean_closure_set(v___f_2085_, 1, v_recur_2084_);
lean_closure_set(v___f_2085_, 2, v___y_2075_);
lean_closure_set(v___f_2085_, 3, v_acc_2082_);
lean_closure_set(v___f_2085_, 4, v_toBind_2076_);
if (lean_obj_tag(v_it_2081_) == 0)
{
lean_object* v_currPos_2086_; lean_object* v_searcher_2087_; lean_object* v___x_2089_; uint8_t v_isShared_2090_; uint8_t v_isSharedCheck_2150_; 
v_currPos_2086_ = lean_ctor_get(v_it_2081_, 0);
v_searcher_2087_ = lean_ctor_get(v_it_2081_, 1);
v_isSharedCheck_2150_ = !lean_is_exclusive(v_it_2081_);
if (v_isSharedCheck_2150_ == 0)
{
v___x_2089_ = v_it_2081_;
v_isShared_2090_ = v_isSharedCheck_2150_;
goto v_resetjp_2088_;
}
else
{
lean_inc(v_searcher_2087_);
lean_inc(v_currPos_2086_);
lean_dec(v_it_2081_);
v___x_2089_ = lean_box(0);
v_isShared_2090_ = v_isSharedCheck_2150_;
goto v_resetjp_2088_;
}
v_resetjp_2088_:
{
lean_object* v___x_2091_; 
lean_inc_ref(v_s_2078_);
v___x_2091_ = lean_apply_2(v_inst_2077_, v_s_2078_, v_searcher_2087_);
switch(lean_obj_tag(v___x_2091_))
{
case 0:
{
lean_object* v_out_2092_; 
v_out_2092_ = lean_ctor_get(v___x_2091_, 1);
lean_inc(v_out_2092_);
if (lean_obj_tag(v_out_2092_) == 0)
{
lean_object* v_it_2093_; lean_object* v___x_2095_; 
lean_dec_ref(v_out_2092_);
lean_dec_ref(v_s_2078_);
v_it_2093_ = lean_ctor_get(v___x_2091_, 0);
lean_inc(v_it_2093_);
lean_dec_ref(v___x_2091_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v_it_2093_);
v___x_2095_ = v___x_2089_;
goto v_reusejp_2094_;
}
else
{
lean_object* v_reuseFailAlloc_2099_; 
v_reuseFailAlloc_2099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2099_, 0, v_currPos_2086_);
lean_ctor_set(v_reuseFailAlloc_2099_, 1, v_it_2093_);
v___x_2095_ = v_reuseFailAlloc_2099_;
goto v_reusejp_2094_;
}
v_reusejp_2094_:
{
lean_object* v___x_2096_; lean_object* v___x_2097_; lean_object* v___x_2098_; 
v___x_2096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2096_, 0, v___x_2095_);
v___x_2097_ = lean_apply_2(v_toPure_2079_, lean_box(0), v___x_2096_);
v___x_2098_ = lean_apply_4(v_lift_2080_, lean_box(0), lean_box(0), v___f_2085_, v___x_2097_);
return v___x_2098_;
}
}
else
{
lean_object* v_it_2100_; lean_object* v___x_2102_; uint8_t v_isShared_2103_; uint8_t v_isSharedCheck_2115_; 
v_it_2100_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2115_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2115_ == 0)
{
lean_object* v_unused_2116_; 
v_unused_2116_ = lean_ctor_get(v___x_2091_, 1);
lean_dec(v_unused_2116_);
v___x_2102_ = v___x_2091_;
v_isShared_2103_ = v_isSharedCheck_2115_;
goto v_resetjp_2101_;
}
else
{
lean_inc(v_it_2100_);
lean_dec(v___x_2091_);
v___x_2102_ = lean_box(0);
v_isShared_2103_ = v_isSharedCheck_2115_;
goto v_resetjp_2101_;
}
v_resetjp_2101_:
{
lean_object* v_startPos_2104_; lean_object* v_endPos_2105_; lean_object* v_slice_2106_; lean_object* v_nextIt_2108_; 
v_startPos_2104_ = lean_ctor_get(v_out_2092_, 0);
lean_inc(v_startPos_2104_);
v_endPos_2105_ = lean_ctor_get(v_out_2092_, 1);
lean_inc(v_endPos_2105_);
lean_dec_ref(v_out_2092_);
v_slice_2106_ = l_String_Slice_slice_x21(v_s_2078_, v_endPos_2105_, v_currPos_2086_);
lean_dec(v_currPos_2086_);
lean_dec(v_endPos_2105_);
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v_it_2100_);
lean_ctor_set(v___x_2089_, 0, v_startPos_2104_);
v_nextIt_2108_ = v___x_2089_;
goto v_reusejp_2107_;
}
else
{
lean_object* v_reuseFailAlloc_2114_; 
v_reuseFailAlloc_2114_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2114_, 0, v_startPos_2104_);
lean_ctor_set(v_reuseFailAlloc_2114_, 1, v_it_2100_);
v_nextIt_2108_ = v_reuseFailAlloc_2114_;
goto v_reusejp_2107_;
}
v_reusejp_2107_:
{
lean_object* v___x_2110_; 
if (v_isShared_2103_ == 0)
{
lean_ctor_set(v___x_2102_, 1, v_slice_2106_);
lean_ctor_set(v___x_2102_, 0, v_nextIt_2108_);
v___x_2110_ = v___x_2102_;
goto v_reusejp_2109_;
}
else
{
lean_object* v_reuseFailAlloc_2113_; 
v_reuseFailAlloc_2113_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2113_, 0, v_nextIt_2108_);
lean_ctor_set(v_reuseFailAlloc_2113_, 1, v_slice_2106_);
v___x_2110_ = v_reuseFailAlloc_2113_;
goto v_reusejp_2109_;
}
v_reusejp_2109_:
{
lean_object* v___x_2111_; lean_object* v___x_2112_; 
v___x_2111_ = lean_apply_2(v_toPure_2079_, lean_box(0), v___x_2110_);
v___x_2112_ = lean_apply_4(v_lift_2080_, lean_box(0), lean_box(0), v___f_2085_, v___x_2111_);
return v___x_2112_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2117_; lean_object* v___x_2119_; uint8_t v_isShared_2120_; uint8_t v_isSharedCheck_2129_; 
lean_dec_ref(v_s_2078_);
v_it_2117_ = lean_ctor_get(v___x_2091_, 0);
v_isSharedCheck_2129_ = !lean_is_exclusive(v___x_2091_);
if (v_isSharedCheck_2129_ == 0)
{
v___x_2119_ = v___x_2091_;
v_isShared_2120_ = v_isSharedCheck_2129_;
goto v_resetjp_2118_;
}
else
{
lean_inc(v_it_2117_);
lean_dec(v___x_2091_);
v___x_2119_ = lean_box(0);
v_isShared_2120_ = v_isSharedCheck_2129_;
goto v_resetjp_2118_;
}
v_resetjp_2118_:
{
lean_object* v___x_2122_; 
if (v_isShared_2090_ == 0)
{
lean_ctor_set(v___x_2089_, 1, v_it_2117_);
v___x_2122_ = v___x_2089_;
goto v_reusejp_2121_;
}
else
{
lean_object* v_reuseFailAlloc_2128_; 
v_reuseFailAlloc_2128_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2128_, 0, v_currPos_2086_);
lean_ctor_set(v_reuseFailAlloc_2128_, 1, v_it_2117_);
v___x_2122_ = v_reuseFailAlloc_2128_;
goto v_reusejp_2121_;
}
v_reusejp_2121_:
{
lean_object* v___x_2124_; 
if (v_isShared_2120_ == 0)
{
lean_ctor_set(v___x_2119_, 0, v___x_2122_);
v___x_2124_ = v___x_2119_;
goto v_reusejp_2123_;
}
else
{
lean_object* v_reuseFailAlloc_2127_; 
v_reuseFailAlloc_2127_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2127_, 0, v___x_2122_);
v___x_2124_ = v_reuseFailAlloc_2127_;
goto v_reusejp_2123_;
}
v_reusejp_2123_:
{
lean_object* v___x_2125_; lean_object* v___x_2126_; 
v___x_2125_ = lean_apply_2(v_toPure_2079_, lean_box(0), v___x_2124_);
v___x_2126_ = lean_apply_4(v_lift_2080_, lean_box(0), lean_box(0), v___f_2085_, v___x_2125_);
return v___x_2126_;
}
}
}
}
default: 
{
lean_object* v___x_2130_; uint8_t v___x_2131_; 
lean_del_object(v___x_2089_);
v___x_2130_ = lean_unsigned_to_nat(0u);
v___x_2131_ = lean_nat_dec_eq(v_currPos_2086_, v___x_2130_);
if (v___x_2131_ == 0)
{
lean_object* v_str_2132_; lean_object* v_startInclusive_2133_; lean_object* v___x_2135_; uint8_t v_isShared_2136_; uint8_t v_isSharedCheck_2145_; 
v_str_2132_ = lean_ctor_get(v_s_2078_, 0);
v_startInclusive_2133_ = lean_ctor_get(v_s_2078_, 1);
v_isSharedCheck_2145_ = !lean_is_exclusive(v_s_2078_);
if (v_isSharedCheck_2145_ == 0)
{
lean_object* v_unused_2146_; 
v_unused_2146_ = lean_ctor_get(v_s_2078_, 2);
lean_dec(v_unused_2146_);
v___x_2135_ = v_s_2078_;
v_isShared_2136_ = v_isSharedCheck_2145_;
goto v_resetjp_2134_;
}
else
{
lean_inc(v_startInclusive_2133_);
lean_inc(v_str_2132_);
lean_dec(v_s_2078_);
v___x_2135_ = lean_box(0);
v_isShared_2136_ = v_isSharedCheck_2145_;
goto v_resetjp_2134_;
}
v_resetjp_2134_:
{
lean_object* v___x_2137_; lean_object* v_slice_2139_; 
v___x_2137_ = lean_nat_add(v_startInclusive_2133_, v_currPos_2086_);
lean_dec(v_currPos_2086_);
if (v_isShared_2136_ == 0)
{
lean_ctor_set(v___x_2135_, 2, v___x_2137_);
v_slice_2139_ = v___x_2135_;
goto v_reusejp_2138_;
}
else
{
lean_object* v_reuseFailAlloc_2144_; 
v_reuseFailAlloc_2144_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2144_, 0, v_str_2132_);
lean_ctor_set(v_reuseFailAlloc_2144_, 1, v_startInclusive_2133_);
lean_ctor_set(v_reuseFailAlloc_2144_, 2, v___x_2137_);
v_slice_2139_ = v_reuseFailAlloc_2144_;
goto v_reusejp_2138_;
}
v_reusejp_2138_:
{
lean_object* v___x_2140_; lean_object* v___x_2141_; lean_object* v___x_2142_; lean_object* v___x_2143_; 
v___x_2140_ = lean_box(1);
v___x_2141_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2141_, 0, v___x_2140_);
lean_ctor_set(v___x_2141_, 1, v_slice_2139_);
v___x_2142_ = lean_apply_2(v_toPure_2079_, lean_box(0), v___x_2141_);
v___x_2143_ = lean_apply_4(v_lift_2080_, lean_box(0), lean_box(0), v___f_2085_, v___x_2142_);
return v___x_2143_;
}
}
}
else
{
lean_object* v___x_2147_; lean_object* v___x_2148_; lean_object* v___x_2149_; 
lean_dec(v_currPos_2086_);
lean_dec_ref(v_s_2078_);
v___x_2147_ = lean_box(2);
v___x_2148_ = lean_apply_2(v_toPure_2079_, lean_box(0), v___x_2147_);
v___x_2149_ = lean_apply_4(v_lift_2080_, lean_box(0), lean_box(0), v___f_2085_, v___x_2148_);
return v___x_2149_;
}
}
}
}
}
else
{
lean_object* v___x_2151_; lean_object* v___x_2152_; lean_object* v___x_2153_; 
lean_dec_ref(v_s_2078_);
lean_dec(v_inst_2077_);
v___x_2151_ = lean_box(2);
v___x_2152_ = lean_apply_2(v_toPure_2079_, lean_box(0), v___x_2151_);
v___x_2153_ = lean_apply_4(v_lift_2080_, lean_box(0), lean_box(0), v___f_2085_, v___x_2152_);
return v___x_2153_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object* v_inst_2154_, lean_object* v_inst_2155_, lean_object* v_s_2156_, lean_object* v_toPure_2157_, lean_object* v_lift_2158_, lean_object* v_00_u03b3_2159_, lean_object* v_Pl_2160_, lean_object* v_it_2161_, lean_object* v_init_2162_, lean_object* v___y_2163_){
_start:
{
lean_object* v_toApplicative_2164_; lean_object* v_toBind_2165_; lean_object* v_toPure_2166_; lean_object* v___f_2167_; lean_object* v___x_2168_; 
v_toApplicative_2164_ = lean_ctor_get(v_inst_2154_, 0);
lean_inc_ref(v_toApplicative_2164_);
v_toBind_2165_ = lean_ctor_get(v_inst_2154_, 1);
lean_inc(v_toBind_2165_);
lean_dec_ref(v_inst_2154_);
v_toPure_2166_ = lean_ctor_get(v_toApplicative_2164_, 1);
lean_inc(v_toPure_2166_);
lean_dec_ref(v_toApplicative_2164_);
v___f_2167_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2), 11, 7);
lean_closure_set(v___f_2167_, 0, v_toPure_2166_);
lean_closure_set(v___f_2167_, 1, v___y_2163_);
lean_closure_set(v___f_2167_, 2, v_toBind_2165_);
lean_closure_set(v___f_2167_, 3, v_inst_2155_);
lean_closure_set(v___f_2167_, 4, v_s_2156_);
lean_closure_set(v___f_2167_, 5, v_toPure_2157_);
lean_closure_set(v___f_2167_, 6, v_lift_2158_);
v___x_2168_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2167_, v_it_2161_, v_init_2162_, lean_box(0));
return v___x_2168_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(lean_object* v_inst_2169_, lean_object* v_s_2170_, lean_object* v_inst_2171_, lean_object* v_inst_2172_){
_start:
{
lean_object* v_toApplicative_2173_; lean_object* v_toPure_2174_; lean_object* v___f_2175_; 
v_toApplicative_2173_ = lean_ctor_get(v_inst_2171_, 0);
lean_inc_ref(v_toApplicative_2173_);
lean_dec_ref(v_inst_2171_);
v_toPure_2174_ = lean_ctor_get(v_toApplicative_2173_, 1);
lean_inc(v_toPure_2174_);
lean_dec_ref(v_toApplicative_2173_);
v___f_2175_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3), 10, 4);
lean_closure_set(v___f_2175_, 0, v_inst_2172_);
lean_closure_set(v___f_2175_, 1, v_inst_2169_);
lean_closure_set(v___f_2175_, 2, v_s_2170_);
lean_closure_set(v___f_2175_, 3, v_toPure_2174_);
return v___f_2175_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(lean_object* v_00_u03c1_2176_, lean_object* v_00_u03c1_2177_, lean_object* v_00_u03c3_2178_, lean_object* v_inst_2179_, lean_object* v_inst_2180_, lean_object* v_m_2181_, lean_object* v_n_2182_, lean_object* v_s_2183_, lean_object* v_inst_2184_, lean_object* v_inst_2185_){
_start:
{
lean_object* v___x_2186_; 
v___x_2186_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(v_inst_2179_, v_s_2183_, v_inst_2184_, v_inst_2185_);
return v___x_2186_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___boxed(lean_object* v_00_u03c1_2187_, lean_object* v_00_u03c1_2188_, lean_object* v_00_u03c3_2189_, lean_object* v_inst_2190_, lean_object* v_inst_2191_, lean_object* v_m_2192_, lean_object* v_n_2193_, lean_object* v_s_2194_, lean_object* v_inst_2195_, lean_object* v_inst_2196_){
_start:
{
lean_object* v_res_2197_; 
v_res_2197_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(v_00_u03c1_2187_, v_00_u03c1_2188_, v_00_u03c3_2189_, v_inst_2190_, v_inst_2191_, v_m_2192_, v_n_2193_, v_s_2194_, v_inst_2195_, v_inst_2196_);
lean_dec(v_inst_2191_);
lean_dec(v_00_u03c1_2188_);
return v_res_2197_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___redArg(lean_object* v_s_2198_, lean_object* v_inst_2199_){
_start:
{
lean_object* v_startInclusive_2200_; lean_object* v_endExclusive_2201_; lean_object* v___x_2202_; lean_object* v___x_2203_; lean_object* v___x_2204_; 
v_startInclusive_2200_ = lean_ctor_get(v_s_2198_, 1);
v_endExclusive_2201_ = lean_ctor_get(v_s_2198_, 2);
v___x_2202_ = lean_nat_sub(v_endExclusive_2201_, v_startInclusive_2200_);
v___x_2203_ = lean_apply_1(v_inst_2199_, v_s_2198_);
v___x_2204_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2204_, 0, v___x_2202_);
lean_ctor_set(v___x_2204_, 1, v___x_2203_);
return v___x_2204_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit(lean_object* v_00_u03c3_2205_, lean_object* v_00_u03c1_2206_, lean_object* v_s_2207_, lean_object* v_pat_2208_, lean_object* v_inst_2209_){
_start:
{
lean_object* v___x_2210_; 
v___x_2210_ = l_String_Slice_revSplit___redArg(v_s_2207_, v_inst_2209_);
return v___x_2210_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___boxed(lean_object* v_00_u03c3_2211_, lean_object* v_00_u03c1_2212_, lean_object* v_s_2213_, lean_object* v_pat_2214_, lean_object* v_inst_2215_){
_start:
{
lean_object* v_res_2216_; 
v_res_2216_ = l_String_Slice_revSplit(v_00_u03c3_2211_, v_00_u03c1_2212_, v_s_2213_, v_pat_2214_, v_inst_2215_);
lean_dec(v_pat_2214_);
return v_res_2216_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___redArg(lean_object* v_s_2217_, lean_object* v_inst_2218_){
_start:
{
lean_object* v_dropSuffix_x3f_2219_; lean_object* v___x_2220_; 
v_dropSuffix_x3f_2219_ = lean_ctor_get(v_inst_2218_, 0);
lean_inc_ref(v_dropSuffix_x3f_2219_);
lean_dec_ref(v_inst_2218_);
lean_inc_ref(v_s_2217_);
v___x_2220_ = lean_apply_1(v_dropSuffix_x3f_2219_, v_s_2217_);
if (lean_obj_tag(v___x_2220_) == 0)
{
lean_object* v___x_2221_; 
lean_dec_ref(v_s_2217_);
v___x_2221_ = lean_box(0);
return v___x_2221_;
}
else
{
lean_object* v_val_2222_; lean_object* v___x_2224_; uint8_t v_isShared_2225_; uint8_t v_isSharedCheck_2240_; 
v_val_2222_ = lean_ctor_get(v___x_2220_, 0);
v_isSharedCheck_2240_ = !lean_is_exclusive(v___x_2220_);
if (v_isSharedCheck_2240_ == 0)
{
v___x_2224_ = v___x_2220_;
v_isShared_2225_ = v_isSharedCheck_2240_;
goto v_resetjp_2223_;
}
else
{
lean_inc(v_val_2222_);
lean_dec(v___x_2220_);
v___x_2224_ = lean_box(0);
v_isShared_2225_ = v_isSharedCheck_2240_;
goto v_resetjp_2223_;
}
v_resetjp_2223_:
{
lean_object* v_str_2226_; lean_object* v_startInclusive_2227_; lean_object* v___x_2229_; uint8_t v_isShared_2230_; uint8_t v_isSharedCheck_2238_; 
v_str_2226_ = lean_ctor_get(v_s_2217_, 0);
v_startInclusive_2227_ = lean_ctor_get(v_s_2217_, 1);
v_isSharedCheck_2238_ = !lean_is_exclusive(v_s_2217_);
if (v_isSharedCheck_2238_ == 0)
{
lean_object* v_unused_2239_; 
v_unused_2239_ = lean_ctor_get(v_s_2217_, 2);
lean_dec(v_unused_2239_);
v___x_2229_ = v_s_2217_;
v_isShared_2230_ = v_isSharedCheck_2238_;
goto v_resetjp_2228_;
}
else
{
lean_inc(v_startInclusive_2227_);
lean_inc(v_str_2226_);
lean_dec(v_s_2217_);
v___x_2229_ = lean_box(0);
v_isShared_2230_ = v_isSharedCheck_2238_;
goto v_resetjp_2228_;
}
v_resetjp_2228_:
{
lean_object* v___x_2231_; lean_object* v___x_2233_; 
v___x_2231_ = lean_nat_add(v_startInclusive_2227_, v_val_2222_);
lean_dec(v_val_2222_);
if (v_isShared_2230_ == 0)
{
lean_ctor_set(v___x_2229_, 2, v___x_2231_);
v___x_2233_ = v___x_2229_;
goto v_reusejp_2232_;
}
else
{
lean_object* v_reuseFailAlloc_2237_; 
v_reuseFailAlloc_2237_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2237_, 0, v_str_2226_);
lean_ctor_set(v_reuseFailAlloc_2237_, 1, v_startInclusive_2227_);
lean_ctor_set(v_reuseFailAlloc_2237_, 2, v___x_2231_);
v___x_2233_ = v_reuseFailAlloc_2237_;
goto v_reusejp_2232_;
}
v_reusejp_2232_:
{
lean_object* v___x_2235_; 
if (v_isShared_2225_ == 0)
{
lean_ctor_set(v___x_2224_, 0, v___x_2233_);
v___x_2235_ = v___x_2224_;
goto v_reusejp_2234_;
}
else
{
lean_object* v_reuseFailAlloc_2236_; 
v_reuseFailAlloc_2236_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2236_, 0, v___x_2233_);
v___x_2235_ = v_reuseFailAlloc_2236_;
goto v_reusejp_2234_;
}
v_reusejp_2234_:
{
return v___x_2235_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f(lean_object* v_00_u03c1_2241_, lean_object* v_s_2242_, lean_object* v_pat_2243_, lean_object* v_inst_2244_){
_start:
{
lean_object* v_dropSuffix_x3f_2245_; lean_object* v___x_2246_; 
v_dropSuffix_x3f_2245_ = lean_ctor_get(v_inst_2244_, 0);
lean_inc_ref(v_dropSuffix_x3f_2245_);
lean_dec_ref(v_inst_2244_);
lean_inc_ref(v_s_2242_);
v___x_2246_ = lean_apply_1(v_dropSuffix_x3f_2245_, v_s_2242_);
if (lean_obj_tag(v___x_2246_) == 0)
{
lean_object* v___x_2247_; 
lean_dec_ref(v_s_2242_);
v___x_2247_ = lean_box(0);
return v___x_2247_;
}
else
{
lean_object* v_val_2248_; lean_object* v___x_2250_; uint8_t v_isShared_2251_; uint8_t v_isSharedCheck_2266_; 
v_val_2248_ = lean_ctor_get(v___x_2246_, 0);
v_isSharedCheck_2266_ = !lean_is_exclusive(v___x_2246_);
if (v_isSharedCheck_2266_ == 0)
{
v___x_2250_ = v___x_2246_;
v_isShared_2251_ = v_isSharedCheck_2266_;
goto v_resetjp_2249_;
}
else
{
lean_inc(v_val_2248_);
lean_dec(v___x_2246_);
v___x_2250_ = lean_box(0);
v_isShared_2251_ = v_isSharedCheck_2266_;
goto v_resetjp_2249_;
}
v_resetjp_2249_:
{
lean_object* v_str_2252_; lean_object* v_startInclusive_2253_; lean_object* v___x_2255_; uint8_t v_isShared_2256_; uint8_t v_isSharedCheck_2264_; 
v_str_2252_ = lean_ctor_get(v_s_2242_, 0);
v_startInclusive_2253_ = lean_ctor_get(v_s_2242_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_s_2242_);
if (v_isSharedCheck_2264_ == 0)
{
lean_object* v_unused_2265_; 
v_unused_2265_ = lean_ctor_get(v_s_2242_, 2);
lean_dec(v_unused_2265_);
v___x_2255_ = v_s_2242_;
v_isShared_2256_ = v_isSharedCheck_2264_;
goto v_resetjp_2254_;
}
else
{
lean_inc(v_startInclusive_2253_);
lean_inc(v_str_2252_);
lean_dec(v_s_2242_);
v___x_2255_ = lean_box(0);
v_isShared_2256_ = v_isSharedCheck_2264_;
goto v_resetjp_2254_;
}
v_resetjp_2254_:
{
lean_object* v___x_2257_; lean_object* v___x_2259_; 
v___x_2257_ = lean_nat_add(v_startInclusive_2253_, v_val_2248_);
lean_dec(v_val_2248_);
if (v_isShared_2256_ == 0)
{
lean_ctor_set(v___x_2255_, 2, v___x_2257_);
v___x_2259_ = v___x_2255_;
goto v_reusejp_2258_;
}
else
{
lean_object* v_reuseFailAlloc_2263_; 
v_reuseFailAlloc_2263_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2263_, 0, v_str_2252_);
lean_ctor_set(v_reuseFailAlloc_2263_, 1, v_startInclusive_2253_);
lean_ctor_set(v_reuseFailAlloc_2263_, 2, v___x_2257_);
v___x_2259_ = v_reuseFailAlloc_2263_;
goto v_reusejp_2258_;
}
v_reusejp_2258_:
{
lean_object* v___x_2261_; 
if (v_isShared_2251_ == 0)
{
lean_ctor_set(v___x_2250_, 0, v___x_2259_);
v___x_2261_ = v___x_2250_;
goto v_reusejp_2260_;
}
else
{
lean_object* v_reuseFailAlloc_2262_; 
v_reuseFailAlloc_2262_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2262_, 0, v___x_2259_);
v___x_2261_ = v_reuseFailAlloc_2262_;
goto v_reusejp_2260_;
}
v_reusejp_2260_:
{
return v___x_2261_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_2267_, lean_object* v_s_2268_, lean_object* v_pat_2269_, lean_object* v_inst_2270_){
_start:
{
lean_object* v_res_2271_; 
v_res_2271_ = l_String_Slice_dropSuffix_x3f(v_00_u03c1_2267_, v_s_2268_, v_pat_2269_, v_inst_2270_);
lean_dec(v_pat_2269_);
return v_res_2271_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___redArg(lean_object* v_s_2272_, lean_object* v_inst_2273_){
_start:
{
lean_object* v_dropSuffix_x3f_2274_; lean_object* v___x_2275_; 
v_dropSuffix_x3f_2274_ = lean_ctor_get(v_inst_2273_, 0);
lean_inc_ref(v_dropSuffix_x3f_2274_);
lean_dec_ref(v_inst_2273_);
lean_inc_ref(v_s_2272_);
v___x_2275_ = lean_apply_1(v_dropSuffix_x3f_2274_, v_s_2272_);
if (lean_obj_tag(v___x_2275_) == 0)
{
return v_s_2272_;
}
else
{
lean_object* v_val_2276_; lean_object* v_str_2277_; lean_object* v_startInclusive_2278_; lean_object* v___x_2280_; uint8_t v_isShared_2281_; uint8_t v_isSharedCheck_2286_; 
v_val_2276_ = lean_ctor_get(v___x_2275_, 0);
lean_inc(v_val_2276_);
lean_dec_ref(v___x_2275_);
v_str_2277_ = lean_ctor_get(v_s_2272_, 0);
v_startInclusive_2278_ = lean_ctor_get(v_s_2272_, 1);
v_isSharedCheck_2286_ = !lean_is_exclusive(v_s_2272_);
if (v_isSharedCheck_2286_ == 0)
{
lean_object* v_unused_2287_; 
v_unused_2287_ = lean_ctor_get(v_s_2272_, 2);
lean_dec(v_unused_2287_);
v___x_2280_ = v_s_2272_;
v_isShared_2281_ = v_isSharedCheck_2286_;
goto v_resetjp_2279_;
}
else
{
lean_inc(v_startInclusive_2278_);
lean_inc(v_str_2277_);
lean_dec(v_s_2272_);
v___x_2280_ = lean_box(0);
v_isShared_2281_ = v_isSharedCheck_2286_;
goto v_resetjp_2279_;
}
v_resetjp_2279_:
{
lean_object* v___x_2282_; lean_object* v___x_2284_; 
v___x_2282_ = lean_nat_add(v_startInclusive_2278_, v_val_2276_);
lean_dec(v_val_2276_);
if (v_isShared_2281_ == 0)
{
lean_ctor_set(v___x_2280_, 2, v___x_2282_);
v___x_2284_ = v___x_2280_;
goto v_reusejp_2283_;
}
else
{
lean_object* v_reuseFailAlloc_2285_; 
v_reuseFailAlloc_2285_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2285_, 0, v_str_2277_);
lean_ctor_set(v_reuseFailAlloc_2285_, 1, v_startInclusive_2278_);
lean_ctor_set(v_reuseFailAlloc_2285_, 2, v___x_2282_);
v___x_2284_ = v_reuseFailAlloc_2285_;
goto v_reusejp_2283_;
}
v_reusejp_2283_:
{
return v___x_2284_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix(lean_object* v_00_u03c1_2288_, lean_object* v_s_2289_, lean_object* v_pat_2290_, lean_object* v_inst_2291_){
_start:
{
lean_object* v___x_2292_; 
v___x_2292_ = l_String_Slice_dropSuffix___redArg(v_s_2289_, v_inst_2291_);
return v___x_2292_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___boxed(lean_object* v_00_u03c1_2293_, lean_object* v_s_2294_, lean_object* v_pat_2295_, lean_object* v_inst_2296_){
_start:
{
lean_object* v_res_2297_; 
v_res_2297_ = l_String_Slice_dropSuffix(v_00_u03c1_2293_, v_s_2294_, v_pat_2295_, v_inst_2296_);
lean_dec(v_pat_2295_);
return v_res_2297_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object* v_s_2298_, lean_object* v_n_2299_){
_start:
{
lean_object* v_str_2300_; lean_object* v_startInclusive_2301_; lean_object* v_endExclusive_2302_; lean_object* v___x_2303_; lean_object* v___x_2304_; lean_object* v___x_2306_; uint8_t v_isShared_2307_; uint8_t v_isSharedCheck_2312_; 
v_str_2300_ = lean_ctor_get(v_s_2298_, 0);
lean_inc_ref(v_str_2300_);
v_startInclusive_2301_ = lean_ctor_get(v_s_2298_, 1);
lean_inc(v_startInclusive_2301_);
v_endExclusive_2302_ = lean_ctor_get(v_s_2298_, 2);
v___x_2303_ = lean_nat_sub(v_endExclusive_2302_, v_startInclusive_2301_);
v___x_2304_ = l_String_Slice_Pos_prevn(v_s_2298_, v___x_2303_, v_n_2299_);
v_isSharedCheck_2312_ = !lean_is_exclusive(v_s_2298_);
if (v_isSharedCheck_2312_ == 0)
{
lean_object* v_unused_2313_; lean_object* v_unused_2314_; lean_object* v_unused_2315_; 
v_unused_2313_ = lean_ctor_get(v_s_2298_, 2);
lean_dec(v_unused_2313_);
v_unused_2314_ = lean_ctor_get(v_s_2298_, 1);
lean_dec(v_unused_2314_);
v_unused_2315_ = lean_ctor_get(v_s_2298_, 0);
lean_dec(v_unused_2315_);
v___x_2306_ = v_s_2298_;
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
else
{
lean_dec(v_s_2298_);
v___x_2306_ = lean_box(0);
v_isShared_2307_ = v_isSharedCheck_2312_;
goto v_resetjp_2305_;
}
v_resetjp_2305_:
{
lean_object* v___x_2308_; lean_object* v___x_2310_; 
v___x_2308_ = lean_nat_add(v_startInclusive_2301_, v___x_2304_);
lean_dec(v___x_2304_);
if (v_isShared_2307_ == 0)
{
lean_ctor_set(v___x_2306_, 2, v___x_2308_);
v___x_2310_ = v___x_2306_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2311_; 
v_reuseFailAlloc_2311_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2311_, 0, v_str_2300_);
lean_ctor_set(v_reuseFailAlloc_2311_, 1, v_startInclusive_2301_);
lean_ctor_set(v_reuseFailAlloc_2311_, 2, v___x_2308_);
v___x_2310_ = v_reuseFailAlloc_2311_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
return v___x_2310_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___redArg(lean_object* v_s_2316_, lean_object* v_inst_2317_, lean_object* v_curr_2318_){
_start:
{
lean_object* v_dropSuffix_x3f_2319_; lean_object* v_str_2320_; lean_object* v_startInclusive_2321_; lean_object* v___x_2322_; lean_object* v___x_2323_; lean_object* v___x_2324_; 
v_dropSuffix_x3f_2319_ = lean_ctor_get(v_inst_2317_, 0);
v_str_2320_ = lean_ctor_get(v_s_2316_, 0);
v_startInclusive_2321_ = lean_ctor_get(v_s_2316_, 1);
v___x_2322_ = lean_nat_add(v_startInclusive_2321_, v_curr_2318_);
lean_inc(v_startInclusive_2321_);
lean_inc_ref(v_str_2320_);
v___x_2323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2323_, 0, v_str_2320_);
lean_ctor_set(v___x_2323_, 1, v_startInclusive_2321_);
lean_ctor_set(v___x_2323_, 2, v___x_2322_);
lean_inc_ref(v_dropSuffix_x3f_2319_);
lean_inc_ref(v___x_2323_);
v___x_2324_ = lean_apply_1(v_dropSuffix_x3f_2319_, v___x_2323_);
if (lean_obj_tag(v___x_2324_) == 1)
{
lean_object* v_val_2325_; uint8_t v___x_2326_; 
v_val_2325_ = lean_ctor_get(v___x_2324_, 0);
lean_inc(v_val_2325_);
lean_dec_ref(v___x_2324_);
v___x_2326_ = lean_nat_dec_lt(v_val_2325_, v_curr_2318_);
lean_dec(v_curr_2318_);
if (v___x_2326_ == 0)
{
lean_dec(v_val_2325_);
lean_dec_ref(v_inst_2317_);
return v___x_2323_;
}
else
{
lean_dec_ref(v___x_2323_);
v_curr_2318_ = v_val_2325_;
goto _start;
}
}
else
{
lean_dec(v___x_2324_);
lean_dec(v_curr_2318_);
lean_dec_ref(v_inst_2317_);
return v___x_2323_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___redArg___boxed(lean_object* v_s_2328_, lean_object* v_inst_2329_, lean_object* v_curr_2330_){
_start:
{
lean_object* v_res_2331_; 
v_res_2331_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___redArg(v_s_2328_, v_inst_2329_, v_curr_2330_);
lean_dec_ref(v_s_2328_);
return v_res_2331_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go(lean_object* v_00_u03c1_2332_, lean_object* v_s_2333_, lean_object* v_pat_2334_, lean_object* v_inst_2335_, lean_object* v_curr_2336_){
_start:
{
lean_object* v___x_2337_; 
v___x_2337_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___redArg(v_s_2333_, v_inst_2335_, v_curr_2336_);
return v___x_2337_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___boxed(lean_object* v_00_u03c1_2338_, lean_object* v_s_2339_, lean_object* v_pat_2340_, lean_object* v_inst_2341_, lean_object* v_curr_2342_){
_start:
{
lean_object* v_res_2343_; 
v_res_2343_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go(v_00_u03c1_2338_, v_s_2339_, v_pat_2340_, v_inst_2341_, v_curr_2342_);
lean_dec(v_pat_2340_);
lean_dec_ref(v_s_2339_);
return v_res_2343_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go_match__1_splitter___redArg(lean_object* v_x_2344_, lean_object* v_h__1_2345_, lean_object* v_h__2_2346_){
_start:
{
if (lean_obj_tag(v_x_2344_) == 1)
{
lean_object* v_val_2347_; lean_object* v___x_2348_; 
lean_dec(v_h__2_2346_);
v_val_2347_ = lean_ctor_get(v_x_2344_, 0);
lean_inc(v_val_2347_);
lean_dec_ref(v_x_2344_);
v___x_2348_ = lean_apply_1(v_h__1_2345_, v_val_2347_);
return v___x_2348_;
}
else
{
lean_object* v___x_2349_; 
lean_dec(v_h__1_2345_);
v___x_2349_ = lean_apply_2(v_h__2_2346_, v_x_2344_, lean_box(0));
return v___x_2349_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go_match__1_splitter(lean_object* v_s_2350_, lean_object* v_curr_2351_, lean_object* v_motive_2352_, lean_object* v_x_2353_, lean_object* v_h__1_2354_, lean_object* v_h__2_2355_){
_start:
{
if (lean_obj_tag(v_x_2353_) == 1)
{
lean_object* v_val_2356_; lean_object* v___x_2357_; 
lean_dec(v_h__2_2355_);
v_val_2356_ = lean_ctor_get(v_x_2353_, 0);
lean_inc(v_val_2356_);
lean_dec_ref(v_x_2353_);
v___x_2357_ = lean_apply_1(v_h__1_2354_, v_val_2356_);
return v___x_2357_;
}
else
{
lean_object* v___x_2358_; 
lean_dec(v_h__1_2354_);
v___x_2358_ = lean_apply_2(v_h__2_2355_, v_x_2353_, lean_box(0));
return v___x_2358_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go_match__1_splitter___boxed(lean_object* v_s_2359_, lean_object* v_curr_2360_, lean_object* v_motive_2361_, lean_object* v_x_2362_, lean_object* v_h__1_2363_, lean_object* v_h__2_2364_){
_start:
{
lean_object* v_res_2365_; 
v_res_2365_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go_match__1_splitter(v_s_2359_, v_curr_2360_, v_motive_2361_, v_x_2362_, v_h__1_2363_, v_h__2_2364_);
lean_dec(v_curr_2360_);
lean_dec_ref(v_s_2359_);
return v_res_2365_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object* v_s_2366_, lean_object* v_inst_2367_){
_start:
{
lean_object* v_startInclusive_2368_; lean_object* v_endExclusive_2369_; lean_object* v___x_2370_; lean_object* v___x_2371_; 
v_startInclusive_2368_ = lean_ctor_get(v_s_2366_, 1);
v_endExclusive_2369_ = lean_ctor_get(v_s_2366_, 2);
v___x_2370_ = lean_nat_sub(v_endExclusive_2369_, v_startInclusive_2368_);
v___x_2371_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___redArg(v_s_2366_, v_inst_2367_, v___x_2370_);
return v___x_2371_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg___boxed(lean_object* v_s_2372_, lean_object* v_inst_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_String_Slice_dropEndWhile___redArg(v_s_2372_, v_inst_2373_);
lean_dec_ref(v_s_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object* v_00_u03c1_2375_, lean_object* v_s_2376_, lean_object* v_pat_2377_, lean_object* v_inst_2378_){
_start:
{
lean_object* v_startInclusive_2379_; lean_object* v_endExclusive_2380_; lean_object* v___x_2381_; lean_object* v___x_2382_; 
v_startInclusive_2379_ = lean_ctor_get(v_s_2376_, 1);
v_endExclusive_2380_ = lean_ctor_get(v_s_2376_, 2);
v___x_2381_ = lean_nat_sub(v_endExclusive_2380_, v_startInclusive_2379_);
v___x_2382_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___redArg(v_s_2376_, v_inst_2378_, v___x_2381_);
return v___x_2382_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object* v_00_u03c1_2383_, lean_object* v_s_2384_, lean_object* v_pat_2385_, lean_object* v_inst_2386_){
_start:
{
lean_object* v_res_2387_; 
v_res_2387_ = l_String_Slice_dropEndWhile(v_00_u03c1_2383_, v_s_2384_, v_pat_2385_, v_inst_2386_);
lean_dec(v_pat_2385_);
lean_dec_ref(v_s_2384_);
return v_res_2387_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiEnd___closed__0(void){
_start:
{
lean_object* v___x_2388_; lean_object* v___x_2389_; 
v___x_2388_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_2389_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_2388_);
return v___x_2389_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object* v_s_2390_){
_start:
{
lean_object* v___x_2391_; lean_object* v_startInclusive_2392_; lean_object* v_endExclusive_2393_; lean_object* v___x_2394_; lean_object* v___x_2395_; 
v___x_2391_ = lean_obj_once(&l_String_Slice_trimAsciiEnd___closed__0, &l_String_Slice_trimAsciiEnd___closed__0_once, _init_l_String_Slice_trimAsciiEnd___closed__0);
v_startInclusive_2392_ = lean_ctor_get(v_s_2390_, 1);
v_endExclusive_2393_ = lean_ctor_get(v_s_2390_, 2);
v___x_2394_ = lean_nat_sub(v_endExclusive_2393_, v_startInclusive_2392_);
v___x_2395_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___redArg(v_s_2390_, v___x_2391_, v___x_2394_);
return v___x_2395_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd___boxed(lean_object* v_s_2396_){
_start:
{
lean_object* v_res_2397_; 
v_res_2397_ = l_String_Slice_trimAsciiEnd(v_s_2396_);
lean_dec_ref(v_s_2396_);
return v_res_2397_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object* v_s_2398_, lean_object* v_n_2399_){
_start:
{
lean_object* v_str_2400_; lean_object* v_startInclusive_2401_; lean_object* v_endExclusive_2402_; lean_object* v___x_2403_; lean_object* v___x_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2412_; 
v_str_2400_ = lean_ctor_get(v_s_2398_, 0);
lean_inc_ref(v_str_2400_);
v_startInclusive_2401_ = lean_ctor_get(v_s_2398_, 1);
lean_inc(v_startInclusive_2401_);
v_endExclusive_2402_ = lean_ctor_get(v_s_2398_, 2);
lean_inc(v_endExclusive_2402_);
v___x_2403_ = lean_nat_sub(v_endExclusive_2402_, v_startInclusive_2401_);
v___x_2404_ = l_String_Slice_Pos_prevn(v_s_2398_, v___x_2403_, v_n_2399_);
v_isSharedCheck_2412_ = !lean_is_exclusive(v_s_2398_);
if (v_isSharedCheck_2412_ == 0)
{
lean_object* v_unused_2413_; lean_object* v_unused_2414_; lean_object* v_unused_2415_; 
v_unused_2413_ = lean_ctor_get(v_s_2398_, 2);
lean_dec(v_unused_2413_);
v_unused_2414_ = lean_ctor_get(v_s_2398_, 1);
lean_dec(v_unused_2414_);
v_unused_2415_ = lean_ctor_get(v_s_2398_, 0);
lean_dec(v_unused_2415_);
v___x_2406_ = v_s_2398_;
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
else
{
lean_dec(v_s_2398_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2412_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v___x_2410_; 
v___x_2408_ = lean_nat_add(v_startInclusive_2401_, v___x_2404_);
lean_dec(v___x_2404_);
lean_dec(v_startInclusive_2401_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 1, v___x_2408_);
v___x_2410_ = v___x_2406_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2411_; 
v_reuseFailAlloc_2411_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2411_, 0, v_str_2400_);
lean_ctor_set(v_reuseFailAlloc_2411_, 1, v___x_2408_);
lean_ctor_set(v_reuseFailAlloc_2411_, 2, v_endExclusive_2402_);
v___x_2410_ = v_reuseFailAlloc_2411_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
return v___x_2410_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___redArg(lean_object* v_s_2416_, lean_object* v_inst_2417_, lean_object* v_curr_2418_){
_start:
{
lean_object* v_dropSuffix_x3f_2419_; lean_object* v_str_2420_; lean_object* v_startInclusive_2421_; lean_object* v_endExclusive_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; lean_object* v___x_2425_; 
v_dropSuffix_x3f_2419_ = lean_ctor_get(v_inst_2417_, 0);
v_str_2420_ = lean_ctor_get(v_s_2416_, 0);
v_startInclusive_2421_ = lean_ctor_get(v_s_2416_, 1);
v_endExclusive_2422_ = lean_ctor_get(v_s_2416_, 2);
v___x_2423_ = lean_nat_add(v_startInclusive_2421_, v_curr_2418_);
lean_inc(v___x_2423_);
lean_inc(v_startInclusive_2421_);
lean_inc_ref(v_str_2420_);
v___x_2424_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2424_, 0, v_str_2420_);
lean_ctor_set(v___x_2424_, 1, v_startInclusive_2421_);
lean_ctor_set(v___x_2424_, 2, v___x_2423_);
lean_inc_ref(v_dropSuffix_x3f_2419_);
v___x_2425_ = lean_apply_1(v_dropSuffix_x3f_2419_, v___x_2424_);
if (lean_obj_tag(v___x_2425_) == 1)
{
lean_object* v_val_2426_; uint8_t v___x_2427_; 
v_val_2426_ = lean_ctor_get(v___x_2425_, 0);
lean_inc(v_val_2426_);
lean_dec_ref(v___x_2425_);
v___x_2427_ = lean_nat_dec_lt(v_val_2426_, v_curr_2418_);
lean_dec(v_curr_2418_);
if (v___x_2427_ == 0)
{
lean_object* v___x_2429_; uint8_t v_isShared_2430_; uint8_t v_isSharedCheck_2434_; 
lean_inc(v_endExclusive_2422_);
lean_inc_ref(v_str_2420_);
lean_dec(v_val_2426_);
lean_dec_ref(v_inst_2417_);
v_isSharedCheck_2434_ = !lean_is_exclusive(v_s_2416_);
if (v_isSharedCheck_2434_ == 0)
{
lean_object* v_unused_2435_; lean_object* v_unused_2436_; lean_object* v_unused_2437_; 
v_unused_2435_ = lean_ctor_get(v_s_2416_, 2);
lean_dec(v_unused_2435_);
v_unused_2436_ = lean_ctor_get(v_s_2416_, 1);
lean_dec(v_unused_2436_);
v_unused_2437_ = lean_ctor_get(v_s_2416_, 0);
lean_dec(v_unused_2437_);
v___x_2429_ = v_s_2416_;
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
else
{
lean_dec(v_s_2416_);
v___x_2429_ = lean_box(0);
v_isShared_2430_ = v_isSharedCheck_2434_;
goto v_resetjp_2428_;
}
v_resetjp_2428_:
{
lean_object* v___x_2432_; 
if (v_isShared_2430_ == 0)
{
lean_ctor_set(v___x_2429_, 1, v___x_2423_);
v___x_2432_ = v___x_2429_;
goto v_reusejp_2431_;
}
else
{
lean_object* v_reuseFailAlloc_2433_; 
v_reuseFailAlloc_2433_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2433_, 0, v_str_2420_);
lean_ctor_set(v_reuseFailAlloc_2433_, 1, v___x_2423_);
lean_ctor_set(v_reuseFailAlloc_2433_, 2, v_endExclusive_2422_);
v___x_2432_ = v_reuseFailAlloc_2433_;
goto v_reusejp_2431_;
}
v_reusejp_2431_:
{
return v___x_2432_;
}
}
}
else
{
lean_dec(v___x_2423_);
v_curr_2418_ = v_val_2426_;
goto _start;
}
}
else
{
lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2445_; 
lean_inc(v_endExclusive_2422_);
lean_inc_ref(v_str_2420_);
lean_dec(v___x_2425_);
lean_dec(v_curr_2418_);
lean_dec_ref(v_inst_2417_);
v_isSharedCheck_2445_ = !lean_is_exclusive(v_s_2416_);
if (v_isSharedCheck_2445_ == 0)
{
lean_object* v_unused_2446_; lean_object* v_unused_2447_; lean_object* v_unused_2448_; 
v_unused_2446_ = lean_ctor_get(v_s_2416_, 2);
lean_dec(v_unused_2446_);
v_unused_2447_ = lean_ctor_get(v_s_2416_, 1);
lean_dec(v_unused_2447_);
v_unused_2448_ = lean_ctor_get(v_s_2416_, 0);
lean_dec(v_unused_2448_);
v___x_2440_ = v_s_2416_;
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
else
{
lean_dec(v_s_2416_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2445_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v___x_2443_; 
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 1, v___x_2423_);
v___x_2443_ = v___x_2440_;
goto v_reusejp_2442_;
}
else
{
lean_object* v_reuseFailAlloc_2444_; 
v_reuseFailAlloc_2444_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2444_, 0, v_str_2420_);
lean_ctor_set(v_reuseFailAlloc_2444_, 1, v___x_2423_);
lean_ctor_set(v_reuseFailAlloc_2444_, 2, v_endExclusive_2422_);
v___x_2443_ = v_reuseFailAlloc_2444_;
goto v_reusejp_2442_;
}
v_reusejp_2442_:
{
return v___x_2443_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go(lean_object* v_00_u03c1_2449_, lean_object* v_s_2450_, lean_object* v_pat_2451_, lean_object* v_inst_2452_, lean_object* v_curr_2453_){
_start:
{
lean_object* v___x_2454_; 
v___x_2454_ = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___redArg(v_s_2450_, v_inst_2452_, v_curr_2453_);
return v___x_2454_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___boxed(lean_object* v_00_u03c1_2455_, lean_object* v_s_2456_, lean_object* v_pat_2457_, lean_object* v_inst_2458_, lean_object* v_curr_2459_){
_start:
{
lean_object* v_res_2460_; 
v_res_2460_ = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go(v_00_u03c1_2455_, v_s_2456_, v_pat_2457_, v_inst_2458_, v_curr_2459_);
lean_dec(v_pat_2457_);
return v_res_2460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___redArg(lean_object* v_s_2461_, lean_object* v_inst_2462_){
_start:
{
lean_object* v_startInclusive_2463_; lean_object* v_endExclusive_2464_; lean_object* v___x_2465_; lean_object* v___x_2466_; 
v_startInclusive_2463_ = lean_ctor_get(v_s_2461_, 1);
v_endExclusive_2464_ = lean_ctor_get(v_s_2461_, 2);
v___x_2465_ = lean_nat_sub(v_endExclusive_2464_, v_startInclusive_2463_);
v___x_2466_ = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___redArg(v_s_2461_, v_inst_2462_, v___x_2465_);
return v___x_2466_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile(lean_object* v_00_u03c1_2467_, lean_object* v_s_2468_, lean_object* v_pat_2469_, lean_object* v_inst_2470_){
_start:
{
lean_object* v_startInclusive_2471_; lean_object* v_endExclusive_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; 
v_startInclusive_2471_ = lean_ctor_get(v_s_2468_, 1);
v_endExclusive_2472_ = lean_ctor_get(v_s_2468_, 2);
v___x_2473_ = lean_nat_sub(v_endExclusive_2472_, v_startInclusive_2471_);
v___x_2474_ = l___private_Init_Data_String_Slice_0__String_Slice_takeEndWhile_go___redArg(v_s_2468_, v_inst_2470_, v___x_2473_);
return v___x_2474_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___boxed(lean_object* v_00_u03c1_2475_, lean_object* v_s_2476_, lean_object* v_pat_2477_, lean_object* v_inst_2478_){
_start:
{
lean_object* v_res_2479_; 
v_res_2479_ = l_String_Slice_takeEndWhile(v_00_u03c1_2475_, v_s_2476_, v_pat_2477_, v_inst_2478_);
lean_dec(v_pat_2477_);
return v_res_2479_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___redArg(lean_object* v_inst_2480_, lean_object* v_s_2481_, lean_object* v_inst_2482_){
_start:
{
lean_object* v___f_2483_; lean_object* v_searcher_2484_; lean_object* v___x_2485_; lean_object* v___f_2486_; lean_object* v___x_2487_; 
v___f_2483_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_2481_);
v_searcher_2484_ = lean_apply_1(v_inst_2482_, v_s_2481_);
v___x_2485_ = lean_box(0);
v___f_2486_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_2487_ = lean_apply_7(v_inst_2480_, v_s_2481_, v___f_2483_, lean_box(0), lean_box(0), v_searcher_2484_, v___x_2485_, v___f_2486_);
return v___x_2487_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f(lean_object* v_00_u03c3_2488_, lean_object* v_inst_2489_, lean_object* v_inst_2490_, lean_object* v_00_u03c1_2491_, lean_object* v_s_2492_, lean_object* v_pat_2493_, lean_object* v_inst_2494_){
_start:
{
lean_object* v___x_2495_; 
v___x_2495_ = l_String_Slice_revFind_x3f___redArg(v_inst_2490_, v_s_2492_, v_inst_2494_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___boxed(lean_object* v_00_u03c3_2496_, lean_object* v_inst_2497_, lean_object* v_inst_2498_, lean_object* v_00_u03c1_2499_, lean_object* v_s_2500_, lean_object* v_pat_2501_, lean_object* v_inst_2502_){
_start:
{
lean_object* v_res_2503_; 
v_res_2503_ = l_String_Slice_revFind_x3f(v_00_u03c3_2496_, v_inst_2497_, v_inst_2498_, v_00_u03c1_2499_, v_s_2500_, v_pat_2501_, v_inst_2502_);
lean_dec(v_pat_2501_);
lean_dec(v_inst_2497_);
return v_res_2503_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_Slice_trimAscii_spec__0(lean_object* v_s_2504_, lean_object* v_curr_2505_){
_start:
{
lean_object* v_str_2506_; lean_object* v_startInclusive_2507_; lean_object* v_endExclusive_2508_; lean_object* v___x_2509_; lean_object* v___x_2510_; uint8_t v___y_2518_; lean_object* v___x_2519_; lean_object* v___x_2520_; uint8_t v___x_2521_; 
v_str_2506_ = lean_ctor_get(v_s_2504_, 0);
v_startInclusive_2507_ = lean_ctor_get(v_s_2504_, 1);
v_endExclusive_2508_ = lean_ctor_get(v_s_2504_, 2);
v___x_2509_ = lean_nat_add(v_startInclusive_2507_, v_curr_2505_);
lean_inc(v_endExclusive_2508_);
lean_inc(v___x_2509_);
lean_inc_ref(v_str_2506_);
v___x_2510_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2510_, 0, v_str_2506_);
lean_ctor_set(v___x_2510_, 1, v___x_2509_);
lean_ctor_set(v___x_2510_, 2, v_endExclusive_2508_);
v___x_2519_ = lean_unsigned_to_nat(0u);
v___x_2520_ = lean_nat_sub(v_endExclusive_2508_, v___x_2509_);
v___x_2521_ = lean_nat_dec_eq(v___x_2519_, v___x_2520_);
lean_dec(v___x_2520_);
if (v___x_2521_ == 0)
{
uint32_t v___x_2522_; uint8_t v___y_2524_; uint32_t v___x_2529_; uint8_t v___x_2530_; 
v___x_2522_ = lean_string_utf8_get_fast(v_str_2506_, v___x_2509_);
v___x_2529_ = 32;
v___x_2530_ = lean_uint32_dec_eq(v___x_2522_, v___x_2529_);
if (v___x_2530_ == 0)
{
uint32_t v___x_2531_; uint8_t v___x_2532_; 
v___x_2531_ = 9;
v___x_2532_ = lean_uint32_dec_eq(v___x_2522_, v___x_2531_);
v___y_2524_ = v___x_2532_;
goto v___jp_2523_;
}
else
{
v___y_2524_ = v___x_2530_;
goto v___jp_2523_;
}
v___jp_2523_:
{
if (v___y_2524_ == 0)
{
uint32_t v___x_2525_; uint8_t v___x_2526_; 
v___x_2525_ = 13;
v___x_2526_ = lean_uint32_dec_eq(v___x_2522_, v___x_2525_);
if (v___x_2526_ == 0)
{
uint32_t v___x_2527_; uint8_t v___x_2528_; 
v___x_2527_ = 10;
v___x_2528_ = lean_uint32_dec_eq(v___x_2522_, v___x_2527_);
v___y_2518_ = v___x_2528_;
goto v___jp_2517_;
}
else
{
v___y_2518_ = v___x_2526_;
goto v___jp_2517_;
}
}
else
{
goto v___jp_2511_;
}
}
}
else
{
lean_dec(v___x_2509_);
lean_dec(v_curr_2505_);
return v___x_2510_;
}
v___jp_2511_:
{
lean_object* v___x_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; uint8_t v___x_2515_; 
v___x_2512_ = lean_string_utf8_next_fast(v_str_2506_, v___x_2509_);
v___x_2513_ = lean_nat_sub(v___x_2512_, v___x_2509_);
lean_dec(v___x_2509_);
v___x_2514_ = lean_nat_add(v_curr_2505_, v___x_2513_);
lean_dec(v___x_2513_);
v___x_2515_ = lean_nat_dec_lt(v_curr_2505_, v___x_2514_);
lean_dec(v_curr_2505_);
if (v___x_2515_ == 0)
{
lean_dec(v___x_2514_);
return v___x_2510_;
}
else
{
lean_dec_ref(v___x_2510_);
v_curr_2505_ = v___x_2514_;
goto _start;
}
}
v___jp_2517_:
{
if (v___y_2518_ == 0)
{
lean_dec(v___x_2509_);
lean_dec(v_curr_2505_);
return v___x_2510_;
}
else
{
goto v___jp_2511_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_Slice_trimAscii_spec__0___boxed(lean_object* v_s_2533_, lean_object* v_curr_2534_){
_start:
{
lean_object* v_res_2535_; 
v_res_2535_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_Slice_trimAscii_spec__0(v_s_2533_, v_curr_2534_);
lean_dec_ref(v_s_2533_);
return v_res_2535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_Slice_trimAscii_spec__1(lean_object* v_s_2536_, lean_object* v_curr_2537_){
_start:
{
lean_object* v_str_2538_; lean_object* v_startInclusive_2539_; lean_object* v___x_2540_; lean_object* v___x_2541_; lean_object* v___x_2542_; lean_object* v___x_2543_; uint8_t v___x_2544_; 
v_str_2538_ = lean_ctor_get(v_s_2536_, 0);
v_startInclusive_2539_ = lean_ctor_get(v_s_2536_, 1);
v___x_2540_ = lean_nat_add(v_startInclusive_2539_, v_curr_2537_);
lean_inc(v___x_2540_);
lean_inc(v_startInclusive_2539_);
lean_inc_ref(v_str_2538_);
v___x_2541_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2541_, 0, v_str_2538_);
lean_ctor_set(v___x_2541_, 1, v_startInclusive_2539_);
lean_ctor_set(v___x_2541_, 2, v___x_2540_);
v___x_2542_ = lean_nat_sub(v___x_2540_, v_startInclusive_2539_);
lean_dec(v___x_2540_);
v___x_2543_ = lean_unsigned_to_nat(0u);
v___x_2544_ = lean_nat_dec_eq(v___x_2542_, v___x_2543_);
if (v___x_2544_ == 0)
{
lean_object* v___x_2545_; lean_object* v___x_2546_; lean_object* v___x_2547_; uint8_t v___y_2552_; lean_object* v___x_2553_; uint32_t v___x_2554_; uint8_t v___y_2556_; uint32_t v___x_2561_; uint8_t v___x_2562_; 
v___x_2545_ = lean_unsigned_to_nat(1u);
v___x_2546_ = lean_nat_sub(v___x_2542_, v___x_2545_);
lean_dec(v___x_2542_);
v___x_2547_ = l_String_Slice_posLE(v___x_2541_, v___x_2546_);
v___x_2553_ = lean_nat_add(v_startInclusive_2539_, v___x_2547_);
v___x_2554_ = lean_string_utf8_get_fast(v_str_2538_, v___x_2553_);
lean_dec(v___x_2553_);
v___x_2561_ = 32;
v___x_2562_ = lean_uint32_dec_eq(v___x_2554_, v___x_2561_);
if (v___x_2562_ == 0)
{
uint32_t v___x_2563_; uint8_t v___x_2564_; 
v___x_2563_ = 9;
v___x_2564_ = lean_uint32_dec_eq(v___x_2554_, v___x_2563_);
v___y_2556_ = v___x_2564_;
goto v___jp_2555_;
}
else
{
v___y_2556_ = v___x_2562_;
goto v___jp_2555_;
}
v___jp_2548_:
{
uint8_t v___x_2549_; 
v___x_2549_ = lean_nat_dec_lt(v___x_2547_, v_curr_2537_);
lean_dec(v_curr_2537_);
if (v___x_2549_ == 0)
{
lean_dec(v___x_2547_);
return v___x_2541_;
}
else
{
lean_dec_ref(v___x_2541_);
v_curr_2537_ = v___x_2547_;
goto _start;
}
}
v___jp_2551_:
{
if (v___y_2552_ == 0)
{
lean_dec(v___x_2547_);
lean_dec(v_curr_2537_);
return v___x_2541_;
}
else
{
goto v___jp_2548_;
}
}
v___jp_2555_:
{
if (v___y_2556_ == 0)
{
uint32_t v___x_2557_; uint8_t v___x_2558_; 
v___x_2557_ = 13;
v___x_2558_ = lean_uint32_dec_eq(v___x_2554_, v___x_2557_);
if (v___x_2558_ == 0)
{
uint32_t v___x_2559_; uint8_t v___x_2560_; 
v___x_2559_ = 10;
v___x_2560_ = lean_uint32_dec_eq(v___x_2554_, v___x_2559_);
v___y_2552_ = v___x_2560_;
goto v___jp_2551_;
}
else
{
v___y_2552_ = v___x_2558_;
goto v___jp_2551_;
}
}
else
{
goto v___jp_2548_;
}
}
}
else
{
lean_dec(v___x_2542_);
lean_dec(v_curr_2537_);
return v___x_2541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_Slice_trimAscii_spec__1___boxed(lean_object* v_s_2565_, lean_object* v_curr_2566_){
_start:
{
lean_object* v_res_2567_; 
v_res_2567_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_Slice_trimAscii_spec__1(v_s_2565_, v_curr_2566_);
lean_dec_ref(v_s_2565_);
return v_res_2567_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAscii(lean_object* v_s_2568_){
_start:
{
lean_object* v___x_2569_; lean_object* v___x_2570_; lean_object* v_startInclusive_2571_; lean_object* v_endExclusive_2572_; lean_object* v___x_2573_; lean_object* v___x_2574_; 
v___x_2569_ = lean_unsigned_to_nat(0u);
v___x_2570_ = l___private_Init_Data_String_Slice_0__String_Slice_dropWhile_go___at___00String_Slice_trimAscii_spec__0(v_s_2568_, v___x_2569_);
v_startInclusive_2571_ = lean_ctor_get(v___x_2570_, 1);
lean_inc(v_startInclusive_2571_);
v_endExclusive_2572_ = lean_ctor_get(v___x_2570_, 2);
lean_inc(v_endExclusive_2572_);
v___x_2573_ = lean_nat_sub(v_endExclusive_2572_, v_startInclusive_2571_);
lean_dec(v_startInclusive_2571_);
lean_dec(v_endExclusive_2572_);
v___x_2574_ = l___private_Init_Data_String_Slice_0__String_Slice_dropEndWhile_go___at___00String_Slice_trimAscii_spec__1(v___x_2570_, v___x_2573_);
lean_dec_ref(v___x_2570_);
return v___x_2574_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAscii___boxed(lean_object* v_s_2575_){
_start:
{
lean_object* v_res_2576_; 
v_res_2576_ = l_String_Slice_trimAscii(v_s_2575_);
lean_dec_ref(v_s_2575_);
return v_res_2576_;
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(lean_object* v_s1_2577_, lean_object* v_s1Curr_2578_, lean_object* v_s2_2579_, lean_object* v_s2Curr_2580_){
_start:
{
uint8_t v___y_2582_; uint8_t v___y_2583_; uint8_t v___y_2590_; uint8_t v___y_2591_; uint8_t v___y_2592_; lean_object* v_str_2595_; lean_object* v_startInclusive_2596_; lean_object* v_endExclusive_2597_; lean_object* v___x_2598_; uint8_t v___x_2605_; 
v_str_2595_ = lean_ctor_get(v_s1_2577_, 0);
v_startInclusive_2596_ = lean_ctor_get(v_s1_2577_, 1);
v_endExclusive_2597_ = lean_ctor_get(v_s1_2577_, 2);
v___x_2598_ = lean_nat_sub(v_endExclusive_2597_, v_startInclusive_2596_);
v___x_2605_ = lean_nat_dec_lt(v_s1Curr_2578_, v___x_2598_);
if (v___x_2605_ == 0)
{
goto v___jp_2599_;
}
else
{
lean_object* v_str_2606_; lean_object* v_startInclusive_2607_; lean_object* v_endExclusive_2608_; uint8_t v___y_2610_; lean_object* v___x_2617_; uint8_t v___x_2618_; 
v_str_2606_ = lean_ctor_get(v_s2_2579_, 0);
v_startInclusive_2607_ = lean_ctor_get(v_s2_2579_, 1);
v_endExclusive_2608_ = lean_ctor_get(v_s2_2579_, 2);
v___x_2617_ = lean_nat_sub(v_endExclusive_2608_, v_startInclusive_2607_);
v___x_2618_ = lean_nat_dec_lt(v_s2Curr_2580_, v___x_2617_);
lean_dec(v___x_2617_);
if (v___x_2618_ == 0)
{
goto v___jp_2599_;
}
else
{
lean_object* v___x_2619_; uint8_t v___x_2620_; uint8_t v___y_2622_; uint8_t v___x_2625_; uint8_t v___x_2626_; 
lean_dec(v___x_2598_);
v___x_2619_ = lean_nat_add(v_startInclusive_2596_, v_s1Curr_2578_);
v___x_2620_ = lean_string_get_byte_fast(v_str_2595_, v___x_2619_);
v___x_2625_ = 65;
v___x_2626_ = lean_uint8_dec_le(v___x_2625_, v___x_2620_);
if (v___x_2626_ == 0)
{
v___y_2622_ = v___x_2626_;
goto v___jp_2621_;
}
else
{
uint8_t v___x_2627_; uint8_t v___x_2628_; 
v___x_2627_ = 90;
v___x_2628_ = lean_uint8_dec_le(v___x_2620_, v___x_2627_);
v___y_2622_ = v___x_2628_;
goto v___jp_2621_;
}
v___jp_2621_:
{
if (v___y_2622_ == 0)
{
v___y_2610_ = v___x_2620_;
goto v___jp_2609_;
}
else
{
uint8_t v___x_2623_; uint8_t v___x_2624_; 
v___x_2623_ = 32;
v___x_2624_ = lean_uint8_add(v___x_2620_, v___x_2623_);
v___y_2610_ = v___x_2624_;
goto v___jp_2609_;
}
}
}
v___jp_2609_:
{
lean_object* v___x_2611_; uint8_t v___x_2612_; uint8_t v___x_2613_; uint8_t v___x_2614_; 
v___x_2611_ = lean_nat_add(v_startInclusive_2607_, v_s2Curr_2580_);
v___x_2612_ = lean_string_get_byte_fast(v_str_2606_, v___x_2611_);
v___x_2613_ = 65;
v___x_2614_ = lean_uint8_dec_le(v___x_2613_, v___x_2612_);
if (v___x_2614_ == 0)
{
v___y_2590_ = v___x_2612_;
v___y_2591_ = v___y_2610_;
v___y_2592_ = v___x_2614_;
goto v___jp_2589_;
}
else
{
uint8_t v___x_2615_; uint8_t v___x_2616_; 
v___x_2615_ = 90;
v___x_2616_ = lean_uint8_dec_le(v___x_2612_, v___x_2615_);
v___y_2590_ = v___x_2612_;
v___y_2591_ = v___y_2610_;
v___y_2592_ = v___x_2616_;
goto v___jp_2589_;
}
}
}
v___jp_2581_:
{
uint8_t v___x_2584_; 
v___x_2584_ = lean_uint8_dec_eq(v___y_2582_, v___y_2583_);
if (v___x_2584_ == 0)
{
lean_dec(v_s2Curr_2580_);
lean_dec(v_s1Curr_2578_);
return v___x_2584_;
}
else
{
lean_object* v___x_2585_; lean_object* v___x_2586_; lean_object* v___x_2587_; 
v___x_2585_ = lean_unsigned_to_nat(1u);
v___x_2586_ = lean_nat_add(v_s1Curr_2578_, v___x_2585_);
lean_dec(v_s1Curr_2578_);
v___x_2587_ = lean_nat_add(v_s2Curr_2580_, v___x_2585_);
lean_dec(v_s2Curr_2580_);
v_s1Curr_2578_ = v___x_2586_;
v_s2Curr_2580_ = v___x_2587_;
goto _start;
}
}
v___jp_2589_:
{
if (v___y_2592_ == 0)
{
v___y_2582_ = v___y_2591_;
v___y_2583_ = v___y_2590_;
goto v___jp_2581_;
}
else
{
uint8_t v___x_2593_; uint8_t v___x_2594_; 
v___x_2593_ = 32;
v___x_2594_ = lean_uint8_add(v___y_2590_, v___x_2593_);
v___y_2582_ = v___y_2591_;
v___y_2583_ = v___x_2594_;
goto v___jp_2581_;
}
}
v___jp_2599_:
{
uint8_t v___x_2600_; 
v___x_2600_ = lean_nat_dec_eq(v_s1Curr_2578_, v___x_2598_);
lean_dec(v___x_2598_);
lean_dec(v_s1Curr_2578_);
if (v___x_2600_ == 0)
{
lean_dec(v_s2Curr_2580_);
return v___x_2600_;
}
else
{
lean_object* v_startInclusive_2601_; lean_object* v_endExclusive_2602_; lean_object* v___x_2603_; uint8_t v___x_2604_; 
v_startInclusive_2601_ = lean_ctor_get(v_s2_2579_, 1);
v_endExclusive_2602_ = lean_ctor_get(v_s2_2579_, 2);
v___x_2603_ = lean_nat_sub(v_endExclusive_2602_, v_startInclusive_2601_);
v___x_2604_ = lean_nat_dec_eq(v_s2Curr_2580_, v___x_2603_);
lean_dec(v___x_2603_);
lean_dec(v_s2Curr_2580_);
return v___x_2604_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object* v_s1_2629_, lean_object* v_s1Curr_2630_, lean_object* v_s2_2631_, lean_object* v_s2Curr_2632_){
_start:
{
uint8_t v_res_2633_; lean_object* v_r_2634_; 
v_res_2633_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_2629_, v_s1Curr_2630_, v_s2_2631_, v_s2Curr_2632_);
lean_dec_ref(v_s2_2631_);
lean_dec_ref(v_s1_2629_);
v_r_2634_ = lean_box(v_res_2633_);
return v_r_2634_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object* v_s1_2635_, lean_object* v_s2_2636_){
_start:
{
lean_object* v_startInclusive_2637_; lean_object* v_endExclusive_2638_; lean_object* v_startInclusive_2639_; lean_object* v_endExclusive_2640_; lean_object* v___x_2641_; lean_object* v___x_2642_; uint8_t v___x_2643_; 
v_startInclusive_2637_ = lean_ctor_get(v_s1_2635_, 1);
v_endExclusive_2638_ = lean_ctor_get(v_s1_2635_, 2);
v_startInclusive_2639_ = lean_ctor_get(v_s2_2636_, 1);
v_endExclusive_2640_ = lean_ctor_get(v_s2_2636_, 2);
v___x_2641_ = lean_nat_sub(v_endExclusive_2638_, v_startInclusive_2637_);
v___x_2642_ = lean_nat_sub(v_endExclusive_2640_, v_startInclusive_2639_);
v___x_2643_ = lean_nat_dec_eq(v___x_2641_, v___x_2642_);
lean_dec(v___x_2642_);
lean_dec(v___x_2641_);
if (v___x_2643_ == 0)
{
return v___x_2643_;
}
else
{
lean_object* v___x_2644_; uint8_t v___x_2645_; 
v___x_2644_ = lean_unsigned_to_nat(0u);
v___x_2645_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_2635_, v___x_2644_, v_s2_2636_, v___x_2644_);
return v___x_2645_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object* v_s1_2646_, lean_object* v_s2_2647_){
_start:
{
uint8_t v_res_2648_; lean_object* v_r_2649_; 
v_res_2648_ = l_String_Slice_eqIgnoreAsciiCase(v_s1_2646_, v_s2_2647_);
lean_dec_ref(v_s2_2647_);
lean_dec_ref(v_s1_2646_);
v_r_2649_ = lean_box(v_res_2648_);
return v_r_2649_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines_lineMap(lean_object* v_s_2650_){
_start:
{
lean_object* v_str_2651_; lean_object* v_startInclusive_2652_; lean_object* v_endExclusive_2653_; lean_object* v___x_2654_; lean_object* v___x_2655_; uint8_t v___x_2656_; 
v_str_2651_ = lean_ctor_get(v_s_2650_, 0);
v_startInclusive_2652_ = lean_ctor_get(v_s_2650_, 1);
v_endExclusive_2653_ = lean_ctor_get(v_s_2650_, 2);
v___x_2654_ = lean_nat_sub(v_endExclusive_2653_, v_startInclusive_2652_);
v___x_2655_ = lean_unsigned_to_nat(0u);
v___x_2656_ = lean_nat_dec_eq(v___x_2654_, v___x_2655_);
if (v___x_2656_ == 0)
{
uint32_t v___x_2657_; lean_object* v___x_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; lean_object* v___x_2661_; uint32_t v___x_2662_; uint8_t v___x_2663_; 
v___x_2657_ = 10;
v___x_2658_ = lean_unsigned_to_nat(1u);
v___x_2659_ = lean_nat_sub(v___x_2654_, v___x_2658_);
lean_dec(v___x_2654_);
v___x_2660_ = l_String_Slice_posLE(v_s_2650_, v___x_2659_);
v___x_2661_ = lean_nat_add(v_startInclusive_2652_, v___x_2660_);
lean_dec(v___x_2660_);
v___x_2662_ = lean_string_utf8_get_fast(v_str_2651_, v___x_2661_);
v___x_2663_ = lean_uint32_dec_eq(v___x_2662_, v___x_2657_);
if (v___x_2663_ == 0)
{
lean_dec(v___x_2661_);
return v_s_2650_;
}
else
{
lean_object* v___x_2665_; uint8_t v_isShared_2666_; uint8_t v_isSharedCheck_2679_; 
lean_inc(v_startInclusive_2652_);
lean_inc_ref(v_str_2651_);
v_isSharedCheck_2679_ = !lean_is_exclusive(v_s_2650_);
if (v_isSharedCheck_2679_ == 0)
{
lean_object* v_unused_2680_; lean_object* v_unused_2681_; lean_object* v_unused_2682_; 
v_unused_2680_ = lean_ctor_get(v_s_2650_, 2);
lean_dec(v_unused_2680_);
v_unused_2681_ = lean_ctor_get(v_s_2650_, 1);
lean_dec(v_unused_2681_);
v_unused_2682_ = lean_ctor_get(v_s_2650_, 0);
lean_dec(v_unused_2682_);
v___x_2665_ = v_s_2650_;
v_isShared_2666_ = v_isSharedCheck_2679_;
goto v_resetjp_2664_;
}
else
{
lean_dec(v_s_2650_);
v___x_2665_ = lean_box(0);
v_isShared_2666_ = v_isSharedCheck_2679_;
goto v_resetjp_2664_;
}
v_resetjp_2664_:
{
lean_object* v___x_2668_; 
lean_inc(v___x_2661_);
lean_inc(v_startInclusive_2652_);
lean_inc_ref(v_str_2651_);
if (v_isShared_2666_ == 0)
{
lean_ctor_set(v___x_2665_, 2, v___x_2661_);
v___x_2668_ = v___x_2665_;
goto v_reusejp_2667_;
}
else
{
lean_object* v_reuseFailAlloc_2678_; 
v_reuseFailAlloc_2678_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2678_, 0, v_str_2651_);
lean_ctor_set(v_reuseFailAlloc_2678_, 1, v_startInclusive_2652_);
lean_ctor_set(v_reuseFailAlloc_2678_, 2, v___x_2661_);
v___x_2668_ = v_reuseFailAlloc_2678_;
goto v_reusejp_2667_;
}
v_reusejp_2667_:
{
lean_object* v___x_2669_; uint8_t v___x_2670_; 
v___x_2669_ = lean_nat_sub(v___x_2661_, v_startInclusive_2652_);
lean_dec(v___x_2661_);
v___x_2670_ = lean_nat_dec_eq(v___x_2669_, v___x_2655_);
if (v___x_2670_ == 0)
{
uint32_t v___x_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; uint32_t v___x_2675_; uint8_t v___x_2676_; 
v___x_2671_ = 13;
v___x_2672_ = lean_nat_sub(v___x_2669_, v___x_2658_);
lean_dec(v___x_2669_);
v___x_2673_ = l_String_Slice_posLE(v___x_2668_, v___x_2672_);
v___x_2674_ = lean_nat_add(v_startInclusive_2652_, v___x_2673_);
lean_dec(v___x_2673_);
v___x_2675_ = lean_string_utf8_get_fast(v_str_2651_, v___x_2674_);
v___x_2676_ = lean_uint32_dec_eq(v___x_2675_, v___x_2671_);
if (v___x_2676_ == 0)
{
lean_dec(v___x_2674_);
lean_dec(v_startInclusive_2652_);
lean_dec_ref(v_str_2651_);
return v___x_2668_;
}
else
{
lean_object* v___x_2677_; 
lean_dec_ref(v___x_2668_);
v___x_2677_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2677_, 0, v_str_2651_);
lean_ctor_set(v___x_2677_, 1, v_startInclusive_2652_);
lean_ctor_set(v___x_2677_, 2, v___x_2674_);
return v___x_2677_;
}
}
else
{
lean_dec(v___x_2669_);
lean_dec(v_startInclusive_2652_);
lean_dec_ref(v_str_2651_);
return v___x_2668_;
}
}
}
}
}
else
{
lean_dec(v___x_2654_);
return v_s_2650_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(lean_object* v_s_2685_){
_start:
{
lean_object* v___x_2686_; 
v___x_2686_ = ((lean_object*)(l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0));
return v___x_2686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(lean_object* v_s_2687_){
_start:
{
lean_object* v_res_2688_; 
v_res_2688_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_2687_);
lean_dec_ref(v_s_2687_);
return v_res_2688_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines(lean_object* v_s_2689_){
_start:
{
lean_object* v___x_2690_; 
v___x_2690_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_2689_);
return v___x_2690_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines___boxed(lean_object* v_s_2691_){
_start:
{
lean_object* v_res_2692_; 
v_res_2692_ = l_String_Slice_lines(v_s_2691_);
lean_dec_ref(v_s_2691_);
return v_res_2692_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___lam__0(lean_object* v_endExclusive_2693_, lean_object* v_startInclusive_2694_, lean_object* v_str_2695_, uint8_t v___x_2696_, uint8_t v___x_2697_, lean_object* v_it_2698_, lean_object* v_acc_2699_, lean_object* v_hP_2700_, lean_object* v_recur_2701_){
_start:
{
lean_object* v___x_2702_; uint8_t v___x_2703_; 
v___x_2702_ = lean_nat_sub(v_endExclusive_2693_, v_startInclusive_2694_);
v___x_2703_ = lean_nat_dec_eq(v_it_2698_, v___x_2702_);
lean_dec(v___x_2702_);
if (v___x_2703_ == 0)
{
lean_object* v_snd_2704_; lean_object* v_snd_2705_; lean_object* v_fst_2706_; lean_object* v___x_2708_; uint8_t v_isShared_2709_; uint8_t v_isSharedCheck_2767_; 
v_snd_2704_ = lean_ctor_get(v_acc_2699_, 1);
lean_inc(v_snd_2704_);
v_snd_2705_ = lean_ctor_get(v_snd_2704_, 1);
lean_inc(v_snd_2705_);
v_fst_2706_ = lean_ctor_get(v_acc_2699_, 0);
v_isSharedCheck_2767_ = !lean_is_exclusive(v_acc_2699_);
if (v_isSharedCheck_2767_ == 0)
{
lean_object* v_unused_2768_; 
v_unused_2768_ = lean_ctor_get(v_acc_2699_, 1);
lean_dec(v_unused_2768_);
v___x_2708_ = v_acc_2699_;
v_isShared_2709_ = v_isSharedCheck_2767_;
goto v_resetjp_2707_;
}
else
{
lean_inc(v_fst_2706_);
lean_dec(v_acc_2699_);
v___x_2708_ = lean_box(0);
v_isShared_2709_ = v_isSharedCheck_2767_;
goto v_resetjp_2707_;
}
v_resetjp_2707_:
{
lean_object* v_fst_2710_; lean_object* v___x_2712_; uint8_t v_isShared_2713_; uint8_t v_isSharedCheck_2765_; 
v_fst_2710_ = lean_ctor_get(v_snd_2704_, 0);
v_isSharedCheck_2765_ = !lean_is_exclusive(v_snd_2704_);
if (v_isSharedCheck_2765_ == 0)
{
lean_object* v_unused_2766_; 
v_unused_2766_ = lean_ctor_get(v_snd_2704_, 1);
lean_dec(v_unused_2766_);
v___x_2712_ = v_snd_2704_;
v_isShared_2713_ = v_isSharedCheck_2765_;
goto v_resetjp_2711_;
}
else
{
lean_inc(v_fst_2710_);
lean_dec(v_snd_2704_);
v___x_2712_ = lean_box(0);
v_isShared_2713_ = v_isSharedCheck_2765_;
goto v_resetjp_2711_;
}
v_resetjp_2711_:
{
lean_object* v_snd_2714_; lean_object* v___x_2716_; uint8_t v_isShared_2717_; uint8_t v_isSharedCheck_2763_; 
v_snd_2714_ = lean_ctor_get(v_snd_2705_, 1);
v_isSharedCheck_2763_ = !lean_is_exclusive(v_snd_2705_);
if (v_isSharedCheck_2763_ == 0)
{
lean_object* v_unused_2764_; 
v_unused_2764_ = lean_ctor_get(v_snd_2705_, 0);
lean_dec(v_unused_2764_);
v___x_2716_ = v_snd_2705_;
v_isShared_2717_ = v_isSharedCheck_2763_;
goto v_resetjp_2715_;
}
else
{
lean_inc(v_snd_2714_);
lean_dec(v_snd_2705_);
v___x_2716_ = lean_box(0);
v_isShared_2717_ = v_isSharedCheck_2763_;
goto v_resetjp_2715_;
}
v_resetjp_2715_:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint32_t v___x_2721_; uint8_t v___y_2723_; uint8_t v___y_2724_; uint8_t v___y_2742_; uint8_t v___y_2743_; uint8_t v___y_2748_; uint8_t v___y_2749_; uint8_t v___y_2754_; uint32_t v___x_2759_; uint8_t v___x_2760_; 
v___x_2718_ = lean_nat_add(v_startInclusive_2694_, v_it_2698_);
v___x_2719_ = lean_string_utf8_next_fast(v_str_2695_, v___x_2718_);
v___x_2720_ = lean_nat_sub(v___x_2719_, v_startInclusive_2694_);
v___x_2721_ = lean_string_utf8_get_fast(v_str_2695_, v___x_2718_);
lean_dec(v___x_2718_);
v___x_2759_ = 48;
v___x_2760_ = lean_uint32_dec_le(v___x_2759_, v___x_2721_);
if (v___x_2760_ == 0)
{
v___y_2754_ = v___x_2760_;
goto v___jp_2753_;
}
else
{
uint32_t v___x_2761_; uint8_t v___x_2762_; 
v___x_2761_ = 57;
v___x_2762_ = lean_uint32_dec_le(v___x_2721_, v___x_2761_);
v___y_2754_ = v___x_2762_;
goto v___jp_2753_;
}
v___jp_2722_:
{
uint32_t v___x_2725_; uint8_t v___x_2726_; lean_object* v___x_2727_; lean_object* v___x_2728_; lean_object* v___x_2730_; 
v___x_2725_ = 95;
v___x_2726_ = lean_uint32_dec_eq(v___x_2721_, v___x_2725_);
v___x_2727_ = lean_box(v___y_2723_);
v___x_2728_ = lean_box(v___y_2724_);
if (v_isShared_2717_ == 0)
{
lean_ctor_set(v___x_2716_, 1, v___x_2728_);
lean_ctor_set(v___x_2716_, 0, v___x_2727_);
v___x_2730_ = v___x_2716_;
goto v_reusejp_2729_;
}
else
{
lean_object* v_reuseFailAlloc_2740_; 
v_reuseFailAlloc_2740_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2740_, 0, v___x_2727_);
lean_ctor_set(v_reuseFailAlloc_2740_, 1, v___x_2728_);
v___x_2730_ = v_reuseFailAlloc_2740_;
goto v_reusejp_2729_;
}
v_reusejp_2729_:
{
lean_object* v___x_2731_; lean_object* v___x_2733_; 
v___x_2731_ = lean_box(v___x_2726_);
if (v_isShared_2713_ == 0)
{
lean_ctor_set(v___x_2712_, 1, v___x_2730_);
lean_ctor_set(v___x_2712_, 0, v___x_2731_);
v___x_2733_ = v___x_2712_;
goto v_reusejp_2732_;
}
else
{
lean_object* v_reuseFailAlloc_2739_; 
v_reuseFailAlloc_2739_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2739_, 0, v___x_2731_);
lean_ctor_set(v_reuseFailAlloc_2739_, 1, v___x_2730_);
v___x_2733_ = v_reuseFailAlloc_2739_;
goto v_reusejp_2732_;
}
v_reusejp_2732_:
{
lean_object* v___x_2734_; lean_object* v___x_2736_; 
v___x_2734_ = lean_box(v___x_2696_);
if (v_isShared_2709_ == 0)
{
lean_ctor_set(v___x_2708_, 1, v___x_2733_);
lean_ctor_set(v___x_2708_, 0, v___x_2734_);
v___x_2736_ = v___x_2708_;
goto v_reusejp_2735_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v___x_2734_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v___x_2733_);
v___x_2736_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2735_;
}
v_reusejp_2735_:
{
lean_object* v___x_2737_; 
v___x_2737_ = lean_apply_4(v_recur_2701_, v___x_2720_, v___x_2736_, lean_box(0), lean_box(0));
return v___x_2737_;
}
}
}
}
v___jp_2741_:
{
uint8_t v___x_2744_; 
v___x_2744_ = lean_unbox(v_fst_2710_);
lean_dec(v_fst_2710_);
if (v___x_2744_ == 0)
{
v___y_2723_ = v___y_2742_;
v___y_2724_ = v___y_2743_;
goto v___jp_2722_;
}
else
{
uint32_t v___x_2745_; uint8_t v___x_2746_; 
v___x_2745_ = 95;
v___x_2746_ = lean_uint32_dec_eq(v___x_2721_, v___x_2745_);
if (v___x_2746_ == 0)
{
v___y_2723_ = v___y_2742_;
v___y_2724_ = v___y_2743_;
goto v___jp_2722_;
}
else
{
v___y_2723_ = v___y_2742_;
v___y_2724_ = v___x_2696_;
goto v___jp_2722_;
}
}
}
v___jp_2747_:
{
uint8_t v___x_2750_; 
v___x_2750_ = lean_unbox(v_fst_2706_);
lean_dec(v_fst_2706_);
if (v___x_2750_ == 0)
{
v___y_2742_ = v___y_2748_;
v___y_2743_ = v___y_2749_;
goto v___jp_2741_;
}
else
{
uint32_t v___x_2751_; uint8_t v___x_2752_; 
v___x_2751_ = 95;
v___x_2752_ = lean_uint32_dec_eq(v___x_2721_, v___x_2751_);
if (v___x_2752_ == 0)
{
v___y_2742_ = v___y_2748_;
v___y_2743_ = v___y_2749_;
goto v___jp_2741_;
}
else
{
if (v___x_2696_ == 0)
{
lean_dec(v_fst_2710_);
v___y_2723_ = v___y_2748_;
v___y_2724_ = v___x_2696_;
goto v___jp_2722_;
}
else
{
v___y_2742_ = v___y_2748_;
v___y_2743_ = v___x_2696_;
goto v___jp_2741_;
}
}
}
}
v___jp_2753_:
{
uint8_t v___x_2755_; 
v___x_2755_ = lean_unbox(v_snd_2714_);
if (v___x_2755_ == 0)
{
uint8_t v___x_2756_; 
lean_dec(v_fst_2710_);
lean_dec(v_fst_2706_);
v___x_2756_ = lean_unbox(v_snd_2714_);
lean_dec(v_snd_2714_);
v___y_2723_ = v___y_2754_;
v___y_2724_ = v___x_2756_;
goto v___jp_2722_;
}
else
{
lean_dec(v_snd_2714_);
if (v___y_2754_ == 0)
{
uint32_t v___x_2757_; uint8_t v___x_2758_; 
v___x_2757_ = 95;
v___x_2758_ = lean_uint32_dec_eq(v___x_2721_, v___x_2757_);
if (v___x_2758_ == 0)
{
lean_dec(v_fst_2710_);
lean_dec(v_fst_2706_);
v___y_2723_ = v___y_2754_;
v___y_2724_ = v___x_2758_;
goto v___jp_2722_;
}
else
{
v___y_2748_ = v___y_2754_;
v___y_2749_ = v___x_2758_;
goto v___jp_2747_;
}
}
else
{
v___y_2748_ = v___y_2754_;
v___y_2749_ = v___x_2697_;
goto v___jp_2747_;
}
}
}
}
}
}
}
else
{
lean_dec_ref(v_recur_2701_);
return v_acc_2699_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___lam__0___boxed(lean_object* v_endExclusive_2769_, lean_object* v_startInclusive_2770_, lean_object* v_str_2771_, lean_object* v___x_2772_, lean_object* v___x_2773_, lean_object* v_it_2774_, lean_object* v_acc_2775_, lean_object* v_hP_2776_, lean_object* v_recur_2777_){
_start:
{
uint8_t v___x_966__boxed_2778_; uint8_t v___x_967__boxed_2779_; lean_object* v_res_2780_; 
v___x_966__boxed_2778_ = lean_unbox(v___x_2772_);
v___x_967__boxed_2779_ = lean_unbox(v___x_2773_);
v_res_2780_ = l_String_Slice_isNat___lam__0(v_endExclusive_2769_, v_startInclusive_2770_, v_str_2771_, v___x_966__boxed_2778_, v___x_967__boxed_2779_, v_it_2774_, v_acc_2775_, v_hP_2776_, v_recur_2777_);
lean_dec(v_it_2774_);
lean_dec_ref(v_str_2771_);
lean_dec(v_startInclusive_2770_);
lean_dec(v_endExclusive_2769_);
return v_res_2780_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isNat(lean_object* v_s_2781_){
_start:
{
lean_object* v_str_2782_; lean_object* v_startInclusive_2783_; lean_object* v_endExclusive_2784_; lean_object* v___x_2785_; lean_object* v___x_2786_; uint8_t v___x_2787_; 
v_str_2782_ = lean_ctor_get(v_s_2781_, 0);
v_startInclusive_2783_ = lean_ctor_get(v_s_2781_, 1);
v_endExclusive_2784_ = lean_ctor_get(v_s_2781_, 2);
v___x_2785_ = lean_nat_sub(v_endExclusive_2784_, v_startInclusive_2783_);
v___x_2786_ = lean_unsigned_to_nat(0u);
v___x_2787_ = lean_nat_dec_eq(v___x_2785_, v___x_2786_);
lean_dec(v___x_2785_);
if (v___x_2787_ == 0)
{
uint8_t v___x_2788_; lean_object* v___x_2789_; lean_object* v___x_2790_; lean_object* v___f_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2798_; lean_object* v___x_2799_; lean_object* v_result_2800_; lean_object* v_snd_2801_; lean_object* v_snd_2802_; lean_object* v_snd_2803_; uint8_t v___x_2804_; 
v___x_2788_ = 1;
v___x_2789_ = lean_box(v___x_2787_);
v___x_2790_ = lean_box(v___x_2788_);
lean_inc_ref(v_str_2782_);
lean_inc(v_startInclusive_2783_);
lean_inc(v_endExclusive_2784_);
v___f_2791_ = lean_alloc_closure((void*)(l_String_Slice_isNat___lam__0___boxed), 9, 5);
lean_closure_set(v___f_2791_, 0, v_endExclusive_2784_);
lean_closure_set(v___f_2791_, 1, v_startInclusive_2783_);
lean_closure_set(v___f_2791_, 2, v_str_2782_);
lean_closure_set(v___f_2791_, 3, v___x_2789_);
lean_closure_set(v___f_2791_, 4, v___x_2790_);
v___x_2792_ = lean_box(v___x_2787_);
v___x_2793_ = lean_box(v___x_2788_);
v___x_2794_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2794_, 0, v___x_2792_);
lean_ctor_set(v___x_2794_, 1, v___x_2793_);
v___x_2795_ = lean_box(v___x_2787_);
v___x_2796_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2796_, 0, v___x_2795_);
lean_ctor_set(v___x_2796_, 1, v___x_2794_);
v___x_2797_ = lean_box(v___x_2788_);
v___x_2798_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2798_, 0, v___x_2797_);
lean_ctor_set(v___x_2798_, 1, v___x_2796_);
v___x_2799_ = l_String_Slice_positions(v_s_2781_);
lean_dec_ref(v_s_2781_);
v_result_2800_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2791_, v___x_2799_, v___x_2798_, lean_box(0));
v_snd_2801_ = lean_ctor_get(v_result_2800_, 1);
lean_inc(v_snd_2801_);
lean_dec(v_result_2800_);
v_snd_2802_ = lean_ctor_get(v_snd_2801_, 1);
lean_inc(v_snd_2802_);
lean_dec(v_snd_2801_);
v_snd_2803_ = lean_ctor_get(v_snd_2802_, 1);
v___x_2804_ = lean_unbox(v_snd_2803_);
if (v___x_2804_ == 0)
{
lean_dec(v_snd_2802_);
return v___x_2787_;
}
else
{
lean_object* v_fst_2805_; uint8_t v___x_2806_; 
v_fst_2805_ = lean_ctor_get(v_snd_2802_, 0);
lean_inc(v_fst_2805_);
lean_dec(v_snd_2802_);
v___x_2806_ = lean_unbox(v_fst_2805_);
lean_dec(v_fst_2805_);
return v___x_2806_;
}
}
else
{
uint8_t v___x_2807_; 
lean_dec_ref(v_s_2781_);
v___x_2807_ = 0;
return v___x_2807_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object* v_s_2808_){
_start:
{
uint8_t v_res_2809_; lean_object* v_r_2810_; 
v_res_2809_ = l_String_Slice_isNat(v_s_2808_);
v_r_2810_ = lean_box(v_res_2809_);
return v_r_2810_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object* v_s_2811_, lean_object* v_a_2812_, lean_object* v_b_2813_){
_start:
{
lean_object* v_str_2814_; lean_object* v_startInclusive_2815_; lean_object* v_endExclusive_2816_; lean_object* v___x_2817_; uint8_t v___x_2818_; 
v_str_2814_ = lean_ctor_get(v_s_2811_, 0);
v_startInclusive_2815_ = lean_ctor_get(v_s_2811_, 1);
v_endExclusive_2816_ = lean_ctor_get(v_s_2811_, 2);
v___x_2817_ = lean_nat_sub(v_endExclusive_2816_, v_startInclusive_2815_);
v___x_2818_ = lean_nat_dec_eq(v_a_2812_, v___x_2817_);
lean_dec(v___x_2817_);
if (v___x_2818_ == 0)
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; uint32_t v___x_2822_; uint32_t v___x_2823_; uint8_t v___x_2824_; 
v___x_2819_ = lean_nat_add(v_startInclusive_2815_, v_a_2812_);
lean_dec(v_a_2812_);
v___x_2820_ = lean_string_utf8_next_fast(v_str_2814_, v___x_2819_);
v___x_2821_ = lean_nat_sub(v___x_2820_, v_startInclusive_2815_);
v___x_2822_ = lean_string_utf8_get_fast(v_str_2814_, v___x_2819_);
lean_dec(v___x_2819_);
v___x_2823_ = 95;
v___x_2824_ = lean_uint32_dec_eq(v___x_2822_, v___x_2823_);
if (v___x_2824_ == 0)
{
lean_object* v___x_2825_; lean_object* v___x_2826_; lean_object* v___x_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2830_; 
v___x_2825_ = lean_unsigned_to_nat(10u);
v___x_2826_ = lean_nat_mul(v_b_2813_, v___x_2825_);
lean_dec(v_b_2813_);
v___x_2827_ = lean_uint32_to_nat(v___x_2822_);
v___x_2828_ = lean_unsigned_to_nat(48u);
v___x_2829_ = lean_nat_sub(v___x_2827_, v___x_2828_);
lean_dec(v___x_2827_);
v___x_2830_ = lean_nat_add(v___x_2826_, v___x_2829_);
lean_dec(v___x_2829_);
lean_dec(v___x_2826_);
v_a_2812_ = v___x_2821_;
v_b_2813_ = v___x_2830_;
goto _start;
}
else
{
v_a_2812_ = v___x_2821_;
goto _start;
}
}
else
{
lean_dec(v_a_2812_);
return v_b_2813_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object* v_s_2833_, lean_object* v_a_2834_, lean_object* v_b_2835_){
_start:
{
lean_object* v_res_2836_; 
v_res_2836_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_2833_, v_a_2834_, v_b_2835_);
lean_dec_ref(v_s_2833_);
return v_res_2836_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(lean_object* v___x_2837_, lean_object* v_s_2838_, lean_object* v___x_2839_, lean_object* v_a_2840_, lean_object* v_b_2841_){
_start:
{
lean_object* v_str_2842_; lean_object* v_startInclusive_2843_; lean_object* v_endExclusive_2844_; lean_object* v___x_2845_; uint8_t v___x_2846_; 
v_str_2842_ = lean_ctor_get(v_s_2838_, 0);
v_startInclusive_2843_ = lean_ctor_get(v_s_2838_, 1);
v_endExclusive_2844_ = lean_ctor_get(v_s_2838_, 2);
v___x_2845_ = lean_nat_sub(v_endExclusive_2844_, v_startInclusive_2843_);
v___x_2846_ = lean_nat_dec_eq(v_a_2840_, v___x_2845_);
lean_dec(v___x_2845_);
if (v___x_2846_ == 0)
{
lean_object* v_snd_2847_; lean_object* v_snd_2848_; lean_object* v_fst_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2914_; 
v_snd_2847_ = lean_ctor_get(v_b_2841_, 1);
lean_inc(v_snd_2847_);
v_snd_2848_ = lean_ctor_get(v_snd_2847_, 1);
lean_inc(v_snd_2848_);
v_fst_2849_ = lean_ctor_get(v_b_2841_, 0);
v_isSharedCheck_2914_ = !lean_is_exclusive(v_b_2841_);
if (v_isSharedCheck_2914_ == 0)
{
lean_object* v_unused_2915_; 
v_unused_2915_ = lean_ctor_get(v_b_2841_, 1);
lean_dec(v_unused_2915_);
v___x_2851_ = v_b_2841_;
v_isShared_2852_ = v_isSharedCheck_2914_;
goto v_resetjp_2850_;
}
else
{
lean_inc(v_fst_2849_);
lean_dec(v_b_2841_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2914_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v_fst_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2912_; 
v_fst_2853_ = lean_ctor_get(v_snd_2847_, 0);
v_isSharedCheck_2912_ = !lean_is_exclusive(v_snd_2847_);
if (v_isSharedCheck_2912_ == 0)
{
lean_object* v_unused_2913_; 
v_unused_2913_ = lean_ctor_get(v_snd_2847_, 1);
lean_dec(v_unused_2913_);
v___x_2855_ = v_snd_2847_;
v_isShared_2856_ = v_isSharedCheck_2912_;
goto v_resetjp_2854_;
}
else
{
lean_inc(v_fst_2853_);
lean_dec(v_snd_2847_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2912_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v_snd_2857_; lean_object* v___x_2859_; uint8_t v_isShared_2860_; uint8_t v_isSharedCheck_2910_; 
v_snd_2857_ = lean_ctor_get(v_snd_2848_, 1);
v_isSharedCheck_2910_ = !lean_is_exclusive(v_snd_2848_);
if (v_isSharedCheck_2910_ == 0)
{
lean_object* v_unused_2911_; 
v_unused_2911_ = lean_ctor_get(v_snd_2848_, 0);
lean_dec(v_unused_2911_);
v___x_2859_ = v_snd_2848_;
v_isShared_2860_ = v_isSharedCheck_2910_;
goto v_resetjp_2858_;
}
else
{
lean_inc(v_snd_2857_);
lean_dec(v_snd_2848_);
v___x_2859_ = lean_box(0);
v_isShared_2860_ = v_isSharedCheck_2910_;
goto v_resetjp_2858_;
}
v_resetjp_2858_:
{
lean_object* v___x_2861_; uint8_t v___x_2862_; uint8_t v___x_2863_; lean_object* v___x_2864_; lean_object* v___x_2865_; lean_object* v___x_2866_; lean_object* v___x_2867_; uint32_t v___x_2868_; uint8_t v___y_2870_; uint8_t v___y_2871_; uint8_t v___y_2889_; uint8_t v___y_2890_; uint8_t v___y_2895_; uint8_t v___y_2896_; uint8_t v___y_2901_; uint32_t v___x_2906_; uint8_t v___x_2907_; 
v___x_2861_ = lean_unsigned_to_nat(0u);
v___x_2862_ = lean_nat_dec_eq(v___x_2837_, v___x_2861_);
v___x_2863_ = 1;
v___x_2864_ = lean_nat_add(v___x_2839_, v_a_2840_);
v___x_2865_ = lean_string_utf8_next_fast(v_str_2842_, v___x_2864_);
lean_dec(v___x_2864_);
v___x_2866_ = lean_nat_sub(v___x_2865_, v___x_2839_);
v___x_2867_ = lean_nat_add(v_startInclusive_2843_, v_a_2840_);
lean_dec(v_a_2840_);
v___x_2868_ = lean_string_utf8_get_fast(v_str_2842_, v___x_2867_);
lean_dec(v___x_2867_);
v___x_2906_ = 48;
v___x_2907_ = lean_uint32_dec_le(v___x_2906_, v___x_2868_);
if (v___x_2907_ == 0)
{
v___y_2901_ = v___x_2907_;
goto v___jp_2900_;
}
else
{
uint32_t v___x_2908_; uint8_t v___x_2909_; 
v___x_2908_ = 57;
v___x_2909_ = lean_uint32_dec_le(v___x_2868_, v___x_2908_);
v___y_2901_ = v___x_2909_;
goto v___jp_2900_;
}
v___jp_2869_:
{
uint32_t v___x_2872_; uint8_t v___x_2873_; lean_object* v___x_2874_; lean_object* v___x_2875_; lean_object* v___x_2877_; 
v___x_2872_ = 95;
v___x_2873_ = lean_uint32_dec_eq(v___x_2868_, v___x_2872_);
v___x_2874_ = lean_box(v___y_2870_);
v___x_2875_ = lean_box(v___y_2871_);
if (v_isShared_2860_ == 0)
{
lean_ctor_set(v___x_2859_, 1, v___x_2875_);
lean_ctor_set(v___x_2859_, 0, v___x_2874_);
v___x_2877_ = v___x_2859_;
goto v_reusejp_2876_;
}
else
{
lean_object* v_reuseFailAlloc_2887_; 
v_reuseFailAlloc_2887_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2887_, 0, v___x_2874_);
lean_ctor_set(v_reuseFailAlloc_2887_, 1, v___x_2875_);
v___x_2877_ = v_reuseFailAlloc_2887_;
goto v_reusejp_2876_;
}
v_reusejp_2876_:
{
lean_object* v___x_2878_; lean_object* v___x_2880_; 
v___x_2878_ = lean_box(v___x_2873_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 1, v___x_2877_);
lean_ctor_set(v___x_2855_, 0, v___x_2878_);
v___x_2880_ = v___x_2855_;
goto v_reusejp_2879_;
}
else
{
lean_object* v_reuseFailAlloc_2886_; 
v_reuseFailAlloc_2886_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2886_, 0, v___x_2878_);
lean_ctor_set(v_reuseFailAlloc_2886_, 1, v___x_2877_);
v___x_2880_ = v_reuseFailAlloc_2886_;
goto v_reusejp_2879_;
}
v_reusejp_2879_:
{
lean_object* v___x_2881_; lean_object* v___x_2883_; 
v___x_2881_ = lean_box(v___x_2862_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v___x_2880_);
lean_ctor_set(v___x_2851_, 0, v___x_2881_);
v___x_2883_ = v___x_2851_;
goto v_reusejp_2882_;
}
else
{
lean_object* v_reuseFailAlloc_2885_; 
v_reuseFailAlloc_2885_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2885_, 0, v___x_2881_);
lean_ctor_set(v_reuseFailAlloc_2885_, 1, v___x_2880_);
v___x_2883_ = v_reuseFailAlloc_2885_;
goto v_reusejp_2882_;
}
v_reusejp_2882_:
{
v_a_2840_ = v___x_2866_;
v_b_2841_ = v___x_2883_;
goto _start;
}
}
}
}
v___jp_2888_:
{
uint8_t v___x_2891_; 
v___x_2891_ = lean_unbox(v_fst_2853_);
lean_dec(v_fst_2853_);
if (v___x_2891_ == 0)
{
v___y_2870_ = v___y_2889_;
v___y_2871_ = v___y_2890_;
goto v___jp_2869_;
}
else
{
uint32_t v___x_2892_; uint8_t v___x_2893_; 
v___x_2892_ = 95;
v___x_2893_ = lean_uint32_dec_eq(v___x_2868_, v___x_2892_);
if (v___x_2893_ == 0)
{
v___y_2870_ = v___y_2889_;
v___y_2871_ = v___y_2890_;
goto v___jp_2869_;
}
else
{
v___y_2870_ = v___y_2889_;
v___y_2871_ = v___x_2862_;
goto v___jp_2869_;
}
}
}
v___jp_2894_:
{
uint8_t v___x_2897_; 
v___x_2897_ = lean_unbox(v_fst_2849_);
lean_dec(v_fst_2849_);
if (v___x_2897_ == 0)
{
v___y_2889_ = v___y_2895_;
v___y_2890_ = v___y_2896_;
goto v___jp_2888_;
}
else
{
uint32_t v___x_2898_; uint8_t v___x_2899_; 
v___x_2898_ = 95;
v___x_2899_ = lean_uint32_dec_eq(v___x_2868_, v___x_2898_);
if (v___x_2899_ == 0)
{
v___y_2889_ = v___y_2895_;
v___y_2890_ = v___y_2896_;
goto v___jp_2888_;
}
else
{
if (v___x_2862_ == 0)
{
lean_dec(v_fst_2853_);
v___y_2870_ = v___y_2895_;
v___y_2871_ = v___x_2862_;
goto v___jp_2869_;
}
else
{
v___y_2889_ = v___y_2895_;
v___y_2890_ = v___x_2862_;
goto v___jp_2888_;
}
}
}
}
v___jp_2900_:
{
uint8_t v___x_2902_; 
v___x_2902_ = lean_unbox(v_snd_2857_);
if (v___x_2902_ == 0)
{
uint8_t v___x_2903_; 
lean_dec(v_fst_2853_);
lean_dec(v_fst_2849_);
v___x_2903_ = lean_unbox(v_snd_2857_);
lean_dec(v_snd_2857_);
v___y_2870_ = v___y_2901_;
v___y_2871_ = v___x_2903_;
goto v___jp_2869_;
}
else
{
lean_dec(v_snd_2857_);
if (v___y_2901_ == 0)
{
uint32_t v___x_2904_; uint8_t v___x_2905_; 
v___x_2904_ = 95;
v___x_2905_ = lean_uint32_dec_eq(v___x_2868_, v___x_2904_);
if (v___x_2905_ == 0)
{
lean_dec(v_fst_2853_);
lean_dec(v_fst_2849_);
v___y_2870_ = v___y_2901_;
v___y_2871_ = v___x_2905_;
goto v___jp_2869_;
}
else
{
v___y_2895_ = v___y_2901_;
v___y_2896_ = v___x_2905_;
goto v___jp_2894_;
}
}
else
{
v___y_2895_ = v___y_2901_;
v___y_2896_ = v___x_2863_;
goto v___jp_2894_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_2840_);
return v_b_2841_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg___boxed(lean_object* v___x_2916_, lean_object* v_s_2917_, lean_object* v___x_2918_, lean_object* v_a_2919_, lean_object* v_b_2920_){
_start:
{
lean_object* v_res_2921_; 
v_res_2921_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(v___x_2916_, v_s_2917_, v___x_2918_, v_a_2919_, v_b_2920_);
lean_dec(v___x_2918_);
lean_dec_ref(v_s_2917_);
lean_dec(v___x_2916_);
return v_res_2921_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object* v_s_2922_){
_start:
{
uint8_t v___y_2924_; lean_object* v_startInclusive_2930_; lean_object* v_endExclusive_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; uint8_t v___x_2934_; 
v_startInclusive_2930_ = lean_ctor_get(v_s_2922_, 1);
v_endExclusive_2931_ = lean_ctor_get(v_s_2922_, 2);
v___x_2932_ = lean_nat_sub(v_endExclusive_2931_, v_startInclusive_2930_);
v___x_2933_ = lean_unsigned_to_nat(0u);
v___x_2934_ = lean_nat_dec_eq(v___x_2932_, v___x_2933_);
if (v___x_2934_ == 0)
{
uint8_t v___x_2935_; lean_object* v___x_2936_; lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; lean_object* v___x_2940_; lean_object* v___x_2941_; lean_object* v___x_2942_; lean_object* v___x_2943_; lean_object* v_result_2944_; lean_object* v_snd_2945_; lean_object* v_snd_2946_; lean_object* v_snd_2947_; uint8_t v___x_2948_; 
v___x_2935_ = 1;
v___x_2936_ = lean_box(v___x_2934_);
v___x_2937_ = lean_box(v___x_2935_);
v___x_2938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2938_, 0, v___x_2936_);
lean_ctor_set(v___x_2938_, 1, v___x_2937_);
v___x_2939_ = lean_box(v___x_2934_);
v___x_2940_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2940_, 0, v___x_2939_);
lean_ctor_set(v___x_2940_, 1, v___x_2938_);
v___x_2941_ = lean_box(v___x_2935_);
v___x_2942_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2942_, 0, v___x_2941_);
lean_ctor_set(v___x_2942_, 1, v___x_2940_);
v___x_2943_ = l_String_Slice_positions(v_s_2922_);
v_result_2944_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(v___x_2932_, v_s_2922_, v_startInclusive_2930_, v___x_2943_, v___x_2942_);
lean_dec(v___x_2932_);
v_snd_2945_ = lean_ctor_get(v_result_2944_, 1);
lean_inc(v_snd_2945_);
lean_dec_ref(v_result_2944_);
v_snd_2946_ = lean_ctor_get(v_snd_2945_, 1);
lean_inc(v_snd_2946_);
lean_dec(v_snd_2945_);
v_snd_2947_ = lean_ctor_get(v_snd_2946_, 1);
v___x_2948_ = lean_unbox(v_snd_2947_);
if (v___x_2948_ == 0)
{
lean_dec(v_snd_2946_);
v___y_2924_ = v___x_2934_;
goto v___jp_2923_;
}
else
{
lean_object* v_fst_2949_; uint8_t v___x_2950_; 
v_fst_2949_ = lean_ctor_get(v_snd_2946_, 0);
lean_inc(v_fst_2949_);
lean_dec(v_snd_2946_);
v___x_2950_ = lean_unbox(v_fst_2949_);
lean_dec(v_fst_2949_);
v___y_2924_ = v___x_2950_;
goto v___jp_2923_;
}
}
else
{
lean_object* v___x_2951_; 
lean_dec(v___x_2932_);
v___x_2951_ = lean_box(0);
return v___x_2951_;
}
v___jp_2923_:
{
if (v___y_2924_ == 0)
{
lean_object* v___x_2925_; 
v___x_2925_ = lean_box(0);
return v___x_2925_;
}
else
{
lean_object* v___x_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; 
v___x_2926_ = lean_unsigned_to_nat(0u);
v___x_2927_ = l_String_Slice_positions(v_s_2922_);
v___x_2928_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_2922_, v___x_2927_, v___x_2926_);
v___x_2929_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2929_, 0, v___x_2928_);
return v___x_2929_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object* v_s_2952_){
_start:
{
lean_object* v_res_2953_; 
v_res_2953_ = l_String_Slice_toNat_x3f(v_s_2952_);
lean_dec_ref(v_s_2952_);
return v_res_2953_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object* v_s_2954_, lean_object* v_inst_2955_, lean_object* v_R_2956_, lean_object* v_a_2957_, lean_object* v_b_2958_, lean_object* v_c_2959_){
_start:
{
lean_object* v___x_2960_; 
v___x_2960_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_2954_, v_a_2957_, v_b_2958_);
return v___x_2960_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object* v_s_2961_, lean_object* v_inst_2962_, lean_object* v_R_2963_, lean_object* v_a_2964_, lean_object* v_b_2965_, lean_object* v_c_2966_){
_start:
{
lean_object* v_res_2967_; 
v_res_2967_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(v_s_2961_, v_inst_2962_, v_R_2963_, v_a_2964_, v_b_2965_, v_c_2966_);
lean_dec_ref(v_s_2961_);
return v_res_2967_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1(lean_object* v___x_2968_, lean_object* v_s_2969_, lean_object* v___x_2970_, lean_object* v_inst_2971_, lean_object* v_R_2972_, lean_object* v_a_2973_, lean_object* v_b_2974_, lean_object* v_c_2975_){
_start:
{
lean_object* v___x_2976_; 
v___x_2976_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(v___x_2968_, v_s_2969_, v___x_2970_, v_a_2973_, v_b_2974_);
return v___x_2976_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___boxed(lean_object* v___x_2977_, lean_object* v_s_2978_, lean_object* v___x_2979_, lean_object* v_inst_2980_, lean_object* v_R_2981_, lean_object* v_a_2982_, lean_object* v_b_2983_, lean_object* v_c_2984_){
_start:
{
lean_object* v_res_2985_; 
v_res_2985_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1(v___x_2977_, v_s_2978_, v___x_2979_, v_inst_2980_, v_R_2981_, v_a_2982_, v_b_2983_, v_c_2984_);
lean_dec(v___x_2979_);
lean_dec_ref(v_s_2978_);
lean_dec(v___x_2977_);
return v_res_2985_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_toNat_x21_spec__0(lean_object* v_msg_2986_){
_start:
{
lean_object* v___x_2987_; lean_object* v___x_2988_; 
v___x_2987_ = lean_unsigned_to_nat(0u);
v___x_2988_ = lean_panic_fn(v___x_2987_, v_msg_2986_);
return v___x_2988_;
}
}
static lean_object* _init_l_String_Slice_toNat_x21___closed__3(void){
_start:
{
lean_object* v___x_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; lean_object* v___x_2997_; 
v___x_2992_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__2));
v___x_2993_ = lean_unsigned_to_nat(4u);
v___x_2994_ = lean_unsigned_to_nat(974u);
v___x_2995_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__1));
v___x_2996_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__0));
v___x_2997_ = l_mkPanicMessageWithDecl(v___x_2996_, v___x_2995_, v___x_2994_, v___x_2993_, v___x_2992_);
return v___x_2997_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21(lean_object* v_s_2998_){
_start:
{
uint8_t v___y_3003_; lean_object* v_startInclusive_3007_; lean_object* v_endExclusive_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; uint8_t v___x_3011_; 
v_startInclusive_3007_ = lean_ctor_get(v_s_2998_, 1);
v_endExclusive_3008_ = lean_ctor_get(v_s_2998_, 2);
v___x_3009_ = lean_nat_sub(v_endExclusive_3008_, v_startInclusive_3007_);
v___x_3010_ = lean_unsigned_to_nat(0u);
v___x_3011_ = lean_nat_dec_eq(v___x_3009_, v___x_3010_);
if (v___x_3011_ == 0)
{
uint8_t v___x_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; lean_object* v___x_3016_; lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v_result_3021_; lean_object* v_snd_3022_; lean_object* v_snd_3023_; lean_object* v_snd_3024_; uint8_t v___x_3025_; 
v___x_3012_ = 1;
v___x_3013_ = lean_box(v___x_3011_);
v___x_3014_ = lean_box(v___x_3012_);
v___x_3015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3015_, 0, v___x_3013_);
lean_ctor_set(v___x_3015_, 1, v___x_3014_);
v___x_3016_ = lean_box(v___x_3011_);
v___x_3017_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3017_, 0, v___x_3016_);
lean_ctor_set(v___x_3017_, 1, v___x_3015_);
v___x_3018_ = lean_box(v___x_3012_);
v___x_3019_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3019_, 0, v___x_3018_);
lean_ctor_set(v___x_3019_, 1, v___x_3017_);
v___x_3020_ = l_String_Slice_positions(v_s_2998_);
v_result_3021_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(v___x_3009_, v_s_2998_, v_startInclusive_3007_, v___x_3020_, v___x_3019_);
lean_dec(v___x_3009_);
v_snd_3022_ = lean_ctor_get(v_result_3021_, 1);
lean_inc(v_snd_3022_);
lean_dec_ref(v_result_3021_);
v_snd_3023_ = lean_ctor_get(v_snd_3022_, 1);
lean_inc(v_snd_3023_);
lean_dec(v_snd_3022_);
v_snd_3024_ = lean_ctor_get(v_snd_3023_, 1);
v___x_3025_ = lean_unbox(v_snd_3024_);
if (v___x_3025_ == 0)
{
lean_dec(v_snd_3023_);
v___y_3003_ = v___x_3011_;
goto v___jp_3002_;
}
else
{
lean_object* v_fst_3026_; uint8_t v___x_3027_; 
v_fst_3026_ = lean_ctor_get(v_snd_3023_, 0);
lean_inc(v_fst_3026_);
lean_dec(v_snd_3023_);
v___x_3027_ = lean_unbox(v_fst_3026_);
lean_dec(v_fst_3026_);
v___y_3003_ = v___x_3027_;
goto v___jp_3002_;
}
}
else
{
lean_dec(v___x_3009_);
goto v___jp_2999_;
}
v___jp_2999_:
{
lean_object* v___x_3000_; lean_object* v___x_3001_; 
v___x_3000_ = lean_obj_once(&l_String_Slice_toNat_x21___closed__3, &l_String_Slice_toNat_x21___closed__3_once, _init_l_String_Slice_toNat_x21___closed__3);
v___x_3001_ = l_panic___at___00String_Slice_toNat_x21_spec__0(v___x_3000_);
return v___x_3001_;
}
v___jp_3002_:
{
if (v___y_3003_ == 0)
{
goto v___jp_2999_;
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3005_ = l_String_Slice_positions(v_s_2998_);
v___x_3006_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_2998_, v___x_3005_, v___x_3004_);
return v___x_3006_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21___boxed(lean_object* v_s_3028_){
_start:
{
lean_object* v_res_3029_; 
v_res_3029_ = l_String_Slice_toNat_x21(v_s_3028_);
lean_dec_ref(v_s_3028_);
return v_res_3029_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object* v_s_3030_){
_start:
{
lean_object* v___x_3031_; lean_object* v___x_3032_; 
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = l_String_Slice_Pos_get_x3f(v_s_3030_, v___x_3031_);
return v___x_3032_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object* v_s_3033_){
_start:
{
lean_object* v_res_3034_; 
v_res_3034_ = l_String_Slice_front_x3f(v_s_3033_);
lean_dec_ref(v_s_3033_);
return v_res_3034_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_front(lean_object* v_s_3035_){
_start:
{
lean_object* v___x_3036_; lean_object* v___x_3037_; 
v___x_3036_ = lean_unsigned_to_nat(0u);
v___x_3037_ = l_String_Slice_Pos_get_x3f(v_s_3035_, v___x_3036_);
if (lean_obj_tag(v___x_3037_) == 0)
{
uint32_t v___x_3038_; 
v___x_3038_ = 65;
return v___x_3038_;
}
else
{
lean_object* v_val_3039_; uint32_t v___x_3040_; 
v_val_3039_ = lean_ctor_get(v___x_3037_, 0);
lean_inc(v_val_3039_);
lean_dec_ref(v___x_3037_);
v___x_3040_ = lean_unbox_uint32(v_val_3039_);
lean_dec(v_val_3039_);
return v___x_3040_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object* v_s_3041_){
_start:
{
uint32_t v_res_3042_; lean_object* v_r_3043_; 
v_res_3042_ = l_String_Slice_front(v_s_3041_);
lean_dec_ref(v_s_3041_);
v_r_3043_ = lean_box_uint32(v_res_3042_);
return v_r_3043_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg(lean_object* v___x_3044_, lean_object* v___x_3045_, lean_object* v___x_3046_, lean_object* v___x_3047_, lean_object* v_a_3048_, lean_object* v_b_3049_){
_start:
{
lean_object* v_startInclusive_3050_; lean_object* v_endExclusive_3051_; lean_object* v___x_3052_; uint8_t v___x_3053_; 
v_startInclusive_3050_ = lean_ctor_get(v___x_3045_, 1);
v_endExclusive_3051_ = lean_ctor_get(v___x_3045_, 2);
v___x_3052_ = lean_nat_sub(v_endExclusive_3051_, v_startInclusive_3050_);
v___x_3053_ = lean_nat_dec_eq(v_a_3048_, v___x_3052_);
lean_dec(v___x_3052_);
if (v___x_3053_ == 0)
{
lean_object* v_snd_3054_; lean_object* v_snd_3055_; lean_object* v_fst_3056_; lean_object* v___x_3058_; uint8_t v_isShared_3059_; uint8_t v_isSharedCheck_3120_; 
v_snd_3054_ = lean_ctor_get(v_b_3049_, 1);
lean_inc(v_snd_3054_);
v_snd_3055_ = lean_ctor_get(v_snd_3054_, 1);
lean_inc(v_snd_3055_);
v_fst_3056_ = lean_ctor_get(v_b_3049_, 0);
v_isSharedCheck_3120_ = !lean_is_exclusive(v_b_3049_);
if (v_isSharedCheck_3120_ == 0)
{
lean_object* v_unused_3121_; 
v_unused_3121_ = lean_ctor_get(v_b_3049_, 1);
lean_dec(v_unused_3121_);
v___x_3058_ = v_b_3049_;
v_isShared_3059_ = v_isSharedCheck_3120_;
goto v_resetjp_3057_;
}
else
{
lean_inc(v_fst_3056_);
lean_dec(v_b_3049_);
v___x_3058_ = lean_box(0);
v_isShared_3059_ = v_isSharedCheck_3120_;
goto v_resetjp_3057_;
}
v_resetjp_3057_:
{
lean_object* v_fst_3060_; lean_object* v___x_3062_; uint8_t v_isShared_3063_; uint8_t v_isSharedCheck_3118_; 
v_fst_3060_ = lean_ctor_get(v_snd_3054_, 0);
v_isSharedCheck_3118_ = !lean_is_exclusive(v_snd_3054_);
if (v_isSharedCheck_3118_ == 0)
{
lean_object* v_unused_3119_; 
v_unused_3119_ = lean_ctor_get(v_snd_3054_, 1);
lean_dec(v_unused_3119_);
v___x_3062_ = v_snd_3054_;
v_isShared_3063_ = v_isSharedCheck_3118_;
goto v_resetjp_3061_;
}
else
{
lean_inc(v_fst_3060_);
lean_dec(v_snd_3054_);
v___x_3062_ = lean_box(0);
v_isShared_3063_ = v_isSharedCheck_3118_;
goto v_resetjp_3061_;
}
v_resetjp_3061_:
{
lean_object* v_snd_3064_; lean_object* v___x_3066_; uint8_t v_isShared_3067_; uint8_t v_isSharedCheck_3116_; 
v_snd_3064_ = lean_ctor_get(v_snd_3055_, 1);
v_isSharedCheck_3116_ = !lean_is_exclusive(v_snd_3055_);
if (v_isSharedCheck_3116_ == 0)
{
lean_object* v_unused_3117_; 
v_unused_3117_ = lean_ctor_get(v_snd_3055_, 0);
lean_dec(v_unused_3117_);
v___x_3066_ = v_snd_3055_;
v_isShared_3067_ = v_isSharedCheck_3116_;
goto v_resetjp_3065_;
}
else
{
lean_inc(v_snd_3064_);
lean_dec(v_snd_3055_);
v___x_3066_ = lean_box(0);
v_isShared_3067_ = v_isSharedCheck_3116_;
goto v_resetjp_3065_;
}
v_resetjp_3065_:
{
lean_object* v___x_3068_; uint8_t v___x_3069_; uint8_t v___x_3070_; lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; uint32_t v___x_3074_; uint8_t v___y_3076_; uint8_t v___y_3077_; uint8_t v___y_3095_; uint8_t v___y_3096_; uint8_t v___y_3101_; uint8_t v___y_3102_; uint8_t v___y_3107_; uint32_t v___x_3112_; uint8_t v___x_3113_; 
v___x_3068_ = lean_unsigned_to_nat(0u);
v___x_3069_ = lean_nat_dec_eq(v___x_3044_, v___x_3068_);
v___x_3070_ = 1;
v___x_3071_ = lean_nat_add(v___x_3046_, v_a_3048_);
lean_dec(v_a_3048_);
v___x_3072_ = lean_string_utf8_next_fast(v___x_3047_, v___x_3071_);
v___x_3073_ = lean_nat_sub(v___x_3072_, v___x_3046_);
v___x_3074_ = lean_string_utf8_get_fast(v___x_3047_, v___x_3071_);
lean_dec(v___x_3071_);
v___x_3112_ = 48;
v___x_3113_ = lean_uint32_dec_le(v___x_3112_, v___x_3074_);
if (v___x_3113_ == 0)
{
v___y_3107_ = v___x_3113_;
goto v___jp_3106_;
}
else
{
uint32_t v___x_3114_; uint8_t v___x_3115_; 
v___x_3114_ = 57;
v___x_3115_ = lean_uint32_dec_le(v___x_3074_, v___x_3114_);
v___y_3107_ = v___x_3115_;
goto v___jp_3106_;
}
v___jp_3075_:
{
uint32_t v___x_3078_; uint8_t v___x_3079_; lean_object* v___x_3080_; lean_object* v___x_3081_; lean_object* v___x_3083_; 
v___x_3078_ = 95;
v___x_3079_ = lean_uint32_dec_eq(v___x_3074_, v___x_3078_);
v___x_3080_ = lean_box(v___y_3076_);
v___x_3081_ = lean_box(v___y_3077_);
if (v_isShared_3067_ == 0)
{
lean_ctor_set(v___x_3066_, 1, v___x_3081_);
lean_ctor_set(v___x_3066_, 0, v___x_3080_);
v___x_3083_ = v___x_3066_;
goto v_reusejp_3082_;
}
else
{
lean_object* v_reuseFailAlloc_3093_; 
v_reuseFailAlloc_3093_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3093_, 0, v___x_3080_);
lean_ctor_set(v_reuseFailAlloc_3093_, 1, v___x_3081_);
v___x_3083_ = v_reuseFailAlloc_3093_;
goto v_reusejp_3082_;
}
v_reusejp_3082_:
{
lean_object* v___x_3084_; lean_object* v___x_3086_; 
v___x_3084_ = lean_box(v___x_3079_);
if (v_isShared_3063_ == 0)
{
lean_ctor_set(v___x_3062_, 1, v___x_3083_);
lean_ctor_set(v___x_3062_, 0, v___x_3084_);
v___x_3086_ = v___x_3062_;
goto v_reusejp_3085_;
}
else
{
lean_object* v_reuseFailAlloc_3092_; 
v_reuseFailAlloc_3092_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3092_, 0, v___x_3084_);
lean_ctor_set(v_reuseFailAlloc_3092_, 1, v___x_3083_);
v___x_3086_ = v_reuseFailAlloc_3092_;
goto v_reusejp_3085_;
}
v_reusejp_3085_:
{
lean_object* v___x_3087_; lean_object* v___x_3089_; 
v___x_3087_ = lean_box(v___x_3069_);
if (v_isShared_3059_ == 0)
{
lean_ctor_set(v___x_3058_, 1, v___x_3086_);
lean_ctor_set(v___x_3058_, 0, v___x_3087_);
v___x_3089_ = v___x_3058_;
goto v_reusejp_3088_;
}
else
{
lean_object* v_reuseFailAlloc_3091_; 
v_reuseFailAlloc_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3091_, 0, v___x_3087_);
lean_ctor_set(v_reuseFailAlloc_3091_, 1, v___x_3086_);
v___x_3089_ = v_reuseFailAlloc_3091_;
goto v_reusejp_3088_;
}
v_reusejp_3088_:
{
v_a_3048_ = v___x_3073_;
v_b_3049_ = v___x_3089_;
goto _start;
}
}
}
}
v___jp_3094_:
{
uint8_t v___x_3097_; 
v___x_3097_ = lean_unbox(v_fst_3060_);
lean_dec(v_fst_3060_);
if (v___x_3097_ == 0)
{
v___y_3076_ = v___y_3095_;
v___y_3077_ = v___y_3096_;
goto v___jp_3075_;
}
else
{
uint32_t v___x_3098_; uint8_t v___x_3099_; 
v___x_3098_ = 95;
v___x_3099_ = lean_uint32_dec_eq(v___x_3074_, v___x_3098_);
if (v___x_3099_ == 0)
{
v___y_3076_ = v___y_3095_;
v___y_3077_ = v___y_3096_;
goto v___jp_3075_;
}
else
{
v___y_3076_ = v___y_3095_;
v___y_3077_ = v___x_3069_;
goto v___jp_3075_;
}
}
}
v___jp_3100_:
{
uint8_t v___x_3103_; 
v___x_3103_ = lean_unbox(v_fst_3056_);
lean_dec(v_fst_3056_);
if (v___x_3103_ == 0)
{
v___y_3095_ = v___y_3101_;
v___y_3096_ = v___y_3102_;
goto v___jp_3094_;
}
else
{
uint32_t v___x_3104_; uint8_t v___x_3105_; 
v___x_3104_ = 95;
v___x_3105_ = lean_uint32_dec_eq(v___x_3074_, v___x_3104_);
if (v___x_3105_ == 0)
{
v___y_3095_ = v___y_3101_;
v___y_3096_ = v___y_3102_;
goto v___jp_3094_;
}
else
{
if (v___x_3069_ == 0)
{
lean_dec(v_fst_3060_);
v___y_3076_ = v___y_3101_;
v___y_3077_ = v___x_3069_;
goto v___jp_3075_;
}
else
{
v___y_3095_ = v___y_3101_;
v___y_3096_ = v___x_3069_;
goto v___jp_3094_;
}
}
}
}
v___jp_3106_:
{
uint8_t v___x_3108_; 
v___x_3108_ = lean_unbox(v_snd_3064_);
if (v___x_3108_ == 0)
{
uint8_t v___x_3109_; 
lean_dec(v_fst_3060_);
lean_dec(v_fst_3056_);
v___x_3109_ = lean_unbox(v_snd_3064_);
lean_dec(v_snd_3064_);
v___y_3076_ = v___y_3107_;
v___y_3077_ = v___x_3109_;
goto v___jp_3075_;
}
else
{
lean_dec(v_snd_3064_);
if (v___y_3107_ == 0)
{
uint32_t v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = 95;
v___x_3111_ = lean_uint32_dec_eq(v___x_3074_, v___x_3110_);
if (v___x_3111_ == 0)
{
lean_dec(v_fst_3060_);
lean_dec(v_fst_3056_);
v___y_3076_ = v___y_3107_;
v___y_3077_ = v___x_3111_;
goto v___jp_3075_;
}
else
{
v___y_3101_ = v___y_3107_;
v___y_3102_ = v___x_3111_;
goto v___jp_3100_;
}
}
else
{
v___y_3101_ = v___y_3107_;
v___y_3102_ = v___x_3070_;
goto v___jp_3100_;
}
}
}
}
}
}
}
else
{
lean_dec(v_a_3048_);
return v_b_3049_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg___boxed(lean_object* v___x_3122_, lean_object* v___x_3123_, lean_object* v___x_3124_, lean_object* v___x_3125_, lean_object* v_a_3126_, lean_object* v_b_3127_){
_start:
{
lean_object* v_res_3128_; 
v_res_3128_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg(v___x_3122_, v___x_3123_, v___x_3124_, v___x_3125_, v_a_3126_, v_b_3127_);
lean_dec_ref(v___x_3125_);
lean_dec(v___x_3124_);
lean_dec_ref(v___x_3123_);
lean_dec(v___x_3122_);
return v_res_3128_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isInt(lean_object* v_s_3129_){
_start:
{
uint32_t v___y_3131_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3190_ = lean_unsigned_to_nat(0u);
v___x_3191_ = l_String_Slice_Pos_get_x3f(v_s_3129_, v___x_3190_);
if (lean_obj_tag(v___x_3191_) == 0)
{
uint32_t v___x_3192_; 
v___x_3192_ = 65;
v___y_3131_ = v___x_3192_;
goto v___jp_3130_;
}
else
{
lean_object* v_val_3193_; uint32_t v___x_3194_; 
v_val_3193_ = lean_ctor_get(v___x_3191_, 0);
lean_inc(v_val_3193_);
lean_dec_ref(v___x_3191_);
v___x_3194_ = lean_unbox_uint32(v_val_3193_);
lean_dec(v_val_3193_);
v___y_3131_ = v___x_3194_;
goto v___jp_3130_;
}
v___jp_3130_:
{
uint32_t v___x_3132_; uint8_t v___x_3133_; 
v___x_3132_ = 45;
v___x_3133_ = lean_uint32_dec_eq(v___y_3131_, v___x_3132_);
if (v___x_3133_ == 0)
{
lean_object* v_startInclusive_3134_; lean_object* v_endExclusive_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; uint8_t v___x_3138_; 
v_startInclusive_3134_ = lean_ctor_get(v_s_3129_, 1);
lean_inc(v_startInclusive_3134_);
v_endExclusive_3135_ = lean_ctor_get(v_s_3129_, 2);
v___x_3136_ = lean_nat_sub(v_endExclusive_3135_, v_startInclusive_3134_);
v___x_3137_ = lean_unsigned_to_nat(0u);
v___x_3138_ = lean_nat_dec_eq(v___x_3136_, v___x_3137_);
if (v___x_3138_ == 0)
{
uint8_t v___x_3139_; lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v_result_3148_; lean_object* v_snd_3149_; lean_object* v_snd_3150_; lean_object* v_snd_3151_; uint8_t v___x_3152_; 
v___x_3139_ = 1;
v___x_3140_ = lean_box(v___x_3138_);
v___x_3141_ = lean_box(v___x_3139_);
v___x_3142_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3142_, 0, v___x_3140_);
lean_ctor_set(v___x_3142_, 1, v___x_3141_);
v___x_3143_ = lean_box(v___x_3138_);
v___x_3144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3144_, 0, v___x_3143_);
lean_ctor_set(v___x_3144_, 1, v___x_3142_);
v___x_3145_ = lean_box(v___x_3139_);
v___x_3146_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3146_, 0, v___x_3145_);
lean_ctor_set(v___x_3146_, 1, v___x_3144_);
v___x_3147_ = l_String_Slice_positions(v_s_3129_);
v_result_3148_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(v___x_3136_, v_s_3129_, v_startInclusive_3134_, v___x_3147_, v___x_3146_);
lean_dec(v_startInclusive_3134_);
lean_dec_ref(v_s_3129_);
lean_dec(v___x_3136_);
v_snd_3149_ = lean_ctor_get(v_result_3148_, 1);
lean_inc(v_snd_3149_);
lean_dec_ref(v_result_3148_);
v_snd_3150_ = lean_ctor_get(v_snd_3149_, 1);
lean_inc(v_snd_3150_);
lean_dec(v_snd_3149_);
v_snd_3151_ = lean_ctor_get(v_snd_3150_, 1);
v___x_3152_ = lean_unbox(v_snd_3151_);
if (v___x_3152_ == 0)
{
lean_dec(v_snd_3150_);
return v___x_3138_;
}
else
{
lean_object* v_fst_3153_; uint8_t v___x_3154_; 
v_fst_3153_ = lean_ctor_get(v_snd_3150_, 0);
lean_inc(v_fst_3153_);
lean_dec(v_snd_3150_);
v___x_3154_ = lean_unbox(v_fst_3153_);
lean_dec(v_fst_3153_);
return v___x_3154_;
}
}
else
{
lean_dec(v___x_3136_);
lean_dec(v_startInclusive_3134_);
lean_dec_ref(v_s_3129_);
return v___x_3133_;
}
}
else
{
lean_object* v_str_3155_; lean_object* v_startInclusive_3156_; lean_object* v_endExclusive_3157_; lean_object* v___x_3158_; lean_object* v___x_3159_; lean_object* v___x_3160_; lean_object* v___x_3162_; uint8_t v_isShared_3163_; uint8_t v_isSharedCheck_3186_; 
v_str_3155_ = lean_ctor_get(v_s_3129_, 0);
lean_inc_ref(v_str_3155_);
v_startInclusive_3156_ = lean_ctor_get(v_s_3129_, 1);
lean_inc(v_startInclusive_3156_);
v_endExclusive_3157_ = lean_ctor_get(v_s_3129_, 2);
lean_inc(v_endExclusive_3157_);
v___x_3158_ = lean_unsigned_to_nat(1u);
v___x_3159_ = lean_unsigned_to_nat(0u);
v___x_3160_ = l_String_Slice_Pos_nextn(v_s_3129_, v___x_3159_, v___x_3158_);
v_isSharedCheck_3186_ = !lean_is_exclusive(v_s_3129_);
if (v_isSharedCheck_3186_ == 0)
{
lean_object* v_unused_3187_; lean_object* v_unused_3188_; lean_object* v_unused_3189_; 
v_unused_3187_ = lean_ctor_get(v_s_3129_, 2);
lean_dec(v_unused_3187_);
v_unused_3188_ = lean_ctor_get(v_s_3129_, 1);
lean_dec(v_unused_3188_);
v_unused_3189_ = lean_ctor_get(v_s_3129_, 0);
lean_dec(v_unused_3189_);
v___x_3162_ = v_s_3129_;
v_isShared_3163_ = v_isSharedCheck_3186_;
goto v_resetjp_3161_;
}
else
{
lean_dec(v_s_3129_);
v___x_3162_ = lean_box(0);
v_isShared_3163_ = v_isSharedCheck_3186_;
goto v_resetjp_3161_;
}
v_resetjp_3161_:
{
lean_object* v___x_3164_; lean_object* v___x_3165_; uint8_t v___x_3166_; 
v___x_3164_ = lean_nat_add(v_startInclusive_3156_, v___x_3160_);
lean_dec(v___x_3160_);
lean_dec(v_startInclusive_3156_);
v___x_3165_ = lean_nat_sub(v_endExclusive_3157_, v___x_3164_);
v___x_3166_ = lean_nat_dec_eq(v___x_3165_, v___x_3159_);
if (v___x_3166_ == 0)
{
lean_object* v___x_3168_; 
lean_inc(v___x_3164_);
lean_inc_ref(v_str_3155_);
if (v_isShared_3163_ == 0)
{
lean_ctor_set(v___x_3162_, 1, v___x_3164_);
v___x_3168_ = v___x_3162_;
goto v_reusejp_3167_;
}
else
{
lean_object* v_reuseFailAlloc_3184_; 
v_reuseFailAlloc_3184_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3184_, 0, v_str_3155_);
lean_ctor_set(v_reuseFailAlloc_3184_, 1, v___x_3164_);
lean_ctor_set(v_reuseFailAlloc_3184_, 2, v_endExclusive_3157_);
v___x_3168_ = v_reuseFailAlloc_3184_;
goto v_reusejp_3167_;
}
v_reusejp_3167_:
{
lean_object* v___x_3169_; lean_object* v___x_3170_; lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v_result_3177_; lean_object* v_snd_3178_; lean_object* v_snd_3179_; lean_object* v_snd_3180_; uint8_t v___x_3181_; 
v___x_3169_ = lean_box(v___x_3166_);
v___x_3170_ = lean_box(v___x_3133_);
v___x_3171_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3171_, 0, v___x_3169_);
lean_ctor_set(v___x_3171_, 1, v___x_3170_);
v___x_3172_ = lean_box(v___x_3166_);
v___x_3173_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3173_, 0, v___x_3172_);
lean_ctor_set(v___x_3173_, 1, v___x_3171_);
v___x_3174_ = lean_box(v___x_3133_);
v___x_3175_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3175_, 0, v___x_3174_);
lean_ctor_set(v___x_3175_, 1, v___x_3173_);
v___x_3176_ = l_String_Slice_positions(v___x_3168_);
v_result_3177_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg(v___x_3165_, v___x_3168_, v___x_3164_, v_str_3155_, v___x_3176_, v___x_3175_);
lean_dec_ref(v_str_3155_);
lean_dec(v___x_3164_);
lean_dec_ref(v___x_3168_);
lean_dec(v___x_3165_);
v_snd_3178_ = lean_ctor_get(v_result_3177_, 1);
lean_inc(v_snd_3178_);
lean_dec_ref(v_result_3177_);
v_snd_3179_ = lean_ctor_get(v_snd_3178_, 1);
lean_inc(v_snd_3179_);
lean_dec(v_snd_3178_);
v_snd_3180_ = lean_ctor_get(v_snd_3179_, 1);
v___x_3181_ = lean_unbox(v_snd_3180_);
if (v___x_3181_ == 0)
{
lean_dec(v_snd_3179_);
return v___x_3166_;
}
else
{
lean_object* v_fst_3182_; uint8_t v___x_3183_; 
v_fst_3182_ = lean_ctor_get(v_snd_3179_, 0);
lean_inc(v_fst_3182_);
lean_dec(v_snd_3179_);
v___x_3183_ = lean_unbox(v_fst_3182_);
lean_dec(v_fst_3182_);
return v___x_3183_;
}
}
}
else
{
uint8_t v___x_3185_; 
lean_dec(v___x_3165_);
lean_dec(v___x_3164_);
lean_del_object(v___x_3162_);
lean_dec(v_endExclusive_3157_);
lean_dec_ref(v_str_3155_);
v___x_3185_ = 0;
return v___x_3185_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object* v_s_3195_){
_start:
{
uint8_t v_res_3196_; lean_object* v_r_3197_; 
v_res_3196_ = l_String_Slice_isInt(v_s_3195_);
v_r_3197_ = lean_box(v_res_3196_);
return v_r_3197_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0(lean_object* v___x_3198_, lean_object* v___x_3199_, lean_object* v___x_3200_, lean_object* v___x_3201_, lean_object* v_inst_3202_, lean_object* v_R_3203_, lean_object* v_a_3204_, lean_object* v_b_3205_, lean_object* v_c_3206_){
_start:
{
lean_object* v___x_3207_; 
v___x_3207_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg(v___x_3198_, v___x_3199_, v___x_3200_, v___x_3201_, v_a_3204_, v_b_3205_);
return v___x_3207_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___boxed(lean_object* v___x_3208_, lean_object* v___x_3209_, lean_object* v___x_3210_, lean_object* v___x_3211_, lean_object* v_inst_3212_, lean_object* v_R_3213_, lean_object* v_a_3214_, lean_object* v_b_3215_, lean_object* v_c_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0(v___x_3208_, v___x_3209_, v___x_3210_, v___x_3211_, v_inst_3212_, v_R_3213_, v_a_3214_, v_b_3215_, v_c_3216_);
lean_dec_ref(v___x_3211_);
lean_dec(v___x_3210_);
lean_dec_ref(v___x_3209_);
lean_dec(v___x_3208_);
return v_res_3217_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x3f(lean_object* v_s_3218_){
_start:
{
uint32_t v___y_3220_; lean_object* v___x_3262_; lean_object* v___x_3263_; 
v___x_3262_ = lean_unsigned_to_nat(0u);
v___x_3263_ = l_String_Slice_Pos_get_x3f(v_s_3218_, v___x_3262_);
if (lean_obj_tag(v___x_3263_) == 0)
{
uint32_t v___x_3264_; 
v___x_3264_ = 65;
v___y_3220_ = v___x_3264_;
goto v___jp_3219_;
}
else
{
lean_object* v_val_3265_; uint32_t v___x_3266_; 
v_val_3265_ = lean_ctor_get(v___x_3263_, 0);
lean_inc(v_val_3265_);
lean_dec_ref(v___x_3263_);
v___x_3266_ = lean_unbox_uint32(v_val_3265_);
lean_dec(v_val_3265_);
v___y_3220_ = v___x_3266_;
goto v___jp_3219_;
}
v___jp_3219_:
{
uint32_t v___x_3221_; uint8_t v___x_3222_; 
v___x_3221_ = 45;
v___x_3222_ = lean_uint32_dec_eq(v___y_3220_, v___x_3221_);
if (v___x_3222_ == 0)
{
lean_object* v___x_3223_; 
v___x_3223_ = l_String_Slice_toNat_x3f(v_s_3218_);
lean_dec_ref(v_s_3218_);
if (lean_obj_tag(v___x_3223_) == 0)
{
lean_object* v___x_3224_; 
v___x_3224_ = lean_box(0);
return v___x_3224_;
}
else
{
lean_object* v_val_3225_; lean_object* v___x_3227_; uint8_t v_isShared_3228_; uint8_t v_isSharedCheck_3233_; 
v_val_3225_ = lean_ctor_get(v___x_3223_, 0);
v_isSharedCheck_3233_ = !lean_is_exclusive(v___x_3223_);
if (v_isSharedCheck_3233_ == 0)
{
v___x_3227_ = v___x_3223_;
v_isShared_3228_ = v_isSharedCheck_3233_;
goto v_resetjp_3226_;
}
else
{
lean_inc(v_val_3225_);
lean_dec(v___x_3223_);
v___x_3227_ = lean_box(0);
v_isShared_3228_ = v_isSharedCheck_3233_;
goto v_resetjp_3226_;
}
v_resetjp_3226_:
{
lean_object* v___x_3229_; lean_object* v___x_3231_; 
v___x_3229_ = lean_nat_to_int(v_val_3225_);
if (v_isShared_3228_ == 0)
{
lean_ctor_set(v___x_3227_, 0, v___x_3229_);
v___x_3231_ = v___x_3227_;
goto v_reusejp_3230_;
}
else
{
lean_object* v_reuseFailAlloc_3232_; 
v_reuseFailAlloc_3232_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3232_, 0, v___x_3229_);
v___x_3231_ = v_reuseFailAlloc_3232_;
goto v_reusejp_3230_;
}
v_reusejp_3230_:
{
return v___x_3231_;
}
}
}
}
else
{
lean_object* v_str_3234_; lean_object* v_startInclusive_3235_; lean_object* v_endExclusive_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3239_; lean_object* v___x_3241_; uint8_t v_isShared_3242_; uint8_t v_isSharedCheck_3258_; 
v_str_3234_ = lean_ctor_get(v_s_3218_, 0);
lean_inc_ref(v_str_3234_);
v_startInclusive_3235_ = lean_ctor_get(v_s_3218_, 1);
lean_inc(v_startInclusive_3235_);
v_endExclusive_3236_ = lean_ctor_get(v_s_3218_, 2);
lean_inc(v_endExclusive_3236_);
v___x_3237_ = lean_unsigned_to_nat(1u);
v___x_3238_ = lean_unsigned_to_nat(0u);
v___x_3239_ = l_String_Slice_Pos_nextn(v_s_3218_, v___x_3238_, v___x_3237_);
v_isSharedCheck_3258_ = !lean_is_exclusive(v_s_3218_);
if (v_isSharedCheck_3258_ == 0)
{
lean_object* v_unused_3259_; lean_object* v_unused_3260_; lean_object* v_unused_3261_; 
v_unused_3259_ = lean_ctor_get(v_s_3218_, 2);
lean_dec(v_unused_3259_);
v_unused_3260_ = lean_ctor_get(v_s_3218_, 1);
lean_dec(v_unused_3260_);
v_unused_3261_ = lean_ctor_get(v_s_3218_, 0);
lean_dec(v_unused_3261_);
v___x_3241_ = v_s_3218_;
v_isShared_3242_ = v_isSharedCheck_3258_;
goto v_resetjp_3240_;
}
else
{
lean_dec(v_s_3218_);
v___x_3241_ = lean_box(0);
v_isShared_3242_ = v_isSharedCheck_3258_;
goto v_resetjp_3240_;
}
v_resetjp_3240_:
{
lean_object* v___x_3243_; lean_object* v___x_3245_; 
v___x_3243_ = lean_nat_add(v_startInclusive_3235_, v___x_3239_);
lean_dec(v___x_3239_);
lean_dec(v_startInclusive_3235_);
if (v_isShared_3242_ == 0)
{
lean_ctor_set(v___x_3241_, 1, v___x_3243_);
v___x_3245_ = v___x_3241_;
goto v_reusejp_3244_;
}
else
{
lean_object* v_reuseFailAlloc_3257_; 
v_reuseFailAlloc_3257_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3257_, 0, v_str_3234_);
lean_ctor_set(v_reuseFailAlloc_3257_, 1, v___x_3243_);
lean_ctor_set(v_reuseFailAlloc_3257_, 2, v_endExclusive_3236_);
v___x_3245_ = v_reuseFailAlloc_3257_;
goto v_reusejp_3244_;
}
v_reusejp_3244_:
{
lean_object* v___x_3246_; 
v___x_3246_ = l_String_Slice_toNat_x3f(v___x_3245_);
lean_dec_ref(v___x_3245_);
if (lean_obj_tag(v___x_3246_) == 0)
{
lean_object* v___x_3247_; 
v___x_3247_ = lean_box(0);
return v___x_3247_;
}
else
{
lean_object* v_val_3248_; lean_object* v___x_3250_; uint8_t v_isShared_3251_; uint8_t v_isSharedCheck_3256_; 
v_val_3248_ = lean_ctor_get(v___x_3246_, 0);
v_isSharedCheck_3256_ = !lean_is_exclusive(v___x_3246_);
if (v_isSharedCheck_3256_ == 0)
{
v___x_3250_ = v___x_3246_;
v_isShared_3251_ = v_isSharedCheck_3256_;
goto v_resetjp_3249_;
}
else
{
lean_inc(v_val_3248_);
lean_dec(v___x_3246_);
v___x_3250_ = lean_box(0);
v_isShared_3251_ = v_isSharedCheck_3256_;
goto v_resetjp_3249_;
}
v_resetjp_3249_:
{
lean_object* v___x_3252_; lean_object* v___x_3254_; 
v___x_3252_ = l_Int_negOfNat(v_val_3248_);
lean_dec(v_val_3248_);
if (v_isShared_3251_ == 0)
{
lean_ctor_set(v___x_3250_, 0, v___x_3252_);
v___x_3254_ = v___x_3250_;
goto v_reusejp_3253_;
}
else
{
lean_object* v_reuseFailAlloc_3255_; 
v_reuseFailAlloc_3255_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3255_, 0, v___x_3252_);
v___x_3254_ = v_reuseFailAlloc_3255_;
goto v_reusejp_3253_;
}
v_reusejp_3253_:
{
return v___x_3254_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x21(lean_object* v_s_3268_){
_start:
{
lean_object* v___x_3269_; 
v___x_3269_ = l_String_Slice_toInt_x3f(v_s_3268_);
if (lean_obj_tag(v___x_3269_) == 0)
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; 
v___x_3270_ = l_Int_instInhabited;
v___x_3271_ = ((lean_object*)(l_String_Slice_toInt_x21___closed__0));
v___x_3272_ = l_panic___redArg(v___x_3270_, v___x_3271_);
return v___x_3272_;
}
else
{
lean_object* v_val_3273_; 
v_val_3273_ = lean_ctor_get(v___x_3269_, 0);
lean_inc(v_val_3273_);
lean_dec_ref(v___x_3269_);
return v_val_3273_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object* v_s_3274_){
_start:
{
lean_object* v_startInclusive_3275_; lean_object* v_endExclusive_3276_; lean_object* v___x_3277_; lean_object* v___x_3278_; 
v_startInclusive_3275_ = lean_ctor_get(v_s_3274_, 1);
v_endExclusive_3276_ = lean_ctor_get(v_s_3274_, 2);
v___x_3277_ = lean_nat_sub(v_endExclusive_3276_, v_startInclusive_3275_);
v___x_3278_ = l_String_Slice_Pos_prev_x3f(v_s_3274_, v___x_3277_);
lean_dec(v___x_3277_);
if (lean_obj_tag(v___x_3278_) == 0)
{
lean_object* v___x_3279_; 
v___x_3279_ = lean_box(0);
return v___x_3279_;
}
else
{
lean_object* v_val_3280_; lean_object* v___x_3281_; 
v_val_3280_ = lean_ctor_get(v___x_3278_, 0);
lean_inc(v_val_3280_);
lean_dec_ref(v___x_3278_);
v___x_3281_ = l_String_Slice_Pos_get_x3f(v_s_3274_, v_val_3280_);
lean_dec(v_val_3280_);
return v___x_3281_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object* v_s_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_String_Slice_back_x3f(v_s_3282_);
lean_dec_ref(v_s_3282_);
return v_res_3283_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_back(lean_object* v_s_3284_){
_start:
{
lean_object* v_startInclusive_3285_; lean_object* v_endExclusive_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; 
v_startInclusive_3285_ = lean_ctor_get(v_s_3284_, 1);
v_endExclusive_3286_ = lean_ctor_get(v_s_3284_, 2);
v___x_3287_ = lean_nat_sub(v_endExclusive_3286_, v_startInclusive_3285_);
v___x_3288_ = l_String_Slice_Pos_prev_x3f(v_s_3284_, v___x_3287_);
lean_dec(v___x_3287_);
if (lean_obj_tag(v___x_3288_) == 0)
{
uint32_t v___x_3289_; 
v___x_3289_ = 65;
return v___x_3289_;
}
else
{
lean_object* v_val_3290_; lean_object* v___x_3291_; 
v_val_3290_ = lean_ctor_get(v___x_3288_, 0);
lean_inc(v_val_3290_);
lean_dec_ref(v___x_3288_);
v___x_3291_ = l_String_Slice_Pos_get_x3f(v_s_3284_, v_val_3290_);
lean_dec(v_val_3290_);
if (lean_obj_tag(v___x_3291_) == 0)
{
uint32_t v___x_3292_; 
v___x_3292_ = 65;
return v___x_3292_;
}
else
{
lean_object* v_val_3293_; uint32_t v___x_3294_; 
v_val_3293_ = lean_ctor_get(v___x_3291_, 0);
lean_inc(v_val_3293_);
lean_dec_ref(v___x_3291_);
v___x_3294_ = lean_unbox_uint32(v_val_3293_);
lean_dec(v_val_3293_);
return v___x_3294_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object* v_s_3295_){
_start:
{
uint32_t v_res_3296_; lean_object* v_r_3297_; 
v_res_3296_ = l_String_Slice_back(v_s_3295_);
lean_dec_ref(v_s_3295_);
v_r_3297_ = lean_box_uint32(v_res_3296_);
return v_r_3297_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(lean_object* v_acc_3298_, lean_object* v_s_3299_, lean_object* v_a_3300_){
_start:
{
if (lean_obj_tag(v_a_3300_) == 0)
{
return v_acc_3298_;
}
else
{
lean_object* v_head_3301_; lean_object* v_tail_3302_; lean_object* v_str_3303_; lean_object* v_startInclusive_3304_; lean_object* v_endExclusive_3305_; lean_object* v_str_3306_; lean_object* v_startInclusive_3307_; lean_object* v_endExclusive_3308_; lean_object* v___x_3309_; lean_object* v___x_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_head_3301_ = lean_ctor_get(v_a_3300_, 0);
v_tail_3302_ = lean_ctor_get(v_a_3300_, 1);
v_str_3303_ = lean_ctor_get(v_s_3299_, 0);
v_startInclusive_3304_ = lean_ctor_get(v_s_3299_, 1);
v_endExclusive_3305_ = lean_ctor_get(v_s_3299_, 2);
v_str_3306_ = lean_ctor_get(v_head_3301_, 0);
v_startInclusive_3307_ = lean_ctor_get(v_head_3301_, 1);
v_endExclusive_3308_ = lean_ctor_get(v_head_3301_, 2);
v___x_3309_ = lean_string_utf8_extract(v_str_3303_, v_startInclusive_3304_, v_endExclusive_3305_);
v___x_3310_ = lean_string_append(v_acc_3298_, v___x_3309_);
lean_dec_ref(v___x_3309_);
v___x_3311_ = lean_string_utf8_extract(v_str_3306_, v_startInclusive_3307_, v_endExclusive_3308_);
v___x_3312_ = lean_string_append(v___x_3310_, v___x_3311_);
lean_dec_ref(v___x_3311_);
v_acc_3298_ = v___x_3312_;
v_a_3300_ = v_tail_3302_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go___boxed(lean_object* v_acc_3314_, lean_object* v_s_3315_, lean_object* v_a_3316_){
_start:
{
lean_object* v_res_3317_; 
v_res_3317_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v_acc_3314_, v_s_3315_, v_a_3316_);
lean_dec(v_a_3316_);
lean_dec_ref(v_s_3315_);
return v_res_3317_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object* v_s_3318_, lean_object* v_x_3319_){
_start:
{
if (lean_obj_tag(v_x_3319_) == 0)
{
lean_object* v___x_3320_; 
v___x_3320_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
return v___x_3320_;
}
else
{
lean_object* v_head_3321_; lean_object* v_tail_3322_; lean_object* v_str_3323_; lean_object* v_startInclusive_3324_; lean_object* v_endExclusive_3325_; lean_object* v___x_3326_; lean_object* v___x_3327_; 
v_head_3321_ = lean_ctor_get(v_x_3319_, 0);
v_tail_3322_ = lean_ctor_get(v_x_3319_, 1);
v_str_3323_ = lean_ctor_get(v_head_3321_, 0);
v_startInclusive_3324_ = lean_ctor_get(v_head_3321_, 1);
v_endExclusive_3325_ = lean_ctor_get(v_head_3321_, 2);
v___x_3326_ = lean_string_utf8_extract(v_str_3323_, v_startInclusive_3324_, v_endExclusive_3325_);
v___x_3327_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v___x_3326_, v_s_3318_, v_tail_3322_);
return v___x_3327_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object* v_s_3328_, lean_object* v_x_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_String_Slice_intercalate(v_s_3328_, v_x_3329_);
lean_dec(v_x_3329_);
lean_dec_ref(v_s_3328_);
return v_res_3330_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object* v_s_3331_){
_start:
{
lean_object* v___x_3332_; lean_object* v___x_3333_; 
v___x_3332_ = l_String_Slice_toString(v_s_3331_);
v___x_3333_ = l_String_toName(v___x_3332_);
return v___x_3333_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object* v_s_3334_){
_start:
{
lean_object* v_res_3335_; 
v_res_3335_ = l_String_Slice_toName(v_s_3334_);
lean_dec_ref(v_s_3334_);
return v_res_3335_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object* v_s_3336_){
_start:
{
lean_object* v_str_3337_; lean_object* v_startInclusive_3338_; lean_object* v_endExclusive_3339_; lean_object* v___x_3340_; lean_object* v___x_3341_; 
v_str_3337_ = lean_ctor_get(v_s_3336_, 0);
v_startInclusive_3338_ = lean_ctor_get(v_s_3336_, 1);
v_endExclusive_3339_ = lean_ctor_get(v_s_3336_, 2);
v___x_3340_ = lean_string_utf8_extract(v_str_3337_, v_startInclusive_3338_, v_endExclusive_3339_);
v___x_3341_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3341_, 0, v___x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object* v_s_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_String_Slice_instToFormat___lam__0(v_s_3342_);
lean_dec_ref(v_s_3342_);
return v_res_3343_;
}
}
lean_object* runtime_initialize_Init_Data_String_Pattern(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Ord_Basic(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_Iterators_Combinators_FilterMap(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_ToSlice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Subslice(uint8_t builtin);
lean_object* runtime_initialize_Init_Data_String_Iter(uint8_t builtin);
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
res = runtime_initialize_Init_Data_String_Iter(builtin);
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
lean_object* initialize_Init_Data_String_Iter(uint8_t builtin);
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
res = initialize_Init_Data_String_Iter(builtin);
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
