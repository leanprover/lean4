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
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_isNat___lam__0(lean_object*, uint8_t, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_isNat___lam__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
static const lean_ctor_object l_String_Slice_isNat___closed__0_value = {.m_header = {.m_rc = 0, .m_cs_sz = sizeof(lean_ctor_object) + sizeof(void*)*2 + 0, .m_other = 2, .m_tag = 0}, .m_objs = {((lean_object*)(((size_t)(0) << 1) | 1)),((lean_object*)(((size_t)(0) << 1) | 1))}};
static const lean_object* l_String_Slice_isNat___closed__0 = (const lean_object*)&l_String_Slice_isNat___closed__0_value;
LEAN_EXPORT uint8_t l_String_Slice_isNat(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg___boxed(lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT uint8_t l_String_Slice_isInt(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___redArg(lean_object* v_s_1147_, lean_object* v_inst_1148_){
_start:
{
lean_object* v_skipPrefix_x3f_1149_; lean_object* v___x_1150_; 
v_skipPrefix_x3f_1149_ = lean_ctor_get(v_inst_1148_, 0);
lean_inc_ref(v_skipPrefix_x3f_1149_);
lean_dec_ref(v_inst_1148_);
v___x_1150_ = lean_apply_1(v_skipPrefix_x3f_1149_, v_s_1147_);
return v___x_1150_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f(lean_object* v_00_u03c1_1151_, lean_object* v_s_1152_, lean_object* v_pat_1153_, lean_object* v_inst_1154_){
_start:
{
lean_object* v_skipPrefix_x3f_1155_; lean_object* v___x_1156_; 
v_skipPrefix_x3f_1155_ = lean_ctor_get(v_inst_1154_, 0);
lean_inc_ref(v_skipPrefix_x3f_1155_);
lean_dec_ref(v_inst_1154_);
v___x_1156_ = lean_apply_1(v_skipPrefix_x3f_1155_, v_s_1152_);
return v___x_1156_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___boxed(lean_object* v_00_u03c1_1157_, lean_object* v_s_1158_, lean_object* v_pat_1159_, lean_object* v_inst_1160_){
_start:
{
lean_object* v_res_1161_; 
v_res_1161_ = l_String_Slice_skipPrefix_x3f(v_00_u03c1_1157_, v_s_1158_, v_pat_1159_, v_inst_1160_);
lean_dec(v_pat_1159_);
return v_res_1161_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg(lean_object* v_s_1162_, lean_object* v_pos_1163_, lean_object* v_inst_1164_){
_start:
{
lean_object* v_str_1165_; lean_object* v_startInclusive_1166_; lean_object* v_endExclusive_1167_; lean_object* v___x_1169_; uint8_t v_isShared_1170_; uint8_t v_isSharedCheck_1186_; 
v_str_1165_ = lean_ctor_get(v_s_1162_, 0);
v_startInclusive_1166_ = lean_ctor_get(v_s_1162_, 1);
v_endExclusive_1167_ = lean_ctor_get(v_s_1162_, 2);
v_isSharedCheck_1186_ = !lean_is_exclusive(v_s_1162_);
if (v_isSharedCheck_1186_ == 0)
{
v___x_1169_ = v_s_1162_;
v_isShared_1170_ = v_isSharedCheck_1186_;
goto v_resetjp_1168_;
}
else
{
lean_inc(v_endExclusive_1167_);
lean_inc(v_startInclusive_1166_);
lean_inc(v_str_1165_);
lean_dec(v_s_1162_);
v___x_1169_ = lean_box(0);
v_isShared_1170_ = v_isSharedCheck_1186_;
goto v_resetjp_1168_;
}
v_resetjp_1168_:
{
lean_object* v_skipPrefix_x3f_1171_; lean_object* v___x_1172_; lean_object* v___x_1174_; 
v_skipPrefix_x3f_1171_ = lean_ctor_get(v_inst_1164_, 0);
lean_inc_ref(v_skipPrefix_x3f_1171_);
lean_dec_ref(v_inst_1164_);
v___x_1172_ = lean_nat_add(v_startInclusive_1166_, v_pos_1163_);
lean_dec(v_startInclusive_1166_);
if (v_isShared_1170_ == 0)
{
lean_ctor_set(v___x_1169_, 1, v___x_1172_);
v___x_1174_ = v___x_1169_;
goto v_reusejp_1173_;
}
else
{
lean_object* v_reuseFailAlloc_1185_; 
v_reuseFailAlloc_1185_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1185_, 0, v_str_1165_);
lean_ctor_set(v_reuseFailAlloc_1185_, 1, v___x_1172_);
lean_ctor_set(v_reuseFailAlloc_1185_, 2, v_endExclusive_1167_);
v___x_1174_ = v_reuseFailAlloc_1185_;
goto v_reusejp_1173_;
}
v_reusejp_1173_:
{
lean_object* v___x_1175_; 
v___x_1175_ = lean_apply_1(v_skipPrefix_x3f_1171_, v___x_1174_);
if (lean_obj_tag(v___x_1175_) == 0)
{
return v___x_1175_;
}
else
{
lean_object* v_val_1176_; lean_object* v___x_1178_; uint8_t v_isShared_1179_; uint8_t v_isSharedCheck_1184_; 
v_val_1176_ = lean_ctor_get(v___x_1175_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1175_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1178_ = v___x_1175_;
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
else
{
lean_inc(v_val_1176_);
lean_dec(v___x_1175_);
v___x_1178_ = lean_box(0);
v_isShared_1179_ = v_isSharedCheck_1184_;
goto v_resetjp_1177_;
}
v_resetjp_1177_:
{
lean_object* v___x_1180_; lean_object* v___x_1182_; 
v___x_1180_ = lean_nat_add(v_pos_1163_, v_val_1176_);
lean_dec(v_val_1176_);
if (v_isShared_1179_ == 0)
{
lean_ctor_set(v___x_1178_, 0, v___x_1180_);
v___x_1182_ = v___x_1178_;
goto v_reusejp_1181_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v___x_1180_);
v___x_1182_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1181_;
}
v_reusejp_1181_:
{
return v___x_1182_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg___boxed(lean_object* v_s_1187_, lean_object* v_pos_1188_, lean_object* v_inst_1189_){
_start:
{
lean_object* v_res_1190_; 
v_res_1190_ = l_String_Slice_Pos_skip_x3f___redArg(v_s_1187_, v_pos_1188_, v_inst_1189_);
lean_dec(v_pos_1188_);
return v_res_1190_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f(lean_object* v_00_u03c1_1191_, lean_object* v_s_1192_, lean_object* v_pos_1193_, lean_object* v_pat_1194_, lean_object* v_inst_1195_){
_start:
{
lean_object* v_str_1196_; lean_object* v_startInclusive_1197_; lean_object* v_endExclusive_1198_; lean_object* v___x_1200_; uint8_t v_isShared_1201_; uint8_t v_isSharedCheck_1217_; 
v_str_1196_ = lean_ctor_get(v_s_1192_, 0);
v_startInclusive_1197_ = lean_ctor_get(v_s_1192_, 1);
v_endExclusive_1198_ = lean_ctor_get(v_s_1192_, 2);
v_isSharedCheck_1217_ = !lean_is_exclusive(v_s_1192_);
if (v_isSharedCheck_1217_ == 0)
{
v___x_1200_ = v_s_1192_;
v_isShared_1201_ = v_isSharedCheck_1217_;
goto v_resetjp_1199_;
}
else
{
lean_inc(v_endExclusive_1198_);
lean_inc(v_startInclusive_1197_);
lean_inc(v_str_1196_);
lean_dec(v_s_1192_);
v___x_1200_ = lean_box(0);
v_isShared_1201_ = v_isSharedCheck_1217_;
goto v_resetjp_1199_;
}
v_resetjp_1199_:
{
lean_object* v_skipPrefix_x3f_1202_; lean_object* v___x_1203_; lean_object* v___x_1205_; 
v_skipPrefix_x3f_1202_ = lean_ctor_get(v_inst_1195_, 0);
lean_inc_ref(v_skipPrefix_x3f_1202_);
lean_dec_ref(v_inst_1195_);
v___x_1203_ = lean_nat_add(v_startInclusive_1197_, v_pos_1193_);
lean_dec(v_startInclusive_1197_);
if (v_isShared_1201_ == 0)
{
lean_ctor_set(v___x_1200_, 1, v___x_1203_);
v___x_1205_ = v___x_1200_;
goto v_reusejp_1204_;
}
else
{
lean_object* v_reuseFailAlloc_1216_; 
v_reuseFailAlloc_1216_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1216_, 0, v_str_1196_);
lean_ctor_set(v_reuseFailAlloc_1216_, 1, v___x_1203_);
lean_ctor_set(v_reuseFailAlloc_1216_, 2, v_endExclusive_1198_);
v___x_1205_ = v_reuseFailAlloc_1216_;
goto v_reusejp_1204_;
}
v_reusejp_1204_:
{
lean_object* v___x_1206_; 
v___x_1206_ = lean_apply_1(v_skipPrefix_x3f_1202_, v___x_1205_);
if (lean_obj_tag(v___x_1206_) == 0)
{
return v___x_1206_;
}
else
{
lean_object* v_val_1207_; lean_object* v___x_1209_; uint8_t v_isShared_1210_; uint8_t v_isSharedCheck_1215_; 
v_val_1207_ = lean_ctor_get(v___x_1206_, 0);
v_isSharedCheck_1215_ = !lean_is_exclusive(v___x_1206_);
if (v_isSharedCheck_1215_ == 0)
{
v___x_1209_ = v___x_1206_;
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
else
{
lean_inc(v_val_1207_);
lean_dec(v___x_1206_);
v___x_1209_ = lean_box(0);
v_isShared_1210_ = v_isSharedCheck_1215_;
goto v_resetjp_1208_;
}
v_resetjp_1208_:
{
lean_object* v___x_1211_; lean_object* v___x_1213_; 
v___x_1211_ = lean_nat_add(v_pos_1193_, v_val_1207_);
lean_dec(v_val_1207_);
if (v_isShared_1210_ == 0)
{
lean_ctor_set(v___x_1209_, 0, v___x_1211_);
v___x_1213_ = v___x_1209_;
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_1218_, lean_object* v_s_1219_, lean_object* v_pos_1220_, lean_object* v_pat_1221_, lean_object* v_inst_1222_){
_start:
{
lean_object* v_res_1223_; 
v_res_1223_ = l_String_Slice_Pos_skip_x3f(v_00_u03c1_1218_, v_s_1219_, v_pos_1220_, v_pat_1221_, v_inst_1222_);
lean_dec(v_pat_1221_);
lean_dec(v_pos_1220_);
return v_res_1223_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___redArg(lean_object* v_s_1224_, lean_object* v_inst_1225_){
_start:
{
lean_object* v_skipPrefix_x3f_1226_; lean_object* v___x_1227_; 
v_skipPrefix_x3f_1226_ = lean_ctor_get(v_inst_1225_, 0);
lean_inc_ref(v_skipPrefix_x3f_1226_);
lean_dec_ref(v_inst_1225_);
lean_inc_ref(v_s_1224_);
v___x_1227_ = lean_apply_1(v_skipPrefix_x3f_1226_, v_s_1224_);
if (lean_obj_tag(v___x_1227_) == 0)
{
lean_object* v___x_1228_; 
lean_dec_ref(v_s_1224_);
v___x_1228_ = lean_box(0);
return v___x_1228_;
}
else
{
lean_object* v_val_1229_; lean_object* v___x_1231_; uint8_t v_isShared_1232_; uint8_t v_isSharedCheck_1247_; 
v_val_1229_ = lean_ctor_get(v___x_1227_, 0);
v_isSharedCheck_1247_ = !lean_is_exclusive(v___x_1227_);
if (v_isSharedCheck_1247_ == 0)
{
v___x_1231_ = v___x_1227_;
v_isShared_1232_ = v_isSharedCheck_1247_;
goto v_resetjp_1230_;
}
else
{
lean_inc(v_val_1229_);
lean_dec(v___x_1227_);
v___x_1231_ = lean_box(0);
v_isShared_1232_ = v_isSharedCheck_1247_;
goto v_resetjp_1230_;
}
v_resetjp_1230_:
{
lean_object* v_str_1233_; lean_object* v_startInclusive_1234_; lean_object* v_endExclusive_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1246_; 
v_str_1233_ = lean_ctor_get(v_s_1224_, 0);
v_startInclusive_1234_ = lean_ctor_get(v_s_1224_, 1);
v_endExclusive_1235_ = lean_ctor_get(v_s_1224_, 2);
v_isSharedCheck_1246_ = !lean_is_exclusive(v_s_1224_);
if (v_isSharedCheck_1246_ == 0)
{
v___x_1237_ = v_s_1224_;
v_isShared_1238_ = v_isSharedCheck_1246_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_endExclusive_1235_);
lean_inc(v_startInclusive_1234_);
lean_inc(v_str_1233_);
lean_dec(v_s_1224_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1246_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = lean_nat_add(v_startInclusive_1234_, v_val_1229_);
lean_dec(v_val_1229_);
lean_dec(v_startInclusive_1234_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 1, v___x_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1245_; 
v_reuseFailAlloc_1245_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1245_, 0, v_str_1233_);
lean_ctor_set(v_reuseFailAlloc_1245_, 1, v___x_1239_);
lean_ctor_set(v_reuseFailAlloc_1245_, 2, v_endExclusive_1235_);
v___x_1241_ = v_reuseFailAlloc_1245_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
lean_object* v___x_1243_; 
if (v_isShared_1232_ == 0)
{
lean_ctor_set(v___x_1231_, 0, v___x_1241_);
v___x_1243_ = v___x_1231_;
goto v_reusejp_1242_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v___x_1241_);
v___x_1243_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1242_;
}
v_reusejp_1242_:
{
return v___x_1243_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f(lean_object* v_00_u03c1_1248_, lean_object* v_s_1249_, lean_object* v_pat_1250_, lean_object* v_inst_1251_){
_start:
{
lean_object* v_skipPrefix_x3f_1252_; lean_object* v___x_1253_; 
v_skipPrefix_x3f_1252_ = lean_ctor_get(v_inst_1251_, 0);
lean_inc_ref(v_skipPrefix_x3f_1252_);
lean_dec_ref(v_inst_1251_);
lean_inc_ref(v_s_1249_);
v___x_1253_ = lean_apply_1(v_skipPrefix_x3f_1252_, v_s_1249_);
if (lean_obj_tag(v___x_1253_) == 0)
{
lean_object* v___x_1254_; 
lean_dec_ref(v_s_1249_);
v___x_1254_ = lean_box(0);
return v___x_1254_;
}
else
{
lean_object* v_val_1255_; lean_object* v___x_1257_; uint8_t v_isShared_1258_; uint8_t v_isSharedCheck_1273_; 
v_val_1255_ = lean_ctor_get(v___x_1253_, 0);
v_isSharedCheck_1273_ = !lean_is_exclusive(v___x_1253_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1257_ = v___x_1253_;
v_isShared_1258_ = v_isSharedCheck_1273_;
goto v_resetjp_1256_;
}
else
{
lean_inc(v_val_1255_);
lean_dec(v___x_1253_);
v___x_1257_ = lean_box(0);
v_isShared_1258_ = v_isSharedCheck_1273_;
goto v_resetjp_1256_;
}
v_resetjp_1256_:
{
lean_object* v_str_1259_; lean_object* v_startInclusive_1260_; lean_object* v_endExclusive_1261_; lean_object* v___x_1263_; uint8_t v_isShared_1264_; uint8_t v_isSharedCheck_1272_; 
v_str_1259_ = lean_ctor_get(v_s_1249_, 0);
v_startInclusive_1260_ = lean_ctor_get(v_s_1249_, 1);
v_endExclusive_1261_ = lean_ctor_get(v_s_1249_, 2);
v_isSharedCheck_1272_ = !lean_is_exclusive(v_s_1249_);
if (v_isSharedCheck_1272_ == 0)
{
v___x_1263_ = v_s_1249_;
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
else
{
lean_inc(v_endExclusive_1261_);
lean_inc(v_startInclusive_1260_);
lean_inc(v_str_1259_);
lean_dec(v_s_1249_);
v___x_1263_ = lean_box(0);
v_isShared_1264_ = v_isSharedCheck_1272_;
goto v_resetjp_1262_;
}
v_resetjp_1262_:
{
lean_object* v___x_1265_; lean_object* v___x_1267_; 
v___x_1265_ = lean_nat_add(v_startInclusive_1260_, v_val_1255_);
lean_dec(v_val_1255_);
lean_dec(v_startInclusive_1260_);
if (v_isShared_1264_ == 0)
{
lean_ctor_set(v___x_1263_, 1, v___x_1265_);
v___x_1267_ = v___x_1263_;
goto v_reusejp_1266_;
}
else
{
lean_object* v_reuseFailAlloc_1271_; 
v_reuseFailAlloc_1271_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1271_, 0, v_str_1259_);
lean_ctor_set(v_reuseFailAlloc_1271_, 1, v___x_1265_);
lean_ctor_set(v_reuseFailAlloc_1271_, 2, v_endExclusive_1261_);
v___x_1267_ = v_reuseFailAlloc_1271_;
goto v_reusejp_1266_;
}
v_reusejp_1266_:
{
lean_object* v___x_1269_; 
if (v_isShared_1258_ == 0)
{
lean_ctor_set(v___x_1257_, 0, v___x_1267_);
v___x_1269_ = v___x_1257_;
goto v_reusejp_1268_;
}
else
{
lean_object* v_reuseFailAlloc_1270_; 
v_reuseFailAlloc_1270_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1270_, 0, v___x_1267_);
v___x_1269_ = v_reuseFailAlloc_1270_;
goto v_reusejp_1268_;
}
v_reusejp_1268_:
{
return v___x_1269_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_1274_, lean_object* v_s_1275_, lean_object* v_pat_1276_, lean_object* v_inst_1277_){
_start:
{
lean_object* v_res_1278_; 
v_res_1278_ = l_String_Slice_dropPrefix_x3f(v_00_u03c1_1274_, v_s_1275_, v_pat_1276_, v_inst_1277_);
lean_dec(v_pat_1276_);
return v_res_1278_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___redArg(lean_object* v_s_1279_, lean_object* v_inst_1280_){
_start:
{
lean_object* v_skipPrefix_x3f_1281_; lean_object* v___x_1282_; 
v_skipPrefix_x3f_1281_ = lean_ctor_get(v_inst_1280_, 0);
lean_inc_ref(v_skipPrefix_x3f_1281_);
lean_dec_ref(v_inst_1280_);
lean_inc_ref(v_s_1279_);
v___x_1282_ = lean_apply_1(v_skipPrefix_x3f_1281_, v_s_1279_);
if (lean_obj_tag(v___x_1282_) == 0)
{
return v_s_1279_;
}
else
{
lean_object* v_val_1283_; lean_object* v_str_1284_; lean_object* v_startInclusive_1285_; lean_object* v_endExclusive_1286_; lean_object* v___x_1288_; uint8_t v_isShared_1289_; uint8_t v_isSharedCheck_1294_; 
v_val_1283_ = lean_ctor_get(v___x_1282_, 0);
lean_inc(v_val_1283_);
lean_dec_ref(v___x_1282_);
v_str_1284_ = lean_ctor_get(v_s_1279_, 0);
v_startInclusive_1285_ = lean_ctor_get(v_s_1279_, 1);
v_endExclusive_1286_ = lean_ctor_get(v_s_1279_, 2);
v_isSharedCheck_1294_ = !lean_is_exclusive(v_s_1279_);
if (v_isSharedCheck_1294_ == 0)
{
v___x_1288_ = v_s_1279_;
v_isShared_1289_ = v_isSharedCheck_1294_;
goto v_resetjp_1287_;
}
else
{
lean_inc(v_endExclusive_1286_);
lean_inc(v_startInclusive_1285_);
lean_inc(v_str_1284_);
lean_dec(v_s_1279_);
v___x_1288_ = lean_box(0);
v_isShared_1289_ = v_isSharedCheck_1294_;
goto v_resetjp_1287_;
}
v_resetjp_1287_:
{
lean_object* v___x_1290_; lean_object* v___x_1292_; 
v___x_1290_ = lean_nat_add(v_startInclusive_1285_, v_val_1283_);
lean_dec(v_val_1283_);
lean_dec(v_startInclusive_1285_);
if (v_isShared_1289_ == 0)
{
lean_ctor_set(v___x_1288_, 1, v___x_1290_);
v___x_1292_ = v___x_1288_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1293_; 
v_reuseFailAlloc_1293_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1293_, 0, v_str_1284_);
lean_ctor_set(v_reuseFailAlloc_1293_, 1, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1293_, 2, v_endExclusive_1286_);
v___x_1292_ = v_reuseFailAlloc_1293_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
return v___x_1292_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix(lean_object* v_00_u03c1_1295_, lean_object* v_s_1296_, lean_object* v_pat_1297_, lean_object* v_inst_1298_){
_start:
{
lean_object* v___x_1299_; 
v___x_1299_ = l_String_Slice_dropPrefix___redArg(v_s_1296_, v_inst_1298_);
return v___x_1299_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___boxed(lean_object* v_00_u03c1_1300_, lean_object* v_s_1301_, lean_object* v_pat_1302_, lean_object* v_inst_1303_){
_start:
{
lean_object* v_res_1304_; 
v_res_1304_ = l_String_Slice_dropPrefix(v_00_u03c1_1300_, v_s_1301_, v_pat_1302_, v_inst_1303_);
lean_dec(v_pat_1302_);
return v_res_1304_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__0(lean_object* v_x_1305_, lean_object* v_x_1306_, lean_object* v_f_1307_, lean_object* v_c_1308_){
_start:
{
lean_object* v___x_1309_; 
v___x_1309_ = lean_apply_1(v_f_1307_, v_c_1308_);
return v___x_1309_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1(lean_object* v_s_1310_, lean_object* v_inst_1311_, lean_object* v_replacement_1312_, lean_object* v_x1_1313_, lean_object* v_x2_1314_, lean_object* v_x3_1315_){
_start:
{
if (lean_obj_tag(v_x1_1313_) == 0)
{
lean_object* v_startPos_1316_; lean_object* v_endPos_1317_; lean_object* v___x_1318_; lean_object* v_str_1319_; lean_object* v_startInclusive_1320_; lean_object* v_endExclusive_1321_; lean_object* v___x_1322_; lean_object* v___x_1323_; lean_object* v___x_1324_; 
lean_dec(v_replacement_1312_);
lean_dec_ref(v_inst_1311_);
v_startPos_1316_ = lean_ctor_get(v_x1_1313_, 0);
v_endPos_1317_ = lean_ctor_get(v_x1_1313_, 1);
v___x_1318_ = l_String_Slice_slice_x21(v_s_1310_, v_startPos_1316_, v_endPos_1317_);
v_str_1319_ = lean_ctor_get(v___x_1318_, 0);
lean_inc_ref(v_str_1319_);
v_startInclusive_1320_ = lean_ctor_get(v___x_1318_, 1);
lean_inc(v_startInclusive_1320_);
v_endExclusive_1321_ = lean_ctor_get(v___x_1318_, 2);
lean_inc(v_endExclusive_1321_);
lean_dec_ref(v___x_1318_);
v___x_1322_ = lean_string_utf8_extract(v_str_1319_, v_startInclusive_1320_, v_endExclusive_1321_);
lean_dec(v_endExclusive_1321_);
lean_dec(v_startInclusive_1320_);
lean_dec_ref(v_str_1319_);
v___x_1323_ = lean_string_append(v_x3_1315_, v___x_1322_);
lean_dec_ref(v___x_1322_);
v___x_1324_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1324_, 0, v___x_1323_);
return v___x_1324_;
}
else
{
lean_object* v___x_1325_; lean_object* v_str_1326_; lean_object* v_startInclusive_1327_; lean_object* v_endExclusive_1328_; lean_object* v___x_1329_; lean_object* v___x_1330_; lean_object* v___x_1331_; 
lean_dec_ref(v_s_1310_);
v___x_1325_ = lean_apply_1(v_inst_1311_, v_replacement_1312_);
v_str_1326_ = lean_ctor_get(v___x_1325_, 0);
lean_inc_ref(v_str_1326_);
v_startInclusive_1327_ = lean_ctor_get(v___x_1325_, 1);
lean_inc(v_startInclusive_1327_);
v_endExclusive_1328_ = lean_ctor_get(v___x_1325_, 2);
lean_inc(v_endExclusive_1328_);
lean_dec_ref(v___x_1325_);
v___x_1329_ = lean_string_utf8_extract(v_str_1326_, v_startInclusive_1327_, v_endExclusive_1328_);
lean_dec(v_endExclusive_1328_);
lean_dec(v_startInclusive_1327_);
lean_dec_ref(v_str_1326_);
v___x_1330_ = lean_string_append(v_x3_1315_, v___x_1329_);
lean_dec_ref(v___x_1329_);
v___x_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1331_, 0, v___x_1330_);
return v___x_1331_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1___boxed(lean_object* v_s_1332_, lean_object* v_inst_1333_, lean_object* v_replacement_1334_, lean_object* v_x1_1335_, lean_object* v_x2_1336_, lean_object* v_x3_1337_){
_start:
{
lean_object* v_res_1338_; 
v_res_1338_ = l_String_Slice_replace___redArg___lam__1(v_s_1332_, v_inst_1333_, v_replacement_1334_, v_x1_1335_, v_x2_1336_, v_x3_1337_);
lean_dec_ref(v_x1_1335_);
return v_res_1338_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg(lean_object* v_inst_1341_, lean_object* v_inst_1342_, lean_object* v_s_1343_, lean_object* v_inst_1344_, lean_object* v_replacement_1345_){
_start:
{
lean_object* v___f_1346_; lean_object* v___f_1347_; lean_object* v___x_1348_; lean_object* v___x_1349_; lean_object* v___x_1350_; 
v___f_1346_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1343_);
v___f_1347_ = lean_alloc_closure((void*)(l_String_Slice_replace___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1347_, 0, v_s_1343_);
lean_closure_set(v___f_1347_, 1, v_inst_1342_);
lean_closure_set(v___f_1347_, 2, v_replacement_1345_);
v___x_1348_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
lean_inc_ref(v_s_1343_);
v___x_1349_ = lean_apply_1(v_inst_1344_, v_s_1343_);
v___x_1350_ = lean_apply_7(v_inst_1341_, v_s_1343_, v___f_1346_, lean_box(0), lean_box(0), v___x_1349_, v___x_1348_, v___f_1347_);
return v___x_1350_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace(lean_object* v_00_u03c1_1351_, lean_object* v_00_u03c3_1352_, lean_object* v_inst_1353_, lean_object* v_inst_1354_, lean_object* v_00_u03b1_1355_, lean_object* v_inst_1356_, lean_object* v_s_1357_, lean_object* v_pattern_1358_, lean_object* v_inst_1359_, lean_object* v_replacement_1360_){
_start:
{
lean_object* v___x_1361_; 
v___x_1361_ = l_String_Slice_replace___redArg(v_inst_1354_, v_inst_1356_, v_s_1357_, v_inst_1359_, v_replacement_1360_);
return v___x_1361_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___boxed(lean_object* v_00_u03c1_1362_, lean_object* v_00_u03c3_1363_, lean_object* v_inst_1364_, lean_object* v_inst_1365_, lean_object* v_00_u03b1_1366_, lean_object* v_inst_1367_, lean_object* v_s_1368_, lean_object* v_pattern_1369_, lean_object* v_inst_1370_, lean_object* v_replacement_1371_){
_start:
{
lean_object* v_res_1372_; 
v_res_1372_ = l_String_Slice_replace(v_00_u03c1_1362_, v_00_u03c3_1363_, v_inst_1364_, v_inst_1365_, v_00_u03b1_1366_, v_inst_1367_, v_s_1368_, v_pattern_1369_, v_inst_1370_, v_replacement_1371_);
lean_dec(v_pattern_1369_);
lean_dec(v_inst_1364_);
return v_res_1372_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object* v_s_1373_, lean_object* v_n_1374_){
_start:
{
lean_object* v_str_1375_; lean_object* v_startInclusive_1376_; lean_object* v_endExclusive_1377_; lean_object* v___x_1378_; lean_object* v___x_1379_; lean_object* v___x_1381_; uint8_t v_isShared_1382_; uint8_t v_isSharedCheck_1387_; 
v_str_1375_ = lean_ctor_get(v_s_1373_, 0);
lean_inc_ref(v_str_1375_);
v_startInclusive_1376_ = lean_ctor_get(v_s_1373_, 1);
lean_inc(v_startInclusive_1376_);
v_endExclusive_1377_ = lean_ctor_get(v_s_1373_, 2);
lean_inc(v_endExclusive_1377_);
v___x_1378_ = lean_unsigned_to_nat(0u);
v___x_1379_ = l_String_Slice_Pos_nextn(v_s_1373_, v___x_1378_, v_n_1374_);
v_isSharedCheck_1387_ = !lean_is_exclusive(v_s_1373_);
if (v_isSharedCheck_1387_ == 0)
{
lean_object* v_unused_1388_; lean_object* v_unused_1389_; lean_object* v_unused_1390_; 
v_unused_1388_ = lean_ctor_get(v_s_1373_, 2);
lean_dec(v_unused_1388_);
v_unused_1389_ = lean_ctor_get(v_s_1373_, 1);
lean_dec(v_unused_1389_);
v_unused_1390_ = lean_ctor_get(v_s_1373_, 0);
lean_dec(v_unused_1390_);
v___x_1381_ = v_s_1373_;
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
else
{
lean_dec(v_s_1373_);
v___x_1381_ = lean_box(0);
v_isShared_1382_ = v_isSharedCheck_1387_;
goto v_resetjp_1380_;
}
v_resetjp_1380_:
{
lean_object* v___x_1383_; lean_object* v___x_1385_; 
v___x_1383_ = lean_nat_add(v_startInclusive_1376_, v___x_1379_);
lean_dec(v___x_1379_);
lean_dec(v_startInclusive_1376_);
if (v_isShared_1382_ == 0)
{
lean_ctor_set(v___x_1381_, 1, v___x_1383_);
v___x_1385_ = v___x_1381_;
goto v_reusejp_1384_;
}
else
{
lean_object* v_reuseFailAlloc_1386_; 
v_reuseFailAlloc_1386_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1386_, 0, v_str_1375_);
lean_ctor_set(v_reuseFailAlloc_1386_, 1, v___x_1383_);
lean_ctor_set(v_reuseFailAlloc_1386_, 2, v_endExclusive_1377_);
v___x_1385_ = v_reuseFailAlloc_1386_;
goto v_reusejp_1384_;
}
v_reusejp_1384_:
{
return v___x_1385_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object* v_s_1391_, lean_object* v_pos_1392_, lean_object* v_inst_1393_){
_start:
{
lean_object* v_skipPrefix_x3f_1394_; lean_object* v_str_1395_; lean_object* v_startInclusive_1396_; lean_object* v_endExclusive_1397_; lean_object* v___x_1398_; lean_object* v___x_1399_; lean_object* v___x_1400_; 
v_skipPrefix_x3f_1394_ = lean_ctor_get(v_inst_1393_, 0);
v_str_1395_ = lean_ctor_get(v_s_1391_, 0);
v_startInclusive_1396_ = lean_ctor_get(v_s_1391_, 1);
v_endExclusive_1397_ = lean_ctor_get(v_s_1391_, 2);
v___x_1398_ = lean_nat_add(v_startInclusive_1396_, v_pos_1392_);
lean_inc(v_endExclusive_1397_);
lean_inc_ref(v_str_1395_);
v___x_1399_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1399_, 0, v_str_1395_);
lean_ctor_set(v___x_1399_, 1, v___x_1398_);
lean_ctor_set(v___x_1399_, 2, v_endExclusive_1397_);
lean_inc_ref(v_skipPrefix_x3f_1394_);
v___x_1400_ = lean_apply_1(v_skipPrefix_x3f_1394_, v___x_1399_);
if (lean_obj_tag(v___x_1400_) == 1)
{
lean_object* v_val_1401_; lean_object* v___x_1402_; uint8_t v___x_1403_; 
v_val_1401_ = lean_ctor_get(v___x_1400_, 0);
lean_inc(v_val_1401_);
lean_dec_ref(v___x_1400_);
v___x_1402_ = lean_nat_add(v_pos_1392_, v_val_1401_);
lean_dec(v_val_1401_);
v___x_1403_ = lean_nat_dec_lt(v_pos_1392_, v___x_1402_);
if (v___x_1403_ == 0)
{
lean_dec(v___x_1402_);
lean_dec_ref(v_inst_1393_);
return v_pos_1392_;
}
else
{
lean_dec(v_pos_1392_);
v_pos_1392_ = v___x_1402_;
goto _start;
}
}
else
{
lean_dec(v___x_1400_);
lean_dec_ref(v_inst_1393_);
return v_pos_1392_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg___boxed(lean_object* v_s_1405_, lean_object* v_pos_1406_, lean_object* v_inst_1407_){
_start:
{
lean_object* v_res_1408_; 
v_res_1408_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1405_, v_pos_1406_, v_inst_1407_);
lean_dec_ref(v_s_1405_);
return v_res_1408_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile(lean_object* v_00_u03c1_1409_, lean_object* v_s_1410_, lean_object* v_pos_1411_, lean_object* v_pat_1412_, lean_object* v_inst_1413_){
_start:
{
lean_object* v___x_1414_; 
v___x_1414_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1410_, v_pos_1411_, v_inst_1413_);
return v___x_1414_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___boxed(lean_object* v_00_u03c1_1415_, lean_object* v_s_1416_, lean_object* v_pos_1417_, lean_object* v_pat_1418_, lean_object* v_inst_1419_){
_start:
{
lean_object* v_res_1420_; 
v_res_1420_ = l_String_Slice_Pos_skipWhile(v_00_u03c1_1415_, v_s_1416_, v_pos_1417_, v_pat_1418_, v_inst_1419_);
lean_dec(v_pat_1418_);
lean_dec_ref(v_s_1416_);
return v_res_1420_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object* v_x_1421_, lean_object* v_h__1_1422_, lean_object* v_h__2_1423_){
_start:
{
if (lean_obj_tag(v_x_1421_) == 1)
{
lean_object* v_val_1424_; lean_object* v___x_1425_; 
lean_dec(v_h__2_1423_);
v_val_1424_ = lean_ctor_get(v_x_1421_, 0);
lean_inc(v_val_1424_);
lean_dec_ref(v_x_1421_);
v___x_1425_ = lean_apply_1(v_h__1_1422_, v_val_1424_);
return v___x_1425_;
}
else
{
lean_object* v___x_1426_; 
lean_dec(v_h__1_1422_);
v___x_1426_ = lean_apply_2(v_h__2_1423_, v_x_1421_, lean_box(0));
return v___x_1426_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object* v_s_1427_, lean_object* v_pos_1428_, lean_object* v_motive_1429_, lean_object* v_x_1430_, lean_object* v_h__1_1431_, lean_object* v_h__2_1432_){
_start:
{
if (lean_obj_tag(v_x_1430_) == 1)
{
lean_object* v_val_1433_; lean_object* v___x_1434_; 
lean_dec(v_h__2_1432_);
v_val_1433_ = lean_ctor_get(v_x_1430_, 0);
lean_inc(v_val_1433_);
lean_dec_ref(v_x_1430_);
v___x_1434_ = lean_apply_1(v_h__1_1431_, v_val_1433_);
return v___x_1434_;
}
else
{
lean_object* v___x_1435_; 
lean_dec(v_h__1_1431_);
v___x_1435_ = lean_apply_2(v_h__2_1432_, v_x_1430_, lean_box(0));
return v___x_1435_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object* v_s_1436_, lean_object* v_pos_1437_, lean_object* v_motive_1438_, lean_object* v_x_1439_, lean_object* v_h__1_1440_, lean_object* v_h__2_1441_){
_start:
{
lean_object* v_res_1442_; 
v_res_1442_ = l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_1436_, v_pos_1437_, v_motive_1438_, v_x_1439_, v_h__1_1440_, v_h__2_1441_);
lean_dec(v_pos_1437_);
lean_dec_ref(v_s_1436_);
return v_res_1442_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg(lean_object* v_s_1443_, lean_object* v_inst_1444_){
_start:
{
lean_object* v___x_1445_; lean_object* v___x_1446_; 
v___x_1445_ = lean_unsigned_to_nat(0u);
v___x_1446_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1443_, v___x_1445_, v_inst_1444_);
return v___x_1446_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg___boxed(lean_object* v_s_1447_, lean_object* v_inst_1448_){
_start:
{
lean_object* v_res_1449_; 
v_res_1449_ = l_String_Slice_skipPrefixWhile___redArg(v_s_1447_, v_inst_1448_);
lean_dec_ref(v_s_1447_);
return v_res_1449_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile(lean_object* v_00_u03c1_1450_, lean_object* v_s_1451_, lean_object* v_pat_1452_, lean_object* v_inst_1453_){
_start:
{
lean_object* v___x_1454_; lean_object* v___x_1455_; 
v___x_1454_ = lean_unsigned_to_nat(0u);
v___x_1455_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1451_, v___x_1454_, v_inst_1453_);
return v___x_1455_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___boxed(lean_object* v_00_u03c1_1456_, lean_object* v_s_1457_, lean_object* v_pat_1458_, lean_object* v_inst_1459_){
_start:
{
lean_object* v_res_1460_; 
v_res_1460_ = l_String_Slice_skipPrefixWhile(v_00_u03c1_1456_, v_s_1457_, v_pat_1458_, v_inst_1459_);
lean_dec(v_pat_1458_);
lean_dec_ref(v_s_1457_);
return v_res_1460_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg(lean_object* v_s_1461_, lean_object* v_inst_1462_){
_start:
{
lean_object* v_str_1463_; lean_object* v_startInclusive_1464_; lean_object* v_endExclusive_1465_; lean_object* v___x_1466_; lean_object* v___x_1467_; lean_object* v___x_1469_; uint8_t v_isShared_1470_; uint8_t v_isSharedCheck_1475_; 
v_str_1463_ = lean_ctor_get(v_s_1461_, 0);
lean_inc_ref(v_str_1463_);
v_startInclusive_1464_ = lean_ctor_get(v_s_1461_, 1);
lean_inc(v_startInclusive_1464_);
v_endExclusive_1465_ = lean_ctor_get(v_s_1461_, 2);
lean_inc(v_endExclusive_1465_);
v___x_1466_ = lean_unsigned_to_nat(0u);
v___x_1467_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1461_, v___x_1466_, v_inst_1462_);
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
LEAN_EXPORT lean_object* l_String_Slice_dropWhile(lean_object* v_00_u03c1_1479_, lean_object* v_s_1480_, lean_object* v_pat_1481_, lean_object* v_inst_1482_){
_start:
{
lean_object* v_str_1483_; lean_object* v_startInclusive_1484_; lean_object* v_endExclusive_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; lean_object* v___x_1489_; uint8_t v_isShared_1490_; uint8_t v_isSharedCheck_1495_; 
v_str_1483_ = lean_ctor_get(v_s_1480_, 0);
lean_inc_ref(v_str_1483_);
v_startInclusive_1484_ = lean_ctor_get(v_s_1480_, 1);
lean_inc(v_startInclusive_1484_);
v_endExclusive_1485_ = lean_ctor_get(v_s_1480_, 2);
lean_inc(v_endExclusive_1485_);
v___x_1486_ = lean_unsigned_to_nat(0u);
v___x_1487_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1480_, v___x_1486_, v_inst_1482_);
v_isSharedCheck_1495_ = !lean_is_exclusive(v_s_1480_);
if (v_isSharedCheck_1495_ == 0)
{
lean_object* v_unused_1496_; lean_object* v_unused_1497_; lean_object* v_unused_1498_; 
v_unused_1496_ = lean_ctor_get(v_s_1480_, 2);
lean_dec(v_unused_1496_);
v_unused_1497_ = lean_ctor_get(v_s_1480_, 1);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_s_1480_, 0);
lean_dec(v_unused_1498_);
v___x_1489_ = v_s_1480_;
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
else
{
lean_dec(v_s_1480_);
v___x_1489_ = lean_box(0);
v_isShared_1490_ = v_isSharedCheck_1495_;
goto v_resetjp_1488_;
}
v_resetjp_1488_:
{
lean_object* v___x_1491_; lean_object* v___x_1493_; 
v___x_1491_ = lean_nat_add(v_startInclusive_1484_, v___x_1487_);
lean_dec(v___x_1487_);
lean_dec(v_startInclusive_1484_);
if (v_isShared_1490_ == 0)
{
lean_ctor_set(v___x_1489_, 1, v___x_1491_);
v___x_1493_ = v___x_1489_;
goto v_reusejp_1492_;
}
else
{
lean_object* v_reuseFailAlloc_1494_; 
v_reuseFailAlloc_1494_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1494_, 0, v_str_1483_);
lean_ctor_set(v_reuseFailAlloc_1494_, 1, v___x_1491_);
lean_ctor_set(v_reuseFailAlloc_1494_, 2, v_endExclusive_1485_);
v___x_1493_ = v_reuseFailAlloc_1494_;
goto v_reusejp_1492_;
}
v_reusejp_1492_:
{
return v___x_1493_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___boxed(lean_object* v_00_u03c1_1499_, lean_object* v_s_1500_, lean_object* v_pat_1501_, lean_object* v_inst_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l_String_Slice_dropWhile(v_00_u03c1_1499_, v_s_1500_, v_pat_1501_, v_inst_1502_);
lean_dec(v_pat_1501_);
return v_res_1503_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiStart___closed__1(void){
_start:
{
lean_object* v___x_1505_; lean_object* v___x_1506_; 
v___x_1505_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_1506_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1505_);
return v___x_1506_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart(lean_object* v_s_1507_){
_start:
{
lean_object* v___x_1508_; lean_object* v_str_1509_; lean_object* v_startInclusive_1510_; lean_object* v_endExclusive_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; lean_object* v___x_1515_; uint8_t v_isShared_1516_; uint8_t v_isSharedCheck_1521_; 
v___x_1508_ = lean_obj_once(&l_String_Slice_trimAsciiStart___closed__1, &l_String_Slice_trimAsciiStart___closed__1_once, _init_l_String_Slice_trimAsciiStart___closed__1);
v_str_1509_ = lean_ctor_get(v_s_1507_, 0);
lean_inc_ref(v_str_1509_);
v_startInclusive_1510_ = lean_ctor_get(v_s_1507_, 1);
lean_inc(v_startInclusive_1510_);
v_endExclusive_1511_ = lean_ctor_get(v_s_1507_, 2);
lean_inc(v_endExclusive_1511_);
v___x_1512_ = lean_unsigned_to_nat(0u);
v___x_1513_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1507_, v___x_1512_, v___x_1508_);
v_isSharedCheck_1521_ = !lean_is_exclusive(v_s_1507_);
if (v_isSharedCheck_1521_ == 0)
{
lean_object* v_unused_1522_; lean_object* v_unused_1523_; lean_object* v_unused_1524_; 
v_unused_1522_ = lean_ctor_get(v_s_1507_, 2);
lean_dec(v_unused_1522_);
v_unused_1523_ = lean_ctor_get(v_s_1507_, 1);
lean_dec(v_unused_1523_);
v_unused_1524_ = lean_ctor_get(v_s_1507_, 0);
lean_dec(v_unused_1524_);
v___x_1515_ = v_s_1507_;
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
else
{
lean_dec(v_s_1507_);
v___x_1515_ = lean_box(0);
v_isShared_1516_ = v_isSharedCheck_1521_;
goto v_resetjp_1514_;
}
v_resetjp_1514_:
{
lean_object* v___x_1517_; lean_object* v___x_1519_; 
v___x_1517_ = lean_nat_add(v_startInclusive_1510_, v___x_1513_);
lean_dec(v___x_1513_);
lean_dec(v_startInclusive_1510_);
if (v_isShared_1516_ == 0)
{
lean_ctor_set(v___x_1515_, 1, v___x_1517_);
v___x_1519_ = v___x_1515_;
goto v_reusejp_1518_;
}
else
{
lean_object* v_reuseFailAlloc_1520_; 
v_reuseFailAlloc_1520_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1520_, 0, v_str_1509_);
lean_ctor_set(v_reuseFailAlloc_1520_, 1, v___x_1517_);
lean_ctor_set(v_reuseFailAlloc_1520_, 2, v_endExclusive_1511_);
v___x_1519_ = v_reuseFailAlloc_1520_;
goto v_reusejp_1518_;
}
v_reusejp_1518_:
{
return v___x_1519_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object* v_s_1525_, lean_object* v_n_1526_){
_start:
{
lean_object* v_str_1527_; lean_object* v_startInclusive_1528_; lean_object* v___x_1529_; lean_object* v___x_1530_; lean_object* v___x_1532_; uint8_t v_isShared_1533_; uint8_t v_isSharedCheck_1538_; 
v_str_1527_ = lean_ctor_get(v_s_1525_, 0);
lean_inc_ref(v_str_1527_);
v_startInclusive_1528_ = lean_ctor_get(v_s_1525_, 1);
lean_inc(v_startInclusive_1528_);
v___x_1529_ = lean_unsigned_to_nat(0u);
v___x_1530_ = l_String_Slice_Pos_nextn(v_s_1525_, v___x_1529_, v_n_1526_);
v_isSharedCheck_1538_ = !lean_is_exclusive(v_s_1525_);
if (v_isSharedCheck_1538_ == 0)
{
lean_object* v_unused_1539_; lean_object* v_unused_1540_; lean_object* v_unused_1541_; 
v_unused_1539_ = lean_ctor_get(v_s_1525_, 2);
lean_dec(v_unused_1539_);
v_unused_1540_ = lean_ctor_get(v_s_1525_, 1);
lean_dec(v_unused_1540_);
v_unused_1541_ = lean_ctor_get(v_s_1525_, 0);
lean_dec(v_unused_1541_);
v___x_1532_ = v_s_1525_;
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
else
{
lean_dec(v_s_1525_);
v___x_1532_ = lean_box(0);
v_isShared_1533_ = v_isSharedCheck_1538_;
goto v_resetjp_1531_;
}
v_resetjp_1531_:
{
lean_object* v___x_1534_; lean_object* v___x_1536_; 
v___x_1534_ = lean_nat_add(v_startInclusive_1528_, v___x_1530_);
lean_dec(v___x_1530_);
if (v_isShared_1533_ == 0)
{
lean_ctor_set(v___x_1532_, 2, v___x_1534_);
v___x_1536_ = v___x_1532_;
goto v_reusejp_1535_;
}
else
{
lean_object* v_reuseFailAlloc_1537_; 
v_reuseFailAlloc_1537_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1537_, 0, v_str_1527_);
lean_ctor_set(v_reuseFailAlloc_1537_, 1, v_startInclusive_1528_);
lean_ctor_set(v_reuseFailAlloc_1537_, 2, v___x_1534_);
v___x_1536_ = v_reuseFailAlloc_1537_;
goto v_reusejp_1535_;
}
v_reusejp_1535_:
{
return v___x_1536_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___redArg(lean_object* v_s_1542_, lean_object* v_inst_1543_){
_start:
{
lean_object* v_str_1544_; lean_object* v_startInclusive_1545_; lean_object* v___x_1546_; lean_object* v___x_1547_; lean_object* v___x_1549_; uint8_t v_isShared_1550_; uint8_t v_isSharedCheck_1555_; 
v_str_1544_ = lean_ctor_get(v_s_1542_, 0);
lean_inc_ref(v_str_1544_);
v_startInclusive_1545_ = lean_ctor_get(v_s_1542_, 1);
lean_inc(v_startInclusive_1545_);
v___x_1546_ = lean_unsigned_to_nat(0u);
v___x_1547_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1542_, v___x_1546_, v_inst_1543_);
v_isSharedCheck_1555_ = !lean_is_exclusive(v_s_1542_);
if (v_isSharedCheck_1555_ == 0)
{
lean_object* v_unused_1556_; lean_object* v_unused_1557_; lean_object* v_unused_1558_; 
v_unused_1556_ = lean_ctor_get(v_s_1542_, 2);
lean_dec(v_unused_1556_);
v_unused_1557_ = lean_ctor_get(v_s_1542_, 1);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v_s_1542_, 0);
lean_dec(v_unused_1558_);
v___x_1549_ = v_s_1542_;
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
else
{
lean_dec(v_s_1542_);
v___x_1549_ = lean_box(0);
v_isShared_1550_ = v_isSharedCheck_1555_;
goto v_resetjp_1548_;
}
v_resetjp_1548_:
{
lean_object* v___x_1551_; lean_object* v___x_1553_; 
v___x_1551_ = lean_nat_add(v_startInclusive_1545_, v___x_1547_);
lean_dec(v___x_1547_);
if (v_isShared_1550_ == 0)
{
lean_ctor_set(v___x_1549_, 2, v___x_1551_);
v___x_1553_ = v___x_1549_;
goto v_reusejp_1552_;
}
else
{
lean_object* v_reuseFailAlloc_1554_; 
v_reuseFailAlloc_1554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1554_, 0, v_str_1544_);
lean_ctor_set(v_reuseFailAlloc_1554_, 1, v_startInclusive_1545_);
lean_ctor_set(v_reuseFailAlloc_1554_, 2, v___x_1551_);
v___x_1553_ = v_reuseFailAlloc_1554_;
goto v_reusejp_1552_;
}
v_reusejp_1552_:
{
return v___x_1553_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile(lean_object* v_00_u03c1_1559_, lean_object* v_s_1560_, lean_object* v_pat_1561_, lean_object* v_inst_1562_){
_start:
{
lean_object* v_str_1563_; lean_object* v_startInclusive_1564_; lean_object* v___x_1565_; lean_object* v___x_1566_; lean_object* v___x_1568_; uint8_t v_isShared_1569_; uint8_t v_isSharedCheck_1574_; 
v_str_1563_ = lean_ctor_get(v_s_1560_, 0);
lean_inc_ref(v_str_1563_);
v_startInclusive_1564_ = lean_ctor_get(v_s_1560_, 1);
lean_inc(v_startInclusive_1564_);
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1560_, v___x_1565_, v_inst_1562_);
v_isSharedCheck_1574_ = !lean_is_exclusive(v_s_1560_);
if (v_isSharedCheck_1574_ == 0)
{
lean_object* v_unused_1575_; lean_object* v_unused_1576_; lean_object* v_unused_1577_; 
v_unused_1575_ = lean_ctor_get(v_s_1560_, 2);
lean_dec(v_unused_1575_);
v_unused_1576_ = lean_ctor_get(v_s_1560_, 1);
lean_dec(v_unused_1576_);
v_unused_1577_ = lean_ctor_get(v_s_1560_, 0);
lean_dec(v_unused_1577_);
v___x_1568_ = v_s_1560_;
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
else
{
lean_dec(v_s_1560_);
v___x_1568_ = lean_box(0);
v_isShared_1569_ = v_isSharedCheck_1574_;
goto v_resetjp_1567_;
}
v_resetjp_1567_:
{
lean_object* v___x_1570_; lean_object* v___x_1572_; 
v___x_1570_ = lean_nat_add(v_startInclusive_1564_, v___x_1566_);
lean_dec(v___x_1566_);
if (v_isShared_1569_ == 0)
{
lean_ctor_set(v___x_1568_, 2, v___x_1570_);
v___x_1572_ = v___x_1568_;
goto v_reusejp_1571_;
}
else
{
lean_object* v_reuseFailAlloc_1573_; 
v_reuseFailAlloc_1573_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1573_, 0, v_str_1563_);
lean_ctor_set(v_reuseFailAlloc_1573_, 1, v_startInclusive_1564_);
lean_ctor_set(v_reuseFailAlloc_1573_, 2, v___x_1570_);
v___x_1572_ = v_reuseFailAlloc_1573_;
goto v_reusejp_1571_;
}
v_reusejp_1571_:
{
return v___x_1572_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___boxed(lean_object* v_00_u03c1_1578_, lean_object* v_s_1579_, lean_object* v_pat_1580_, lean_object* v_inst_1581_){
_start:
{
lean_object* v_res_1582_; 
v_res_1582_ = l_String_Slice_takeWhile(v_00_u03c1_1578_, v_s_1579_, v_pat_1580_, v_inst_1581_);
lean_dec(v_pat_1580_);
return v_res_1582_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1(lean_object* v___x_1583_, lean_object* v_x1_1584_, lean_object* v_x2_1585_, lean_object* v_x3_1586_){
_start:
{
if (lean_obj_tag(v_x1_1584_) == 0)
{
lean_object* v___x_1587_; 
v___x_1587_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1587_, 0, v___x_1583_);
return v___x_1587_;
}
else
{
lean_object* v_startPos_1588_; lean_object* v___x_1589_; lean_object* v___x_1590_; 
lean_dec(v___x_1583_);
v_startPos_1588_ = lean_ctor_get(v_x1_1584_, 0);
lean_inc(v_startPos_1588_);
v___x_1589_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1589_, 0, v_startPos_1588_);
v___x_1590_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1590_, 0, v___x_1589_);
return v___x_1590_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1___boxed(lean_object* v___x_1591_, lean_object* v_x1_1592_, lean_object* v_x2_1593_, lean_object* v_x3_1594_){
_start:
{
lean_object* v_res_1595_; 
v_res_1595_ = l_String_Slice_find_x3f___redArg___lam__1(v___x_1591_, v_x1_1592_, v_x2_1593_, v_x3_1594_);
lean_dec(v_x3_1594_);
lean_dec_ref(v_x1_1592_);
return v_res_1595_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg(lean_object* v_inst_1598_, lean_object* v_s_1599_, lean_object* v_inst_1600_){
_start:
{
lean_object* v___f_1601_; lean_object* v_searcher_1602_; lean_object* v___x_1603_; lean_object* v___f_1604_; lean_object* v___x_1605_; 
v___f_1601_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1599_);
v_searcher_1602_ = lean_apply_1(v_inst_1600_, v_s_1599_);
v___x_1603_ = lean_box(0);
v___f_1604_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1605_ = lean_apply_7(v_inst_1598_, v_s_1599_, v___f_1601_, lean_box(0), lean_box(0), v_searcher_1602_, v___x_1603_, v___f_1604_);
return v___x_1605_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f(lean_object* v_00_u03c1_1606_, lean_object* v_00_u03c3_1607_, lean_object* v_inst_1608_, lean_object* v_inst_1609_, lean_object* v_s_1610_, lean_object* v_pat_1611_, lean_object* v_inst_1612_){
_start:
{
lean_object* v___f_1613_; lean_object* v_searcher_1614_; lean_object* v___x_1615_; lean_object* v___f_1616_; lean_object* v___x_1617_; 
v___f_1613_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1610_);
v_searcher_1614_ = lean_apply_1(v_inst_1612_, v_s_1610_);
v___x_1615_ = lean_box(0);
v___f_1616_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1617_ = lean_apply_7(v_inst_1609_, v_s_1610_, v___f_1613_, lean_box(0), lean_box(0), v_searcher_1614_, v___x_1615_, v___f_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___boxed(lean_object* v_00_u03c1_1618_, lean_object* v_00_u03c3_1619_, lean_object* v_inst_1620_, lean_object* v_inst_1621_, lean_object* v_s_1622_, lean_object* v_pat_1623_, lean_object* v_inst_1624_){
_start:
{
lean_object* v_res_1625_; 
v_res_1625_ = l_String_Slice_find_x3f(v_00_u03c1_1618_, v_00_u03c3_1619_, v_inst_1620_, v_inst_1621_, v_s_1622_, v_pat_1623_, v_inst_1624_);
lean_dec(v_pat_1623_);
lean_dec(v_inst_1620_);
return v_res_1625_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___redArg(lean_object* v_inst_1626_, lean_object* v_s_1627_, lean_object* v_inst_1628_){
_start:
{
lean_object* v___f_1629_; lean_object* v_searcher_1630_; lean_object* v___x_1631_; lean_object* v___f_1632_; lean_object* v___x_1633_; 
v___f_1629_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1627_);
v_searcher_1630_ = lean_apply_1(v_inst_1628_, v_s_1627_);
v___x_1631_ = lean_box(0);
v___f_1632_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
lean_inc_ref(v_s_1627_);
v___x_1633_ = lean_apply_7(v_inst_1626_, v_s_1627_, v___f_1629_, lean_box(0), lean_box(0), v_searcher_1630_, v___x_1631_, v___f_1632_);
if (lean_obj_tag(v___x_1633_) == 0)
{
lean_object* v_startInclusive_1634_; lean_object* v_endExclusive_1635_; lean_object* v___x_1636_; 
v_startInclusive_1634_ = lean_ctor_get(v_s_1627_, 1);
lean_inc(v_startInclusive_1634_);
v_endExclusive_1635_ = lean_ctor_get(v_s_1627_, 2);
lean_inc(v_endExclusive_1635_);
lean_dec_ref(v_s_1627_);
v___x_1636_ = lean_nat_sub(v_endExclusive_1635_, v_startInclusive_1634_);
lean_dec(v_startInclusive_1634_);
lean_dec(v_endExclusive_1635_);
return v___x_1636_;
}
else
{
lean_object* v_val_1637_; 
lean_dec_ref(v_s_1627_);
v_val_1637_ = lean_ctor_get(v___x_1633_, 0);
lean_inc(v_val_1637_);
lean_dec_ref(v___x_1633_);
return v_val_1637_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find(lean_object* v_00_u03c1_1638_, lean_object* v_00_u03c3_1639_, lean_object* v_inst_1640_, lean_object* v_inst_1641_, lean_object* v_s_1642_, lean_object* v_pat_1643_, lean_object* v_inst_1644_){
_start:
{
lean_object* v___f_1645_; lean_object* v_searcher_1646_; lean_object* v___x_1647_; lean_object* v___f_1648_; lean_object* v___x_1649_; 
v___f_1645_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1642_);
v_searcher_1646_ = lean_apply_1(v_inst_1644_, v_s_1642_);
v___x_1647_ = lean_box(0);
v___f_1648_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
lean_inc_ref(v_s_1642_);
v___x_1649_ = lean_apply_7(v_inst_1641_, v_s_1642_, v___f_1645_, lean_box(0), lean_box(0), v_searcher_1646_, v___x_1647_, v___f_1648_);
if (lean_obj_tag(v___x_1649_) == 0)
{
lean_object* v_startInclusive_1650_; lean_object* v_endExclusive_1651_; lean_object* v___x_1652_; 
v_startInclusive_1650_ = lean_ctor_get(v_s_1642_, 1);
lean_inc(v_startInclusive_1650_);
v_endExclusive_1651_ = lean_ctor_get(v_s_1642_, 2);
lean_inc(v_endExclusive_1651_);
lean_dec_ref(v_s_1642_);
v___x_1652_ = lean_nat_sub(v_endExclusive_1651_, v_startInclusive_1650_);
lean_dec(v_startInclusive_1650_);
lean_dec(v_endExclusive_1651_);
return v___x_1652_;
}
else
{
lean_object* v_val_1653_; 
lean_dec_ref(v_s_1642_);
v_val_1653_ = lean_ctor_get(v___x_1649_, 0);
lean_inc(v_val_1653_);
lean_dec_ref(v___x_1649_);
return v_val_1653_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___boxed(lean_object* v_00_u03c1_1654_, lean_object* v_00_u03c3_1655_, lean_object* v_inst_1656_, lean_object* v_inst_1657_, lean_object* v_s_1658_, lean_object* v_pat_1659_, lean_object* v_inst_1660_){
_start:
{
lean_object* v_res_1661_; 
v_res_1661_ = l_String_Slice_find(v_00_u03c1_1654_, v_00_u03c3_1655_, v_inst_1656_, v_inst_1657_, v_s_1658_, v_pat_1659_, v_inst_1660_);
lean_dec(v_pat_1659_);
lean_dec(v_inst_1656_);
return v_res_1661_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1(uint8_t v___x_1665_, lean_object* v_x1_1666_, lean_object* v_x2_1667_, uint8_t v_x3_1668_){
_start:
{
if (lean_obj_tag(v_x1_1666_) == 1)
{
lean_object* v___x_1669_; 
v___x_1669_ = ((lean_object*)(l_String_Slice_contains___redArg___lam__1___closed__0));
return v___x_1669_;
}
else
{
lean_object* v___x_1670_; lean_object* v___x_1671_; 
v___x_1670_ = lean_box(v___x_1665_);
v___x_1671_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1671_, 0, v___x_1670_);
return v___x_1671_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1___boxed(lean_object* v___x_1672_, lean_object* v_x1_1673_, lean_object* v_x2_1674_, lean_object* v_x3_1675_){
_start:
{
uint8_t v___x_86__boxed_1676_; uint8_t v_x3_89__boxed_1677_; lean_object* v_res_1678_; 
v___x_86__boxed_1676_ = lean_unbox(v___x_1672_);
v_x3_89__boxed_1677_ = lean_unbox(v_x3_1675_);
v_res_1678_ = l_String_Slice_contains___redArg___lam__1(v___x_86__boxed_1676_, v_x1_1673_, v_x2_1674_, v_x3_89__boxed_1677_);
lean_dec_ref(v_x1_1673_);
return v_res_1678_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___redArg(lean_object* v_inst_1682_, lean_object* v_s_1683_, lean_object* v_inst_1684_){
_start:
{
lean_object* v___f_1685_; lean_object* v_searcher_1686_; uint8_t v___x_1687_; lean_object* v___f_1688_; lean_object* v___x_1689_; lean_object* v___x_1690_; uint8_t v___x_1691_; 
v___f_1685_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1683_);
v_searcher_1686_ = lean_apply_1(v_inst_1684_, v_s_1683_);
v___x_1687_ = 0;
v___f_1688_ = ((lean_object*)(l_String_Slice_contains___redArg___closed__0));
v___x_1689_ = lean_box(v___x_1687_);
v___x_1690_ = lean_apply_7(v_inst_1682_, v_s_1683_, v___f_1685_, lean_box(0), lean_box(0), v_searcher_1686_, v___x_1689_, v___f_1688_);
v___x_1691_ = lean_unbox(v___x_1690_);
return v___x_1691_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___boxed(lean_object* v_inst_1692_, lean_object* v_s_1693_, lean_object* v_inst_1694_){
_start:
{
uint8_t v_res_1695_; lean_object* v_r_1696_; 
v_res_1695_ = l_String_Slice_contains___redArg(v_inst_1692_, v_s_1693_, v_inst_1694_);
v_r_1696_ = lean_box(v_res_1695_);
return v_r_1696_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains(lean_object* v_00_u03c1_1697_, lean_object* v_00_u03c3_1698_, lean_object* v_inst_1699_, lean_object* v_inst_1700_, lean_object* v_s_1701_, lean_object* v_pat_1702_, lean_object* v_inst_1703_){
_start:
{
uint8_t v___x_1704_; 
v___x_1704_ = l_String_Slice_contains___redArg(v_inst_1700_, v_s_1701_, v_inst_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___boxed(lean_object* v_00_u03c1_1705_, lean_object* v_00_u03c3_1706_, lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_s_1709_, lean_object* v_pat_1710_, lean_object* v_inst_1711_){
_start:
{
uint8_t v_res_1712_; lean_object* v_r_1713_; 
v_res_1712_ = l_String_Slice_contains(v_00_u03c1_1705_, v_00_u03c3_1706_, v_inst_1707_, v_inst_1708_, v_s_1709_, v_pat_1710_, v_inst_1711_);
lean_dec(v_pat_1710_);
lean_dec(v_inst_1707_);
v_r_1713_ = lean_box(v_res_1712_);
return v_r_1713_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any___redArg(lean_object* v_inst_1714_, lean_object* v_s_1715_, lean_object* v_inst_1716_){
_start:
{
uint8_t v___x_1717_; 
v___x_1717_ = l_String_Slice_contains___redArg(v_inst_1714_, v_s_1715_, v_inst_1716_);
return v___x_1717_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___redArg___boxed(lean_object* v_inst_1718_, lean_object* v_s_1719_, lean_object* v_inst_1720_){
_start:
{
uint8_t v_res_1721_; lean_object* v_r_1722_; 
v_res_1721_ = l_String_Slice_any___redArg(v_inst_1718_, v_s_1719_, v_inst_1720_);
v_r_1722_ = lean_box(v_res_1721_);
return v_r_1722_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any(lean_object* v_00_u03c1_1723_, lean_object* v_00_u03c3_1724_, lean_object* v_inst_1725_, lean_object* v_inst_1726_, lean_object* v_s_1727_, lean_object* v_pat_1728_, lean_object* v_inst_1729_){
_start:
{
uint8_t v___x_1730_; 
v___x_1730_ = l_String_Slice_contains___redArg(v_inst_1726_, v_s_1727_, v_inst_1729_);
return v___x_1730_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___boxed(lean_object* v_00_u03c1_1731_, lean_object* v_00_u03c3_1732_, lean_object* v_inst_1733_, lean_object* v_inst_1734_, lean_object* v_s_1735_, lean_object* v_pat_1736_, lean_object* v_inst_1737_){
_start:
{
uint8_t v_res_1738_; lean_object* v_r_1739_; 
v_res_1738_ = l_String_Slice_any(v_00_u03c1_1731_, v_00_u03c3_1732_, v_inst_1733_, v_inst_1734_, v_s_1735_, v_pat_1736_, v_inst_1737_);
lean_dec(v_pat_1736_);
lean_dec(v_inst_1733_);
v_r_1739_ = lean_box(v_res_1738_);
return v_r_1739_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all___redArg(lean_object* v_s_1740_, lean_object* v_inst_1741_){
_start:
{
lean_object* v_startInclusive_1742_; lean_object* v_endExclusive_1743_; lean_object* v___x_1744_; lean_object* v___x_1745_; lean_object* v___x_1746_; lean_object* v___x_1747_; uint8_t v___x_1748_; 
v_startInclusive_1742_ = lean_ctor_get(v_s_1740_, 1);
v_endExclusive_1743_ = lean_ctor_get(v_s_1740_, 2);
v___x_1744_ = lean_unsigned_to_nat(0u);
v___x_1745_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1740_, v___x_1744_, v_inst_1741_);
v___x_1746_ = lean_nat_add(v_startInclusive_1742_, v___x_1745_);
lean_dec(v___x_1745_);
v___x_1747_ = lean_nat_sub(v_endExclusive_1743_, v___x_1746_);
lean_dec(v___x_1746_);
v___x_1748_ = lean_nat_dec_eq(v___x_1747_, v___x_1744_);
lean_dec(v___x_1747_);
return v___x_1748_;
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
lean_object* v_startInclusive_1757_; lean_object* v_endExclusive_1758_; lean_object* v___x_1759_; lean_object* v___x_1760_; lean_object* v___x_1761_; lean_object* v___x_1762_; uint8_t v___x_1763_; 
v_startInclusive_1757_ = lean_ctor_get(v_s_1754_, 1);
v_endExclusive_1758_ = lean_ctor_get(v_s_1754_, 2);
v___x_1759_ = lean_unsigned_to_nat(0u);
v___x_1760_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1754_, v___x_1759_, v_inst_1756_);
v___x_1761_ = lean_nat_add(v_startInclusive_1757_, v___x_1760_);
lean_dec(v___x_1760_);
v___x_1762_ = lean_nat_sub(v_endExclusive_1758_, v___x_1761_);
lean_dec(v___x_1761_);
v___x_1763_ = lean_nat_dec_eq(v___x_1762_, v___x_1759_);
lean_dec(v___x_1762_);
return v___x_1763_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___boxed(lean_object* v_00_u03c1_1764_, lean_object* v_s_1765_, lean_object* v_pat_1766_, lean_object* v_inst_1767_){
_start:
{
uint8_t v_res_1768_; lean_object* v_r_1769_; 
v_res_1768_ = l_String_Slice_all(v_00_u03c1_1764_, v_s_1765_, v_pat_1766_, v_inst_1767_);
lean_dec(v_pat_1766_);
lean_dec_ref(v_s_1765_);
v_r_1769_ = lean_box(v_res_1768_);
return v_r_1769_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith___redArg(lean_object* v_s_1770_, lean_object* v_inst_1771_){
_start:
{
lean_object* v_endsWith_1772_; lean_object* v___x_1773_; uint8_t v___x_1774_; 
v_endsWith_1772_ = lean_ctor_get(v_inst_1771_, 2);
lean_inc_ref(v_endsWith_1772_);
lean_dec_ref(v_inst_1771_);
v___x_1773_ = lean_apply_1(v_endsWith_1772_, v_s_1770_);
v___x_1774_ = lean_unbox(v___x_1773_);
return v___x_1774_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___redArg___boxed(lean_object* v_s_1775_, lean_object* v_inst_1776_){
_start:
{
uint8_t v_res_1777_; lean_object* v_r_1778_; 
v_res_1777_ = l_String_Slice_endsWith___redArg(v_s_1775_, v_inst_1776_);
v_r_1778_ = lean_box(v_res_1777_);
return v_r_1778_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith(lean_object* v_00_u03c1_1779_, lean_object* v_s_1780_, lean_object* v_pat_1781_, lean_object* v_inst_1782_){
_start:
{
lean_object* v_endsWith_1783_; lean_object* v___x_1784_; uint8_t v___x_1785_; 
v_endsWith_1783_ = lean_ctor_get(v_inst_1782_, 2);
lean_inc_ref(v_endsWith_1783_);
lean_dec_ref(v_inst_1782_);
v___x_1784_ = lean_apply_1(v_endsWith_1783_, v_s_1780_);
v___x_1785_ = lean_unbox(v___x_1784_);
return v___x_1785_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___boxed(lean_object* v_00_u03c1_1786_, lean_object* v_s_1787_, lean_object* v_pat_1788_, lean_object* v_inst_1789_){
_start:
{
uint8_t v_res_1790_; lean_object* v_r_1791_; 
v_res_1790_ = l_String_Slice_endsWith(v_00_u03c1_1786_, v_s_1787_, v_pat_1788_, v_inst_1789_);
lean_dec(v_pat_1788_);
v_r_1791_ = lean_box(v_res_1790_);
return v_r_1791_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___redArg(lean_object* v_x_1792_){
_start:
{
if (lean_obj_tag(v_x_1792_) == 0)
{
lean_object* v___x_1793_; 
v___x_1793_ = lean_unsigned_to_nat(0u);
return v___x_1793_;
}
else
{
lean_object* v___x_1794_; 
v___x_1794_ = lean_unsigned_to_nat(1u);
return v___x_1794_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___redArg___boxed(lean_object* v_x_1795_){
_start:
{
lean_object* v_res_1796_; 
v_res_1796_ = l_String_Slice_RevSplitIterator_ctorIdx___redArg(v_x_1795_);
lean_dec(v_x_1795_);
return v_res_1796_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx(lean_object* v_00_u03c3_1797_, lean_object* v_00_u03c1_1798_, lean_object* v_pat_1799_, lean_object* v_s_1800_, lean_object* v_inst_1801_, lean_object* v_x_1802_){
_start:
{
lean_object* v___x_1803_; 
v___x_1803_ = l_String_Slice_RevSplitIterator_ctorIdx___redArg(v_x_1802_);
return v___x_1803_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___boxed(lean_object* v_00_u03c3_1804_, lean_object* v_00_u03c1_1805_, lean_object* v_pat_1806_, lean_object* v_s_1807_, lean_object* v_inst_1808_, lean_object* v_x_1809_){
_start:
{
lean_object* v_res_1810_; 
v_res_1810_ = l_String_Slice_RevSplitIterator_ctorIdx(v_00_u03c3_1804_, v_00_u03c1_1805_, v_pat_1806_, v_s_1807_, v_inst_1808_, v_x_1809_);
lean_dec(v_x_1809_);
lean_dec(v_inst_1808_);
lean_dec_ref(v_s_1807_);
lean_dec(v_pat_1806_);
return v_res_1810_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___redArg(lean_object* v_t_1811_, lean_object* v_k_1812_){
_start:
{
if (lean_obj_tag(v_t_1811_) == 0)
{
lean_object* v_currPos_1813_; lean_object* v_searcher_1814_; lean_object* v___x_1815_; 
v_currPos_1813_ = lean_ctor_get(v_t_1811_, 0);
lean_inc(v_currPos_1813_);
v_searcher_1814_ = lean_ctor_get(v_t_1811_, 1);
lean_inc(v_searcher_1814_);
lean_dec_ref(v_t_1811_);
v___x_1815_ = lean_apply_2(v_k_1812_, v_currPos_1813_, v_searcher_1814_);
return v___x_1815_;
}
else
{
return v_k_1812_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim(lean_object* v_00_u03c3_1816_, lean_object* v_00_u03c1_1817_, lean_object* v_pat_1818_, lean_object* v_s_1819_, lean_object* v_inst_1820_, lean_object* v_motive_1821_, lean_object* v_ctorIdx_1822_, lean_object* v_t_1823_, lean_object* v_h_1824_, lean_object* v_k_1825_){
_start:
{
lean_object* v___x_1826_; 
v___x_1826_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1823_, v_k_1825_);
return v___x_1826_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_1827_, lean_object* v_00_u03c1_1828_, lean_object* v_pat_1829_, lean_object* v_s_1830_, lean_object* v_inst_1831_, lean_object* v_motive_1832_, lean_object* v_ctorIdx_1833_, lean_object* v_t_1834_, lean_object* v_h_1835_, lean_object* v_k_1836_){
_start:
{
lean_object* v_res_1837_; 
v_res_1837_ = l_String_Slice_RevSplitIterator_ctorElim(v_00_u03c3_1827_, v_00_u03c1_1828_, v_pat_1829_, v_s_1830_, v_inst_1831_, v_motive_1832_, v_ctorIdx_1833_, v_t_1834_, v_h_1835_, v_k_1836_);
lean_dec(v_ctorIdx_1833_);
lean_dec(v_inst_1831_);
lean_dec_ref(v_s_1830_);
lean_dec(v_pat_1829_);
return v_res_1837_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___redArg(lean_object* v_t_1838_, lean_object* v_operating_1839_){
_start:
{
lean_object* v___x_1840_; 
v___x_1840_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1838_, v_operating_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim(lean_object* v_00_u03c3_1841_, lean_object* v_00_u03c1_1842_, lean_object* v_pat_1843_, lean_object* v_s_1844_, lean_object* v_inst_1845_, lean_object* v_motive_1846_, lean_object* v_t_1847_, lean_object* v_h_1848_, lean_object* v_operating_1849_){
_start:
{
lean_object* v___x_1850_; 
v___x_1850_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1847_, v_operating_1849_);
return v___x_1850_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_1851_, lean_object* v_00_u03c1_1852_, lean_object* v_pat_1853_, lean_object* v_s_1854_, lean_object* v_inst_1855_, lean_object* v_motive_1856_, lean_object* v_t_1857_, lean_object* v_h_1858_, lean_object* v_operating_1859_){
_start:
{
lean_object* v_res_1860_; 
v_res_1860_ = l_String_Slice_RevSplitIterator_operating_elim(v_00_u03c3_1851_, v_00_u03c1_1852_, v_pat_1853_, v_s_1854_, v_inst_1855_, v_motive_1856_, v_t_1857_, v_h_1858_, v_operating_1859_);
lean_dec(v_inst_1855_);
lean_dec_ref(v_s_1854_);
lean_dec(v_pat_1853_);
return v_res_1860_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___redArg(lean_object* v_t_1861_, lean_object* v_atEnd_1862_){
_start:
{
lean_object* v___x_1863_; 
v___x_1863_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1861_, v_atEnd_1862_);
return v___x_1863_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim(lean_object* v_00_u03c3_1864_, lean_object* v_00_u03c1_1865_, lean_object* v_pat_1866_, lean_object* v_s_1867_, lean_object* v_inst_1868_, lean_object* v_motive_1869_, lean_object* v_t_1870_, lean_object* v_h_1871_, lean_object* v_atEnd_1872_){
_start:
{
lean_object* v___x_1873_; 
v___x_1873_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1870_, v_atEnd_1872_);
return v___x_1873_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_1874_, lean_object* v_00_u03c1_1875_, lean_object* v_pat_1876_, lean_object* v_s_1877_, lean_object* v_inst_1878_, lean_object* v_motive_1879_, lean_object* v_t_1880_, lean_object* v_h_1881_, lean_object* v_atEnd_1882_){
_start:
{
lean_object* v_res_1883_; 
v_res_1883_ = l_String_Slice_RevSplitIterator_atEnd_elim(v_00_u03c3_1874_, v_00_u03c1_1875_, v_pat_1876_, v_s_1877_, v_inst_1878_, v_motive_1879_, v_t_1880_, v_h_1881_, v_atEnd_1882_);
lean_dec(v_inst_1878_);
lean_dec_ref(v_s_1877_);
lean_dec(v_pat_1876_);
return v_res_1883_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default(lean_object* v_a_1884_, lean_object* v_a_1885_, lean_object* v_a_1886_, lean_object* v_a_1887_, lean_object* v_a_1888_){
_start:
{
lean_object* v___x_1889_; 
v___x_1889_ = lean_box(1);
return v___x_1889_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___boxed(lean_object* v_a_1890_, lean_object* v_a_1891_, lean_object* v_a_1892_, lean_object* v_a_1893_, lean_object* v_a_1894_){
_start:
{
lean_object* v_res_1895_; 
v_res_1895_ = l_String_Slice_instInhabitedRevSplitIterator_default(v_a_1890_, v_a_1891_, v_a_1892_, v_a_1893_, v_a_1894_);
lean_dec(v_a_1894_);
lean_dec_ref(v_a_1893_);
lean_dec(v_a_1892_);
return v_res_1895_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator(lean_object* v_a_1896_, lean_object* v_a_1897_, lean_object* v_a_1898_, lean_object* v_a_1899_, lean_object* v_a_1900_){
_start:
{
lean_object* v___x_1901_; 
v___x_1901_ = lean_box(1);
return v___x_1901_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___boxed(lean_object* v_a_1902_, lean_object* v_a_1903_, lean_object* v_a_1904_, lean_object* v_a_1905_, lean_object* v_a_1906_){
_start:
{
lean_object* v_res_1907_; 
v_res_1907_ = l_String_Slice_instInhabitedRevSplitIterator(v_a_1902_, v_a_1903_, v_a_1904_, v_a_1905_, v_a_1906_);
lean_dec(v_a_1906_);
lean_dec_ref(v_a_1905_);
lean_dec(v_a_1904_);
return v_res_1907_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0(lean_object* v_inst_1908_, lean_object* v_s_1909_, lean_object* v_inst_1910_, lean_object* v_x_1911_){
_start:
{
if (lean_obj_tag(v_x_1911_) == 0)
{
lean_object* v_currPos_1912_; lean_object* v_searcher_1913_; lean_object* v___x_1915_; uint8_t v_isShared_1916_; uint8_t v_isSharedCheck_1971_; 
v_currPos_1912_ = lean_ctor_get(v_x_1911_, 0);
v_searcher_1913_ = lean_ctor_get(v_x_1911_, 1);
v_isSharedCheck_1971_ = !lean_is_exclusive(v_x_1911_);
if (v_isSharedCheck_1971_ == 0)
{
v___x_1915_ = v_x_1911_;
v_isShared_1916_ = v_isSharedCheck_1971_;
goto v_resetjp_1914_;
}
else
{
lean_inc(v_searcher_1913_);
lean_inc(v_currPos_1912_);
lean_dec(v_x_1911_);
v___x_1915_ = lean_box(0);
v_isShared_1916_ = v_isSharedCheck_1971_;
goto v_resetjp_1914_;
}
v_resetjp_1914_:
{
lean_object* v___x_1917_; 
lean_inc_ref(v_s_1909_);
v___x_1917_ = lean_apply_2(v_inst_1908_, v_s_1909_, v_searcher_1913_);
switch(lean_obj_tag(v___x_1917_))
{
case 0:
{
lean_object* v_out_1918_; 
v_out_1918_ = lean_ctor_get(v___x_1917_, 1);
lean_inc(v_out_1918_);
if (lean_obj_tag(v_out_1918_) == 0)
{
lean_object* v_it_1919_; lean_object* v___x_1921_; 
lean_dec_ref(v_out_1918_);
lean_dec_ref(v_s_1909_);
v_it_1919_ = lean_ctor_get(v___x_1917_, 0);
lean_inc(v_it_1919_);
lean_dec_ref(v___x_1917_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v_it_1919_);
v___x_1921_ = v___x_1915_;
goto v_reusejp_1920_;
}
else
{
lean_object* v_reuseFailAlloc_1924_; 
v_reuseFailAlloc_1924_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1924_, 0, v_currPos_1912_);
lean_ctor_set(v_reuseFailAlloc_1924_, 1, v_it_1919_);
v___x_1921_ = v_reuseFailAlloc_1924_;
goto v_reusejp_1920_;
}
v_reusejp_1920_:
{
lean_object* v___x_1922_; lean_object* v___x_1923_; 
v___x_1922_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1922_, 0, v___x_1921_);
v___x_1923_ = lean_apply_2(v_inst_1910_, lean_box(0), v___x_1922_);
return v___x_1923_;
}
}
else
{
lean_object* v_it_1925_; lean_object* v___x_1927_; uint8_t v_isShared_1928_; uint8_t v_isSharedCheck_1939_; 
v_it_1925_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1939_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1939_ == 0)
{
lean_object* v_unused_1940_; 
v_unused_1940_ = lean_ctor_get(v___x_1917_, 1);
lean_dec(v_unused_1940_);
v___x_1927_ = v___x_1917_;
v_isShared_1928_ = v_isSharedCheck_1939_;
goto v_resetjp_1926_;
}
else
{
lean_inc(v_it_1925_);
lean_dec(v___x_1917_);
v___x_1927_ = lean_box(0);
v_isShared_1928_ = v_isSharedCheck_1939_;
goto v_resetjp_1926_;
}
v_resetjp_1926_:
{
lean_object* v_startPos_1929_; lean_object* v_endPos_1930_; lean_object* v_slice_1931_; lean_object* v_nextIt_1933_; 
v_startPos_1929_ = lean_ctor_get(v_out_1918_, 0);
lean_inc(v_startPos_1929_);
v_endPos_1930_ = lean_ctor_get(v_out_1918_, 1);
lean_inc(v_endPos_1930_);
lean_dec_ref(v_out_1918_);
v_slice_1931_ = l_String_Slice_slice_x21(v_s_1909_, v_endPos_1930_, v_currPos_1912_);
lean_dec(v_currPos_1912_);
lean_dec(v_endPos_1930_);
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v_it_1925_);
lean_ctor_set(v___x_1915_, 0, v_startPos_1929_);
v_nextIt_1933_ = v___x_1915_;
goto v_reusejp_1932_;
}
else
{
lean_object* v_reuseFailAlloc_1938_; 
v_reuseFailAlloc_1938_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1938_, 0, v_startPos_1929_);
lean_ctor_set(v_reuseFailAlloc_1938_, 1, v_it_1925_);
v_nextIt_1933_ = v_reuseFailAlloc_1938_;
goto v_reusejp_1932_;
}
v_reusejp_1932_:
{
lean_object* v___x_1935_; 
if (v_isShared_1928_ == 0)
{
lean_ctor_set(v___x_1927_, 1, v_slice_1931_);
lean_ctor_set(v___x_1927_, 0, v_nextIt_1933_);
v___x_1935_ = v___x_1927_;
goto v_reusejp_1934_;
}
else
{
lean_object* v_reuseFailAlloc_1937_; 
v_reuseFailAlloc_1937_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1937_, 0, v_nextIt_1933_);
lean_ctor_set(v_reuseFailAlloc_1937_, 1, v_slice_1931_);
v___x_1935_ = v_reuseFailAlloc_1937_;
goto v_reusejp_1934_;
}
v_reusejp_1934_:
{
lean_object* v___x_1936_; 
v___x_1936_ = lean_apply_2(v_inst_1910_, lean_box(0), v___x_1935_);
return v___x_1936_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1941_; lean_object* v___x_1943_; uint8_t v_isShared_1944_; uint8_t v_isSharedCheck_1952_; 
lean_dec_ref(v_s_1909_);
v_it_1941_ = lean_ctor_get(v___x_1917_, 0);
v_isSharedCheck_1952_ = !lean_is_exclusive(v___x_1917_);
if (v_isSharedCheck_1952_ == 0)
{
v___x_1943_ = v___x_1917_;
v_isShared_1944_ = v_isSharedCheck_1952_;
goto v_resetjp_1942_;
}
else
{
lean_inc(v_it_1941_);
lean_dec(v___x_1917_);
v___x_1943_ = lean_box(0);
v_isShared_1944_ = v_isSharedCheck_1952_;
goto v_resetjp_1942_;
}
v_resetjp_1942_:
{
lean_object* v___x_1946_; 
if (v_isShared_1916_ == 0)
{
lean_ctor_set(v___x_1915_, 1, v_it_1941_);
v___x_1946_ = v___x_1915_;
goto v_reusejp_1945_;
}
else
{
lean_object* v_reuseFailAlloc_1951_; 
v_reuseFailAlloc_1951_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1951_, 0, v_currPos_1912_);
lean_ctor_set(v_reuseFailAlloc_1951_, 1, v_it_1941_);
v___x_1946_ = v_reuseFailAlloc_1951_;
goto v_reusejp_1945_;
}
v_reusejp_1945_:
{
lean_object* v___x_1948_; 
if (v_isShared_1944_ == 0)
{
lean_ctor_set(v___x_1943_, 0, v___x_1946_);
v___x_1948_ = v___x_1943_;
goto v_reusejp_1947_;
}
else
{
lean_object* v_reuseFailAlloc_1950_; 
v_reuseFailAlloc_1950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1950_, 0, v___x_1946_);
v___x_1948_ = v_reuseFailAlloc_1950_;
goto v_reusejp_1947_;
}
v_reusejp_1947_:
{
lean_object* v___x_1949_; 
v___x_1949_ = lean_apply_2(v_inst_1910_, lean_box(0), v___x_1948_);
return v___x_1949_;
}
}
}
}
default: 
{
lean_object* v___x_1953_; uint8_t v___x_1954_; 
lean_del_object(v___x_1915_);
v___x_1953_ = lean_unsigned_to_nat(0u);
v___x_1954_ = lean_nat_dec_eq(v_currPos_1912_, v___x_1953_);
if (v___x_1954_ == 0)
{
lean_object* v_str_1955_; lean_object* v_startInclusive_1956_; lean_object* v___x_1958_; uint8_t v_isShared_1959_; uint8_t v_isSharedCheck_1967_; 
v_str_1955_ = lean_ctor_get(v_s_1909_, 0);
v_startInclusive_1956_ = lean_ctor_get(v_s_1909_, 1);
v_isSharedCheck_1967_ = !lean_is_exclusive(v_s_1909_);
if (v_isSharedCheck_1967_ == 0)
{
lean_object* v_unused_1968_; 
v_unused_1968_ = lean_ctor_get(v_s_1909_, 2);
lean_dec(v_unused_1968_);
v___x_1958_ = v_s_1909_;
v_isShared_1959_ = v_isSharedCheck_1967_;
goto v_resetjp_1957_;
}
else
{
lean_inc(v_startInclusive_1956_);
lean_inc(v_str_1955_);
lean_dec(v_s_1909_);
v___x_1958_ = lean_box(0);
v_isShared_1959_ = v_isSharedCheck_1967_;
goto v_resetjp_1957_;
}
v_resetjp_1957_:
{
lean_object* v___x_1960_; lean_object* v_slice_1962_; 
v___x_1960_ = lean_nat_add(v_startInclusive_1956_, v_currPos_1912_);
lean_dec(v_currPos_1912_);
if (v_isShared_1959_ == 0)
{
lean_ctor_set(v___x_1958_, 2, v___x_1960_);
v_slice_1962_ = v___x_1958_;
goto v_reusejp_1961_;
}
else
{
lean_object* v_reuseFailAlloc_1966_; 
v_reuseFailAlloc_1966_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1966_, 0, v_str_1955_);
lean_ctor_set(v_reuseFailAlloc_1966_, 1, v_startInclusive_1956_);
lean_ctor_set(v_reuseFailAlloc_1966_, 2, v___x_1960_);
v_slice_1962_ = v_reuseFailAlloc_1966_;
goto v_reusejp_1961_;
}
v_reusejp_1961_:
{
lean_object* v___x_1963_; lean_object* v___x_1964_; lean_object* v___x_1965_; 
v___x_1963_ = lean_box(1);
v___x_1964_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1964_, 0, v___x_1963_);
lean_ctor_set(v___x_1964_, 1, v_slice_1962_);
v___x_1965_ = lean_apply_2(v_inst_1910_, lean_box(0), v___x_1964_);
return v___x_1965_;
}
}
}
else
{
lean_object* v___x_1969_; lean_object* v___x_1970_; 
lean_dec(v_currPos_1912_);
lean_dec_ref(v_s_1909_);
v___x_1969_ = lean_box(2);
v___x_1970_ = lean_apply_2(v_inst_1910_, lean_box(0), v___x_1969_);
return v___x_1970_;
}
}
}
}
}
else
{
lean_object* v___x_1972_; lean_object* v___x_1973_; 
lean_dec_ref(v_s_1909_);
lean_dec(v_inst_1908_);
v___x_1972_ = lean_box(2);
v___x_1973_ = lean_apply_2(v_inst_1910_, lean_box(0), v___x_1972_);
return v___x_1973_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg(lean_object* v_inst_1974_, lean_object* v_s_1975_, lean_object* v_inst_1976_){
_start:
{
lean_object* v___f_1977_; 
v___f_1977_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1977_, 0, v_inst_1974_);
lean_closure_set(v___f_1977_, 1, v_s_1975_);
lean_closure_set(v___f_1977_, 2, v_inst_1976_);
return v___f_1977_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure(lean_object* v_00_u03c1_1978_, lean_object* v_00_u03c1_1979_, lean_object* v_00_u03c3_1980_, lean_object* v_inst_1981_, lean_object* v_inst_1982_, lean_object* v_m_1983_, lean_object* v_s_1984_, lean_object* v_inst_1985_){
_start:
{
lean_object* v___f_1986_; 
v___f_1986_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1986_, 0, v_inst_1981_);
lean_closure_set(v___f_1986_, 1, v_s_1984_);
lean_closure_set(v___f_1986_, 2, v_inst_1985_);
return v___f_1986_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___boxed(lean_object* v_00_u03c1_1987_, lean_object* v_00_u03c1_1988_, lean_object* v_00_u03c3_1989_, lean_object* v_inst_1990_, lean_object* v_inst_1991_, lean_object* v_m_1992_, lean_object* v_s_1993_, lean_object* v_inst_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_String_Slice_RevSplitIterator_instIteratorOfPure(v_00_u03c1_1987_, v_00_u03c1_1988_, v_00_u03c3_1989_, v_inst_1990_, v_inst_1991_, v_m_1992_, v_s_1993_, v_inst_1994_);
lean_dec(v_inst_1991_);
lean_dec(v_00_u03c1_1988_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(lean_object* v_x_1996_){
_start:
{
if (lean_obj_tag(v_x_1996_) == 0)
{
lean_object* v_searcher_1997_; lean_object* v___x_1998_; 
v_searcher_1997_ = lean_ctor_get(v_x_1996_, 1);
lean_inc(v_searcher_1997_);
v___x_1998_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1998_, 0, v_searcher_1997_);
return v___x_1998_;
}
else
{
lean_object* v___x_1999_; 
v___x_1999_ = lean_box(0);
return v___x_1999_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg___boxed(lean_object* v_x_2000_){
_start:
{
lean_object* v_res_2001_; 
v_res_2001_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2000_);
lean_dec(v_x_2000_);
return v_res_2001_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(lean_object* v_00_u03c1_2002_, lean_object* v_00_u03c1_2003_, lean_object* v_00_u03c3_2004_, lean_object* v_inst_2005_, lean_object* v_s_2006_, lean_object* v_x_2007_){
_start:
{
lean_object* v___x_2008_; 
v___x_2008_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2007_);
return v___x_2008_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___boxed(lean_object* v_00_u03c1_2009_, lean_object* v_00_u03c1_2010_, lean_object* v_00_u03c3_2011_, lean_object* v_inst_2012_, lean_object* v_s_2013_, lean_object* v_x_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(v_00_u03c1_2009_, v_00_u03c1_2010_, v_00_u03c3_2011_, v_inst_2012_, v_s_2013_, v_x_2014_);
lean_dec(v_x_2014_);
lean_dec_ref(v_s_2013_);
lean_dec(v_inst_2012_);
lean_dec(v_00_u03c1_2010_);
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(lean_object* v_x_2016_, lean_object* v_h__1_2017_, lean_object* v_h__2_2018_){
_start:
{
if (lean_obj_tag(v_x_2016_) == 0)
{
lean_object* v_currPos_2019_; lean_object* v_searcher_2020_; lean_object* v___x_2021_; 
lean_dec(v_h__2_2018_);
v_currPos_2019_ = lean_ctor_get(v_x_2016_, 0);
lean_inc(v_currPos_2019_);
v_searcher_2020_ = lean_ctor_get(v_x_2016_, 1);
lean_inc(v_searcher_2020_);
lean_dec_ref(v_x_2016_);
v___x_2021_ = lean_apply_2(v_h__1_2017_, v_currPos_2019_, v_searcher_2020_);
return v___x_2021_;
}
else
{
lean_object* v___x_2022_; lean_object* v___x_2023_; 
lean_dec(v_h__1_2017_);
v___x_2022_ = lean_box(0);
v___x_2023_ = lean_apply_1(v_h__2_2018_, v___x_2022_);
return v___x_2023_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(lean_object* v_00_u03c1_2024_, lean_object* v_00_u03c1_2025_, lean_object* v_00_u03c3_2026_, lean_object* v_inst_2027_, lean_object* v_m_2028_, lean_object* v_s_2029_, lean_object* v_motive_2030_, lean_object* v_x_2031_, lean_object* v_h__1_2032_, lean_object* v_h__2_2033_){
_start:
{
lean_object* v___x_2034_; 
v___x_2034_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(v_x_2031_, v_h__1_2032_, v_h__2_2033_);
return v___x_2034_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___boxed(lean_object* v_00_u03c1_2035_, lean_object* v_00_u03c1_2036_, lean_object* v_00_u03c3_2037_, lean_object* v_inst_2038_, lean_object* v_m_2039_, lean_object* v_s_2040_, lean_object* v_motive_2041_, lean_object* v_x_2042_, lean_object* v_h__1_2043_, lean_object* v_h__2_2044_){
_start:
{
lean_object* v_res_2045_; 
v_res_2045_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(v_00_u03c1_2035_, v_00_u03c1_2036_, v_00_u03c3_2037_, v_inst_2038_, v_m_2039_, v_s_2040_, v_motive_2041_, v_x_2042_, v_h__1_2043_, v_h__2_2044_);
lean_dec_ref(v_s_2040_);
lean_dec(v_inst_2038_);
lean_dec(v_00_u03c1_2036_);
return v_res_2045_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(lean_object* v_x_2046_, lean_object* v_x_2047_, lean_object* v_h__1_2048_, lean_object* v_h__2_2049_, lean_object* v_h__3_2050_, lean_object* v_h__4_2051_, lean_object* v_h__5_2052_, lean_object* v_h__6_2053_, lean_object* v_h__7_2054_, lean_object* v_h__8_2055_){
_start:
{
if (lean_obj_tag(v_x_2046_) == 0)
{
lean_dec(v_h__8_2055_);
lean_dec(v_h__7_2054_);
lean_dec(v_h__6_2053_);
switch(lean_obj_tag(v_x_2047_))
{
case 0:
{
lean_object* v_it_2056_; 
lean_dec(v_h__5_2052_);
lean_dec(v_h__4_2051_);
lean_dec(v_h__3_2050_);
v_it_2056_ = lean_ctor_get(v_x_2047_, 0);
if (lean_obj_tag(v_it_2056_) == 0)
{
lean_object* v_currPos_2057_; lean_object* v_searcher_2058_; lean_object* v_out_2059_; lean_object* v_currPos_2060_; lean_object* v_searcher_2061_; lean_object* v___x_2062_; 
lean_inc_ref(v_it_2056_);
lean_dec(v_h__2_2049_);
v_currPos_2057_ = lean_ctor_get(v_x_2046_, 0);
lean_inc(v_currPos_2057_);
v_searcher_2058_ = lean_ctor_get(v_x_2046_, 1);
lean_inc(v_searcher_2058_);
lean_dec_ref(v_x_2046_);
v_out_2059_ = lean_ctor_get(v_x_2047_, 1);
lean_inc(v_out_2059_);
lean_dec_ref(v_x_2047_);
v_currPos_2060_ = lean_ctor_get(v_it_2056_, 0);
lean_inc(v_currPos_2060_);
v_searcher_2061_ = lean_ctor_get(v_it_2056_, 1);
lean_inc(v_searcher_2061_);
lean_dec_ref(v_it_2056_);
v___x_2062_ = lean_apply_5(v_h__1_2048_, v_currPos_2057_, v_searcher_2058_, v_currPos_2060_, v_searcher_2061_, v_out_2059_);
return v___x_2062_;
}
else
{
lean_object* v_currPos_2063_; lean_object* v_searcher_2064_; lean_object* v_out_2065_; lean_object* v___x_2066_; 
lean_dec(v_h__1_2048_);
v_currPos_2063_ = lean_ctor_get(v_x_2046_, 0);
lean_inc(v_currPos_2063_);
v_searcher_2064_ = lean_ctor_get(v_x_2046_, 1);
lean_inc(v_searcher_2064_);
lean_dec_ref(v_x_2046_);
v_out_2065_ = lean_ctor_get(v_x_2047_, 1);
lean_inc(v_out_2065_);
lean_dec_ref(v_x_2047_);
v___x_2066_ = lean_apply_3(v_h__2_2049_, v_currPos_2063_, v_searcher_2064_, v_out_2065_);
return v___x_2066_;
}
}
case 1:
{
lean_object* v_it_2067_; 
lean_dec(v_h__5_2052_);
lean_dec(v_h__2_2049_);
lean_dec(v_h__1_2048_);
v_it_2067_ = lean_ctor_get(v_x_2047_, 0);
lean_inc(v_it_2067_);
lean_dec_ref(v_x_2047_);
if (lean_obj_tag(v_it_2067_) == 0)
{
lean_object* v_currPos_2068_; lean_object* v_searcher_2069_; lean_object* v_currPos_2070_; lean_object* v_searcher_2071_; lean_object* v___x_2072_; 
lean_dec(v_h__4_2051_);
v_currPos_2068_ = lean_ctor_get(v_x_2046_, 0);
lean_inc(v_currPos_2068_);
v_searcher_2069_ = lean_ctor_get(v_x_2046_, 1);
lean_inc(v_searcher_2069_);
lean_dec_ref(v_x_2046_);
v_currPos_2070_ = lean_ctor_get(v_it_2067_, 0);
lean_inc(v_currPos_2070_);
v_searcher_2071_ = lean_ctor_get(v_it_2067_, 1);
lean_inc(v_searcher_2071_);
lean_dec_ref(v_it_2067_);
v___x_2072_ = lean_apply_4(v_h__3_2050_, v_currPos_2068_, v_searcher_2069_, v_currPos_2070_, v_searcher_2071_);
return v___x_2072_;
}
else
{
lean_object* v_currPos_2073_; lean_object* v_searcher_2074_; lean_object* v___x_2075_; 
lean_dec(v_h__3_2050_);
v_currPos_2073_ = lean_ctor_get(v_x_2046_, 0);
lean_inc(v_currPos_2073_);
v_searcher_2074_ = lean_ctor_get(v_x_2046_, 1);
lean_inc(v_searcher_2074_);
lean_dec_ref(v_x_2046_);
v___x_2075_ = lean_apply_2(v_h__4_2051_, v_currPos_2073_, v_searcher_2074_);
return v___x_2075_;
}
}
default: 
{
lean_object* v_currPos_2076_; lean_object* v_searcher_2077_; lean_object* v___x_2078_; 
lean_dec(v_h__4_2051_);
lean_dec(v_h__3_2050_);
lean_dec(v_h__2_2049_);
lean_dec(v_h__1_2048_);
v_currPos_2076_ = lean_ctor_get(v_x_2046_, 0);
lean_inc(v_currPos_2076_);
v_searcher_2077_ = lean_ctor_get(v_x_2046_, 1);
lean_inc(v_searcher_2077_);
lean_dec_ref(v_x_2046_);
v___x_2078_ = lean_apply_2(v_h__5_2052_, v_currPos_2076_, v_searcher_2077_);
return v___x_2078_;
}
}
}
else
{
lean_dec(v_h__5_2052_);
lean_dec(v_h__4_2051_);
lean_dec(v_h__3_2050_);
lean_dec(v_h__2_2049_);
lean_dec(v_h__1_2048_);
switch(lean_obj_tag(v_x_2047_))
{
case 0:
{
lean_object* v_it_2079_; lean_object* v_out_2080_; lean_object* v___x_2081_; 
lean_dec(v_h__8_2055_);
lean_dec(v_h__7_2054_);
v_it_2079_ = lean_ctor_get(v_x_2047_, 0);
lean_inc(v_it_2079_);
v_out_2080_ = lean_ctor_get(v_x_2047_, 1);
lean_inc(v_out_2080_);
lean_dec_ref(v_x_2047_);
v___x_2081_ = lean_apply_2(v_h__6_2053_, v_it_2079_, v_out_2080_);
return v___x_2081_;
}
case 1:
{
lean_object* v_it_2082_; lean_object* v___x_2083_; 
lean_dec(v_h__8_2055_);
lean_dec(v_h__6_2053_);
v_it_2082_ = lean_ctor_get(v_x_2047_, 0);
lean_inc(v_it_2082_);
lean_dec_ref(v_x_2047_);
v___x_2083_ = lean_apply_1(v_h__7_2054_, v_it_2082_);
return v___x_2083_;
}
default: 
{
lean_object* v___x_2084_; lean_object* v___x_2085_; 
lean_dec(v_h__7_2054_);
lean_dec(v_h__6_2053_);
v___x_2084_ = lean_box(0);
v___x_2085_ = lean_apply_1(v_h__8_2055_, v___x_2084_);
return v___x_2085_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(lean_object* v_00_u03c1_2086_, lean_object* v_00_u03c1_2087_, lean_object* v_00_u03c3_2088_, lean_object* v_inst_2089_, lean_object* v_m_2090_, lean_object* v_s_2091_, lean_object* v_motive_2092_, lean_object* v_x_2093_, lean_object* v_x_2094_, lean_object* v_h__1_2095_, lean_object* v_h__2_2096_, lean_object* v_h__3_2097_, lean_object* v_h__4_2098_, lean_object* v_h__5_2099_, lean_object* v_h__6_2100_, lean_object* v_h__7_2101_, lean_object* v_h__8_2102_){
_start:
{
lean_object* v___x_2103_; 
v___x_2103_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(v_x_2093_, v_x_2094_, v_h__1_2095_, v_h__2_2096_, v_h__3_2097_, v_h__4_2098_, v_h__5_2099_, v_h__6_2100_, v_h__7_2101_, v_h__8_2102_);
return v___x_2103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___boxed(lean_object** _args){
lean_object* v_00_u03c1_2104_ = _args[0];
lean_object* v_00_u03c1_2105_ = _args[1];
lean_object* v_00_u03c3_2106_ = _args[2];
lean_object* v_inst_2107_ = _args[3];
lean_object* v_m_2108_ = _args[4];
lean_object* v_s_2109_ = _args[5];
lean_object* v_motive_2110_ = _args[6];
lean_object* v_x_2111_ = _args[7];
lean_object* v_x_2112_ = _args[8];
lean_object* v_h__1_2113_ = _args[9];
lean_object* v_h__2_2114_ = _args[10];
lean_object* v_h__3_2115_ = _args[11];
lean_object* v_h__4_2116_ = _args[12];
lean_object* v_h__5_2117_ = _args[13];
lean_object* v_h__6_2118_ = _args[14];
lean_object* v_h__7_2119_ = _args[15];
lean_object* v_h__8_2120_ = _args[16];
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(v_00_u03c1_2104_, v_00_u03c1_2105_, v_00_u03c3_2106_, v_inst_2107_, v_m_2108_, v_s_2109_, v_motive_2110_, v_x_2111_, v_x_2112_, v_h__1_2113_, v_h__2_2114_, v_h__3_2115_, v_h__4_2116_, v_h__5_2117_, v_h__6_2118_, v_h__7_2119_, v_h__8_2120_);
lean_dec_ref(v_s_2109_);
lean_dec(v_inst_2107_);
lean_dec(v_00_u03c1_2105_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___redArg(lean_object* v_x_2122_, lean_object* v_h__1_2123_, lean_object* v_h__2_2124_){
_start:
{
if (lean_obj_tag(v_x_2122_) == 0)
{
lean_object* v_currPos_2125_; lean_object* v_searcher_2126_; lean_object* v___x_2127_; 
lean_dec(v_h__2_2124_);
v_currPos_2125_ = lean_ctor_get(v_x_2122_, 0);
lean_inc(v_currPos_2125_);
v_searcher_2126_ = lean_ctor_get(v_x_2122_, 1);
lean_inc(v_searcher_2126_);
lean_dec_ref(v_x_2122_);
v___x_2127_ = lean_apply_2(v_h__1_2123_, v_currPos_2125_, v_searcher_2126_);
return v___x_2127_;
}
else
{
lean_object* v___x_2128_; lean_object* v___x_2129_; 
lean_dec(v_h__1_2123_);
v___x_2128_ = lean_box(0);
v___x_2129_ = lean_apply_1(v_h__2_2124_, v___x_2128_);
return v___x_2129_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_2130_, lean_object* v_00_u03c1_2131_, lean_object* v_00_u03c3_2132_, lean_object* v_inst_2133_, lean_object* v_s_2134_, lean_object* v_motive_2135_, lean_object* v_x_2136_, lean_object* v_h__1_2137_, lean_object* v_h__2_2138_){
_start:
{
lean_object* v___x_2139_; 
v___x_2139_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___redArg(v_x_2136_, v_h__1_2137_, v_h__2_2138_);
return v___x_2139_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_2140_, lean_object* v_00_u03c1_2141_, lean_object* v_00_u03c3_2142_, lean_object* v_inst_2143_, lean_object* v_s_2144_, lean_object* v_motive_2145_, lean_object* v_x_2146_, lean_object* v_h__1_2147_, lean_object* v_h__2_2148_){
_start:
{
lean_object* v_res_2149_; 
v_res_2149_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(v_00_u03c1_2140_, v_00_u03c1_2141_, v_00_u03c3_2142_, v_inst_2143_, v_s_2144_, v_motive_2145_, v_x_2146_, v_h__1_2147_, v_h__2_2148_);
lean_dec_ref(v_s_2144_);
lean_dec(v_inst_2143_);
lean_dec(v_00_u03c1_2141_);
return v_res_2149_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(lean_object* v_00_u03c1_2150_, lean_object* v_00_u03c1_2151_, lean_object* v_00_u03c3_2152_, lean_object* v_inst_2153_, lean_object* v_inst_2154_, lean_object* v_s_2155_, lean_object* v_inst_2156_){
_start:
{
lean_object* v___x_2157_; 
v___x_2157_ = lean_box(0);
return v___x_2157_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_2158_, lean_object* v_00_u03c1_2159_, lean_object* v_00_u03c3_2160_, lean_object* v_inst_2161_, lean_object* v_inst_2162_, lean_object* v_s_2163_, lean_object* v_inst_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(v_00_u03c1_2158_, v_00_u03c1_2159_, v_00_u03c3_2160_, v_inst_2161_, v_inst_2162_, v_s_2163_, v_inst_2164_);
lean_dec_ref(v_s_2163_);
lean_dec(v_inst_2162_);
lean_dec(v_inst_2161_);
lean_dec(v_00_u03c1_2159_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object* v_toPure_2166_, lean_object* v_recur_2167_, lean_object* v_it_2168_, lean_object* v_____do__lift_2169_){
_start:
{
if (lean_obj_tag(v_____do__lift_2169_) == 0)
{
lean_object* v_a_2170_; lean_object* v___x_2171_; 
lean_dec(v_it_2168_);
lean_dec(v_recur_2167_);
v_a_2170_ = lean_ctor_get(v_____do__lift_2169_, 0);
lean_inc(v_a_2170_);
lean_dec_ref(v_____do__lift_2169_);
v___x_2171_ = lean_apply_2(v_toPure_2166_, lean_box(0), v_a_2170_);
return v___x_2171_;
}
else
{
lean_object* v_a_2172_; lean_object* v___x_2173_; 
lean_dec(v_toPure_2166_);
v_a_2172_ = lean_ctor_get(v_____do__lift_2169_, 0);
lean_inc(v_a_2172_);
lean_dec_ref(v_____do__lift_2169_);
v___x_2173_ = lean_apply_4(v_recur_2167_, v_it_2168_, v_a_2172_, lean_box(0), lean_box(0));
return v___x_2173_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object* v_toPure_2174_, lean_object* v_recur_2175_, lean_object* v___y_2176_, lean_object* v_acc_2177_, lean_object* v_toBind_2178_, lean_object* v_s_2179_){
_start:
{
switch(lean_obj_tag(v_s_2179_))
{
case 0:
{
lean_object* v_it_2180_; lean_object* v_out_2181_; lean_object* v___f_2182_; lean_object* v___x_2183_; lean_object* v___x_2184_; 
v_it_2180_ = lean_ctor_get(v_s_2179_, 0);
lean_inc(v_it_2180_);
v_out_2181_ = lean_ctor_get(v_s_2179_, 1);
lean_inc(v_out_2181_);
lean_dec_ref(v_s_2179_);
v___f_2182_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2182_, 0, v_toPure_2174_);
lean_closure_set(v___f_2182_, 1, v_recur_2175_);
lean_closure_set(v___f_2182_, 2, v_it_2180_);
v___x_2183_ = lean_apply_3(v___y_2176_, v_out_2181_, lean_box(0), v_acc_2177_);
v___x_2184_ = lean_apply_4(v_toBind_2178_, lean_box(0), lean_box(0), v___x_2183_, v___f_2182_);
return v___x_2184_;
}
case 1:
{
lean_object* v_it_2185_; lean_object* v___x_2186_; 
lean_dec(v_toBind_2178_);
lean_dec(v___y_2176_);
lean_dec(v_toPure_2174_);
v_it_2185_ = lean_ctor_get(v_s_2179_, 0);
lean_inc(v_it_2185_);
lean_dec_ref(v_s_2179_);
v___x_2186_ = lean_apply_4(v_recur_2175_, v_it_2185_, v_acc_2177_, lean_box(0), lean_box(0));
return v___x_2186_;
}
default: 
{
lean_object* v___x_2187_; 
lean_dec(v_toBind_2178_);
lean_dec(v___y_2176_);
lean_dec(v_recur_2175_);
v___x_2187_ = lean_apply_2(v_toPure_2174_, lean_box(0), v_acc_2177_);
return v___x_2187_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object* v_toPure_2188_, lean_object* v___y_2189_, lean_object* v_toBind_2190_, lean_object* v_inst_2191_, lean_object* v_s_2192_, lean_object* v_toPure_2193_, lean_object* v_lift_2194_, lean_object* v_it_2195_, lean_object* v_acc_2196_, lean_object* v_hP_2197_, lean_object* v_recur_2198_){
_start:
{
lean_object* v___f_2199_; 
v___f_2199_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2199_, 0, v_toPure_2188_);
lean_closure_set(v___f_2199_, 1, v_recur_2198_);
lean_closure_set(v___f_2199_, 2, v___y_2189_);
lean_closure_set(v___f_2199_, 3, v_acc_2196_);
lean_closure_set(v___f_2199_, 4, v_toBind_2190_);
if (lean_obj_tag(v_it_2195_) == 0)
{
lean_object* v_currPos_2200_; lean_object* v_searcher_2201_; lean_object* v___x_2203_; uint8_t v_isShared_2204_; uint8_t v_isSharedCheck_2264_; 
v_currPos_2200_ = lean_ctor_get(v_it_2195_, 0);
v_searcher_2201_ = lean_ctor_get(v_it_2195_, 1);
v_isSharedCheck_2264_ = !lean_is_exclusive(v_it_2195_);
if (v_isSharedCheck_2264_ == 0)
{
v___x_2203_ = v_it_2195_;
v_isShared_2204_ = v_isSharedCheck_2264_;
goto v_resetjp_2202_;
}
else
{
lean_inc(v_searcher_2201_);
lean_inc(v_currPos_2200_);
lean_dec(v_it_2195_);
v___x_2203_ = lean_box(0);
v_isShared_2204_ = v_isSharedCheck_2264_;
goto v_resetjp_2202_;
}
v_resetjp_2202_:
{
lean_object* v___x_2205_; 
lean_inc_ref(v_s_2192_);
v___x_2205_ = lean_apply_2(v_inst_2191_, v_s_2192_, v_searcher_2201_);
switch(lean_obj_tag(v___x_2205_))
{
case 0:
{
lean_object* v_out_2206_; 
v_out_2206_ = lean_ctor_get(v___x_2205_, 1);
lean_inc(v_out_2206_);
if (lean_obj_tag(v_out_2206_) == 0)
{
lean_object* v_it_2207_; lean_object* v___x_2209_; 
lean_dec_ref(v_out_2206_);
lean_dec_ref(v_s_2192_);
v_it_2207_ = lean_ctor_get(v___x_2205_, 0);
lean_inc(v_it_2207_);
lean_dec_ref(v___x_2205_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 1, v_it_2207_);
v___x_2209_ = v___x_2203_;
goto v_reusejp_2208_;
}
else
{
lean_object* v_reuseFailAlloc_2213_; 
v_reuseFailAlloc_2213_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2213_, 0, v_currPos_2200_);
lean_ctor_set(v_reuseFailAlloc_2213_, 1, v_it_2207_);
v___x_2209_ = v_reuseFailAlloc_2213_;
goto v_reusejp_2208_;
}
v_reusejp_2208_:
{
lean_object* v___x_2210_; lean_object* v___x_2211_; lean_object* v___x_2212_; 
v___x_2210_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2210_, 0, v___x_2209_);
v___x_2211_ = lean_apply_2(v_toPure_2193_, lean_box(0), v___x_2210_);
v___x_2212_ = lean_apply_4(v_lift_2194_, lean_box(0), lean_box(0), v___f_2199_, v___x_2211_);
return v___x_2212_;
}
}
else
{
lean_object* v_it_2214_; lean_object* v___x_2216_; uint8_t v_isShared_2217_; uint8_t v_isSharedCheck_2229_; 
v_it_2214_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2229_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2229_ == 0)
{
lean_object* v_unused_2230_; 
v_unused_2230_ = lean_ctor_get(v___x_2205_, 1);
lean_dec(v_unused_2230_);
v___x_2216_ = v___x_2205_;
v_isShared_2217_ = v_isSharedCheck_2229_;
goto v_resetjp_2215_;
}
else
{
lean_inc(v_it_2214_);
lean_dec(v___x_2205_);
v___x_2216_ = lean_box(0);
v_isShared_2217_ = v_isSharedCheck_2229_;
goto v_resetjp_2215_;
}
v_resetjp_2215_:
{
lean_object* v_startPos_2218_; lean_object* v_endPos_2219_; lean_object* v_slice_2220_; lean_object* v_nextIt_2222_; 
v_startPos_2218_ = lean_ctor_get(v_out_2206_, 0);
lean_inc(v_startPos_2218_);
v_endPos_2219_ = lean_ctor_get(v_out_2206_, 1);
lean_inc(v_endPos_2219_);
lean_dec_ref(v_out_2206_);
v_slice_2220_ = l_String_Slice_slice_x21(v_s_2192_, v_endPos_2219_, v_currPos_2200_);
lean_dec(v_currPos_2200_);
lean_dec(v_endPos_2219_);
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 1, v_it_2214_);
lean_ctor_set(v___x_2203_, 0, v_startPos_2218_);
v_nextIt_2222_ = v___x_2203_;
goto v_reusejp_2221_;
}
else
{
lean_object* v_reuseFailAlloc_2228_; 
v_reuseFailAlloc_2228_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2228_, 0, v_startPos_2218_);
lean_ctor_set(v_reuseFailAlloc_2228_, 1, v_it_2214_);
v_nextIt_2222_ = v_reuseFailAlloc_2228_;
goto v_reusejp_2221_;
}
v_reusejp_2221_:
{
lean_object* v___x_2224_; 
if (v_isShared_2217_ == 0)
{
lean_ctor_set(v___x_2216_, 1, v_slice_2220_);
lean_ctor_set(v___x_2216_, 0, v_nextIt_2222_);
v___x_2224_ = v___x_2216_;
goto v_reusejp_2223_;
}
else
{
lean_object* v_reuseFailAlloc_2227_; 
v_reuseFailAlloc_2227_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2227_, 0, v_nextIt_2222_);
lean_ctor_set(v_reuseFailAlloc_2227_, 1, v_slice_2220_);
v___x_2224_ = v_reuseFailAlloc_2227_;
goto v_reusejp_2223_;
}
v_reusejp_2223_:
{
lean_object* v___x_2225_; lean_object* v___x_2226_; 
v___x_2225_ = lean_apply_2(v_toPure_2193_, lean_box(0), v___x_2224_);
v___x_2226_ = lean_apply_4(v_lift_2194_, lean_box(0), lean_box(0), v___f_2199_, v___x_2225_);
return v___x_2226_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2231_; lean_object* v___x_2233_; uint8_t v_isShared_2234_; uint8_t v_isSharedCheck_2243_; 
lean_dec_ref(v_s_2192_);
v_it_2231_ = lean_ctor_get(v___x_2205_, 0);
v_isSharedCheck_2243_ = !lean_is_exclusive(v___x_2205_);
if (v_isSharedCheck_2243_ == 0)
{
v___x_2233_ = v___x_2205_;
v_isShared_2234_ = v_isSharedCheck_2243_;
goto v_resetjp_2232_;
}
else
{
lean_inc(v_it_2231_);
lean_dec(v___x_2205_);
v___x_2233_ = lean_box(0);
v_isShared_2234_ = v_isSharedCheck_2243_;
goto v_resetjp_2232_;
}
v_resetjp_2232_:
{
lean_object* v___x_2236_; 
if (v_isShared_2204_ == 0)
{
lean_ctor_set(v___x_2203_, 1, v_it_2231_);
v___x_2236_ = v___x_2203_;
goto v_reusejp_2235_;
}
else
{
lean_object* v_reuseFailAlloc_2242_; 
v_reuseFailAlloc_2242_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2242_, 0, v_currPos_2200_);
lean_ctor_set(v_reuseFailAlloc_2242_, 1, v_it_2231_);
v___x_2236_ = v_reuseFailAlloc_2242_;
goto v_reusejp_2235_;
}
v_reusejp_2235_:
{
lean_object* v___x_2238_; 
if (v_isShared_2234_ == 0)
{
lean_ctor_set(v___x_2233_, 0, v___x_2236_);
v___x_2238_ = v___x_2233_;
goto v_reusejp_2237_;
}
else
{
lean_object* v_reuseFailAlloc_2241_; 
v_reuseFailAlloc_2241_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2241_, 0, v___x_2236_);
v___x_2238_ = v_reuseFailAlloc_2241_;
goto v_reusejp_2237_;
}
v_reusejp_2237_:
{
lean_object* v___x_2239_; lean_object* v___x_2240_; 
v___x_2239_ = lean_apply_2(v_toPure_2193_, lean_box(0), v___x_2238_);
v___x_2240_ = lean_apply_4(v_lift_2194_, lean_box(0), lean_box(0), v___f_2199_, v___x_2239_);
return v___x_2240_;
}
}
}
}
default: 
{
lean_object* v___x_2244_; uint8_t v___x_2245_; 
lean_del_object(v___x_2203_);
v___x_2244_ = lean_unsigned_to_nat(0u);
v___x_2245_ = lean_nat_dec_eq(v_currPos_2200_, v___x_2244_);
if (v___x_2245_ == 0)
{
lean_object* v_str_2246_; lean_object* v_startInclusive_2247_; lean_object* v___x_2249_; uint8_t v_isShared_2250_; uint8_t v_isSharedCheck_2259_; 
v_str_2246_ = lean_ctor_get(v_s_2192_, 0);
v_startInclusive_2247_ = lean_ctor_get(v_s_2192_, 1);
v_isSharedCheck_2259_ = !lean_is_exclusive(v_s_2192_);
if (v_isSharedCheck_2259_ == 0)
{
lean_object* v_unused_2260_; 
v_unused_2260_ = lean_ctor_get(v_s_2192_, 2);
lean_dec(v_unused_2260_);
v___x_2249_ = v_s_2192_;
v_isShared_2250_ = v_isSharedCheck_2259_;
goto v_resetjp_2248_;
}
else
{
lean_inc(v_startInclusive_2247_);
lean_inc(v_str_2246_);
lean_dec(v_s_2192_);
v___x_2249_ = lean_box(0);
v_isShared_2250_ = v_isSharedCheck_2259_;
goto v_resetjp_2248_;
}
v_resetjp_2248_:
{
lean_object* v___x_2251_; lean_object* v_slice_2253_; 
v___x_2251_ = lean_nat_add(v_startInclusive_2247_, v_currPos_2200_);
lean_dec(v_currPos_2200_);
if (v_isShared_2250_ == 0)
{
lean_ctor_set(v___x_2249_, 2, v___x_2251_);
v_slice_2253_ = v___x_2249_;
goto v_reusejp_2252_;
}
else
{
lean_object* v_reuseFailAlloc_2258_; 
v_reuseFailAlloc_2258_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2258_, 0, v_str_2246_);
lean_ctor_set(v_reuseFailAlloc_2258_, 1, v_startInclusive_2247_);
lean_ctor_set(v_reuseFailAlloc_2258_, 2, v___x_2251_);
v_slice_2253_ = v_reuseFailAlloc_2258_;
goto v_reusejp_2252_;
}
v_reusejp_2252_:
{
lean_object* v___x_2254_; lean_object* v___x_2255_; lean_object* v___x_2256_; lean_object* v___x_2257_; 
v___x_2254_ = lean_box(1);
v___x_2255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2255_, 0, v___x_2254_);
lean_ctor_set(v___x_2255_, 1, v_slice_2253_);
v___x_2256_ = lean_apply_2(v_toPure_2193_, lean_box(0), v___x_2255_);
v___x_2257_ = lean_apply_4(v_lift_2194_, lean_box(0), lean_box(0), v___f_2199_, v___x_2256_);
return v___x_2257_;
}
}
}
else
{
lean_object* v___x_2261_; lean_object* v___x_2262_; lean_object* v___x_2263_; 
lean_dec(v_currPos_2200_);
lean_dec_ref(v_s_2192_);
v___x_2261_ = lean_box(2);
v___x_2262_ = lean_apply_2(v_toPure_2193_, lean_box(0), v___x_2261_);
v___x_2263_ = lean_apply_4(v_lift_2194_, lean_box(0), lean_box(0), v___f_2199_, v___x_2262_);
return v___x_2263_;
}
}
}
}
}
else
{
lean_object* v___x_2265_; lean_object* v___x_2266_; lean_object* v___x_2267_; 
lean_dec_ref(v_s_2192_);
lean_dec(v_inst_2191_);
v___x_2265_ = lean_box(2);
v___x_2266_ = lean_apply_2(v_toPure_2193_, lean_box(0), v___x_2265_);
v___x_2267_ = lean_apply_4(v_lift_2194_, lean_box(0), lean_box(0), v___f_2199_, v___x_2266_);
return v___x_2267_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object* v_inst_2268_, lean_object* v_inst_2269_, lean_object* v_s_2270_, lean_object* v_toPure_2271_, lean_object* v_lift_2272_, lean_object* v_00_u03b3_2273_, lean_object* v_Pl_2274_, lean_object* v_it_2275_, lean_object* v_init_2276_, lean_object* v___y_2277_){
_start:
{
lean_object* v_toApplicative_2278_; lean_object* v_toBind_2279_; lean_object* v_toPure_2280_; lean_object* v___f_2281_; lean_object* v___x_2282_; 
v_toApplicative_2278_ = lean_ctor_get(v_inst_2268_, 0);
lean_inc_ref(v_toApplicative_2278_);
v_toBind_2279_ = lean_ctor_get(v_inst_2268_, 1);
lean_inc(v_toBind_2279_);
lean_dec_ref(v_inst_2268_);
v_toPure_2280_ = lean_ctor_get(v_toApplicative_2278_, 1);
lean_inc(v_toPure_2280_);
lean_dec_ref(v_toApplicative_2278_);
v___f_2281_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2), 11, 7);
lean_closure_set(v___f_2281_, 0, v_toPure_2280_);
lean_closure_set(v___f_2281_, 1, v___y_2277_);
lean_closure_set(v___f_2281_, 2, v_toBind_2279_);
lean_closure_set(v___f_2281_, 3, v_inst_2269_);
lean_closure_set(v___f_2281_, 4, v_s_2270_);
lean_closure_set(v___f_2281_, 5, v_toPure_2271_);
lean_closure_set(v___f_2281_, 6, v_lift_2272_);
v___x_2282_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2281_, v_it_2275_, v_init_2276_, lean_box(0));
return v___x_2282_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(lean_object* v_inst_2283_, lean_object* v_s_2284_, lean_object* v_inst_2285_, lean_object* v_inst_2286_){
_start:
{
lean_object* v_toApplicative_2287_; lean_object* v_toPure_2288_; lean_object* v___f_2289_; 
v_toApplicative_2287_ = lean_ctor_get(v_inst_2285_, 0);
lean_inc_ref(v_toApplicative_2287_);
lean_dec_ref(v_inst_2285_);
v_toPure_2288_ = lean_ctor_get(v_toApplicative_2287_, 1);
lean_inc(v_toPure_2288_);
lean_dec_ref(v_toApplicative_2287_);
v___f_2289_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3), 10, 4);
lean_closure_set(v___f_2289_, 0, v_inst_2286_);
lean_closure_set(v___f_2289_, 1, v_inst_2283_);
lean_closure_set(v___f_2289_, 2, v_s_2284_);
lean_closure_set(v___f_2289_, 3, v_toPure_2288_);
return v___f_2289_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(lean_object* v_00_u03c1_2290_, lean_object* v_00_u03c1_2291_, lean_object* v_00_u03c3_2292_, lean_object* v_inst_2293_, lean_object* v_inst_2294_, lean_object* v_m_2295_, lean_object* v_n_2296_, lean_object* v_s_2297_, lean_object* v_inst_2298_, lean_object* v_inst_2299_){
_start:
{
lean_object* v___x_2300_; 
v___x_2300_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(v_inst_2293_, v_s_2297_, v_inst_2298_, v_inst_2299_);
return v___x_2300_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___boxed(lean_object* v_00_u03c1_2301_, lean_object* v_00_u03c1_2302_, lean_object* v_00_u03c3_2303_, lean_object* v_inst_2304_, lean_object* v_inst_2305_, lean_object* v_m_2306_, lean_object* v_n_2307_, lean_object* v_s_2308_, lean_object* v_inst_2309_, lean_object* v_inst_2310_){
_start:
{
lean_object* v_res_2311_; 
v_res_2311_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(v_00_u03c1_2301_, v_00_u03c1_2302_, v_00_u03c3_2303_, v_inst_2304_, v_inst_2305_, v_m_2306_, v_n_2307_, v_s_2308_, v_inst_2309_, v_inst_2310_);
lean_dec(v_inst_2305_);
lean_dec(v_00_u03c1_2302_);
return v_res_2311_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___redArg(lean_object* v_s_2312_, lean_object* v_inst_2313_){
_start:
{
lean_object* v_startInclusive_2314_; lean_object* v_endExclusive_2315_; lean_object* v___x_2316_; lean_object* v___x_2317_; lean_object* v___x_2318_; 
v_startInclusive_2314_ = lean_ctor_get(v_s_2312_, 1);
v_endExclusive_2315_ = lean_ctor_get(v_s_2312_, 2);
v___x_2316_ = lean_nat_sub(v_endExclusive_2315_, v_startInclusive_2314_);
v___x_2317_ = lean_apply_1(v_inst_2313_, v_s_2312_);
v___x_2318_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2318_, 0, v___x_2316_);
lean_ctor_set(v___x_2318_, 1, v___x_2317_);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit(lean_object* v_00_u03c3_2319_, lean_object* v_00_u03c1_2320_, lean_object* v_s_2321_, lean_object* v_pat_2322_, lean_object* v_inst_2323_){
_start:
{
lean_object* v___x_2324_; 
v___x_2324_ = l_String_Slice_revSplit___redArg(v_s_2321_, v_inst_2323_);
return v___x_2324_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___boxed(lean_object* v_00_u03c3_2325_, lean_object* v_00_u03c1_2326_, lean_object* v_s_2327_, lean_object* v_pat_2328_, lean_object* v_inst_2329_){
_start:
{
lean_object* v_res_2330_; 
v_res_2330_ = l_String_Slice_revSplit(v_00_u03c3_2325_, v_00_u03c1_2326_, v_s_2327_, v_pat_2328_, v_inst_2329_);
lean_dec(v_pat_2328_);
return v_res_2330_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___redArg(lean_object* v_s_2331_, lean_object* v_inst_2332_){
_start:
{
lean_object* v_skipSuffix_x3f_2333_; lean_object* v___x_2334_; 
v_skipSuffix_x3f_2333_ = lean_ctor_get(v_inst_2332_, 0);
lean_inc_ref(v_skipSuffix_x3f_2333_);
lean_dec_ref(v_inst_2332_);
v___x_2334_ = lean_apply_1(v_skipSuffix_x3f_2333_, v_s_2331_);
return v___x_2334_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f(lean_object* v_00_u03c1_2335_, lean_object* v_s_2336_, lean_object* v_pat_2337_, lean_object* v_inst_2338_){
_start:
{
lean_object* v_skipSuffix_x3f_2339_; lean_object* v___x_2340_; 
v_skipSuffix_x3f_2339_ = lean_ctor_get(v_inst_2338_, 0);
lean_inc_ref(v_skipSuffix_x3f_2339_);
lean_dec_ref(v_inst_2338_);
v___x_2340_ = lean_apply_1(v_skipSuffix_x3f_2339_, v_s_2336_);
return v___x_2340_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___boxed(lean_object* v_00_u03c1_2341_, lean_object* v_s_2342_, lean_object* v_pat_2343_, lean_object* v_inst_2344_){
_start:
{
lean_object* v_res_2345_; 
v_res_2345_ = l_String_Slice_skipSuffix_x3f(v_00_u03c1_2341_, v_s_2342_, v_pat_2343_, v_inst_2344_);
lean_dec(v_pat_2343_);
return v_res_2345_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg(lean_object* v_s_2346_, lean_object* v_pos_2347_, lean_object* v_inst_2348_){
_start:
{
lean_object* v_str_2349_; lean_object* v_startInclusive_2350_; lean_object* v_endExclusive_2351_; lean_object* v___x_2353_; uint8_t v_isShared_2354_; uint8_t v_isSharedCheck_2370_; 
v_str_2349_ = lean_ctor_get(v_s_2346_, 0);
v_startInclusive_2350_ = lean_ctor_get(v_s_2346_, 1);
v_endExclusive_2351_ = lean_ctor_get(v_s_2346_, 2);
v_isSharedCheck_2370_ = !lean_is_exclusive(v_s_2346_);
if (v_isSharedCheck_2370_ == 0)
{
v___x_2353_ = v_s_2346_;
v_isShared_2354_ = v_isSharedCheck_2370_;
goto v_resetjp_2352_;
}
else
{
lean_inc(v_endExclusive_2351_);
lean_inc(v_startInclusive_2350_);
lean_inc(v_str_2349_);
lean_dec(v_s_2346_);
v___x_2353_ = lean_box(0);
v_isShared_2354_ = v_isSharedCheck_2370_;
goto v_resetjp_2352_;
}
v_resetjp_2352_:
{
lean_object* v_skipPrefix_x3f_2355_; lean_object* v___x_2356_; lean_object* v___x_2358_; 
v_skipPrefix_x3f_2355_ = lean_ctor_get(v_inst_2348_, 0);
lean_inc_ref(v_skipPrefix_x3f_2355_);
lean_dec_ref(v_inst_2348_);
v___x_2356_ = lean_nat_add(v_startInclusive_2350_, v_pos_2347_);
lean_dec(v_startInclusive_2350_);
if (v_isShared_2354_ == 0)
{
lean_ctor_set(v___x_2353_, 1, v___x_2356_);
v___x_2358_ = v___x_2353_;
goto v_reusejp_2357_;
}
else
{
lean_object* v_reuseFailAlloc_2369_; 
v_reuseFailAlloc_2369_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2369_, 0, v_str_2349_);
lean_ctor_set(v_reuseFailAlloc_2369_, 1, v___x_2356_);
lean_ctor_set(v_reuseFailAlloc_2369_, 2, v_endExclusive_2351_);
v___x_2358_ = v_reuseFailAlloc_2369_;
goto v_reusejp_2357_;
}
v_reusejp_2357_:
{
lean_object* v___x_2359_; 
v___x_2359_ = lean_apply_1(v_skipPrefix_x3f_2355_, v___x_2358_);
if (lean_obj_tag(v___x_2359_) == 0)
{
return v___x_2359_;
}
else
{
lean_object* v_val_2360_; lean_object* v___x_2362_; uint8_t v_isShared_2363_; uint8_t v_isSharedCheck_2368_; 
v_val_2360_ = lean_ctor_get(v___x_2359_, 0);
v_isSharedCheck_2368_ = !lean_is_exclusive(v___x_2359_);
if (v_isSharedCheck_2368_ == 0)
{
v___x_2362_ = v___x_2359_;
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
else
{
lean_inc(v_val_2360_);
lean_dec(v___x_2359_);
v___x_2362_ = lean_box(0);
v_isShared_2363_ = v_isSharedCheck_2368_;
goto v_resetjp_2361_;
}
v_resetjp_2361_:
{
lean_object* v___x_2364_; lean_object* v___x_2366_; 
v___x_2364_ = lean_nat_add(v_pos_2347_, v_val_2360_);
lean_dec(v_val_2360_);
if (v_isShared_2363_ == 0)
{
lean_ctor_set(v___x_2362_, 0, v___x_2364_);
v___x_2366_ = v___x_2362_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2367_; 
v_reuseFailAlloc_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2367_, 0, v___x_2364_);
v___x_2366_ = v_reuseFailAlloc_2367_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
return v___x_2366_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg___boxed(lean_object* v_s_2371_, lean_object* v_pos_2372_, lean_object* v_inst_2373_){
_start:
{
lean_object* v_res_2374_; 
v_res_2374_ = l_String_Slice_Pos_revSkip_x3f___redArg(v_s_2371_, v_pos_2372_, v_inst_2373_);
lean_dec(v_pos_2372_);
return v_res_2374_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f(lean_object* v_00_u03c1_2375_, lean_object* v_s_2376_, lean_object* v_pos_2377_, lean_object* v_pat_2378_, lean_object* v_inst_2379_){
_start:
{
lean_object* v_str_2380_; lean_object* v_startInclusive_2381_; lean_object* v_endExclusive_2382_; lean_object* v___x_2384_; uint8_t v_isShared_2385_; uint8_t v_isSharedCheck_2401_; 
v_str_2380_ = lean_ctor_get(v_s_2376_, 0);
v_startInclusive_2381_ = lean_ctor_get(v_s_2376_, 1);
v_endExclusive_2382_ = lean_ctor_get(v_s_2376_, 2);
v_isSharedCheck_2401_ = !lean_is_exclusive(v_s_2376_);
if (v_isSharedCheck_2401_ == 0)
{
v___x_2384_ = v_s_2376_;
v_isShared_2385_ = v_isSharedCheck_2401_;
goto v_resetjp_2383_;
}
else
{
lean_inc(v_endExclusive_2382_);
lean_inc(v_startInclusive_2381_);
lean_inc(v_str_2380_);
lean_dec(v_s_2376_);
v___x_2384_ = lean_box(0);
v_isShared_2385_ = v_isSharedCheck_2401_;
goto v_resetjp_2383_;
}
v_resetjp_2383_:
{
lean_object* v_skipPrefix_x3f_2386_; lean_object* v___x_2387_; lean_object* v___x_2389_; 
v_skipPrefix_x3f_2386_ = lean_ctor_get(v_inst_2379_, 0);
lean_inc_ref(v_skipPrefix_x3f_2386_);
lean_dec_ref(v_inst_2379_);
v___x_2387_ = lean_nat_add(v_startInclusive_2381_, v_pos_2377_);
lean_dec(v_startInclusive_2381_);
if (v_isShared_2385_ == 0)
{
lean_ctor_set(v___x_2384_, 1, v___x_2387_);
v___x_2389_ = v___x_2384_;
goto v_reusejp_2388_;
}
else
{
lean_object* v_reuseFailAlloc_2400_; 
v_reuseFailAlloc_2400_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2400_, 0, v_str_2380_);
lean_ctor_set(v_reuseFailAlloc_2400_, 1, v___x_2387_);
lean_ctor_set(v_reuseFailAlloc_2400_, 2, v_endExclusive_2382_);
v___x_2389_ = v_reuseFailAlloc_2400_;
goto v_reusejp_2388_;
}
v_reusejp_2388_:
{
lean_object* v___x_2390_; 
v___x_2390_ = lean_apply_1(v_skipPrefix_x3f_2386_, v___x_2389_);
if (lean_obj_tag(v___x_2390_) == 0)
{
return v___x_2390_;
}
else
{
lean_object* v_val_2391_; lean_object* v___x_2393_; uint8_t v_isShared_2394_; uint8_t v_isSharedCheck_2399_; 
v_val_2391_ = lean_ctor_get(v___x_2390_, 0);
v_isSharedCheck_2399_ = !lean_is_exclusive(v___x_2390_);
if (v_isSharedCheck_2399_ == 0)
{
v___x_2393_ = v___x_2390_;
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
else
{
lean_inc(v_val_2391_);
lean_dec(v___x_2390_);
v___x_2393_ = lean_box(0);
v_isShared_2394_ = v_isSharedCheck_2399_;
goto v_resetjp_2392_;
}
v_resetjp_2392_:
{
lean_object* v___x_2395_; lean_object* v___x_2397_; 
v___x_2395_ = lean_nat_add(v_pos_2377_, v_val_2391_);
lean_dec(v_val_2391_);
if (v_isShared_2394_ == 0)
{
lean_ctor_set(v___x_2393_, 0, v___x_2395_);
v___x_2397_ = v___x_2393_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2395_);
v___x_2397_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
return v___x_2397_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_2402_, lean_object* v_s_2403_, lean_object* v_pos_2404_, lean_object* v_pat_2405_, lean_object* v_inst_2406_){
_start:
{
lean_object* v_res_2407_; 
v_res_2407_ = l_String_Slice_Pos_revSkip_x3f(v_00_u03c1_2402_, v_s_2403_, v_pos_2404_, v_pat_2405_, v_inst_2406_);
lean_dec(v_pat_2405_);
lean_dec(v_pos_2404_);
return v_res_2407_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___redArg(lean_object* v_s_2408_, lean_object* v_inst_2409_){
_start:
{
lean_object* v_skipSuffix_x3f_2410_; lean_object* v___x_2411_; 
v_skipSuffix_x3f_2410_ = lean_ctor_get(v_inst_2409_, 0);
lean_inc_ref(v_skipSuffix_x3f_2410_);
lean_dec_ref(v_inst_2409_);
lean_inc_ref(v_s_2408_);
v___x_2411_ = lean_apply_1(v_skipSuffix_x3f_2410_, v_s_2408_);
if (lean_obj_tag(v___x_2411_) == 0)
{
lean_object* v___x_2412_; 
lean_dec_ref(v_s_2408_);
v___x_2412_ = lean_box(0);
return v___x_2412_;
}
else
{
lean_object* v_val_2413_; lean_object* v___x_2415_; uint8_t v_isShared_2416_; uint8_t v_isSharedCheck_2431_; 
v_val_2413_ = lean_ctor_get(v___x_2411_, 0);
v_isSharedCheck_2431_ = !lean_is_exclusive(v___x_2411_);
if (v_isSharedCheck_2431_ == 0)
{
v___x_2415_ = v___x_2411_;
v_isShared_2416_ = v_isSharedCheck_2431_;
goto v_resetjp_2414_;
}
else
{
lean_inc(v_val_2413_);
lean_dec(v___x_2411_);
v___x_2415_ = lean_box(0);
v_isShared_2416_ = v_isSharedCheck_2431_;
goto v_resetjp_2414_;
}
v_resetjp_2414_:
{
lean_object* v_str_2417_; lean_object* v_startInclusive_2418_; lean_object* v___x_2420_; uint8_t v_isShared_2421_; uint8_t v_isSharedCheck_2429_; 
v_str_2417_ = lean_ctor_get(v_s_2408_, 0);
v_startInclusive_2418_ = lean_ctor_get(v_s_2408_, 1);
v_isSharedCheck_2429_ = !lean_is_exclusive(v_s_2408_);
if (v_isSharedCheck_2429_ == 0)
{
lean_object* v_unused_2430_; 
v_unused_2430_ = lean_ctor_get(v_s_2408_, 2);
lean_dec(v_unused_2430_);
v___x_2420_ = v_s_2408_;
v_isShared_2421_ = v_isSharedCheck_2429_;
goto v_resetjp_2419_;
}
else
{
lean_inc(v_startInclusive_2418_);
lean_inc(v_str_2417_);
lean_dec(v_s_2408_);
v___x_2420_ = lean_box(0);
v_isShared_2421_ = v_isSharedCheck_2429_;
goto v_resetjp_2419_;
}
v_resetjp_2419_:
{
lean_object* v___x_2422_; lean_object* v___x_2424_; 
v___x_2422_ = lean_nat_add(v_startInclusive_2418_, v_val_2413_);
lean_dec(v_val_2413_);
if (v_isShared_2421_ == 0)
{
lean_ctor_set(v___x_2420_, 2, v___x_2422_);
v___x_2424_ = v___x_2420_;
goto v_reusejp_2423_;
}
else
{
lean_object* v_reuseFailAlloc_2428_; 
v_reuseFailAlloc_2428_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2428_, 0, v_str_2417_);
lean_ctor_set(v_reuseFailAlloc_2428_, 1, v_startInclusive_2418_);
lean_ctor_set(v_reuseFailAlloc_2428_, 2, v___x_2422_);
v___x_2424_ = v_reuseFailAlloc_2428_;
goto v_reusejp_2423_;
}
v_reusejp_2423_:
{
lean_object* v___x_2426_; 
if (v_isShared_2416_ == 0)
{
lean_ctor_set(v___x_2415_, 0, v___x_2424_);
v___x_2426_ = v___x_2415_;
goto v_reusejp_2425_;
}
else
{
lean_object* v_reuseFailAlloc_2427_; 
v_reuseFailAlloc_2427_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2427_, 0, v___x_2424_);
v___x_2426_ = v_reuseFailAlloc_2427_;
goto v_reusejp_2425_;
}
v_reusejp_2425_:
{
return v___x_2426_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f(lean_object* v_00_u03c1_2432_, lean_object* v_s_2433_, lean_object* v_pat_2434_, lean_object* v_inst_2435_){
_start:
{
lean_object* v_skipSuffix_x3f_2436_; lean_object* v___x_2437_; 
v_skipSuffix_x3f_2436_ = lean_ctor_get(v_inst_2435_, 0);
lean_inc_ref(v_skipSuffix_x3f_2436_);
lean_dec_ref(v_inst_2435_);
lean_inc_ref(v_s_2433_);
v___x_2437_ = lean_apply_1(v_skipSuffix_x3f_2436_, v_s_2433_);
if (lean_obj_tag(v___x_2437_) == 0)
{
lean_object* v___x_2438_; 
lean_dec_ref(v_s_2433_);
v___x_2438_ = lean_box(0);
return v___x_2438_;
}
else
{
lean_object* v_val_2439_; lean_object* v___x_2441_; uint8_t v_isShared_2442_; uint8_t v_isSharedCheck_2457_; 
v_val_2439_ = lean_ctor_get(v___x_2437_, 0);
v_isSharedCheck_2457_ = !lean_is_exclusive(v___x_2437_);
if (v_isSharedCheck_2457_ == 0)
{
v___x_2441_ = v___x_2437_;
v_isShared_2442_ = v_isSharedCheck_2457_;
goto v_resetjp_2440_;
}
else
{
lean_inc(v_val_2439_);
lean_dec(v___x_2437_);
v___x_2441_ = lean_box(0);
v_isShared_2442_ = v_isSharedCheck_2457_;
goto v_resetjp_2440_;
}
v_resetjp_2440_:
{
lean_object* v_str_2443_; lean_object* v_startInclusive_2444_; lean_object* v___x_2446_; uint8_t v_isShared_2447_; uint8_t v_isSharedCheck_2455_; 
v_str_2443_ = lean_ctor_get(v_s_2433_, 0);
v_startInclusive_2444_ = lean_ctor_get(v_s_2433_, 1);
v_isSharedCheck_2455_ = !lean_is_exclusive(v_s_2433_);
if (v_isSharedCheck_2455_ == 0)
{
lean_object* v_unused_2456_; 
v_unused_2456_ = lean_ctor_get(v_s_2433_, 2);
lean_dec(v_unused_2456_);
v___x_2446_ = v_s_2433_;
v_isShared_2447_ = v_isSharedCheck_2455_;
goto v_resetjp_2445_;
}
else
{
lean_inc(v_startInclusive_2444_);
lean_inc(v_str_2443_);
lean_dec(v_s_2433_);
v___x_2446_ = lean_box(0);
v_isShared_2447_ = v_isSharedCheck_2455_;
goto v_resetjp_2445_;
}
v_resetjp_2445_:
{
lean_object* v___x_2448_; lean_object* v___x_2450_; 
v___x_2448_ = lean_nat_add(v_startInclusive_2444_, v_val_2439_);
lean_dec(v_val_2439_);
if (v_isShared_2447_ == 0)
{
lean_ctor_set(v___x_2446_, 2, v___x_2448_);
v___x_2450_ = v___x_2446_;
goto v_reusejp_2449_;
}
else
{
lean_object* v_reuseFailAlloc_2454_; 
v_reuseFailAlloc_2454_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2454_, 0, v_str_2443_);
lean_ctor_set(v_reuseFailAlloc_2454_, 1, v_startInclusive_2444_);
lean_ctor_set(v_reuseFailAlloc_2454_, 2, v___x_2448_);
v___x_2450_ = v_reuseFailAlloc_2454_;
goto v_reusejp_2449_;
}
v_reusejp_2449_:
{
lean_object* v___x_2452_; 
if (v_isShared_2442_ == 0)
{
lean_ctor_set(v___x_2441_, 0, v___x_2450_);
v___x_2452_ = v___x_2441_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v___x_2450_);
v___x_2452_ = v_reuseFailAlloc_2453_;
goto v_reusejp_2451_;
}
v_reusejp_2451_:
{
return v___x_2452_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_2458_, lean_object* v_s_2459_, lean_object* v_pat_2460_, lean_object* v_inst_2461_){
_start:
{
lean_object* v_res_2462_; 
v_res_2462_ = l_String_Slice_dropSuffix_x3f(v_00_u03c1_2458_, v_s_2459_, v_pat_2460_, v_inst_2461_);
lean_dec(v_pat_2460_);
return v_res_2462_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___redArg(lean_object* v_s_2463_, lean_object* v_inst_2464_){
_start:
{
lean_object* v_skipSuffix_x3f_2465_; lean_object* v___x_2466_; 
v_skipSuffix_x3f_2465_ = lean_ctor_get(v_inst_2464_, 0);
lean_inc_ref(v_skipSuffix_x3f_2465_);
lean_dec_ref(v_inst_2464_);
lean_inc_ref(v_s_2463_);
v___x_2466_ = lean_apply_1(v_skipSuffix_x3f_2465_, v_s_2463_);
if (lean_obj_tag(v___x_2466_) == 0)
{
return v_s_2463_;
}
else
{
lean_object* v_val_2467_; lean_object* v_str_2468_; lean_object* v_startInclusive_2469_; lean_object* v___x_2471_; uint8_t v_isShared_2472_; uint8_t v_isSharedCheck_2477_; 
v_val_2467_ = lean_ctor_get(v___x_2466_, 0);
lean_inc(v_val_2467_);
lean_dec_ref(v___x_2466_);
v_str_2468_ = lean_ctor_get(v_s_2463_, 0);
v_startInclusive_2469_ = lean_ctor_get(v_s_2463_, 1);
v_isSharedCheck_2477_ = !lean_is_exclusive(v_s_2463_);
if (v_isSharedCheck_2477_ == 0)
{
lean_object* v_unused_2478_; 
v_unused_2478_ = lean_ctor_get(v_s_2463_, 2);
lean_dec(v_unused_2478_);
v___x_2471_ = v_s_2463_;
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
else
{
lean_inc(v_startInclusive_2469_);
lean_inc(v_str_2468_);
lean_dec(v_s_2463_);
v___x_2471_ = lean_box(0);
v_isShared_2472_ = v_isSharedCheck_2477_;
goto v_resetjp_2470_;
}
v_resetjp_2470_:
{
lean_object* v___x_2473_; lean_object* v___x_2475_; 
v___x_2473_ = lean_nat_add(v_startInclusive_2469_, v_val_2467_);
lean_dec(v_val_2467_);
if (v_isShared_2472_ == 0)
{
lean_ctor_set(v___x_2471_, 2, v___x_2473_);
v___x_2475_ = v___x_2471_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2476_; 
v_reuseFailAlloc_2476_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2476_, 0, v_str_2468_);
lean_ctor_set(v_reuseFailAlloc_2476_, 1, v_startInclusive_2469_);
lean_ctor_set(v_reuseFailAlloc_2476_, 2, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2476_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
return v___x_2475_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix(lean_object* v_00_u03c1_2479_, lean_object* v_s_2480_, lean_object* v_pat_2481_, lean_object* v_inst_2482_){
_start:
{
lean_object* v___x_2483_; 
v___x_2483_ = l_String_Slice_dropSuffix___redArg(v_s_2480_, v_inst_2482_);
return v___x_2483_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___boxed(lean_object* v_00_u03c1_2484_, lean_object* v_s_2485_, lean_object* v_pat_2486_, lean_object* v_inst_2487_){
_start:
{
lean_object* v_res_2488_; 
v_res_2488_ = l_String_Slice_dropSuffix(v_00_u03c1_2484_, v_s_2485_, v_pat_2486_, v_inst_2487_);
lean_dec(v_pat_2486_);
return v_res_2488_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object* v_s_2489_, lean_object* v_n_2490_){
_start:
{
lean_object* v_str_2491_; lean_object* v_startInclusive_2492_; lean_object* v_endExclusive_2493_; lean_object* v___x_2494_; lean_object* v___x_2495_; lean_object* v___x_2497_; uint8_t v_isShared_2498_; uint8_t v_isSharedCheck_2503_; 
v_str_2491_ = lean_ctor_get(v_s_2489_, 0);
lean_inc_ref(v_str_2491_);
v_startInclusive_2492_ = lean_ctor_get(v_s_2489_, 1);
lean_inc(v_startInclusive_2492_);
v_endExclusive_2493_ = lean_ctor_get(v_s_2489_, 2);
v___x_2494_ = lean_nat_sub(v_endExclusive_2493_, v_startInclusive_2492_);
v___x_2495_ = l_String_Slice_Pos_prevn(v_s_2489_, v___x_2494_, v_n_2490_);
v_isSharedCheck_2503_ = !lean_is_exclusive(v_s_2489_);
if (v_isSharedCheck_2503_ == 0)
{
lean_object* v_unused_2504_; lean_object* v_unused_2505_; lean_object* v_unused_2506_; 
v_unused_2504_ = lean_ctor_get(v_s_2489_, 2);
lean_dec(v_unused_2504_);
v_unused_2505_ = lean_ctor_get(v_s_2489_, 1);
lean_dec(v_unused_2505_);
v_unused_2506_ = lean_ctor_get(v_s_2489_, 0);
lean_dec(v_unused_2506_);
v___x_2497_ = v_s_2489_;
v_isShared_2498_ = v_isSharedCheck_2503_;
goto v_resetjp_2496_;
}
else
{
lean_dec(v_s_2489_);
v___x_2497_ = lean_box(0);
v_isShared_2498_ = v_isSharedCheck_2503_;
goto v_resetjp_2496_;
}
v_resetjp_2496_:
{
lean_object* v___x_2499_; lean_object* v___x_2501_; 
v___x_2499_ = lean_nat_add(v_startInclusive_2492_, v___x_2495_);
lean_dec(v___x_2495_);
if (v_isShared_2498_ == 0)
{
lean_ctor_set(v___x_2497_, 2, v___x_2499_);
v___x_2501_ = v___x_2497_;
goto v_reusejp_2500_;
}
else
{
lean_object* v_reuseFailAlloc_2502_; 
v_reuseFailAlloc_2502_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2502_, 0, v_str_2491_);
lean_ctor_set(v_reuseFailAlloc_2502_, 1, v_startInclusive_2492_);
lean_ctor_set(v_reuseFailAlloc_2502_, 2, v___x_2499_);
v___x_2501_ = v_reuseFailAlloc_2502_;
goto v_reusejp_2500_;
}
v_reusejp_2500_:
{
return v___x_2501_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object* v_s_2507_, lean_object* v_pos_2508_, lean_object* v_inst_2509_){
_start:
{
lean_object* v_skipSuffix_x3f_2510_; lean_object* v_str_2511_; lean_object* v_startInclusive_2512_; lean_object* v___x_2513_; lean_object* v___x_2514_; lean_object* v___x_2515_; 
v_skipSuffix_x3f_2510_ = lean_ctor_get(v_inst_2509_, 0);
v_str_2511_ = lean_ctor_get(v_s_2507_, 0);
v_startInclusive_2512_ = lean_ctor_get(v_s_2507_, 1);
v___x_2513_ = lean_nat_add(v_startInclusive_2512_, v_pos_2508_);
lean_inc(v_startInclusive_2512_);
lean_inc_ref(v_str_2511_);
v___x_2514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2514_, 0, v_str_2511_);
lean_ctor_set(v___x_2514_, 1, v_startInclusive_2512_);
lean_ctor_set(v___x_2514_, 2, v___x_2513_);
lean_inc_ref(v_skipSuffix_x3f_2510_);
v___x_2515_ = lean_apply_1(v_skipSuffix_x3f_2510_, v___x_2514_);
if (lean_obj_tag(v___x_2515_) == 1)
{
lean_object* v_val_2516_; uint8_t v___x_2517_; 
v_val_2516_ = lean_ctor_get(v___x_2515_, 0);
lean_inc(v_val_2516_);
lean_dec_ref(v___x_2515_);
v___x_2517_ = lean_nat_dec_lt(v_val_2516_, v_pos_2508_);
if (v___x_2517_ == 0)
{
lean_dec(v_val_2516_);
lean_dec_ref(v_inst_2509_);
return v_pos_2508_;
}
else
{
lean_dec(v_pos_2508_);
v_pos_2508_ = v_val_2516_;
goto _start;
}
}
else
{
lean_dec(v___x_2515_);
lean_dec_ref(v_inst_2509_);
return v_pos_2508_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg___boxed(lean_object* v_s_2519_, lean_object* v_pos_2520_, lean_object* v_inst_2521_){
_start:
{
lean_object* v_res_2522_; 
v_res_2522_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2519_, v_pos_2520_, v_inst_2521_);
lean_dec_ref(v_s_2519_);
return v_res_2522_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile(lean_object* v_00_u03c1_2523_, lean_object* v_s_2524_, lean_object* v_pos_2525_, lean_object* v_pat_2526_, lean_object* v_inst_2527_){
_start:
{
lean_object* v___x_2528_; 
v___x_2528_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2524_, v_pos_2525_, v_inst_2527_);
return v___x_2528_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_2529_, lean_object* v_s_2530_, lean_object* v_pos_2531_, lean_object* v_pat_2532_, lean_object* v_inst_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_String_Slice_Pos_revSkipWhile(v_00_u03c1_2529_, v_s_2530_, v_pos_2531_, v_pat_2532_, v_inst_2533_);
lean_dec(v_pat_2532_);
lean_dec_ref(v_s_2530_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_revSkipWhile_match__1_splitter___redArg(lean_object* v_x_2535_, lean_object* v_h__1_2536_, lean_object* v_h__2_2537_){
_start:
{
if (lean_obj_tag(v_x_2535_) == 1)
{
lean_object* v_val_2538_; lean_object* v___x_2539_; 
lean_dec(v_h__2_2537_);
v_val_2538_ = lean_ctor_get(v_x_2535_, 0);
lean_inc(v_val_2538_);
lean_dec_ref(v_x_2535_);
v___x_2539_ = lean_apply_1(v_h__1_2536_, v_val_2538_);
return v___x_2539_;
}
else
{
lean_object* v___x_2540_; 
lean_dec(v_h__1_2536_);
v___x_2540_ = lean_apply_2(v_h__2_2537_, v_x_2535_, lean_box(0));
return v___x_2540_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_revSkipWhile_match__1_splitter(lean_object* v_s_2541_, lean_object* v_pos_2542_, lean_object* v_motive_2543_, lean_object* v_x_2544_, lean_object* v_h__1_2545_, lean_object* v_h__2_2546_){
_start:
{
if (lean_obj_tag(v_x_2544_) == 1)
{
lean_object* v_val_2547_; lean_object* v___x_2548_; 
lean_dec(v_h__2_2546_);
v_val_2547_ = lean_ctor_get(v_x_2544_, 0);
lean_inc(v_val_2547_);
lean_dec_ref(v_x_2544_);
v___x_2548_ = lean_apply_1(v_h__1_2545_, v_val_2547_);
return v___x_2548_;
}
else
{
lean_object* v___x_2549_; 
lean_dec(v_h__1_2545_);
v___x_2549_ = lean_apply_2(v_h__2_2546_, v_x_2544_, lean_box(0));
return v___x_2549_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_revSkipWhile_match__1_splitter___boxed(lean_object* v_s_2550_, lean_object* v_pos_2551_, lean_object* v_motive_2552_, lean_object* v_x_2553_, lean_object* v_h__1_2554_, lean_object* v_h__2_2555_){
_start:
{
lean_object* v_res_2556_; 
v_res_2556_ = l___private_Init_Data_String_Slice_0__String_Slice_Pos_revSkipWhile_match__1_splitter(v_s_2550_, v_pos_2551_, v_motive_2552_, v_x_2553_, v_h__1_2554_, v_h__2_2555_);
lean_dec(v_pos_2551_);
lean_dec_ref(v_s_2550_);
return v_res_2556_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg(lean_object* v_s_2557_, lean_object* v_inst_2558_){
_start:
{
lean_object* v_startInclusive_2559_; lean_object* v_endExclusive_2560_; lean_object* v___x_2561_; lean_object* v___x_2562_; 
v_startInclusive_2559_ = lean_ctor_get(v_s_2557_, 1);
v_endExclusive_2560_ = lean_ctor_get(v_s_2557_, 2);
v___x_2561_ = lean_nat_sub(v_endExclusive_2560_, v_startInclusive_2559_);
v___x_2562_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2557_, v___x_2561_, v_inst_2558_);
return v___x_2562_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg___boxed(lean_object* v_s_2563_, lean_object* v_inst_2564_){
_start:
{
lean_object* v_res_2565_; 
v_res_2565_ = l_String_Slice_skipSuffixWhile___redArg(v_s_2563_, v_inst_2564_);
lean_dec_ref(v_s_2563_);
return v_res_2565_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile(lean_object* v_00_u03c1_2566_, lean_object* v_s_2567_, lean_object* v_pat_2568_, lean_object* v_inst_2569_){
_start:
{
lean_object* v_startInclusive_2570_; lean_object* v_endExclusive_2571_; lean_object* v___x_2572_; lean_object* v___x_2573_; 
v_startInclusive_2570_ = lean_ctor_get(v_s_2567_, 1);
v_endExclusive_2571_ = lean_ctor_get(v_s_2567_, 2);
v___x_2572_ = lean_nat_sub(v_endExclusive_2571_, v_startInclusive_2570_);
v___x_2573_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2567_, v___x_2572_, v_inst_2569_);
return v___x_2573_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___boxed(lean_object* v_00_u03c1_2574_, lean_object* v_s_2575_, lean_object* v_pat_2576_, lean_object* v_inst_2577_){
_start:
{
lean_object* v_res_2578_; 
v_res_2578_ = l_String_Slice_skipSuffixWhile(v_00_u03c1_2574_, v_s_2575_, v_pat_2576_, v_inst_2577_);
lean_dec(v_pat_2576_);
lean_dec_ref(v_s_2575_);
return v_res_2578_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object* v_s_2579_, lean_object* v_inst_2580_){
_start:
{
lean_object* v_str_2581_; lean_object* v_startInclusive_2582_; lean_object* v_endExclusive_2583_; lean_object* v___x_2584_; lean_object* v___x_2585_; lean_object* v___x_2587_; uint8_t v_isShared_2588_; uint8_t v_isSharedCheck_2593_; 
v_str_2581_ = lean_ctor_get(v_s_2579_, 0);
lean_inc_ref(v_str_2581_);
v_startInclusive_2582_ = lean_ctor_get(v_s_2579_, 1);
lean_inc(v_startInclusive_2582_);
v_endExclusive_2583_ = lean_ctor_get(v_s_2579_, 2);
v___x_2584_ = lean_nat_sub(v_endExclusive_2583_, v_startInclusive_2582_);
v___x_2585_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2579_, v___x_2584_, v_inst_2580_);
v_isSharedCheck_2593_ = !lean_is_exclusive(v_s_2579_);
if (v_isSharedCheck_2593_ == 0)
{
lean_object* v_unused_2594_; lean_object* v_unused_2595_; lean_object* v_unused_2596_; 
v_unused_2594_ = lean_ctor_get(v_s_2579_, 2);
lean_dec(v_unused_2594_);
v_unused_2595_ = lean_ctor_get(v_s_2579_, 1);
lean_dec(v_unused_2595_);
v_unused_2596_ = lean_ctor_get(v_s_2579_, 0);
lean_dec(v_unused_2596_);
v___x_2587_ = v_s_2579_;
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
else
{
lean_dec(v_s_2579_);
v___x_2587_ = lean_box(0);
v_isShared_2588_ = v_isSharedCheck_2593_;
goto v_resetjp_2586_;
}
v_resetjp_2586_:
{
lean_object* v___x_2589_; lean_object* v___x_2591_; 
v___x_2589_ = lean_nat_add(v_startInclusive_2582_, v___x_2585_);
lean_dec(v___x_2585_);
if (v_isShared_2588_ == 0)
{
lean_ctor_set(v___x_2587_, 2, v___x_2589_);
v___x_2591_ = v___x_2587_;
goto v_reusejp_2590_;
}
else
{
lean_object* v_reuseFailAlloc_2592_; 
v_reuseFailAlloc_2592_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2592_, 0, v_str_2581_);
lean_ctor_set(v_reuseFailAlloc_2592_, 1, v_startInclusive_2582_);
lean_ctor_set(v_reuseFailAlloc_2592_, 2, v___x_2589_);
v___x_2591_ = v_reuseFailAlloc_2592_;
goto v_reusejp_2590_;
}
v_reusejp_2590_:
{
return v___x_2591_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object* v_00_u03c1_2597_, lean_object* v_s_2598_, lean_object* v_pat_2599_, lean_object* v_inst_2600_){
_start:
{
lean_object* v_str_2601_; lean_object* v_startInclusive_2602_; lean_object* v_endExclusive_2603_; lean_object* v___x_2604_; lean_object* v___x_2605_; lean_object* v___x_2607_; uint8_t v_isShared_2608_; uint8_t v_isSharedCheck_2613_; 
v_str_2601_ = lean_ctor_get(v_s_2598_, 0);
lean_inc_ref(v_str_2601_);
v_startInclusive_2602_ = lean_ctor_get(v_s_2598_, 1);
lean_inc(v_startInclusive_2602_);
v_endExclusive_2603_ = lean_ctor_get(v_s_2598_, 2);
v___x_2604_ = lean_nat_sub(v_endExclusive_2603_, v_startInclusive_2602_);
v___x_2605_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2598_, v___x_2604_, v_inst_2600_);
v_isSharedCheck_2613_ = !lean_is_exclusive(v_s_2598_);
if (v_isSharedCheck_2613_ == 0)
{
lean_object* v_unused_2614_; lean_object* v_unused_2615_; lean_object* v_unused_2616_; 
v_unused_2614_ = lean_ctor_get(v_s_2598_, 2);
lean_dec(v_unused_2614_);
v_unused_2615_ = lean_ctor_get(v_s_2598_, 1);
lean_dec(v_unused_2615_);
v_unused_2616_ = lean_ctor_get(v_s_2598_, 0);
lean_dec(v_unused_2616_);
v___x_2607_ = v_s_2598_;
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
else
{
lean_dec(v_s_2598_);
v___x_2607_ = lean_box(0);
v_isShared_2608_ = v_isSharedCheck_2613_;
goto v_resetjp_2606_;
}
v_resetjp_2606_:
{
lean_object* v___x_2609_; lean_object* v___x_2611_; 
v___x_2609_ = lean_nat_add(v_startInclusive_2602_, v___x_2605_);
lean_dec(v___x_2605_);
if (v_isShared_2608_ == 0)
{
lean_ctor_set(v___x_2607_, 2, v___x_2609_);
v___x_2611_ = v___x_2607_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v_str_2601_);
lean_ctor_set(v_reuseFailAlloc_2612_, 1, v_startInclusive_2602_);
lean_ctor_set(v_reuseFailAlloc_2612_, 2, v___x_2609_);
v___x_2611_ = v_reuseFailAlloc_2612_;
goto v_reusejp_2610_;
}
v_reusejp_2610_:
{
return v___x_2611_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object* v_00_u03c1_2617_, lean_object* v_s_2618_, lean_object* v_pat_2619_, lean_object* v_inst_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_String_Slice_dropEndWhile(v_00_u03c1_2617_, v_s_2618_, v_pat_2619_, v_inst_2620_);
lean_dec(v_pat_2619_);
return v_res_2621_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiEnd___closed__0(void){
_start:
{
lean_object* v___x_2622_; lean_object* v___x_2623_; 
v___x_2622_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_2623_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_2622_);
return v___x_2623_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object* v_s_2624_){
_start:
{
lean_object* v___x_2625_; lean_object* v_str_2626_; lean_object* v_startInclusive_2627_; lean_object* v_endExclusive_2628_; lean_object* v___x_2629_; lean_object* v___x_2630_; lean_object* v___x_2632_; uint8_t v_isShared_2633_; uint8_t v_isSharedCheck_2638_; 
v___x_2625_ = lean_obj_once(&l_String_Slice_trimAsciiEnd___closed__0, &l_String_Slice_trimAsciiEnd___closed__0_once, _init_l_String_Slice_trimAsciiEnd___closed__0);
v_str_2626_ = lean_ctor_get(v_s_2624_, 0);
lean_inc_ref(v_str_2626_);
v_startInclusive_2627_ = lean_ctor_get(v_s_2624_, 1);
lean_inc(v_startInclusive_2627_);
v_endExclusive_2628_ = lean_ctor_get(v_s_2624_, 2);
v___x_2629_ = lean_nat_sub(v_endExclusive_2628_, v_startInclusive_2627_);
v___x_2630_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2624_, v___x_2629_, v___x_2625_);
v_isSharedCheck_2638_ = !lean_is_exclusive(v_s_2624_);
if (v_isSharedCheck_2638_ == 0)
{
lean_object* v_unused_2639_; lean_object* v_unused_2640_; lean_object* v_unused_2641_; 
v_unused_2639_ = lean_ctor_get(v_s_2624_, 2);
lean_dec(v_unused_2639_);
v_unused_2640_ = lean_ctor_get(v_s_2624_, 1);
lean_dec(v_unused_2640_);
v_unused_2641_ = lean_ctor_get(v_s_2624_, 0);
lean_dec(v_unused_2641_);
v___x_2632_ = v_s_2624_;
v_isShared_2633_ = v_isSharedCheck_2638_;
goto v_resetjp_2631_;
}
else
{
lean_dec(v_s_2624_);
v___x_2632_ = lean_box(0);
v_isShared_2633_ = v_isSharedCheck_2638_;
goto v_resetjp_2631_;
}
v_resetjp_2631_:
{
lean_object* v___x_2634_; lean_object* v___x_2636_; 
v___x_2634_ = lean_nat_add(v_startInclusive_2627_, v___x_2630_);
lean_dec(v___x_2630_);
if (v_isShared_2633_ == 0)
{
lean_ctor_set(v___x_2632_, 2, v___x_2634_);
v___x_2636_ = v___x_2632_;
goto v_reusejp_2635_;
}
else
{
lean_object* v_reuseFailAlloc_2637_; 
v_reuseFailAlloc_2637_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2637_, 0, v_str_2626_);
lean_ctor_set(v_reuseFailAlloc_2637_, 1, v_startInclusive_2627_);
lean_ctor_set(v_reuseFailAlloc_2637_, 2, v___x_2634_);
v___x_2636_ = v_reuseFailAlloc_2637_;
goto v_reusejp_2635_;
}
v_reusejp_2635_:
{
return v___x_2636_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object* v_s_2642_, lean_object* v_n_2643_){
_start:
{
lean_object* v_str_2644_; lean_object* v_startInclusive_2645_; lean_object* v_endExclusive_2646_; lean_object* v___x_2647_; lean_object* v___x_2648_; lean_object* v___x_2650_; uint8_t v_isShared_2651_; uint8_t v_isSharedCheck_2656_; 
v_str_2644_ = lean_ctor_get(v_s_2642_, 0);
lean_inc_ref(v_str_2644_);
v_startInclusive_2645_ = lean_ctor_get(v_s_2642_, 1);
lean_inc(v_startInclusive_2645_);
v_endExclusive_2646_ = lean_ctor_get(v_s_2642_, 2);
lean_inc(v_endExclusive_2646_);
v___x_2647_ = lean_nat_sub(v_endExclusive_2646_, v_startInclusive_2645_);
v___x_2648_ = l_String_Slice_Pos_prevn(v_s_2642_, v___x_2647_, v_n_2643_);
v_isSharedCheck_2656_ = !lean_is_exclusive(v_s_2642_);
if (v_isSharedCheck_2656_ == 0)
{
lean_object* v_unused_2657_; lean_object* v_unused_2658_; lean_object* v_unused_2659_; 
v_unused_2657_ = lean_ctor_get(v_s_2642_, 2);
lean_dec(v_unused_2657_);
v_unused_2658_ = lean_ctor_get(v_s_2642_, 1);
lean_dec(v_unused_2658_);
v_unused_2659_ = lean_ctor_get(v_s_2642_, 0);
lean_dec(v_unused_2659_);
v___x_2650_ = v_s_2642_;
v_isShared_2651_ = v_isSharedCheck_2656_;
goto v_resetjp_2649_;
}
else
{
lean_dec(v_s_2642_);
v___x_2650_ = lean_box(0);
v_isShared_2651_ = v_isSharedCheck_2656_;
goto v_resetjp_2649_;
}
v_resetjp_2649_:
{
lean_object* v___x_2652_; lean_object* v___x_2654_; 
v___x_2652_ = lean_nat_add(v_startInclusive_2645_, v___x_2648_);
lean_dec(v___x_2648_);
lean_dec(v_startInclusive_2645_);
if (v_isShared_2651_ == 0)
{
lean_ctor_set(v___x_2650_, 1, v___x_2652_);
v___x_2654_ = v___x_2650_;
goto v_reusejp_2653_;
}
else
{
lean_object* v_reuseFailAlloc_2655_; 
v_reuseFailAlloc_2655_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2655_, 0, v_str_2644_);
lean_ctor_set(v_reuseFailAlloc_2655_, 1, v___x_2652_);
lean_ctor_set(v_reuseFailAlloc_2655_, 2, v_endExclusive_2646_);
v___x_2654_ = v_reuseFailAlloc_2655_;
goto v_reusejp_2653_;
}
v_reusejp_2653_:
{
return v___x_2654_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___redArg(lean_object* v_s_2660_, lean_object* v_inst_2661_){
_start:
{
lean_object* v_str_2662_; lean_object* v_startInclusive_2663_; lean_object* v_endExclusive_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; lean_object* v___x_2668_; uint8_t v_isShared_2669_; uint8_t v_isSharedCheck_2674_; 
v_str_2662_ = lean_ctor_get(v_s_2660_, 0);
lean_inc_ref(v_str_2662_);
v_startInclusive_2663_ = lean_ctor_get(v_s_2660_, 1);
lean_inc(v_startInclusive_2663_);
v_endExclusive_2664_ = lean_ctor_get(v_s_2660_, 2);
lean_inc(v_endExclusive_2664_);
v___x_2665_ = lean_nat_sub(v_endExclusive_2664_, v_startInclusive_2663_);
v___x_2666_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2660_, v___x_2665_, v_inst_2661_);
v_isSharedCheck_2674_ = !lean_is_exclusive(v_s_2660_);
if (v_isSharedCheck_2674_ == 0)
{
lean_object* v_unused_2675_; lean_object* v_unused_2676_; lean_object* v_unused_2677_; 
v_unused_2675_ = lean_ctor_get(v_s_2660_, 2);
lean_dec(v_unused_2675_);
v_unused_2676_ = lean_ctor_get(v_s_2660_, 1);
lean_dec(v_unused_2676_);
v_unused_2677_ = lean_ctor_get(v_s_2660_, 0);
lean_dec(v_unused_2677_);
v___x_2668_ = v_s_2660_;
v_isShared_2669_ = v_isSharedCheck_2674_;
goto v_resetjp_2667_;
}
else
{
lean_dec(v_s_2660_);
v___x_2668_ = lean_box(0);
v_isShared_2669_ = v_isSharedCheck_2674_;
goto v_resetjp_2667_;
}
v_resetjp_2667_:
{
lean_object* v___x_2670_; lean_object* v___x_2672_; 
v___x_2670_ = lean_nat_add(v_startInclusive_2663_, v___x_2666_);
lean_dec(v___x_2666_);
lean_dec(v_startInclusive_2663_);
if (v_isShared_2669_ == 0)
{
lean_ctor_set(v___x_2668_, 1, v___x_2670_);
v___x_2672_ = v___x_2668_;
goto v_reusejp_2671_;
}
else
{
lean_object* v_reuseFailAlloc_2673_; 
v_reuseFailAlloc_2673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2673_, 0, v_str_2662_);
lean_ctor_set(v_reuseFailAlloc_2673_, 1, v___x_2670_);
lean_ctor_set(v_reuseFailAlloc_2673_, 2, v_endExclusive_2664_);
v___x_2672_ = v_reuseFailAlloc_2673_;
goto v_reusejp_2671_;
}
v_reusejp_2671_:
{
return v___x_2672_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile(lean_object* v_00_u03c1_2678_, lean_object* v_s_2679_, lean_object* v_pat_2680_, lean_object* v_inst_2681_){
_start:
{
lean_object* v_str_2682_; lean_object* v_startInclusive_2683_; lean_object* v_endExclusive_2684_; lean_object* v___x_2685_; lean_object* v___x_2686_; lean_object* v___x_2688_; uint8_t v_isShared_2689_; uint8_t v_isSharedCheck_2694_; 
v_str_2682_ = lean_ctor_get(v_s_2679_, 0);
lean_inc_ref(v_str_2682_);
v_startInclusive_2683_ = lean_ctor_get(v_s_2679_, 1);
lean_inc(v_startInclusive_2683_);
v_endExclusive_2684_ = lean_ctor_get(v_s_2679_, 2);
lean_inc(v_endExclusive_2684_);
v___x_2685_ = lean_nat_sub(v_endExclusive_2684_, v_startInclusive_2683_);
v___x_2686_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2679_, v___x_2685_, v_inst_2681_);
v_isSharedCheck_2694_ = !lean_is_exclusive(v_s_2679_);
if (v_isSharedCheck_2694_ == 0)
{
lean_object* v_unused_2695_; lean_object* v_unused_2696_; lean_object* v_unused_2697_; 
v_unused_2695_ = lean_ctor_get(v_s_2679_, 2);
lean_dec(v_unused_2695_);
v_unused_2696_ = lean_ctor_get(v_s_2679_, 1);
lean_dec(v_unused_2696_);
v_unused_2697_ = lean_ctor_get(v_s_2679_, 0);
lean_dec(v_unused_2697_);
v___x_2688_ = v_s_2679_;
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
else
{
lean_dec(v_s_2679_);
v___x_2688_ = lean_box(0);
v_isShared_2689_ = v_isSharedCheck_2694_;
goto v_resetjp_2687_;
}
v_resetjp_2687_:
{
lean_object* v___x_2690_; lean_object* v___x_2692_; 
v___x_2690_ = lean_nat_add(v_startInclusive_2683_, v___x_2686_);
lean_dec(v___x_2686_);
lean_dec(v_startInclusive_2683_);
if (v_isShared_2689_ == 0)
{
lean_ctor_set(v___x_2688_, 1, v___x_2690_);
v___x_2692_ = v___x_2688_;
goto v_reusejp_2691_;
}
else
{
lean_object* v_reuseFailAlloc_2693_; 
v_reuseFailAlloc_2693_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2693_, 0, v_str_2682_);
lean_ctor_set(v_reuseFailAlloc_2693_, 1, v___x_2690_);
lean_ctor_set(v_reuseFailAlloc_2693_, 2, v_endExclusive_2684_);
v___x_2692_ = v_reuseFailAlloc_2693_;
goto v_reusejp_2691_;
}
v_reusejp_2691_:
{
return v___x_2692_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___boxed(lean_object* v_00_u03c1_2698_, lean_object* v_s_2699_, lean_object* v_pat_2700_, lean_object* v_inst_2701_){
_start:
{
lean_object* v_res_2702_; 
v_res_2702_ = l_String_Slice_takeEndWhile(v_00_u03c1_2698_, v_s_2699_, v_pat_2700_, v_inst_2701_);
lean_dec(v_pat_2700_);
return v_res_2702_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___redArg(lean_object* v_inst_2703_, lean_object* v_s_2704_, lean_object* v_inst_2705_){
_start:
{
lean_object* v___f_2706_; lean_object* v_searcher_2707_; lean_object* v___x_2708_; lean_object* v___f_2709_; lean_object* v___x_2710_; 
v___f_2706_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_2704_);
v_searcher_2707_ = lean_apply_1(v_inst_2705_, v_s_2704_);
v___x_2708_ = lean_box(0);
v___f_2709_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_2710_ = lean_apply_7(v_inst_2703_, v_s_2704_, v___f_2706_, lean_box(0), lean_box(0), v_searcher_2707_, v___x_2708_, v___f_2709_);
return v___x_2710_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f(lean_object* v_00_u03c3_2711_, lean_object* v_inst_2712_, lean_object* v_inst_2713_, lean_object* v_00_u03c1_2714_, lean_object* v_s_2715_, lean_object* v_pat_2716_, lean_object* v_inst_2717_){
_start:
{
lean_object* v___x_2718_; 
v___x_2718_ = l_String_Slice_revFind_x3f___redArg(v_inst_2713_, v_s_2715_, v_inst_2717_);
return v___x_2718_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___boxed(lean_object* v_00_u03c3_2719_, lean_object* v_inst_2720_, lean_object* v_inst_2721_, lean_object* v_00_u03c1_2722_, lean_object* v_s_2723_, lean_object* v_pat_2724_, lean_object* v_inst_2725_){
_start:
{
lean_object* v_res_2726_; 
v_res_2726_ = l_String_Slice_revFind_x3f(v_00_u03c3_2719_, v_inst_2720_, v_inst_2721_, v_00_u03c1_2722_, v_s_2723_, v_pat_2724_, v_inst_2725_);
lean_dec(v_pat_2724_);
lean_dec(v_inst_2720_);
return v_res_2726_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(lean_object* v_s_2727_, lean_object* v_pos_2728_){
_start:
{
lean_object* v_str_2729_; lean_object* v_startInclusive_2730_; lean_object* v_endExclusive_2731_; lean_object* v___x_2732_; uint8_t v___y_2740_; lean_object* v___x_2741_; lean_object* v___x_2742_; uint8_t v___x_2743_; 
v_str_2729_ = lean_ctor_get(v_s_2727_, 0);
v_startInclusive_2730_ = lean_ctor_get(v_s_2727_, 1);
v_endExclusive_2731_ = lean_ctor_get(v_s_2727_, 2);
v___x_2732_ = lean_nat_add(v_startInclusive_2730_, v_pos_2728_);
v___x_2741_ = lean_unsigned_to_nat(0u);
v___x_2742_ = lean_nat_sub(v_endExclusive_2731_, v___x_2732_);
v___x_2743_ = lean_nat_dec_eq(v___x_2741_, v___x_2742_);
lean_dec(v___x_2742_);
if (v___x_2743_ == 0)
{
uint32_t v___x_2744_; uint8_t v___y_2746_; uint32_t v___x_2751_; uint8_t v___x_2752_; 
v___x_2744_ = lean_string_utf8_get_fast(v_str_2729_, v___x_2732_);
v___x_2751_ = 32;
v___x_2752_ = lean_uint32_dec_eq(v___x_2744_, v___x_2751_);
if (v___x_2752_ == 0)
{
uint32_t v___x_2753_; uint8_t v___x_2754_; 
v___x_2753_ = 9;
v___x_2754_ = lean_uint32_dec_eq(v___x_2744_, v___x_2753_);
v___y_2746_ = v___x_2754_;
goto v___jp_2745_;
}
else
{
v___y_2746_ = v___x_2752_;
goto v___jp_2745_;
}
v___jp_2745_:
{
if (v___y_2746_ == 0)
{
uint32_t v___x_2747_; uint8_t v___x_2748_; 
v___x_2747_ = 13;
v___x_2748_ = lean_uint32_dec_eq(v___x_2744_, v___x_2747_);
if (v___x_2748_ == 0)
{
uint32_t v___x_2749_; uint8_t v___x_2750_; 
v___x_2749_ = 10;
v___x_2750_ = lean_uint32_dec_eq(v___x_2744_, v___x_2749_);
v___y_2740_ = v___x_2750_;
goto v___jp_2739_;
}
else
{
v___y_2740_ = v___x_2748_;
goto v___jp_2739_;
}
}
else
{
goto v___jp_2733_;
}
}
}
else
{
lean_dec(v___x_2732_);
return v_pos_2728_;
}
v___jp_2733_:
{
lean_object* v___x_2734_; lean_object* v___x_2735_; lean_object* v___x_2736_; uint8_t v___x_2737_; 
v___x_2734_ = lean_string_utf8_next_fast(v_str_2729_, v___x_2732_);
v___x_2735_ = lean_nat_sub(v___x_2734_, v___x_2732_);
lean_dec(v___x_2732_);
v___x_2736_ = lean_nat_add(v_pos_2728_, v___x_2735_);
lean_dec(v___x_2735_);
v___x_2737_ = lean_nat_dec_lt(v_pos_2728_, v___x_2736_);
if (v___x_2737_ == 0)
{
lean_dec(v___x_2736_);
return v_pos_2728_;
}
else
{
lean_dec(v_pos_2728_);
v_pos_2728_ = v___x_2736_;
goto _start;
}
}
v___jp_2739_:
{
if (v___y_2740_ == 0)
{
lean_dec(v___x_2732_);
return v_pos_2728_;
}
else
{
goto v___jp_2733_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0___boxed(lean_object* v_s_2755_, lean_object* v_pos_2756_){
_start:
{
lean_object* v_res_2757_; 
v_res_2757_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2755_, v_pos_2756_);
lean_dec_ref(v_s_2755_);
return v_res_2757_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(lean_object* v_s_2758_, lean_object* v_pos_2759_){
_start:
{
lean_object* v_str_2760_; lean_object* v_startInclusive_2761_; lean_object* v___x_2762_; lean_object* v___x_2763_; lean_object* v___x_2764_; uint8_t v___x_2765_; 
v_str_2760_ = lean_ctor_get(v_s_2758_, 0);
v_startInclusive_2761_ = lean_ctor_get(v_s_2758_, 1);
v___x_2762_ = lean_nat_add(v_startInclusive_2761_, v_pos_2759_);
v___x_2763_ = lean_nat_sub(v___x_2762_, v_startInclusive_2761_);
v___x_2764_ = lean_unsigned_to_nat(0u);
v___x_2765_ = lean_nat_dec_eq(v___x_2763_, v___x_2764_);
if (v___x_2765_ == 0)
{
lean_object* v___x_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2769_; uint8_t v___y_2774_; lean_object* v___x_2775_; uint32_t v___x_2776_; uint8_t v___y_2778_; uint32_t v___x_2783_; uint8_t v___x_2784_; 
lean_inc(v_startInclusive_2761_);
lean_inc_ref(v_str_2760_);
v___x_2766_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2766_, 0, v_str_2760_);
lean_ctor_set(v___x_2766_, 1, v_startInclusive_2761_);
lean_ctor_set(v___x_2766_, 2, v___x_2762_);
v___x_2767_ = lean_unsigned_to_nat(1u);
v___x_2768_ = lean_nat_sub(v___x_2763_, v___x_2767_);
lean_dec(v___x_2763_);
v___x_2769_ = l_String_Slice_posLE(v___x_2766_, v___x_2768_);
lean_dec_ref(v___x_2766_);
v___x_2775_ = lean_nat_add(v_startInclusive_2761_, v___x_2769_);
v___x_2776_ = lean_string_utf8_get_fast(v_str_2760_, v___x_2775_);
lean_dec(v___x_2775_);
v___x_2783_ = 32;
v___x_2784_ = lean_uint32_dec_eq(v___x_2776_, v___x_2783_);
if (v___x_2784_ == 0)
{
uint32_t v___x_2785_; uint8_t v___x_2786_; 
v___x_2785_ = 9;
v___x_2786_ = lean_uint32_dec_eq(v___x_2776_, v___x_2785_);
v___y_2778_ = v___x_2786_;
goto v___jp_2777_;
}
else
{
v___y_2778_ = v___x_2784_;
goto v___jp_2777_;
}
v___jp_2770_:
{
uint8_t v___x_2771_; 
v___x_2771_ = lean_nat_dec_lt(v___x_2769_, v_pos_2759_);
if (v___x_2771_ == 0)
{
lean_dec(v___x_2769_);
return v_pos_2759_;
}
else
{
lean_dec(v_pos_2759_);
v_pos_2759_ = v___x_2769_;
goto _start;
}
}
v___jp_2773_:
{
if (v___y_2774_ == 0)
{
lean_dec(v___x_2769_);
return v_pos_2759_;
}
else
{
goto v___jp_2770_;
}
}
v___jp_2777_:
{
if (v___y_2778_ == 0)
{
uint32_t v___x_2779_; uint8_t v___x_2780_; 
v___x_2779_ = 13;
v___x_2780_ = lean_uint32_dec_eq(v___x_2776_, v___x_2779_);
if (v___x_2780_ == 0)
{
uint32_t v___x_2781_; uint8_t v___x_2782_; 
v___x_2781_ = 10;
v___x_2782_ = lean_uint32_dec_eq(v___x_2776_, v___x_2781_);
v___y_2774_ = v___x_2782_;
goto v___jp_2773_;
}
else
{
v___y_2774_ = v___x_2780_;
goto v___jp_2773_;
}
}
else
{
goto v___jp_2770_;
}
}
}
else
{
lean_dec(v___x_2763_);
lean_dec(v___x_2762_);
return v_pos_2759_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1___boxed(lean_object* v_s_2787_, lean_object* v_pos_2788_){
_start:
{
lean_object* v_res_2789_; 
v_res_2789_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v_s_2787_, v_pos_2788_);
lean_dec_ref(v_s_2787_);
return v_res_2789_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAscii(lean_object* v_s_2790_){
_start:
{
lean_object* v_str_2791_; lean_object* v_startInclusive_2792_; lean_object* v_endExclusive_2793_; lean_object* v___x_2794_; lean_object* v___x_2795_; lean_object* v___x_2797_; uint8_t v_isShared_2798_; uint8_t v_isSharedCheck_2807_; 
v_str_2791_ = lean_ctor_get(v_s_2790_, 0);
lean_inc_ref(v_str_2791_);
v_startInclusive_2792_ = lean_ctor_get(v_s_2790_, 1);
lean_inc(v_startInclusive_2792_);
v_endExclusive_2793_ = lean_ctor_get(v_s_2790_, 2);
lean_inc(v_endExclusive_2793_);
v___x_2794_ = lean_unsigned_to_nat(0u);
v___x_2795_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2790_, v___x_2794_);
v_isSharedCheck_2807_ = !lean_is_exclusive(v_s_2790_);
if (v_isSharedCheck_2807_ == 0)
{
lean_object* v_unused_2808_; lean_object* v_unused_2809_; lean_object* v_unused_2810_; 
v_unused_2808_ = lean_ctor_get(v_s_2790_, 2);
lean_dec(v_unused_2808_);
v_unused_2809_ = lean_ctor_get(v_s_2790_, 1);
lean_dec(v_unused_2809_);
v_unused_2810_ = lean_ctor_get(v_s_2790_, 0);
lean_dec(v_unused_2810_);
v___x_2797_ = v_s_2790_;
v_isShared_2798_ = v_isSharedCheck_2807_;
goto v_resetjp_2796_;
}
else
{
lean_dec(v_s_2790_);
v___x_2797_ = lean_box(0);
v_isShared_2798_ = v_isSharedCheck_2807_;
goto v_resetjp_2796_;
}
v_resetjp_2796_:
{
lean_object* v___x_2799_; lean_object* v___x_2801_; 
v___x_2799_ = lean_nat_add(v_startInclusive_2792_, v___x_2795_);
lean_dec(v___x_2795_);
lean_dec(v_startInclusive_2792_);
lean_inc(v_endExclusive_2793_);
lean_inc(v___x_2799_);
lean_inc_ref(v_str_2791_);
if (v_isShared_2798_ == 0)
{
lean_ctor_set(v___x_2797_, 1, v___x_2799_);
v___x_2801_ = v___x_2797_;
goto v_reusejp_2800_;
}
else
{
lean_object* v_reuseFailAlloc_2806_; 
v_reuseFailAlloc_2806_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2806_, 0, v_str_2791_);
lean_ctor_set(v_reuseFailAlloc_2806_, 1, v___x_2799_);
lean_ctor_set(v_reuseFailAlloc_2806_, 2, v_endExclusive_2793_);
v___x_2801_ = v_reuseFailAlloc_2806_;
goto v_reusejp_2800_;
}
v_reusejp_2800_:
{
lean_object* v___x_2802_; lean_object* v___x_2803_; lean_object* v___x_2804_; lean_object* v___x_2805_; 
v___x_2802_ = lean_nat_sub(v_endExclusive_2793_, v___x_2799_);
lean_dec(v_endExclusive_2793_);
v___x_2803_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v___x_2801_, v___x_2802_);
lean_dec_ref(v___x_2801_);
v___x_2804_ = lean_nat_add(v___x_2799_, v___x_2803_);
lean_dec(v___x_2803_);
v___x_2805_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2805_, 0, v_str_2791_);
lean_ctor_set(v___x_2805_, 1, v___x_2799_);
lean_ctor_set(v___x_2805_, 2, v___x_2804_);
return v___x_2805_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(lean_object* v_s1_2811_, lean_object* v_s1Curr_2812_, lean_object* v_s2_2813_, lean_object* v_s2Curr_2814_){
_start:
{
uint8_t v___y_2816_; uint8_t v___y_2817_; uint8_t v___y_2824_; uint8_t v___y_2825_; uint8_t v___y_2826_; lean_object* v_str_2829_; lean_object* v_startInclusive_2830_; lean_object* v_endExclusive_2831_; lean_object* v___x_2832_; uint8_t v___x_2839_; 
v_str_2829_ = lean_ctor_get(v_s1_2811_, 0);
v_startInclusive_2830_ = lean_ctor_get(v_s1_2811_, 1);
v_endExclusive_2831_ = lean_ctor_get(v_s1_2811_, 2);
v___x_2832_ = lean_nat_sub(v_endExclusive_2831_, v_startInclusive_2830_);
v___x_2839_ = lean_nat_dec_lt(v_s1Curr_2812_, v___x_2832_);
if (v___x_2839_ == 0)
{
goto v___jp_2833_;
}
else
{
lean_object* v_str_2840_; lean_object* v_startInclusive_2841_; lean_object* v_endExclusive_2842_; uint8_t v___y_2844_; lean_object* v___x_2851_; uint8_t v___x_2852_; 
v_str_2840_ = lean_ctor_get(v_s2_2813_, 0);
v_startInclusive_2841_ = lean_ctor_get(v_s2_2813_, 1);
v_endExclusive_2842_ = lean_ctor_get(v_s2_2813_, 2);
v___x_2851_ = lean_nat_sub(v_endExclusive_2842_, v_startInclusive_2841_);
v___x_2852_ = lean_nat_dec_lt(v_s2Curr_2814_, v___x_2851_);
lean_dec(v___x_2851_);
if (v___x_2852_ == 0)
{
goto v___jp_2833_;
}
else
{
lean_object* v___x_2853_; uint8_t v___x_2854_; uint8_t v___y_2856_; uint8_t v___x_2859_; uint8_t v___x_2860_; 
lean_dec(v___x_2832_);
v___x_2853_ = lean_nat_add(v_startInclusive_2830_, v_s1Curr_2812_);
v___x_2854_ = lean_string_get_byte_fast(v_str_2829_, v___x_2853_);
v___x_2859_ = 65;
v___x_2860_ = lean_uint8_dec_le(v___x_2859_, v___x_2854_);
if (v___x_2860_ == 0)
{
v___y_2856_ = v___x_2860_;
goto v___jp_2855_;
}
else
{
uint8_t v___x_2861_; uint8_t v___x_2862_; 
v___x_2861_ = 90;
v___x_2862_ = lean_uint8_dec_le(v___x_2854_, v___x_2861_);
v___y_2856_ = v___x_2862_;
goto v___jp_2855_;
}
v___jp_2855_:
{
if (v___y_2856_ == 0)
{
v___y_2844_ = v___x_2854_;
goto v___jp_2843_;
}
else
{
uint8_t v___x_2857_; uint8_t v___x_2858_; 
v___x_2857_ = 32;
v___x_2858_ = lean_uint8_add(v___x_2854_, v___x_2857_);
v___y_2844_ = v___x_2858_;
goto v___jp_2843_;
}
}
}
v___jp_2843_:
{
lean_object* v___x_2845_; uint8_t v___x_2846_; uint8_t v___x_2847_; uint8_t v___x_2848_; 
v___x_2845_ = lean_nat_add(v_startInclusive_2841_, v_s2Curr_2814_);
v___x_2846_ = lean_string_get_byte_fast(v_str_2840_, v___x_2845_);
v___x_2847_ = 65;
v___x_2848_ = lean_uint8_dec_le(v___x_2847_, v___x_2846_);
if (v___x_2848_ == 0)
{
v___y_2824_ = v___y_2844_;
v___y_2825_ = v___x_2846_;
v___y_2826_ = v___x_2848_;
goto v___jp_2823_;
}
else
{
uint8_t v___x_2849_; uint8_t v___x_2850_; 
v___x_2849_ = 90;
v___x_2850_ = lean_uint8_dec_le(v___x_2846_, v___x_2849_);
v___y_2824_ = v___y_2844_;
v___y_2825_ = v___x_2846_;
v___y_2826_ = v___x_2850_;
goto v___jp_2823_;
}
}
}
v___jp_2815_:
{
uint8_t v___x_2818_; 
v___x_2818_ = lean_uint8_dec_eq(v___y_2816_, v___y_2817_);
if (v___x_2818_ == 0)
{
lean_dec(v_s2Curr_2814_);
lean_dec(v_s1Curr_2812_);
return v___x_2818_;
}
else
{
lean_object* v___x_2819_; lean_object* v___x_2820_; lean_object* v___x_2821_; 
v___x_2819_ = lean_unsigned_to_nat(1u);
v___x_2820_ = lean_nat_add(v_s1Curr_2812_, v___x_2819_);
lean_dec(v_s1Curr_2812_);
v___x_2821_ = lean_nat_add(v_s2Curr_2814_, v___x_2819_);
lean_dec(v_s2Curr_2814_);
v_s1Curr_2812_ = v___x_2820_;
v_s2Curr_2814_ = v___x_2821_;
goto _start;
}
}
v___jp_2823_:
{
if (v___y_2826_ == 0)
{
v___y_2816_ = v___y_2824_;
v___y_2817_ = v___y_2825_;
goto v___jp_2815_;
}
else
{
uint8_t v___x_2827_; uint8_t v___x_2828_; 
v___x_2827_ = 32;
v___x_2828_ = lean_uint8_add(v___y_2825_, v___x_2827_);
v___y_2816_ = v___y_2824_;
v___y_2817_ = v___x_2828_;
goto v___jp_2815_;
}
}
v___jp_2833_:
{
uint8_t v___x_2834_; 
v___x_2834_ = lean_nat_dec_eq(v_s1Curr_2812_, v___x_2832_);
lean_dec(v___x_2832_);
lean_dec(v_s1Curr_2812_);
if (v___x_2834_ == 0)
{
lean_dec(v_s2Curr_2814_);
return v___x_2834_;
}
else
{
lean_object* v_startInclusive_2835_; lean_object* v_endExclusive_2836_; lean_object* v___x_2837_; uint8_t v___x_2838_; 
v_startInclusive_2835_ = lean_ctor_get(v_s2_2813_, 1);
v_endExclusive_2836_ = lean_ctor_get(v_s2_2813_, 2);
v___x_2837_ = lean_nat_sub(v_endExclusive_2836_, v_startInclusive_2835_);
v___x_2838_ = lean_nat_dec_eq(v_s2Curr_2814_, v___x_2837_);
lean_dec(v___x_2837_);
lean_dec(v_s2Curr_2814_);
return v___x_2838_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object* v_s1_2863_, lean_object* v_s1Curr_2864_, lean_object* v_s2_2865_, lean_object* v_s2Curr_2866_){
_start:
{
uint8_t v_res_2867_; lean_object* v_r_2868_; 
v_res_2867_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_2863_, v_s1Curr_2864_, v_s2_2865_, v_s2Curr_2866_);
lean_dec_ref(v_s2_2865_);
lean_dec_ref(v_s1_2863_);
v_r_2868_ = lean_box(v_res_2867_);
return v_r_2868_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object* v_s1_2869_, lean_object* v_s2_2870_){
_start:
{
lean_object* v_startInclusive_2871_; lean_object* v_endExclusive_2872_; lean_object* v_startInclusive_2873_; lean_object* v_endExclusive_2874_; lean_object* v___x_2875_; lean_object* v___x_2876_; uint8_t v___x_2877_; 
v_startInclusive_2871_ = lean_ctor_get(v_s1_2869_, 1);
v_endExclusive_2872_ = lean_ctor_get(v_s1_2869_, 2);
v_startInclusive_2873_ = lean_ctor_get(v_s2_2870_, 1);
v_endExclusive_2874_ = lean_ctor_get(v_s2_2870_, 2);
v___x_2875_ = lean_nat_sub(v_endExclusive_2872_, v_startInclusive_2871_);
v___x_2876_ = lean_nat_sub(v_endExclusive_2874_, v_startInclusive_2873_);
v___x_2877_ = lean_nat_dec_eq(v___x_2875_, v___x_2876_);
lean_dec(v___x_2876_);
lean_dec(v___x_2875_);
if (v___x_2877_ == 0)
{
return v___x_2877_;
}
else
{
lean_object* v___x_2878_; uint8_t v___x_2879_; 
v___x_2878_ = lean_unsigned_to_nat(0u);
v___x_2879_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_2869_, v___x_2878_, v_s2_2870_, v___x_2878_);
return v___x_2879_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object* v_s1_2880_, lean_object* v_s2_2881_){
_start:
{
uint8_t v_res_2882_; lean_object* v_r_2883_; 
v_res_2882_ = l_String_Slice_eqIgnoreAsciiCase(v_s1_2880_, v_s2_2881_);
lean_dec_ref(v_s2_2881_);
lean_dec_ref(v_s1_2880_);
v_r_2883_ = lean_box(v_res_2882_);
return v_r_2883_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines_lineMap(lean_object* v_s_2884_){
_start:
{
lean_object* v_str_2885_; lean_object* v_startInclusive_2886_; lean_object* v_endExclusive_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; uint8_t v___x_2890_; 
v_str_2885_ = lean_ctor_get(v_s_2884_, 0);
v_startInclusive_2886_ = lean_ctor_get(v_s_2884_, 1);
v_endExclusive_2887_ = lean_ctor_get(v_s_2884_, 2);
v___x_2888_ = lean_nat_sub(v_endExclusive_2887_, v_startInclusive_2886_);
v___x_2889_ = lean_unsigned_to_nat(0u);
v___x_2890_ = lean_nat_dec_eq(v___x_2888_, v___x_2889_);
if (v___x_2890_ == 0)
{
uint32_t v___x_2891_; lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; uint32_t v___x_2896_; uint8_t v___x_2897_; 
v___x_2891_ = 10;
v___x_2892_ = lean_unsigned_to_nat(1u);
v___x_2893_ = lean_nat_sub(v___x_2888_, v___x_2892_);
lean_dec(v___x_2888_);
v___x_2894_ = l_String_Slice_posLE(v_s_2884_, v___x_2893_);
v___x_2895_ = lean_nat_add(v_startInclusive_2886_, v___x_2894_);
lean_dec(v___x_2894_);
v___x_2896_ = lean_string_utf8_get_fast(v_str_2885_, v___x_2895_);
v___x_2897_ = lean_uint32_dec_eq(v___x_2896_, v___x_2891_);
if (v___x_2897_ == 0)
{
lean_dec(v___x_2895_);
return v_s_2884_;
}
else
{
lean_object* v___x_2899_; uint8_t v_isShared_2900_; uint8_t v_isSharedCheck_2913_; 
lean_inc(v_startInclusive_2886_);
lean_inc_ref(v_str_2885_);
v_isSharedCheck_2913_ = !lean_is_exclusive(v_s_2884_);
if (v_isSharedCheck_2913_ == 0)
{
lean_object* v_unused_2914_; lean_object* v_unused_2915_; lean_object* v_unused_2916_; 
v_unused_2914_ = lean_ctor_get(v_s_2884_, 2);
lean_dec(v_unused_2914_);
v_unused_2915_ = lean_ctor_get(v_s_2884_, 1);
lean_dec(v_unused_2915_);
v_unused_2916_ = lean_ctor_get(v_s_2884_, 0);
lean_dec(v_unused_2916_);
v___x_2899_ = v_s_2884_;
v_isShared_2900_ = v_isSharedCheck_2913_;
goto v_resetjp_2898_;
}
else
{
lean_dec(v_s_2884_);
v___x_2899_ = lean_box(0);
v_isShared_2900_ = v_isSharedCheck_2913_;
goto v_resetjp_2898_;
}
v_resetjp_2898_:
{
lean_object* v___x_2902_; 
lean_inc(v___x_2895_);
lean_inc(v_startInclusive_2886_);
lean_inc_ref(v_str_2885_);
if (v_isShared_2900_ == 0)
{
lean_ctor_set(v___x_2899_, 2, v___x_2895_);
v___x_2902_ = v___x_2899_;
goto v_reusejp_2901_;
}
else
{
lean_object* v_reuseFailAlloc_2912_; 
v_reuseFailAlloc_2912_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2912_, 0, v_str_2885_);
lean_ctor_set(v_reuseFailAlloc_2912_, 1, v_startInclusive_2886_);
lean_ctor_set(v_reuseFailAlloc_2912_, 2, v___x_2895_);
v___x_2902_ = v_reuseFailAlloc_2912_;
goto v_reusejp_2901_;
}
v_reusejp_2901_:
{
lean_object* v___x_2903_; uint8_t v___x_2904_; 
v___x_2903_ = lean_nat_sub(v___x_2895_, v_startInclusive_2886_);
lean_dec(v___x_2895_);
v___x_2904_ = lean_nat_dec_eq(v___x_2903_, v___x_2889_);
if (v___x_2904_ == 0)
{
uint32_t v___x_2905_; lean_object* v___x_2906_; lean_object* v___x_2907_; lean_object* v___x_2908_; uint32_t v___x_2909_; uint8_t v___x_2910_; 
v___x_2905_ = 13;
v___x_2906_ = lean_nat_sub(v___x_2903_, v___x_2892_);
lean_dec(v___x_2903_);
v___x_2907_ = l_String_Slice_posLE(v___x_2902_, v___x_2906_);
v___x_2908_ = lean_nat_add(v_startInclusive_2886_, v___x_2907_);
lean_dec(v___x_2907_);
v___x_2909_ = lean_string_utf8_get_fast(v_str_2885_, v___x_2908_);
v___x_2910_ = lean_uint32_dec_eq(v___x_2909_, v___x_2905_);
if (v___x_2910_ == 0)
{
lean_dec(v___x_2908_);
lean_dec(v_startInclusive_2886_);
lean_dec_ref(v_str_2885_);
return v___x_2902_;
}
else
{
lean_object* v___x_2911_; 
lean_dec_ref(v___x_2902_);
v___x_2911_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2911_, 0, v_str_2885_);
lean_ctor_set(v___x_2911_, 1, v_startInclusive_2886_);
lean_ctor_set(v___x_2911_, 2, v___x_2908_);
return v___x_2911_;
}
}
else
{
lean_dec(v___x_2903_);
lean_dec(v_startInclusive_2886_);
lean_dec_ref(v_str_2885_);
return v___x_2902_;
}
}
}
}
}
else
{
lean_dec(v___x_2888_);
return v_s_2884_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(lean_object* v_s_2919_){
_start:
{
lean_object* v___x_2920_; 
v___x_2920_ = ((lean_object*)(l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0));
return v___x_2920_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(lean_object* v_s_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_2921_);
lean_dec_ref(v_s_2921_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines(lean_object* v_s_2923_){
_start:
{
lean_object* v___x_2924_; 
v___x_2924_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_2923_);
return v___x_2924_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines___boxed(lean_object* v_s_2925_){
_start:
{
lean_object* v_res_2926_; 
v_res_2926_ = l_String_Slice_lines(v_s_2925_);
lean_dec_ref(v_s_2925_);
return v_res_2926_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___lam__0(lean_object* v_s_2927_, uint8_t v_lastWasDigit_2928_, lean_object* v___x_2929_, lean_object* v___x_2930_, lean_object* v_it_2931_, lean_object* v_acc_2932_, lean_object* v_hP_2933_, lean_object* v_recur_2934_){
_start:
{
lean_object* v_str_2935_; lean_object* v_startInclusive_2936_; lean_object* v_endExclusive_2937_; lean_object* v___x_2938_; uint8_t v___x_2939_; 
v_str_2935_ = lean_ctor_get(v_s_2927_, 0);
v_startInclusive_2936_ = lean_ctor_get(v_s_2927_, 1);
v_endExclusive_2937_ = lean_ctor_get(v_s_2927_, 2);
v___x_2938_ = lean_nat_sub(v_endExclusive_2937_, v_startInclusive_2936_);
v___x_2939_ = lean_nat_dec_eq(v_it_2931_, v___x_2938_);
lean_dec(v___x_2938_);
if (v___x_2939_ == 0)
{
lean_object* v_snd_2940_; lean_object* v___x_2942_; uint8_t v_isShared_2943_; uint8_t v_isSharedCheck_2971_; 
v_snd_2940_ = lean_ctor_get(v_acc_2932_, 1);
v_isSharedCheck_2971_ = !lean_is_exclusive(v_acc_2932_);
if (v_isSharedCheck_2971_ == 0)
{
lean_object* v_unused_2972_; 
v_unused_2972_ = lean_ctor_get(v_acc_2932_, 0);
lean_dec(v_unused_2972_);
v___x_2942_ = v_acc_2932_;
v_isShared_2943_ = v_isSharedCheck_2971_;
goto v_resetjp_2941_;
}
else
{
lean_inc(v_snd_2940_);
lean_dec(v_acc_2932_);
v___x_2942_ = lean_box(0);
v_isShared_2943_ = v_isSharedCheck_2971_;
goto v_resetjp_2941_;
}
v_resetjp_2941_:
{
lean_object* v___x_2944_; lean_object* v___x_2945_; lean_object* v___x_2946_; uint8_t v___y_2948_; uint32_t v___x_2959_; uint32_t v___x_2960_; uint8_t v___x_2961_; 
v___x_2944_ = lean_nat_add(v_startInclusive_2936_, v_it_2931_);
v___x_2945_ = lean_string_utf8_next_fast(v_str_2935_, v___x_2944_);
v___x_2946_ = lean_nat_sub(v___x_2945_, v_startInclusive_2936_);
v___x_2959_ = lean_string_utf8_get_fast(v_str_2935_, v___x_2944_);
lean_dec(v___x_2944_);
v___x_2960_ = 95;
v___x_2961_ = lean_uint32_dec_eq(v___x_2959_, v___x_2960_);
if (v___x_2961_ == 0)
{
uint32_t v___x_2962_; uint8_t v___x_2963_; 
lean_dec_ref(v___x_2930_);
v___x_2962_ = 48;
v___x_2963_ = lean_uint32_dec_le(v___x_2962_, v___x_2959_);
if (v___x_2963_ == 0)
{
v___y_2948_ = v___x_2963_;
goto v___jp_2947_;
}
else
{
uint32_t v___x_2964_; uint8_t v___x_2965_; 
v___x_2964_ = 57;
v___x_2965_ = lean_uint32_dec_le(v___x_2959_, v___x_2964_);
v___y_2948_ = v___x_2965_;
goto v___jp_2947_;
}
}
else
{
uint8_t v___x_2966_; 
lean_del_object(v___x_2942_);
lean_dec(v___x_2929_);
v___x_2966_ = lean_unbox(v_snd_2940_);
if (v___x_2966_ == 0)
{
lean_object* v___x_2967_; lean_object* v___x_2968_; lean_object* v___x_2969_; 
lean_dec(v___x_2946_);
lean_dec_ref(v_recur_2934_);
lean_dec_ref(v___x_2930_);
v___x_2967_ = lean_box(v_lastWasDigit_2928_);
v___x_2968_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2968_, 0, v___x_2967_);
v___x_2969_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2969_, 0, v___x_2968_);
lean_ctor_set(v___x_2969_, 1, v_snd_2940_);
return v___x_2969_;
}
else
{
lean_object* v___x_2970_; 
lean_dec(v_snd_2940_);
v___x_2970_ = lean_apply_4(v_recur_2934_, v___x_2946_, v___x_2930_, lean_box(0), lean_box(0));
return v___x_2970_;
}
}
v___jp_2947_:
{
if (v___y_2948_ == 0)
{
lean_object* v___x_2949_; lean_object* v___x_2950_; lean_object* v___x_2952_; 
lean_dec(v___x_2946_);
lean_dec_ref(v_recur_2934_);
lean_dec(v___x_2929_);
v___x_2949_ = lean_box(v_lastWasDigit_2928_);
v___x_2950_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2950_, 0, v___x_2949_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 0, v___x_2950_);
v___x_2952_ = v___x_2942_;
goto v_reusejp_2951_;
}
else
{
lean_object* v_reuseFailAlloc_2953_; 
v_reuseFailAlloc_2953_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2953_, 0, v___x_2950_);
lean_ctor_set(v_reuseFailAlloc_2953_, 1, v_snd_2940_);
v___x_2952_ = v_reuseFailAlloc_2953_;
goto v_reusejp_2951_;
}
v_reusejp_2951_:
{
return v___x_2952_;
}
}
else
{
lean_object* v___x_2954_; lean_object* v___x_2956_; 
lean_dec(v_snd_2940_);
v___x_2954_ = lean_box(v___y_2948_);
if (v_isShared_2943_ == 0)
{
lean_ctor_set(v___x_2942_, 1, v___x_2954_);
lean_ctor_set(v___x_2942_, 0, v___x_2929_);
v___x_2956_ = v___x_2942_;
goto v_reusejp_2955_;
}
else
{
lean_object* v_reuseFailAlloc_2958_; 
v_reuseFailAlloc_2958_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2958_, 0, v___x_2929_);
lean_ctor_set(v_reuseFailAlloc_2958_, 1, v___x_2954_);
v___x_2956_ = v_reuseFailAlloc_2958_;
goto v_reusejp_2955_;
}
v_reusejp_2955_:
{
lean_object* v___x_2957_; 
v___x_2957_ = lean_apply_4(v_recur_2934_, v___x_2946_, v___x_2956_, lean_box(0), lean_box(0));
return v___x_2957_;
}
}
}
}
}
else
{
lean_dec_ref(v_recur_2934_);
lean_dec_ref(v___x_2930_);
lean_dec(v___x_2929_);
return v_acc_2932_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___lam__0___boxed(lean_object* v_s_2973_, lean_object* v_lastWasDigit_2974_, lean_object* v___x_2975_, lean_object* v___x_2976_, lean_object* v_it_2977_, lean_object* v_acc_2978_, lean_object* v_hP_2979_, lean_object* v_recur_2980_){
_start:
{
uint8_t v_lastWasDigit_boxed_2981_; lean_object* v_res_2982_; 
v_lastWasDigit_boxed_2981_ = lean_unbox(v_lastWasDigit_2974_);
v_res_2982_ = l_String_Slice_isNat___lam__0(v_s_2973_, v_lastWasDigit_boxed_2981_, v___x_2975_, v___x_2976_, v_it_2977_, v_acc_2978_, v_hP_2979_, v_recur_2980_);
lean_dec(v_it_2977_);
lean_dec_ref(v_s_2973_);
return v_res_2982_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isNat(lean_object* v_s_2987_){
_start:
{
uint8_t v_lastWasDigit_2988_; lean_object* v___x_2989_; lean_object* v___x_2990_; lean_object* v___x_2991_; lean_object* v___f_2992_; lean_object* v___x_2993_; lean_object* v___x_2994_; lean_object* v_fst_2995_; 
v_lastWasDigit_2988_ = 0;
v___x_2989_ = lean_box(0);
v___x_2990_ = ((lean_object*)(l_String_Slice_isNat___closed__0));
v___x_2991_ = lean_box(v_lastWasDigit_2988_);
lean_inc_ref(v_s_2987_);
v___f_2992_ = lean_alloc_closure((void*)(l_String_Slice_isNat___lam__0___boxed), 8, 4);
lean_closure_set(v___f_2992_, 0, v_s_2987_);
lean_closure_set(v___f_2992_, 1, v___x_2991_);
lean_closure_set(v___f_2992_, 2, v___x_2989_);
lean_closure_set(v___f_2992_, 3, v___x_2990_);
v___x_2993_ = l_String_Slice_positions(v_s_2987_);
lean_dec_ref(v_s_2987_);
v___x_2994_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2992_, v___x_2993_, v___x_2990_, lean_box(0));
v_fst_2995_ = lean_ctor_get(v___x_2994_, 0);
lean_inc(v_fst_2995_);
if (lean_obj_tag(v_fst_2995_) == 0)
{
lean_object* v_snd_2996_; uint8_t v___x_2997_; 
v_snd_2996_ = lean_ctor_get(v___x_2994_, 1);
lean_inc(v_snd_2996_);
lean_dec(v___x_2994_);
v___x_2997_ = lean_unbox(v_snd_2996_);
lean_dec(v_snd_2996_);
return v___x_2997_;
}
else
{
lean_object* v_val_2998_; uint8_t v___x_2999_; 
lean_dec(v___x_2994_);
v_val_2998_ = lean_ctor_get(v_fst_2995_, 0);
lean_inc(v_val_2998_);
lean_dec_ref(v_fst_2995_);
v___x_2999_ = lean_unbox(v_val_2998_);
lean_dec(v_val_2998_);
return v___x_2999_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object* v_s_3000_){
_start:
{
uint8_t v_res_3001_; lean_object* v_r_3002_; 
v_res_3001_ = l_String_Slice_isNat(v_s_3000_);
v_r_3002_ = lean_box(v_res_3001_);
return v_r_3002_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object* v_s_3003_, lean_object* v_a_3004_, lean_object* v_b_3005_){
_start:
{
lean_object* v_str_3006_; lean_object* v_startInclusive_3007_; lean_object* v_endExclusive_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v_str_3006_ = lean_ctor_get(v_s_3003_, 0);
v_startInclusive_3007_ = lean_ctor_get(v_s_3003_, 1);
v_endExclusive_3008_ = lean_ctor_get(v_s_3003_, 2);
v___x_3009_ = lean_nat_sub(v_endExclusive_3008_, v_startInclusive_3007_);
v___x_3010_ = lean_nat_dec_eq(v_a_3004_, v___x_3009_);
lean_dec(v___x_3009_);
if (v___x_3010_ == 0)
{
lean_object* v___x_3011_; lean_object* v___x_3012_; lean_object* v___x_3013_; uint32_t v___x_3014_; uint32_t v___x_3015_; uint8_t v___x_3016_; 
v___x_3011_ = lean_nat_add(v_startInclusive_3007_, v_a_3004_);
lean_dec(v_a_3004_);
v___x_3012_ = lean_string_utf8_next_fast(v_str_3006_, v___x_3011_);
v___x_3013_ = lean_nat_sub(v___x_3012_, v_startInclusive_3007_);
v___x_3014_ = lean_string_utf8_get_fast(v_str_3006_, v___x_3011_);
lean_dec(v___x_3011_);
v___x_3015_ = 95;
v___x_3016_ = lean_uint32_dec_eq(v___x_3014_, v___x_3015_);
if (v___x_3016_ == 0)
{
lean_object* v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; lean_object* v___x_3022_; 
v___x_3017_ = lean_unsigned_to_nat(10u);
v___x_3018_ = lean_nat_mul(v_b_3005_, v___x_3017_);
lean_dec(v_b_3005_);
v___x_3019_ = lean_uint32_to_nat(v___x_3014_);
v___x_3020_ = lean_unsigned_to_nat(48u);
v___x_3021_ = lean_nat_sub(v___x_3019_, v___x_3020_);
lean_dec(v___x_3019_);
v___x_3022_ = lean_nat_add(v___x_3018_, v___x_3021_);
lean_dec(v___x_3021_);
lean_dec(v___x_3018_);
v_a_3004_ = v___x_3013_;
v_b_3005_ = v___x_3022_;
goto _start;
}
else
{
v_a_3004_ = v___x_3013_;
goto _start;
}
}
else
{
lean_dec(v_a_3004_);
return v_b_3005_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object* v_s_3025_, lean_object* v_a_3026_, lean_object* v_b_3027_){
_start:
{
lean_object* v_res_3028_; 
v_res_3028_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3025_, v_a_3026_, v_b_3027_);
lean_dec_ref(v_s_3025_);
return v_res_3028_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(lean_object* v_s_3029_, lean_object* v_a_3030_, lean_object* v_b_3031_){
_start:
{
lean_object* v_str_3032_; lean_object* v_startInclusive_3033_; lean_object* v_endExclusive_3034_; lean_object* v___x_3035_; uint8_t v_lastWasDigit_3036_; 
v_str_3032_ = lean_ctor_get(v_s_3029_, 0);
v_startInclusive_3033_ = lean_ctor_get(v_s_3029_, 1);
v_endExclusive_3034_ = lean_ctor_get(v_s_3029_, 2);
v___x_3035_ = lean_nat_sub(v_endExclusive_3034_, v_startInclusive_3033_);
v_lastWasDigit_3036_ = lean_nat_dec_eq(v_a_3030_, v___x_3035_);
lean_dec(v___x_3035_);
if (v_lastWasDigit_3036_ == 0)
{
lean_object* v_snd_3037_; lean_object* v___x_3039_; uint8_t v_isShared_3040_; uint8_t v_isSharedCheck_3071_; 
v_snd_3037_ = lean_ctor_get(v_b_3031_, 1);
v_isSharedCheck_3071_ = !lean_is_exclusive(v_b_3031_);
if (v_isSharedCheck_3071_ == 0)
{
lean_object* v_unused_3072_; 
v_unused_3072_ = lean_ctor_get(v_b_3031_, 0);
lean_dec(v_unused_3072_);
v___x_3039_ = v_b_3031_;
v_isShared_3040_ = v_isSharedCheck_3071_;
goto v_resetjp_3038_;
}
else
{
lean_inc(v_snd_3037_);
lean_dec(v_b_3031_);
v___x_3039_ = lean_box(0);
v_isShared_3040_ = v_isSharedCheck_3071_;
goto v_resetjp_3038_;
}
v_resetjp_3038_:
{
lean_object* v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; uint8_t v___y_3046_; uint32_t v___x_3057_; uint32_t v___x_3058_; uint8_t v___x_3059_; 
v___x_3041_ = lean_box(0);
v___x_3042_ = lean_nat_add(v_startInclusive_3033_, v_a_3030_);
lean_dec(v_a_3030_);
v___x_3043_ = lean_string_utf8_next_fast(v_str_3032_, v___x_3042_);
v___x_3044_ = lean_nat_sub(v___x_3043_, v_startInclusive_3033_);
v___x_3057_ = lean_string_utf8_get_fast(v_str_3032_, v___x_3042_);
lean_dec(v___x_3042_);
v___x_3058_ = 95;
v___x_3059_ = lean_uint32_dec_eq(v___x_3057_, v___x_3058_);
if (v___x_3059_ == 0)
{
uint32_t v___x_3060_; uint8_t v___x_3061_; 
v___x_3060_ = 48;
v___x_3061_ = lean_uint32_dec_le(v___x_3060_, v___x_3057_);
if (v___x_3061_ == 0)
{
v___y_3046_ = v___x_3061_;
goto v___jp_3045_;
}
else
{
uint32_t v___x_3062_; uint8_t v___x_3063_; 
v___x_3062_ = 57;
v___x_3063_ = lean_uint32_dec_le(v___x_3057_, v___x_3062_);
v___y_3046_ = v___x_3063_;
goto v___jp_3045_;
}
}
else
{
uint8_t v___x_3064_; 
lean_del_object(v___x_3039_);
v___x_3064_ = lean_unbox(v_snd_3037_);
if (v___x_3064_ == 0)
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; 
lean_dec(v___x_3044_);
v___x_3065_ = lean_box(v_lastWasDigit_3036_);
v___x_3066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3066_, 0, v___x_3065_);
v___x_3067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3067_, 0, v___x_3066_);
lean_ctor_set(v___x_3067_, 1, v_snd_3037_);
return v___x_3067_;
}
else
{
lean_object* v___x_3068_; lean_object* v___x_3069_; 
lean_dec(v_snd_3037_);
v___x_3068_ = lean_box(v_lastWasDigit_3036_);
v___x_3069_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3069_, 0, v___x_3041_);
lean_ctor_set(v___x_3069_, 1, v___x_3068_);
v_a_3030_ = v___x_3044_;
v_b_3031_ = v___x_3069_;
goto _start;
}
}
v___jp_3045_:
{
if (v___y_3046_ == 0)
{
lean_object* v___x_3047_; lean_object* v___x_3048_; lean_object* v___x_3050_; 
lean_dec(v___x_3044_);
v___x_3047_ = lean_box(v_lastWasDigit_3036_);
v___x_3048_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3048_, 0, v___x_3047_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 0, v___x_3048_);
v___x_3050_ = v___x_3039_;
goto v_reusejp_3049_;
}
else
{
lean_object* v_reuseFailAlloc_3051_; 
v_reuseFailAlloc_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3051_, 0, v___x_3048_);
lean_ctor_set(v_reuseFailAlloc_3051_, 1, v_snd_3037_);
v___x_3050_ = v_reuseFailAlloc_3051_;
goto v_reusejp_3049_;
}
v_reusejp_3049_:
{
return v___x_3050_;
}
}
else
{
lean_object* v___x_3052_; lean_object* v___x_3054_; 
lean_dec(v_snd_3037_);
v___x_3052_ = lean_box(v___y_3046_);
if (v_isShared_3040_ == 0)
{
lean_ctor_set(v___x_3039_, 1, v___x_3052_);
lean_ctor_set(v___x_3039_, 0, v___x_3041_);
v___x_3054_ = v___x_3039_;
goto v_reusejp_3053_;
}
else
{
lean_object* v_reuseFailAlloc_3056_; 
v_reuseFailAlloc_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3056_, 0, v___x_3041_);
lean_ctor_set(v_reuseFailAlloc_3056_, 1, v___x_3052_);
v___x_3054_ = v_reuseFailAlloc_3056_;
goto v_reusejp_3053_;
}
v_reusejp_3053_:
{
v_a_3030_ = v___x_3044_;
v_b_3031_ = v___x_3054_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_3030_);
return v_b_3031_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg___boxed(lean_object* v_s_3073_, lean_object* v_a_3074_, lean_object* v_b_3075_){
_start:
{
lean_object* v_res_3076_; 
v_res_3076_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(v_s_3073_, v_a_3074_, v_b_3075_);
lean_dec_ref(v_s_3073_);
return v_res_3076_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object* v_s_3077_){
_start:
{
uint8_t v___y_3079_; lean_object* v___x_3085_; lean_object* v___x_3086_; lean_object* v___x_3087_; lean_object* v_fst_3088_; 
v___x_3085_ = ((lean_object*)(l_String_Slice_isNat___closed__0));
v___x_3086_ = l_String_Slice_positions(v_s_3077_);
v___x_3087_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(v_s_3077_, v___x_3086_, v___x_3085_);
v_fst_3088_ = lean_ctor_get(v___x_3087_, 0);
lean_inc(v_fst_3088_);
if (lean_obj_tag(v_fst_3088_) == 0)
{
lean_object* v_snd_3089_; uint8_t v___x_3090_; 
v_snd_3089_ = lean_ctor_get(v___x_3087_, 1);
lean_inc(v_snd_3089_);
lean_dec_ref(v___x_3087_);
v___x_3090_ = lean_unbox(v_snd_3089_);
lean_dec(v_snd_3089_);
v___y_3079_ = v___x_3090_;
goto v___jp_3078_;
}
else
{
lean_object* v_val_3091_; uint8_t v___x_3092_; 
lean_dec_ref(v___x_3087_);
v_val_3091_ = lean_ctor_get(v_fst_3088_, 0);
lean_inc(v_val_3091_);
lean_dec_ref(v_fst_3088_);
v___x_3092_ = lean_unbox(v_val_3091_);
lean_dec(v_val_3091_);
v___y_3079_ = v___x_3092_;
goto v___jp_3078_;
}
v___jp_3078_:
{
if (v___y_3079_ == 0)
{
lean_object* v___x_3080_; 
v___x_3080_ = lean_box(0);
return v___x_3080_;
}
else
{
lean_object* v___x_3081_; lean_object* v___x_3082_; lean_object* v___x_3083_; lean_object* v___x_3084_; 
v___x_3081_ = lean_unsigned_to_nat(0u);
v___x_3082_ = l_String_Slice_positions(v_s_3077_);
v___x_3083_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3077_, v___x_3082_, v___x_3081_);
v___x_3084_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3084_, 0, v___x_3083_);
return v___x_3084_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object* v_s_3093_){
_start:
{
lean_object* v_res_3094_; 
v_res_3094_ = l_String_Slice_toNat_x3f(v_s_3093_);
lean_dec_ref(v_s_3093_);
return v_res_3094_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object* v_s_3095_, lean_object* v_inst_3096_, lean_object* v_R_3097_, lean_object* v_a_3098_, lean_object* v_b_3099_, lean_object* v_c_3100_){
_start:
{
lean_object* v___x_3101_; 
v___x_3101_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3095_, v_a_3098_, v_b_3099_);
return v___x_3101_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object* v_s_3102_, lean_object* v_inst_3103_, lean_object* v_R_3104_, lean_object* v_a_3105_, lean_object* v_b_3106_, lean_object* v_c_3107_){
_start:
{
lean_object* v_res_3108_; 
v_res_3108_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(v_s_3102_, v_inst_3103_, v_R_3104_, v_a_3105_, v_b_3106_, v_c_3107_);
lean_dec_ref(v_s_3102_);
return v_res_3108_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1(lean_object* v_s_3109_, lean_object* v_inst_3110_, lean_object* v_R_3111_, lean_object* v_a_3112_, lean_object* v_b_3113_, lean_object* v_c_3114_){
_start:
{
lean_object* v___x_3115_; 
v___x_3115_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(v_s_3109_, v_a_3112_, v_b_3113_);
return v___x_3115_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___boxed(lean_object* v_s_3116_, lean_object* v_inst_3117_, lean_object* v_R_3118_, lean_object* v_a_3119_, lean_object* v_b_3120_, lean_object* v_c_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1(v_s_3116_, v_inst_3117_, v_R_3118_, v_a_3119_, v_b_3120_, v_c_3121_);
lean_dec_ref(v_s_3116_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_toNat_x21_spec__0(lean_object* v_msg_3123_){
_start:
{
lean_object* v___x_3124_; lean_object* v___x_3125_; 
v___x_3124_ = lean_unsigned_to_nat(0u);
v___x_3125_ = lean_panic_fn(v___x_3124_, v_msg_3123_);
return v___x_3125_;
}
}
static lean_object* _init_l_String_Slice_toNat_x21___closed__3(void){
_start:
{
lean_object* v___x_3129_; lean_object* v___x_3130_; lean_object* v___x_3131_; lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; 
v___x_3129_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__2));
v___x_3130_ = lean_unsigned_to_nat(4u);
v___x_3131_ = lean_unsigned_to_nat(1013u);
v___x_3132_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__1));
v___x_3133_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__0));
v___x_3134_ = l_mkPanicMessageWithDecl(v___x_3133_, v___x_3132_, v___x_3131_, v___x_3130_, v___x_3129_);
return v___x_3134_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21(lean_object* v_s_3135_){
_start:
{
uint8_t v___y_3137_; lean_object* v___x_3143_; lean_object* v___x_3144_; lean_object* v___x_3145_; lean_object* v_fst_3146_; 
v___x_3143_ = ((lean_object*)(l_String_Slice_isNat___closed__0));
v___x_3144_ = l_String_Slice_positions(v_s_3135_);
v___x_3145_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(v_s_3135_, v___x_3144_, v___x_3143_);
v_fst_3146_ = lean_ctor_get(v___x_3145_, 0);
lean_inc(v_fst_3146_);
if (lean_obj_tag(v_fst_3146_) == 0)
{
lean_object* v_snd_3147_; uint8_t v___x_3148_; 
v_snd_3147_ = lean_ctor_get(v___x_3145_, 1);
lean_inc(v_snd_3147_);
lean_dec_ref(v___x_3145_);
v___x_3148_ = lean_unbox(v_snd_3147_);
lean_dec(v_snd_3147_);
v___y_3137_ = v___x_3148_;
goto v___jp_3136_;
}
else
{
lean_object* v_val_3149_; uint8_t v___x_3150_; 
lean_dec_ref(v___x_3145_);
v_val_3149_ = lean_ctor_get(v_fst_3146_, 0);
lean_inc(v_val_3149_);
lean_dec_ref(v_fst_3146_);
v___x_3150_ = lean_unbox(v_val_3149_);
lean_dec(v_val_3149_);
v___y_3137_ = v___x_3150_;
goto v___jp_3136_;
}
v___jp_3136_:
{
if (v___y_3137_ == 0)
{
lean_object* v___x_3138_; lean_object* v___x_3139_; 
v___x_3138_ = lean_obj_once(&l_String_Slice_toNat_x21___closed__3, &l_String_Slice_toNat_x21___closed__3_once, _init_l_String_Slice_toNat_x21___closed__3);
v___x_3139_ = l_panic___at___00String_Slice_toNat_x21_spec__0(v___x_3138_);
return v___x_3139_;
}
else
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; 
v___x_3140_ = lean_unsigned_to_nat(0u);
v___x_3141_ = l_String_Slice_positions(v_s_3135_);
v___x_3142_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3135_, v___x_3141_, v___x_3140_);
return v___x_3142_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21___boxed(lean_object* v_s_3151_){
_start:
{
lean_object* v_res_3152_; 
v_res_3152_ = l_String_Slice_toNat_x21(v_s_3151_);
lean_dec_ref(v_s_3151_);
return v_res_3152_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object* v_s_3153_){
_start:
{
lean_object* v___x_3154_; lean_object* v___x_3155_; 
v___x_3154_ = lean_unsigned_to_nat(0u);
v___x_3155_ = l_String_Slice_Pos_get_x3f(v_s_3153_, v___x_3154_);
return v___x_3155_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object* v_s_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_String_Slice_front_x3f(v_s_3156_);
lean_dec_ref(v_s_3156_);
return v_res_3157_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_front(lean_object* v_s_3158_){
_start:
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_unsigned_to_nat(0u);
v___x_3160_ = l_String_Slice_Pos_get_x3f(v_s_3158_, v___x_3159_);
if (lean_obj_tag(v___x_3160_) == 0)
{
uint32_t v___x_3161_; 
v___x_3161_ = 65;
return v___x_3161_;
}
else
{
lean_object* v_val_3162_; uint32_t v___x_3163_; 
v_val_3162_ = lean_ctor_get(v___x_3160_, 0);
lean_inc(v_val_3162_);
lean_dec_ref(v___x_3160_);
v___x_3163_ = lean_unbox_uint32(v_val_3162_);
lean_dec(v_val_3162_);
return v___x_3163_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object* v_s_3164_){
_start:
{
uint32_t v_res_3165_; lean_object* v_r_3166_; 
v_res_3165_ = l_String_Slice_front(v_s_3164_);
lean_dec_ref(v_s_3164_);
v_r_3166_ = lean_box_uint32(v_res_3165_);
return v_r_3166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg(lean_object* v___x_3167_, lean_object* v___x_3168_, lean_object* v___x_3169_, lean_object* v_a_3170_, lean_object* v_b_3171_){
_start:
{
lean_object* v_startInclusive_3172_; lean_object* v_endExclusive_3173_; lean_object* v___x_3174_; uint8_t v_lastWasDigit_3175_; 
v_startInclusive_3172_ = lean_ctor_get(v___x_3167_, 1);
v_endExclusive_3173_ = lean_ctor_get(v___x_3167_, 2);
v___x_3174_ = lean_nat_sub(v_endExclusive_3173_, v_startInclusive_3172_);
v_lastWasDigit_3175_ = lean_nat_dec_eq(v_a_3170_, v___x_3174_);
lean_dec(v___x_3174_);
if (v_lastWasDigit_3175_ == 0)
{
lean_object* v_snd_3176_; lean_object* v___x_3178_; uint8_t v_isShared_3179_; uint8_t v_isSharedCheck_3210_; 
v_snd_3176_ = lean_ctor_get(v_b_3171_, 1);
v_isSharedCheck_3210_ = !lean_is_exclusive(v_b_3171_);
if (v_isSharedCheck_3210_ == 0)
{
lean_object* v_unused_3211_; 
v_unused_3211_ = lean_ctor_get(v_b_3171_, 0);
lean_dec(v_unused_3211_);
v___x_3178_ = v_b_3171_;
v_isShared_3179_ = v_isSharedCheck_3210_;
goto v_resetjp_3177_;
}
else
{
lean_inc(v_snd_3176_);
lean_dec(v_b_3171_);
v___x_3178_ = lean_box(0);
v_isShared_3179_ = v_isSharedCheck_3210_;
goto v_resetjp_3177_;
}
v_resetjp_3177_:
{
lean_object* v___x_3180_; lean_object* v___x_3181_; lean_object* v___x_3182_; lean_object* v___x_3183_; uint8_t v___y_3185_; uint32_t v___x_3196_; uint32_t v___x_3197_; uint8_t v___x_3198_; 
v___x_3180_ = lean_box(0);
v___x_3181_ = lean_nat_add(v___x_3168_, v_a_3170_);
lean_dec(v_a_3170_);
v___x_3182_ = lean_string_utf8_next_fast(v___x_3169_, v___x_3181_);
v___x_3183_ = lean_nat_sub(v___x_3182_, v___x_3168_);
v___x_3196_ = lean_string_utf8_get_fast(v___x_3169_, v___x_3181_);
lean_dec(v___x_3181_);
v___x_3197_ = 95;
v___x_3198_ = lean_uint32_dec_eq(v___x_3196_, v___x_3197_);
if (v___x_3198_ == 0)
{
uint32_t v___x_3199_; uint8_t v___x_3200_; 
v___x_3199_ = 48;
v___x_3200_ = lean_uint32_dec_le(v___x_3199_, v___x_3196_);
if (v___x_3200_ == 0)
{
v___y_3185_ = v___x_3200_;
goto v___jp_3184_;
}
else
{
uint32_t v___x_3201_; uint8_t v___x_3202_; 
v___x_3201_ = 57;
v___x_3202_ = lean_uint32_dec_le(v___x_3196_, v___x_3201_);
v___y_3185_ = v___x_3202_;
goto v___jp_3184_;
}
}
else
{
uint8_t v___x_3203_; 
lean_del_object(v___x_3178_);
v___x_3203_ = lean_unbox(v_snd_3176_);
if (v___x_3203_ == 0)
{
lean_object* v___x_3204_; lean_object* v___x_3205_; lean_object* v___x_3206_; 
lean_dec(v___x_3183_);
v___x_3204_ = lean_box(v_lastWasDigit_3175_);
v___x_3205_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3205_, 0, v___x_3204_);
v___x_3206_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3206_, 0, v___x_3205_);
lean_ctor_set(v___x_3206_, 1, v_snd_3176_);
return v___x_3206_;
}
else
{
lean_object* v___x_3207_; lean_object* v___x_3208_; 
lean_dec(v_snd_3176_);
v___x_3207_ = lean_box(v_lastWasDigit_3175_);
v___x_3208_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3208_, 0, v___x_3180_);
lean_ctor_set(v___x_3208_, 1, v___x_3207_);
v_a_3170_ = v___x_3183_;
v_b_3171_ = v___x_3208_;
goto _start;
}
}
v___jp_3184_:
{
if (v___y_3185_ == 0)
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3189_; 
lean_dec(v___x_3183_);
v___x_3186_ = lean_box(v_lastWasDigit_3175_);
v___x_3187_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3187_, 0, v___x_3186_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 0, v___x_3187_);
v___x_3189_ = v___x_3178_;
goto v_reusejp_3188_;
}
else
{
lean_object* v_reuseFailAlloc_3190_; 
v_reuseFailAlloc_3190_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3190_, 0, v___x_3187_);
lean_ctor_set(v_reuseFailAlloc_3190_, 1, v_snd_3176_);
v___x_3189_ = v_reuseFailAlloc_3190_;
goto v_reusejp_3188_;
}
v_reusejp_3188_:
{
return v___x_3189_;
}
}
else
{
lean_object* v___x_3191_; lean_object* v___x_3193_; 
lean_dec(v_snd_3176_);
v___x_3191_ = lean_box(v___y_3185_);
if (v_isShared_3179_ == 0)
{
lean_ctor_set(v___x_3178_, 1, v___x_3191_);
lean_ctor_set(v___x_3178_, 0, v___x_3180_);
v___x_3193_ = v___x_3178_;
goto v_reusejp_3192_;
}
else
{
lean_object* v_reuseFailAlloc_3195_; 
v_reuseFailAlloc_3195_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3195_, 0, v___x_3180_);
lean_ctor_set(v_reuseFailAlloc_3195_, 1, v___x_3191_);
v___x_3193_ = v_reuseFailAlloc_3195_;
goto v_reusejp_3192_;
}
v_reusejp_3192_:
{
v_a_3170_ = v___x_3183_;
v_b_3171_ = v___x_3193_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_3170_);
return v_b_3171_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg___boxed(lean_object* v___x_3212_, lean_object* v___x_3213_, lean_object* v___x_3214_, lean_object* v_a_3215_, lean_object* v_b_3216_){
_start:
{
lean_object* v_res_3217_; 
v_res_3217_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg(v___x_3212_, v___x_3213_, v___x_3214_, v_a_3215_, v_b_3216_);
lean_dec_ref(v___x_3214_);
lean_dec(v___x_3213_);
lean_dec_ref(v___x_3212_);
return v_res_3217_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isInt(lean_object* v_s_3218_){
_start:
{
uint32_t v___y_3220_; lean_object* v___x_3258_; lean_object* v___x_3259_; 
v___x_3258_ = lean_unsigned_to_nat(0u);
v___x_3259_ = l_String_Slice_Pos_get_x3f(v_s_3218_, v___x_3258_);
if (lean_obj_tag(v___x_3259_) == 0)
{
uint32_t v___x_3260_; 
v___x_3260_ = 65;
v___y_3220_ = v___x_3260_;
goto v___jp_3219_;
}
else
{
lean_object* v_val_3261_; uint32_t v___x_3262_; 
v_val_3261_ = lean_ctor_get(v___x_3259_, 0);
lean_inc(v_val_3261_);
lean_dec_ref(v___x_3259_);
v___x_3262_ = lean_unbox_uint32(v_val_3261_);
lean_dec(v_val_3261_);
v___y_3220_ = v___x_3262_;
goto v___jp_3219_;
}
v___jp_3219_:
{
uint32_t v___x_3221_; uint8_t v_lastWasDigit_3222_; 
v___x_3221_ = 45;
v_lastWasDigit_3222_ = lean_uint32_dec_eq(v___y_3220_, v___x_3221_);
if (v_lastWasDigit_3222_ == 0)
{
lean_object* v___x_3223_; lean_object* v___x_3224_; lean_object* v___x_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; lean_object* v_fst_3228_; 
v___x_3223_ = lean_box(0);
v___x_3224_ = lean_box(v_lastWasDigit_3222_);
v___x_3225_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3225_, 0, v___x_3223_);
lean_ctor_set(v___x_3225_, 1, v___x_3224_);
v___x_3226_ = l_String_Slice_positions(v_s_3218_);
v___x_3227_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__1___redArg(v_s_3218_, v___x_3226_, v___x_3225_);
lean_dec_ref(v_s_3218_);
v_fst_3228_ = lean_ctor_get(v___x_3227_, 0);
lean_inc(v_fst_3228_);
if (lean_obj_tag(v_fst_3228_) == 0)
{
lean_object* v_snd_3229_; uint8_t v___x_3230_; 
v_snd_3229_ = lean_ctor_get(v___x_3227_, 1);
lean_inc(v_snd_3229_);
lean_dec_ref(v___x_3227_);
v___x_3230_ = lean_unbox(v_snd_3229_);
lean_dec(v_snd_3229_);
return v___x_3230_;
}
else
{
lean_object* v_val_3231_; uint8_t v___x_3232_; 
lean_dec_ref(v___x_3227_);
v_val_3231_ = lean_ctor_get(v_fst_3228_, 0);
lean_inc(v_val_3231_);
lean_dec_ref(v_fst_3228_);
v___x_3232_ = lean_unbox(v_val_3231_);
lean_dec(v_val_3231_);
return v___x_3232_;
}
}
else
{
lean_object* v_str_3233_; lean_object* v_startInclusive_3234_; lean_object* v_endExclusive_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3238_; lean_object* v___x_3240_; uint8_t v_isShared_3241_; uint8_t v_isSharedCheck_3254_; 
v_str_3233_ = lean_ctor_get(v_s_3218_, 0);
lean_inc_ref(v_str_3233_);
v_startInclusive_3234_ = lean_ctor_get(v_s_3218_, 1);
lean_inc(v_startInclusive_3234_);
v_endExclusive_3235_ = lean_ctor_get(v_s_3218_, 2);
lean_inc(v_endExclusive_3235_);
v___x_3236_ = lean_unsigned_to_nat(1u);
v___x_3237_ = lean_unsigned_to_nat(0u);
v___x_3238_ = l_String_Slice_Pos_nextn(v_s_3218_, v___x_3237_, v___x_3236_);
v_isSharedCheck_3254_ = !lean_is_exclusive(v_s_3218_);
if (v_isSharedCheck_3254_ == 0)
{
lean_object* v_unused_3255_; lean_object* v_unused_3256_; lean_object* v_unused_3257_; 
v_unused_3255_ = lean_ctor_get(v_s_3218_, 2);
lean_dec(v_unused_3255_);
v_unused_3256_ = lean_ctor_get(v_s_3218_, 1);
lean_dec(v_unused_3256_);
v_unused_3257_ = lean_ctor_get(v_s_3218_, 0);
lean_dec(v_unused_3257_);
v___x_3240_ = v_s_3218_;
v_isShared_3241_ = v_isSharedCheck_3254_;
goto v_resetjp_3239_;
}
else
{
lean_dec(v_s_3218_);
v___x_3240_ = lean_box(0);
v_isShared_3241_ = v_isSharedCheck_3254_;
goto v_resetjp_3239_;
}
v_resetjp_3239_:
{
lean_object* v___x_3242_; lean_object* v___x_3244_; 
v___x_3242_ = lean_nat_add(v_startInclusive_3234_, v___x_3238_);
lean_dec(v___x_3238_);
lean_dec(v_startInclusive_3234_);
lean_inc(v___x_3242_);
lean_inc_ref(v_str_3233_);
if (v_isShared_3241_ == 0)
{
lean_ctor_set(v___x_3240_, 1, v___x_3242_);
v___x_3244_ = v___x_3240_;
goto v_reusejp_3243_;
}
else
{
lean_object* v_reuseFailAlloc_3253_; 
v_reuseFailAlloc_3253_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3253_, 0, v_str_3233_);
lean_ctor_set(v_reuseFailAlloc_3253_, 1, v___x_3242_);
lean_ctor_set(v_reuseFailAlloc_3253_, 2, v_endExclusive_3235_);
v___x_3244_ = v_reuseFailAlloc_3253_;
goto v_reusejp_3243_;
}
v_reusejp_3243_:
{
lean_object* v___x_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; lean_object* v_fst_3248_; 
v___x_3245_ = ((lean_object*)(l_String_Slice_isNat___closed__0));
v___x_3246_ = l_String_Slice_positions(v___x_3244_);
v___x_3247_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg(v___x_3244_, v___x_3242_, v_str_3233_, v___x_3246_, v___x_3245_);
lean_dec_ref(v_str_3233_);
lean_dec(v___x_3242_);
lean_dec_ref(v___x_3244_);
v_fst_3248_ = lean_ctor_get(v___x_3247_, 0);
lean_inc(v_fst_3248_);
if (lean_obj_tag(v_fst_3248_) == 0)
{
lean_object* v_snd_3249_; uint8_t v___x_3250_; 
v_snd_3249_ = lean_ctor_get(v___x_3247_, 1);
lean_inc(v_snd_3249_);
lean_dec_ref(v___x_3247_);
v___x_3250_ = lean_unbox(v_snd_3249_);
lean_dec(v_snd_3249_);
return v___x_3250_;
}
else
{
lean_object* v_val_3251_; uint8_t v___x_3252_; 
lean_dec_ref(v___x_3247_);
v_val_3251_ = lean_ctor_get(v_fst_3248_, 0);
lean_inc(v_val_3251_);
lean_dec_ref(v_fst_3248_);
v___x_3252_ = lean_unbox(v_val_3251_);
lean_dec(v_val_3251_);
return v___x_3252_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object* v_s_3263_){
_start:
{
uint8_t v_res_3264_; lean_object* v_r_3265_; 
v_res_3264_ = l_String_Slice_isInt(v_s_3263_);
v_r_3265_ = lean_box(v_res_3264_);
return v_r_3265_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0(lean_object* v___x_3266_, lean_object* v___x_3267_, lean_object* v___x_3268_, lean_object* v_inst_3269_, lean_object* v_R_3270_, lean_object* v_a_3271_, lean_object* v_b_3272_, lean_object* v_c_3273_){
_start:
{
lean_object* v___x_3274_; 
v___x_3274_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___redArg(v___x_3266_, v___x_3267_, v___x_3268_, v_a_3271_, v_b_3272_);
return v___x_3274_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0___boxed(lean_object* v___x_3275_, lean_object* v___x_3276_, lean_object* v___x_3277_, lean_object* v_inst_3278_, lean_object* v_R_3279_, lean_object* v_a_3280_, lean_object* v_b_3281_, lean_object* v_c_3282_){
_start:
{
lean_object* v_res_3283_; 
v_res_3283_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isInt_spec__0(v___x_3275_, v___x_3276_, v___x_3277_, v_inst_3278_, v_R_3279_, v_a_3280_, v_b_3281_, v_c_3282_);
lean_dec_ref(v___x_3277_);
lean_dec(v___x_3276_);
lean_dec_ref(v___x_3275_);
return v_res_3283_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x3f(lean_object* v_s_3284_){
_start:
{
uint32_t v___y_3286_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v___x_3328_ = lean_unsigned_to_nat(0u);
v___x_3329_ = l_String_Slice_Pos_get_x3f(v_s_3284_, v___x_3328_);
if (lean_obj_tag(v___x_3329_) == 0)
{
uint32_t v___x_3330_; 
v___x_3330_ = 65;
v___y_3286_ = v___x_3330_;
goto v___jp_3285_;
}
else
{
lean_object* v_val_3331_; uint32_t v___x_3332_; 
v_val_3331_ = lean_ctor_get(v___x_3329_, 0);
lean_inc(v_val_3331_);
lean_dec_ref(v___x_3329_);
v___x_3332_ = lean_unbox_uint32(v_val_3331_);
lean_dec(v_val_3331_);
v___y_3286_ = v___x_3332_;
goto v___jp_3285_;
}
v___jp_3285_:
{
uint32_t v___x_3287_; uint8_t v___x_3288_; 
v___x_3287_ = 45;
v___x_3288_ = lean_uint32_dec_eq(v___y_3286_, v___x_3287_);
if (v___x_3288_ == 0)
{
lean_object* v___x_3289_; 
v___x_3289_ = l_String_Slice_toNat_x3f(v_s_3284_);
lean_dec_ref(v_s_3284_);
if (lean_obj_tag(v___x_3289_) == 0)
{
lean_object* v___x_3290_; 
v___x_3290_ = lean_box(0);
return v___x_3290_;
}
else
{
lean_object* v_val_3291_; lean_object* v___x_3293_; uint8_t v_isShared_3294_; uint8_t v_isSharedCheck_3299_; 
v_val_3291_ = lean_ctor_get(v___x_3289_, 0);
v_isSharedCheck_3299_ = !lean_is_exclusive(v___x_3289_);
if (v_isSharedCheck_3299_ == 0)
{
v___x_3293_ = v___x_3289_;
v_isShared_3294_ = v_isSharedCheck_3299_;
goto v_resetjp_3292_;
}
else
{
lean_inc(v_val_3291_);
lean_dec(v___x_3289_);
v___x_3293_ = lean_box(0);
v_isShared_3294_ = v_isSharedCheck_3299_;
goto v_resetjp_3292_;
}
v_resetjp_3292_:
{
lean_object* v___x_3295_; lean_object* v___x_3297_; 
v___x_3295_ = lean_nat_to_int(v_val_3291_);
if (v_isShared_3294_ == 0)
{
lean_ctor_set(v___x_3293_, 0, v___x_3295_);
v___x_3297_ = v___x_3293_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3298_; 
v_reuseFailAlloc_3298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3298_, 0, v___x_3295_);
v___x_3297_ = v_reuseFailAlloc_3298_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
return v___x_3297_;
}
}
}
}
else
{
lean_object* v_str_3300_; lean_object* v_startInclusive_3301_; lean_object* v_endExclusive_3302_; lean_object* v___x_3303_; lean_object* v___x_3304_; lean_object* v___x_3305_; lean_object* v___x_3307_; uint8_t v_isShared_3308_; uint8_t v_isSharedCheck_3324_; 
v_str_3300_ = lean_ctor_get(v_s_3284_, 0);
lean_inc_ref(v_str_3300_);
v_startInclusive_3301_ = lean_ctor_get(v_s_3284_, 1);
lean_inc(v_startInclusive_3301_);
v_endExclusive_3302_ = lean_ctor_get(v_s_3284_, 2);
lean_inc(v_endExclusive_3302_);
v___x_3303_ = lean_unsigned_to_nat(1u);
v___x_3304_ = lean_unsigned_to_nat(0u);
v___x_3305_ = l_String_Slice_Pos_nextn(v_s_3284_, v___x_3304_, v___x_3303_);
v_isSharedCheck_3324_ = !lean_is_exclusive(v_s_3284_);
if (v_isSharedCheck_3324_ == 0)
{
lean_object* v_unused_3325_; lean_object* v_unused_3326_; lean_object* v_unused_3327_; 
v_unused_3325_ = lean_ctor_get(v_s_3284_, 2);
lean_dec(v_unused_3325_);
v_unused_3326_ = lean_ctor_get(v_s_3284_, 1);
lean_dec(v_unused_3326_);
v_unused_3327_ = lean_ctor_get(v_s_3284_, 0);
lean_dec(v_unused_3327_);
v___x_3307_ = v_s_3284_;
v_isShared_3308_ = v_isSharedCheck_3324_;
goto v_resetjp_3306_;
}
else
{
lean_dec(v_s_3284_);
v___x_3307_ = lean_box(0);
v_isShared_3308_ = v_isSharedCheck_3324_;
goto v_resetjp_3306_;
}
v_resetjp_3306_:
{
lean_object* v___x_3309_; lean_object* v___x_3311_; 
v___x_3309_ = lean_nat_add(v_startInclusive_3301_, v___x_3305_);
lean_dec(v___x_3305_);
lean_dec(v_startInclusive_3301_);
if (v_isShared_3308_ == 0)
{
lean_ctor_set(v___x_3307_, 1, v___x_3309_);
v___x_3311_ = v___x_3307_;
goto v_reusejp_3310_;
}
else
{
lean_object* v_reuseFailAlloc_3323_; 
v_reuseFailAlloc_3323_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3323_, 0, v_str_3300_);
lean_ctor_set(v_reuseFailAlloc_3323_, 1, v___x_3309_);
lean_ctor_set(v_reuseFailAlloc_3323_, 2, v_endExclusive_3302_);
v___x_3311_ = v_reuseFailAlloc_3323_;
goto v_reusejp_3310_;
}
v_reusejp_3310_:
{
lean_object* v___x_3312_; 
v___x_3312_ = l_String_Slice_toNat_x3f(v___x_3311_);
lean_dec_ref(v___x_3311_);
if (lean_obj_tag(v___x_3312_) == 0)
{
lean_object* v___x_3313_; 
v___x_3313_ = lean_box(0);
return v___x_3313_;
}
else
{
lean_object* v_val_3314_; lean_object* v___x_3316_; uint8_t v_isShared_3317_; uint8_t v_isSharedCheck_3322_; 
v_val_3314_ = lean_ctor_get(v___x_3312_, 0);
v_isSharedCheck_3322_ = !lean_is_exclusive(v___x_3312_);
if (v_isSharedCheck_3322_ == 0)
{
v___x_3316_ = v___x_3312_;
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
else
{
lean_inc(v_val_3314_);
lean_dec(v___x_3312_);
v___x_3316_ = lean_box(0);
v_isShared_3317_ = v_isSharedCheck_3322_;
goto v_resetjp_3315_;
}
v_resetjp_3315_:
{
lean_object* v___x_3318_; lean_object* v___x_3320_; 
v___x_3318_ = l_Int_negOfNat(v_val_3314_);
lean_dec(v_val_3314_);
if (v_isShared_3317_ == 0)
{
lean_ctor_set(v___x_3316_, 0, v___x_3318_);
v___x_3320_ = v___x_3316_;
goto v_reusejp_3319_;
}
else
{
lean_object* v_reuseFailAlloc_3321_; 
v_reuseFailAlloc_3321_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3321_, 0, v___x_3318_);
v___x_3320_ = v_reuseFailAlloc_3321_;
goto v_reusejp_3319_;
}
v_reusejp_3319_:
{
return v___x_3320_;
}
}
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x21(lean_object* v_s_3334_){
_start:
{
lean_object* v___x_3335_; 
v___x_3335_ = l_String_Slice_toInt_x3f(v_s_3334_);
if (lean_obj_tag(v___x_3335_) == 0)
{
lean_object* v___x_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v___x_3336_ = l_Int_instInhabited;
v___x_3337_ = ((lean_object*)(l_String_Slice_toInt_x21___closed__0));
v___x_3338_ = l_panic___redArg(v___x_3336_, v___x_3337_);
return v___x_3338_;
}
else
{
lean_object* v_val_3339_; 
v_val_3339_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_val_3339_);
lean_dec_ref(v___x_3335_);
return v_val_3339_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object* v_s_3340_){
_start:
{
lean_object* v_startInclusive_3341_; lean_object* v_endExclusive_3342_; lean_object* v___x_3343_; lean_object* v___x_3344_; 
v_startInclusive_3341_ = lean_ctor_get(v_s_3340_, 1);
v_endExclusive_3342_ = lean_ctor_get(v_s_3340_, 2);
v___x_3343_ = lean_nat_sub(v_endExclusive_3342_, v_startInclusive_3341_);
v___x_3344_ = l_String_Slice_Pos_prev_x3f(v_s_3340_, v___x_3343_);
lean_dec(v___x_3343_);
if (lean_obj_tag(v___x_3344_) == 0)
{
lean_object* v___x_3345_; 
v___x_3345_ = lean_box(0);
return v___x_3345_;
}
else
{
lean_object* v_val_3346_; lean_object* v___x_3347_; 
v_val_3346_ = lean_ctor_get(v___x_3344_, 0);
lean_inc(v_val_3346_);
lean_dec_ref(v___x_3344_);
v___x_3347_ = l_String_Slice_Pos_get_x3f(v_s_3340_, v_val_3346_);
lean_dec(v_val_3346_);
return v___x_3347_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object* v_s_3348_){
_start:
{
lean_object* v_res_3349_; 
v_res_3349_ = l_String_Slice_back_x3f(v_s_3348_);
lean_dec_ref(v_s_3348_);
return v_res_3349_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_back(lean_object* v_s_3350_){
_start:
{
lean_object* v_startInclusive_3351_; lean_object* v_endExclusive_3352_; lean_object* v___x_3353_; lean_object* v___x_3354_; 
v_startInclusive_3351_ = lean_ctor_get(v_s_3350_, 1);
v_endExclusive_3352_ = lean_ctor_get(v_s_3350_, 2);
v___x_3353_ = lean_nat_sub(v_endExclusive_3352_, v_startInclusive_3351_);
v___x_3354_ = l_String_Slice_Pos_prev_x3f(v_s_3350_, v___x_3353_);
lean_dec(v___x_3353_);
if (lean_obj_tag(v___x_3354_) == 0)
{
uint32_t v___x_3355_; 
v___x_3355_ = 65;
return v___x_3355_;
}
else
{
lean_object* v_val_3356_; lean_object* v___x_3357_; 
v_val_3356_ = lean_ctor_get(v___x_3354_, 0);
lean_inc(v_val_3356_);
lean_dec_ref(v___x_3354_);
v___x_3357_ = l_String_Slice_Pos_get_x3f(v_s_3350_, v_val_3356_);
lean_dec(v_val_3356_);
if (lean_obj_tag(v___x_3357_) == 0)
{
uint32_t v___x_3358_; 
v___x_3358_ = 65;
return v___x_3358_;
}
else
{
lean_object* v_val_3359_; uint32_t v___x_3360_; 
v_val_3359_ = lean_ctor_get(v___x_3357_, 0);
lean_inc(v_val_3359_);
lean_dec_ref(v___x_3357_);
v___x_3360_ = lean_unbox_uint32(v_val_3359_);
lean_dec(v_val_3359_);
return v___x_3360_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object* v_s_3361_){
_start:
{
uint32_t v_res_3362_; lean_object* v_r_3363_; 
v_res_3362_ = l_String_Slice_back(v_s_3361_);
lean_dec_ref(v_s_3361_);
v_r_3363_ = lean_box_uint32(v_res_3362_);
return v_r_3363_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(lean_object* v_acc_3364_, lean_object* v_s_3365_, lean_object* v_a_3366_){
_start:
{
if (lean_obj_tag(v_a_3366_) == 0)
{
return v_acc_3364_;
}
else
{
lean_object* v_head_3367_; lean_object* v_tail_3368_; lean_object* v_str_3369_; lean_object* v_startInclusive_3370_; lean_object* v_endExclusive_3371_; lean_object* v_str_3372_; lean_object* v_startInclusive_3373_; lean_object* v_endExclusive_3374_; lean_object* v___x_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; lean_object* v___x_3378_; 
v_head_3367_ = lean_ctor_get(v_a_3366_, 0);
v_tail_3368_ = lean_ctor_get(v_a_3366_, 1);
v_str_3369_ = lean_ctor_get(v_s_3365_, 0);
v_startInclusive_3370_ = lean_ctor_get(v_s_3365_, 1);
v_endExclusive_3371_ = lean_ctor_get(v_s_3365_, 2);
v_str_3372_ = lean_ctor_get(v_head_3367_, 0);
v_startInclusive_3373_ = lean_ctor_get(v_head_3367_, 1);
v_endExclusive_3374_ = lean_ctor_get(v_head_3367_, 2);
v___x_3375_ = lean_string_utf8_extract(v_str_3369_, v_startInclusive_3370_, v_endExclusive_3371_);
v___x_3376_ = lean_string_append(v_acc_3364_, v___x_3375_);
lean_dec_ref(v___x_3375_);
v___x_3377_ = lean_string_utf8_extract(v_str_3372_, v_startInclusive_3373_, v_endExclusive_3374_);
v___x_3378_ = lean_string_append(v___x_3376_, v___x_3377_);
lean_dec_ref(v___x_3377_);
v_acc_3364_ = v___x_3378_;
v_a_3366_ = v_tail_3368_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go___boxed(lean_object* v_acc_3380_, lean_object* v_s_3381_, lean_object* v_a_3382_){
_start:
{
lean_object* v_res_3383_; 
v_res_3383_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v_acc_3380_, v_s_3381_, v_a_3382_);
lean_dec(v_a_3382_);
lean_dec_ref(v_s_3381_);
return v_res_3383_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object* v_s_3384_, lean_object* v_x_3385_){
_start:
{
if (lean_obj_tag(v_x_3385_) == 0)
{
lean_object* v___x_3386_; 
v___x_3386_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
return v___x_3386_;
}
else
{
lean_object* v_head_3387_; lean_object* v_tail_3388_; lean_object* v_str_3389_; lean_object* v_startInclusive_3390_; lean_object* v_endExclusive_3391_; lean_object* v___x_3392_; lean_object* v___x_3393_; 
v_head_3387_ = lean_ctor_get(v_x_3385_, 0);
v_tail_3388_ = lean_ctor_get(v_x_3385_, 1);
v_str_3389_ = lean_ctor_get(v_head_3387_, 0);
v_startInclusive_3390_ = lean_ctor_get(v_head_3387_, 1);
v_endExclusive_3391_ = lean_ctor_get(v_head_3387_, 2);
v___x_3392_ = lean_string_utf8_extract(v_str_3389_, v_startInclusive_3390_, v_endExclusive_3391_);
v___x_3393_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v___x_3392_, v_s_3384_, v_tail_3388_);
return v___x_3393_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object* v_s_3394_, lean_object* v_x_3395_){
_start:
{
lean_object* v_res_3396_; 
v_res_3396_ = l_String_Slice_intercalate(v_s_3394_, v_x_3395_);
lean_dec(v_x_3395_);
lean_dec_ref(v_s_3394_);
return v_res_3396_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object* v_s_3397_){
_start:
{
lean_object* v___x_3398_; lean_object* v___x_3399_; 
v___x_3398_ = l_String_Slice_toString(v_s_3397_);
v___x_3399_ = l_String_toName(v___x_3398_);
return v___x_3399_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object* v_s_3400_){
_start:
{
lean_object* v_res_3401_; 
v_res_3401_ = l_String_Slice_toName(v_s_3400_);
lean_dec_ref(v_s_3400_);
return v_res_3401_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object* v_s_3402_){
_start:
{
lean_object* v_str_3403_; lean_object* v_startInclusive_3404_; lean_object* v_endExclusive_3405_; lean_object* v___x_3406_; lean_object* v___x_3407_; 
v_str_3403_ = lean_ctor_get(v_s_3402_, 0);
v_startInclusive_3404_ = lean_ctor_get(v_s_3402_, 1);
v_endExclusive_3405_ = lean_ctor_get(v_s_3402_, 2);
v___x_3406_ = lean_string_utf8_extract(v_str_3403_, v_startInclusive_3404_, v_endExclusive_3405_);
v___x_3407_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3407_, 0, v___x_3406_);
return v___x_3407_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object* v_s_3408_){
_start:
{
lean_object* v_res_3409_; 
v_res_3409_ = l_String_Slice_instToFormat___lam__0(v_s_3408_);
lean_dec_ref(v_s_3408_);
return v_res_3409_;
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
