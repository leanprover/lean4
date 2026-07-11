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
uint8_t lean_bool_not(uint8_t);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_lt(lean_object*, lean_object*);
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
lean_object* lean_panic_fn_borrowed(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
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
lean_dec_ref_known(v_t_117_, 2);
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
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default(lean_object* v_00_u03c3_190_, lean_object* v_00_u03c1_191_, lean_object* v_pat_192_, lean_object* v_s_193_, lean_object* v_inst_194_){
_start:
{
lean_object* v___x_195_; 
v___x_195_ = lean_box(1);
return v___x_195_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___boxed(lean_object* v_00_u03c3_196_, lean_object* v_00_u03c1_197_, lean_object* v_pat_198_, lean_object* v_s_199_, lean_object* v_inst_200_){
_start:
{
lean_object* v_res_201_; 
v_res_201_ = l_String_Slice_instInhabitedSplitIterator_default(v_00_u03c3_196_, v_00_u03c1_197_, v_pat_198_, v_s_199_, v_inst_200_);
lean_dec(v_inst_200_);
lean_dec_ref(v_s_199_);
lean_dec(v_pat_198_);
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
lean_dec_ref_known(v_out_227_, 2);
lean_dec_ref(v_s_219_);
v_it_228_ = lean_ctor_get(v___x_226_, 0);
lean_inc(v_it_228_);
lean_dec_ref_known(v___x_226_, 2);
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
lean_dec_ref_known(v_out_227_, 2);
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
lean_dec_ref_known(v_x_304_, 2);
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
lean_dec_ref_known(v_x_318_, 2);
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
lean_dec_ref_known(v_x_336_, 2);
v_startPos_343_ = lean_ctor_get(v_out_341_, 0);
lean_inc(v_startPos_343_);
v_endPos_344_ = lean_ctor_get(v_out_341_, 1);
lean_inc(v_endPos_344_);
lean_dec_ref_known(v_out_341_, 2);
v___x_345_ = lean_apply_5(v_h__2_338_, v_it_342_, v_startPos_343_, v_endPos_344_, lean_box(0), lean_box(0));
return v___x_345_;
}
else
{
lean_object* v_it_346_; lean_object* v_startPos_347_; lean_object* v_endPos_348_; lean_object* v___x_349_; 
lean_dec(v_h__2_338_);
v_it_346_ = lean_ctor_get(v_x_336_, 0);
lean_inc(v_it_346_);
lean_dec_ref_known(v_x_336_, 2);
v_startPos_347_ = lean_ctor_get(v_out_341_, 0);
lean_inc(v_startPos_347_);
v_endPos_348_ = lean_ctor_get(v_out_341_, 1);
lean_inc(v_endPos_348_);
lean_dec_ref_known(v_out_341_, 2);
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
lean_dec_ref_known(v_x_336_, 1);
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
lean_dec_ref_known(v_x_358_, 2);
v_startPos_365_ = lean_ctor_get(v_out_363_, 0);
lean_inc(v_startPos_365_);
v_endPos_366_ = lean_ctor_get(v_out_363_, 1);
lean_inc(v_endPos_366_);
lean_dec_ref_known(v_out_363_, 2);
v___x_367_ = lean_apply_5(v_h__2_360_, v_it_364_, v_startPos_365_, v_endPos_366_, lean_box(0), lean_box(0));
return v___x_367_;
}
else
{
lean_object* v_it_368_; lean_object* v_startPos_369_; lean_object* v_endPos_370_; lean_object* v___x_371_; 
lean_dec(v_h__2_360_);
v_it_368_ = lean_ctor_get(v_x_358_, 0);
lean_inc(v_it_368_);
lean_dec_ref_known(v_x_358_, 2);
v_startPos_369_ = lean_ctor_get(v_out_363_, 0);
lean_inc(v_startPos_369_);
v_endPos_370_ = lean_ctor_get(v_out_363_, 1);
lean_inc(v_endPos_370_);
lean_dec_ref_known(v_out_363_, 2);
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
lean_dec_ref_known(v_x_358_, 1);
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
lean_dec_ref_known(v_x_386_, 2);
v_out_399_ = lean_ctor_get(v_x_387_, 1);
lean_inc(v_out_399_);
lean_dec_ref_known(v_x_387_, 2);
v_currPos_400_ = lean_ctor_get(v_it_396_, 0);
lean_inc(v_currPos_400_);
v_searcher_401_ = lean_ctor_get(v_it_396_, 1);
lean_inc(v_searcher_401_);
lean_dec_ref_known(v_it_396_, 2);
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
lean_dec_ref_known(v_x_386_, 2);
v_out_405_ = lean_ctor_get(v_x_387_, 1);
lean_inc(v_out_405_);
lean_dec_ref_known(v_x_387_, 2);
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
lean_dec_ref_known(v_x_387_, 1);
if (lean_obj_tag(v_it_407_) == 0)
{
lean_object* v_currPos_408_; lean_object* v_searcher_409_; lean_object* v_currPos_410_; lean_object* v_searcher_411_; lean_object* v___x_412_; 
lean_dec(v_h__4_391_);
v_currPos_408_ = lean_ctor_get(v_x_386_, 0);
lean_inc(v_currPos_408_);
v_searcher_409_ = lean_ctor_get(v_x_386_, 1);
lean_inc(v_searcher_409_);
lean_dec_ref_known(v_x_386_, 2);
v_currPos_410_ = lean_ctor_get(v_it_407_, 0);
lean_inc(v_currPos_410_);
v_searcher_411_ = lean_ctor_get(v_it_407_, 1);
lean_inc(v_searcher_411_);
lean_dec_ref_known(v_it_407_, 2);
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
lean_dec_ref_known(v_x_386_, 2);
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
lean_dec_ref_known(v_x_386_, 2);
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
lean_dec_ref_known(v_x_387_, 2);
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
lean_dec_ref_known(v_x_387_, 1);
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
lean_dec_ref_known(v_x_432_, 2);
v_out_445_ = lean_ctor_get(v_x_433_, 1);
lean_inc(v_out_445_);
lean_dec_ref_known(v_x_433_, 2);
v_currPos_446_ = lean_ctor_get(v_it_442_, 0);
lean_inc(v_currPos_446_);
v_searcher_447_ = lean_ctor_get(v_it_442_, 1);
lean_inc(v_searcher_447_);
lean_dec_ref_known(v_it_442_, 2);
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
lean_dec_ref_known(v_x_432_, 2);
v_out_451_ = lean_ctor_get(v_x_433_, 1);
lean_inc(v_out_451_);
lean_dec_ref_known(v_x_433_, 2);
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
lean_dec_ref_known(v_x_433_, 1);
if (lean_obj_tag(v_it_453_) == 0)
{
lean_object* v_currPos_454_; lean_object* v_searcher_455_; lean_object* v_currPos_456_; lean_object* v_searcher_457_; lean_object* v___x_458_; 
lean_dec(v_h__4_437_);
v_currPos_454_ = lean_ctor_get(v_x_432_, 0);
lean_inc(v_currPos_454_);
v_searcher_455_ = lean_ctor_get(v_x_432_, 1);
lean_inc(v_searcher_455_);
lean_dec_ref_known(v_x_432_, 2);
v_currPos_456_ = lean_ctor_get(v_it_453_, 0);
lean_inc(v_currPos_456_);
v_searcher_457_ = lean_ctor_get(v_it_453_, 1);
lean_inc(v_searcher_457_);
lean_dec_ref_known(v_it_453_, 2);
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
lean_dec_ref_known(v_x_432_, 2);
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
lean_dec_ref_known(v_x_432_, 2);
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
lean_dec_ref_known(v_x_433_, 2);
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
lean_dec_ref_known(v_x_433_, 1);
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
lean_dec_ref_known(v_x_489_, 2);
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
lean_dec_ref_known(v_x_503_, 2);
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
lean_dec_ref_known(v_____do__lift_540_, 1);
v___x_542_ = lean_apply_2(v_toPure_537_, lean_box(0), v_a_541_);
return v___x_542_;
}
else
{
lean_object* v_a_543_; lean_object* v___x_544_; 
lean_dec(v_toPure_537_);
v_a_543_ = lean_ctor_get(v_____do__lift_540_, 0);
lean_inc(v_a_543_);
lean_dec_ref_known(v_____do__lift_540_, 1);
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
lean_dec_ref_known(v_s_550_, 2);
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
lean_dec_ref_known(v_s_550_, 1);
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
lean_dec_ref_known(v_out_576_, 2);
lean_dec_ref(v_s_563_);
v_it_577_ = lean_ctor_get(v___x_575_, 0);
lean_inc(v_it_577_);
lean_dec_ref_known(v___x_575_, 2);
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
lean_dec_ref_known(v_out_576_, 2);
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
lean_dec_ref_known(v_t_710_, 2);
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
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default(lean_object* v_00_u03c3_783_, lean_object* v_00_u03c1_784_, lean_object* v_pat_785_, lean_object* v_s_786_, lean_object* v_inst_787_){
_start:
{
lean_object* v___x_788_; 
v___x_788_ = lean_box(1);
return v___x_788_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___boxed(lean_object* v_00_u03c3_789_, lean_object* v_00_u03c1_790_, lean_object* v_pat_791_, lean_object* v_s_792_, lean_object* v_inst_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default(v_00_u03c3_789_, v_00_u03c1_790_, v_pat_791_, v_s_792_, v_inst_793_);
lean_dec(v_inst_793_);
lean_dec_ref(v_s_792_);
lean_dec(v_pat_791_);
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
lean_object* v_currPos_810_; lean_object* v_searcher_811_; lean_object* v___x_813_; uint8_t v_isShared_814_; uint8_t v_isSharedCheck_864_; 
v_currPos_810_ = lean_ctor_get(v_x_809_, 0);
v_searcher_811_ = lean_ctor_get(v_x_809_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_x_809_);
if (v_isSharedCheck_864_ == 0)
{
v___x_813_ = v_x_809_;
v_isShared_814_ = v_isSharedCheck_864_;
goto v_resetjp_812_;
}
else
{
lean_inc(v_searcher_811_);
lean_inc(v_currPos_810_);
lean_dec(v_x_809_);
v___x_813_ = lean_box(0);
v_isShared_814_ = v_isSharedCheck_864_;
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
lean_dec_ref_known(v_out_816_, 2);
lean_dec_ref(v_s_808_);
v_it_817_ = lean_ctor_get(v___x_815_, 0);
lean_inc(v_it_817_);
lean_dec_ref_known(v___x_815_, 2);
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
lean_dec_ref_known(v_out_816_, 2);
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
lean_object* v_str_847_; lean_object* v_startInclusive_848_; lean_object* v_endExclusive_849_; lean_object* v___x_851_; uint8_t v_isShared_852_; uint8_t v_isSharedCheck_863_; 
lean_del_object(v___x_813_);
v_str_847_ = lean_ctor_get(v_s_808_, 0);
v_startInclusive_848_ = lean_ctor_get(v_s_808_, 1);
v_endExclusive_849_ = lean_ctor_get(v_s_808_, 2);
v_isSharedCheck_863_ = !lean_is_exclusive(v_s_808_);
if (v_isSharedCheck_863_ == 0)
{
v___x_851_ = v_s_808_;
v_isShared_852_ = v_isSharedCheck_863_;
goto v_resetjp_850_;
}
else
{
lean_inc(v_endExclusive_849_);
lean_inc(v_startInclusive_848_);
lean_inc(v_str_847_);
lean_dec(v_s_808_);
v___x_851_ = lean_box(0);
v_isShared_852_ = v_isSharedCheck_863_;
goto v_resetjp_850_;
}
v_resetjp_850_:
{
lean_object* v___x_853_; uint8_t v___x_854_; uint8_t v___x_855_; 
v___x_853_ = lean_nat_sub(v_endExclusive_849_, v_startInclusive_848_);
v___x_854_ = lean_nat_dec_eq(v_currPos_810_, v___x_853_);
lean_dec(v___x_853_);
v___x_855_ = lean_bool_not(v___x_854_);
if (v___x_855_ == 0)
{
lean_object* v___x_856_; 
lean_del_object(v___x_851_);
lean_dec(v_endExclusive_849_);
lean_dec(v_startInclusive_848_);
lean_dec_ref(v_str_847_);
lean_dec(v_currPos_810_);
v___x_856_ = lean_box(2);
return v___x_856_;
}
else
{
lean_object* v___x_857_; lean_object* v_slice_859_; 
v___x_857_ = lean_nat_add(v_startInclusive_848_, v_currPos_810_);
lean_dec(v_currPos_810_);
lean_dec(v_startInclusive_848_);
if (v_isShared_852_ == 0)
{
lean_ctor_set(v___x_851_, 1, v___x_857_);
v_slice_859_ = v___x_851_;
goto v_reusejp_858_;
}
else
{
lean_object* v_reuseFailAlloc_862_; 
v_reuseFailAlloc_862_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_862_, 0, v_str_847_);
lean_ctor_set(v_reuseFailAlloc_862_, 1, v___x_857_);
lean_ctor_set(v_reuseFailAlloc_862_, 2, v_endExclusive_849_);
v_slice_859_ = v_reuseFailAlloc_862_;
goto v_reusejp_858_;
}
v_reusejp_858_:
{
lean_object* v___x_860_; lean_object* v___x_861_; 
v___x_860_ = lean_box(1);
v___x_861_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_861_, 0, v___x_860_);
lean_ctor_set(v___x_861_, 1, v_slice_859_);
return v___x_861_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_865_; 
lean_dec_ref(v_s_808_);
lean_dec(v_inst_807_);
v___x_865_ = lean_box(2);
return v___x_865_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg(lean_object* v_inst_866_, lean_object* v_s_867_){
_start:
{
lean_object* v___f_868_; 
v___f_868_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_868_, 0, v_inst_866_);
lean_closure_set(v___f_868_, 1, v_s_867_);
return v___f_868_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId(lean_object* v_00_u03c1_869_, lean_object* v_00_u03c3_870_, lean_object* v_inst_871_, lean_object* v_pat_872_, lean_object* v_inst_873_, lean_object* v_s_874_){
_start:
{
lean_object* v___f_875_; 
v___f_875_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_875_, 0, v_inst_871_);
lean_closure_set(v___f_875_, 1, v_s_874_);
return v___f_875_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___boxed(lean_object* v_00_u03c1_876_, lean_object* v_00_u03c3_877_, lean_object* v_inst_878_, lean_object* v_pat_879_, lean_object* v_inst_880_, lean_object* v_s_881_){
_start:
{
lean_object* v_res_882_; 
v_res_882_ = l_String_Slice_SplitInclusiveIterator_instIteratorId(v_00_u03c1_876_, v_00_u03c3_877_, v_inst_878_, v_pat_879_, v_inst_880_, v_s_881_);
lean_dec(v_inst_880_);
lean_dec(v_pat_879_);
return v_res_882_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(lean_object* v_x_883_){
_start:
{
if (lean_obj_tag(v_x_883_) == 0)
{
lean_object* v_searcher_884_; lean_object* v___x_885_; 
v_searcher_884_ = lean_ctor_get(v_x_883_, 1);
lean_inc(v_searcher_884_);
v___x_885_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_885_, 0, v_searcher_884_);
return v___x_885_;
}
else
{
lean_object* v___x_886_; 
v___x_886_ = lean_box(0);
return v___x_886_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg___boxed(lean_object* v_x_887_){
_start:
{
lean_object* v_res_888_; 
v_res_888_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_887_);
lean_dec(v_x_887_);
return v_res_888_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(lean_object* v_00_u03c1_889_, lean_object* v_00_u03c3_890_, lean_object* v_pat_891_, lean_object* v_inst_892_, lean_object* v_s_893_, lean_object* v_x_894_){
_start:
{
lean_object* v___x_895_; 
v___x_895_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_894_);
return v___x_895_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___boxed(lean_object* v_00_u03c1_896_, lean_object* v_00_u03c3_897_, lean_object* v_pat_898_, lean_object* v_inst_899_, lean_object* v_s_900_, lean_object* v_x_901_){
_start:
{
lean_object* v_res_902_; 
v_res_902_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(v_00_u03c1_896_, v_00_u03c3_897_, v_pat_898_, v_inst_899_, v_s_900_, v_x_901_);
lean_dec(v_x_901_);
lean_dec_ref(v_s_900_);
lean_dec(v_inst_899_);
lean_dec(v_pat_898_);
return v_res_902_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___redArg(lean_object* v_x_903_, lean_object* v_h__1_904_, lean_object* v_h__2_905_){
_start:
{
if (lean_obj_tag(v_x_903_) == 0)
{
lean_object* v_currPos_906_; lean_object* v_searcher_907_; lean_object* v___x_908_; 
lean_dec(v_h__2_905_);
v_currPos_906_ = lean_ctor_get(v_x_903_, 0);
lean_inc(v_currPos_906_);
v_searcher_907_ = lean_ctor_get(v_x_903_, 1);
lean_inc(v_searcher_907_);
lean_dec_ref_known(v_x_903_, 2);
v___x_908_ = lean_apply_2(v_h__1_904_, v_currPos_906_, v_searcher_907_);
return v___x_908_;
}
else
{
lean_object* v___x_909_; lean_object* v___x_910_; 
lean_dec(v_h__1_904_);
v___x_909_ = lean_box(0);
v___x_910_ = lean_apply_1(v_h__2_905_, v___x_909_);
return v___x_910_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(lean_object* v_00_u03c1_911_, lean_object* v_00_u03c3_912_, lean_object* v_pat_913_, lean_object* v_inst_914_, lean_object* v_s_915_, lean_object* v_motive_916_, lean_object* v_x_917_, lean_object* v_h__1_918_, lean_object* v_h__2_919_){
_start:
{
if (lean_obj_tag(v_x_917_) == 0)
{
lean_object* v_currPos_920_; lean_object* v_searcher_921_; lean_object* v___x_922_; 
lean_dec(v_h__2_919_);
v_currPos_920_ = lean_ctor_get(v_x_917_, 0);
lean_inc(v_currPos_920_);
v_searcher_921_ = lean_ctor_get(v_x_917_, 1);
lean_inc(v_searcher_921_);
lean_dec_ref_known(v_x_917_, 2);
v___x_922_ = lean_apply_2(v_h__1_918_, v_currPos_920_, v_searcher_921_);
return v___x_922_;
}
else
{
lean_object* v___x_923_; lean_object* v___x_924_; 
lean_dec(v_h__1_918_);
v___x_923_ = lean_box(0);
v___x_924_ = lean_apply_1(v_h__2_919_, v___x_923_);
return v___x_924_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___boxed(lean_object* v_00_u03c1_925_, lean_object* v_00_u03c3_926_, lean_object* v_pat_927_, lean_object* v_inst_928_, lean_object* v_s_929_, lean_object* v_motive_930_, lean_object* v_x_931_, lean_object* v_h__1_932_, lean_object* v_h__2_933_){
_start:
{
lean_object* v_res_934_; 
v_res_934_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(v_00_u03c1_925_, v_00_u03c3_926_, v_pat_927_, v_inst_928_, v_s_929_, v_motive_930_, v_x_931_, v_h__1_932_, v_h__2_933_);
lean_dec_ref(v_s_929_);
lean_dec(v_inst_928_);
lean_dec(v_pat_927_);
return v_res_934_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___redArg(lean_object* v_x_935_, lean_object* v_x_936_, lean_object* v_h__1_937_, lean_object* v_h__2_938_, lean_object* v_h__3_939_, lean_object* v_h__4_940_, lean_object* v_h__5_941_, lean_object* v_h__6_942_, lean_object* v_h__7_943_, lean_object* v_h__8_944_){
_start:
{
if (lean_obj_tag(v_x_935_) == 0)
{
lean_dec(v_h__8_944_);
lean_dec(v_h__7_943_);
lean_dec(v_h__6_942_);
switch(lean_obj_tag(v_x_936_))
{
case 0:
{
lean_object* v_it_945_; 
lean_dec(v_h__5_941_);
lean_dec(v_h__4_940_);
lean_dec(v_h__3_939_);
v_it_945_ = lean_ctor_get(v_x_936_, 0);
if (lean_obj_tag(v_it_945_) == 0)
{
lean_object* v_currPos_946_; lean_object* v_searcher_947_; lean_object* v_out_948_; lean_object* v_currPos_949_; lean_object* v_searcher_950_; lean_object* v___x_951_; 
lean_inc_ref(v_it_945_);
lean_dec(v_h__2_938_);
v_currPos_946_ = lean_ctor_get(v_x_935_, 0);
lean_inc(v_currPos_946_);
v_searcher_947_ = lean_ctor_get(v_x_935_, 1);
lean_inc(v_searcher_947_);
lean_dec_ref_known(v_x_935_, 2);
v_out_948_ = lean_ctor_get(v_x_936_, 1);
lean_inc(v_out_948_);
lean_dec_ref_known(v_x_936_, 2);
v_currPos_949_ = lean_ctor_get(v_it_945_, 0);
lean_inc(v_currPos_949_);
v_searcher_950_ = lean_ctor_get(v_it_945_, 1);
lean_inc(v_searcher_950_);
lean_dec_ref_known(v_it_945_, 2);
v___x_951_ = lean_apply_5(v_h__1_937_, v_currPos_946_, v_searcher_947_, v_currPos_949_, v_searcher_950_, v_out_948_);
return v___x_951_;
}
else
{
lean_object* v_currPos_952_; lean_object* v_searcher_953_; lean_object* v_out_954_; lean_object* v___x_955_; 
lean_dec(v_h__1_937_);
v_currPos_952_ = lean_ctor_get(v_x_935_, 0);
lean_inc(v_currPos_952_);
v_searcher_953_ = lean_ctor_get(v_x_935_, 1);
lean_inc(v_searcher_953_);
lean_dec_ref_known(v_x_935_, 2);
v_out_954_ = lean_ctor_get(v_x_936_, 1);
lean_inc(v_out_954_);
lean_dec_ref_known(v_x_936_, 2);
v___x_955_ = lean_apply_3(v_h__2_938_, v_currPos_952_, v_searcher_953_, v_out_954_);
return v___x_955_;
}
}
case 1:
{
lean_object* v_it_956_; 
lean_dec(v_h__5_941_);
lean_dec(v_h__2_938_);
lean_dec(v_h__1_937_);
v_it_956_ = lean_ctor_get(v_x_936_, 0);
lean_inc(v_it_956_);
lean_dec_ref_known(v_x_936_, 1);
if (lean_obj_tag(v_it_956_) == 0)
{
lean_object* v_currPos_957_; lean_object* v_searcher_958_; lean_object* v_currPos_959_; lean_object* v_searcher_960_; lean_object* v___x_961_; 
lean_dec(v_h__4_940_);
v_currPos_957_ = lean_ctor_get(v_x_935_, 0);
lean_inc(v_currPos_957_);
v_searcher_958_ = lean_ctor_get(v_x_935_, 1);
lean_inc(v_searcher_958_);
lean_dec_ref_known(v_x_935_, 2);
v_currPos_959_ = lean_ctor_get(v_it_956_, 0);
lean_inc(v_currPos_959_);
v_searcher_960_ = lean_ctor_get(v_it_956_, 1);
lean_inc(v_searcher_960_);
lean_dec_ref_known(v_it_956_, 2);
v___x_961_ = lean_apply_4(v_h__3_939_, v_currPos_957_, v_searcher_958_, v_currPos_959_, v_searcher_960_);
return v___x_961_;
}
else
{
lean_object* v_currPos_962_; lean_object* v_searcher_963_; lean_object* v___x_964_; 
lean_dec(v_h__3_939_);
v_currPos_962_ = lean_ctor_get(v_x_935_, 0);
lean_inc(v_currPos_962_);
v_searcher_963_ = lean_ctor_get(v_x_935_, 1);
lean_inc(v_searcher_963_);
lean_dec_ref_known(v_x_935_, 2);
v___x_964_ = lean_apply_2(v_h__4_940_, v_currPos_962_, v_searcher_963_);
return v___x_964_;
}
}
default: 
{
lean_object* v_currPos_965_; lean_object* v_searcher_966_; lean_object* v___x_967_; 
lean_dec(v_h__4_940_);
lean_dec(v_h__3_939_);
lean_dec(v_h__2_938_);
lean_dec(v_h__1_937_);
v_currPos_965_ = lean_ctor_get(v_x_935_, 0);
lean_inc(v_currPos_965_);
v_searcher_966_ = lean_ctor_get(v_x_935_, 1);
lean_inc(v_searcher_966_);
lean_dec_ref_known(v_x_935_, 2);
v___x_967_ = lean_apply_2(v_h__5_941_, v_currPos_965_, v_searcher_966_);
return v___x_967_;
}
}
}
else
{
lean_dec(v_h__5_941_);
lean_dec(v_h__4_940_);
lean_dec(v_h__3_939_);
lean_dec(v_h__2_938_);
lean_dec(v_h__1_937_);
switch(lean_obj_tag(v_x_936_))
{
case 0:
{
lean_object* v_it_968_; lean_object* v_out_969_; lean_object* v___x_970_; 
lean_dec(v_h__8_944_);
lean_dec(v_h__7_943_);
v_it_968_ = lean_ctor_get(v_x_936_, 0);
lean_inc(v_it_968_);
v_out_969_ = lean_ctor_get(v_x_936_, 1);
lean_inc(v_out_969_);
lean_dec_ref_known(v_x_936_, 2);
v___x_970_ = lean_apply_2(v_h__6_942_, v_it_968_, v_out_969_);
return v___x_970_;
}
case 1:
{
lean_object* v_it_971_; lean_object* v___x_972_; 
lean_dec(v_h__8_944_);
lean_dec(v_h__6_942_);
v_it_971_ = lean_ctor_get(v_x_936_, 0);
lean_inc(v_it_971_);
lean_dec_ref_known(v_x_936_, 1);
v___x_972_ = lean_apply_1(v_h__7_943_, v_it_971_);
return v___x_972_;
}
default: 
{
lean_object* v___x_973_; lean_object* v___x_974_; 
lean_dec(v_h__7_943_);
lean_dec(v_h__6_942_);
v___x_973_ = lean_box(0);
v___x_974_ = lean_apply_1(v_h__8_944_, v___x_973_);
return v___x_974_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(lean_object* v_00_u03c1_975_, lean_object* v_00_u03c3_976_, lean_object* v_pat_977_, lean_object* v_inst_978_, lean_object* v_s_979_, lean_object* v_motive_980_, lean_object* v_x_981_, lean_object* v_x_982_, lean_object* v_h__1_983_, lean_object* v_h__2_984_, lean_object* v_h__3_985_, lean_object* v_h__4_986_, lean_object* v_h__5_987_, lean_object* v_h__6_988_, lean_object* v_h__7_989_, lean_object* v_h__8_990_){
_start:
{
if (lean_obj_tag(v_x_981_) == 0)
{
lean_dec(v_h__8_990_);
lean_dec(v_h__7_989_);
lean_dec(v_h__6_988_);
switch(lean_obj_tag(v_x_982_))
{
case 0:
{
lean_object* v_it_991_; 
lean_dec(v_h__5_987_);
lean_dec(v_h__4_986_);
lean_dec(v_h__3_985_);
v_it_991_ = lean_ctor_get(v_x_982_, 0);
if (lean_obj_tag(v_it_991_) == 0)
{
lean_object* v_currPos_992_; lean_object* v_searcher_993_; lean_object* v_out_994_; lean_object* v_currPos_995_; lean_object* v_searcher_996_; lean_object* v___x_997_; 
lean_inc_ref(v_it_991_);
lean_dec(v_h__2_984_);
v_currPos_992_ = lean_ctor_get(v_x_981_, 0);
lean_inc(v_currPos_992_);
v_searcher_993_ = lean_ctor_get(v_x_981_, 1);
lean_inc(v_searcher_993_);
lean_dec_ref_known(v_x_981_, 2);
v_out_994_ = lean_ctor_get(v_x_982_, 1);
lean_inc(v_out_994_);
lean_dec_ref_known(v_x_982_, 2);
v_currPos_995_ = lean_ctor_get(v_it_991_, 0);
lean_inc(v_currPos_995_);
v_searcher_996_ = lean_ctor_get(v_it_991_, 1);
lean_inc(v_searcher_996_);
lean_dec_ref_known(v_it_991_, 2);
v___x_997_ = lean_apply_5(v_h__1_983_, v_currPos_992_, v_searcher_993_, v_currPos_995_, v_searcher_996_, v_out_994_);
return v___x_997_;
}
else
{
lean_object* v_currPos_998_; lean_object* v_searcher_999_; lean_object* v_out_1000_; lean_object* v___x_1001_; 
lean_dec(v_h__1_983_);
v_currPos_998_ = lean_ctor_get(v_x_981_, 0);
lean_inc(v_currPos_998_);
v_searcher_999_ = lean_ctor_get(v_x_981_, 1);
lean_inc(v_searcher_999_);
lean_dec_ref_known(v_x_981_, 2);
v_out_1000_ = lean_ctor_get(v_x_982_, 1);
lean_inc(v_out_1000_);
lean_dec_ref_known(v_x_982_, 2);
v___x_1001_ = lean_apply_3(v_h__2_984_, v_currPos_998_, v_searcher_999_, v_out_1000_);
return v___x_1001_;
}
}
case 1:
{
lean_object* v_it_1002_; 
lean_dec(v_h__5_987_);
lean_dec(v_h__2_984_);
lean_dec(v_h__1_983_);
v_it_1002_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_it_1002_);
lean_dec_ref_known(v_x_982_, 1);
if (lean_obj_tag(v_it_1002_) == 0)
{
lean_object* v_currPos_1003_; lean_object* v_searcher_1004_; lean_object* v_currPos_1005_; lean_object* v_searcher_1006_; lean_object* v___x_1007_; 
lean_dec(v_h__4_986_);
v_currPos_1003_ = lean_ctor_get(v_x_981_, 0);
lean_inc(v_currPos_1003_);
v_searcher_1004_ = lean_ctor_get(v_x_981_, 1);
lean_inc(v_searcher_1004_);
lean_dec_ref_known(v_x_981_, 2);
v_currPos_1005_ = lean_ctor_get(v_it_1002_, 0);
lean_inc(v_currPos_1005_);
v_searcher_1006_ = lean_ctor_get(v_it_1002_, 1);
lean_inc(v_searcher_1006_);
lean_dec_ref_known(v_it_1002_, 2);
v___x_1007_ = lean_apply_4(v_h__3_985_, v_currPos_1003_, v_searcher_1004_, v_currPos_1005_, v_searcher_1006_);
return v___x_1007_;
}
else
{
lean_object* v_currPos_1008_; lean_object* v_searcher_1009_; lean_object* v___x_1010_; 
lean_dec(v_h__3_985_);
v_currPos_1008_ = lean_ctor_get(v_x_981_, 0);
lean_inc(v_currPos_1008_);
v_searcher_1009_ = lean_ctor_get(v_x_981_, 1);
lean_inc(v_searcher_1009_);
lean_dec_ref_known(v_x_981_, 2);
v___x_1010_ = lean_apply_2(v_h__4_986_, v_currPos_1008_, v_searcher_1009_);
return v___x_1010_;
}
}
default: 
{
lean_object* v_currPos_1011_; lean_object* v_searcher_1012_; lean_object* v___x_1013_; 
lean_dec(v_h__4_986_);
lean_dec(v_h__3_985_);
lean_dec(v_h__2_984_);
lean_dec(v_h__1_983_);
v_currPos_1011_ = lean_ctor_get(v_x_981_, 0);
lean_inc(v_currPos_1011_);
v_searcher_1012_ = lean_ctor_get(v_x_981_, 1);
lean_inc(v_searcher_1012_);
lean_dec_ref_known(v_x_981_, 2);
v___x_1013_ = lean_apply_2(v_h__5_987_, v_currPos_1011_, v_searcher_1012_);
return v___x_1013_;
}
}
}
else
{
lean_dec(v_h__5_987_);
lean_dec(v_h__4_986_);
lean_dec(v_h__3_985_);
lean_dec(v_h__2_984_);
lean_dec(v_h__1_983_);
switch(lean_obj_tag(v_x_982_))
{
case 0:
{
lean_object* v_it_1014_; lean_object* v_out_1015_; lean_object* v___x_1016_; 
lean_dec(v_h__8_990_);
lean_dec(v_h__7_989_);
v_it_1014_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_it_1014_);
v_out_1015_ = lean_ctor_get(v_x_982_, 1);
lean_inc(v_out_1015_);
lean_dec_ref_known(v_x_982_, 2);
v___x_1016_ = lean_apply_2(v_h__6_988_, v_it_1014_, v_out_1015_);
return v___x_1016_;
}
case 1:
{
lean_object* v_it_1017_; lean_object* v___x_1018_; 
lean_dec(v_h__8_990_);
lean_dec(v_h__6_988_);
v_it_1017_ = lean_ctor_get(v_x_982_, 0);
lean_inc(v_it_1017_);
lean_dec_ref_known(v_x_982_, 1);
v___x_1018_ = lean_apply_1(v_h__7_989_, v_it_1017_);
return v___x_1018_;
}
default: 
{
lean_object* v___x_1019_; lean_object* v___x_1020_; 
lean_dec(v_h__7_989_);
lean_dec(v_h__6_988_);
v___x_1019_ = lean_box(0);
v___x_1020_ = lean_apply_1(v_h__8_990_, v___x_1019_);
return v___x_1020_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___boxed(lean_object* v_00_u03c1_1021_, lean_object* v_00_u03c3_1022_, lean_object* v_pat_1023_, lean_object* v_inst_1024_, lean_object* v_s_1025_, lean_object* v_motive_1026_, lean_object* v_x_1027_, lean_object* v_x_1028_, lean_object* v_h__1_1029_, lean_object* v_h__2_1030_, lean_object* v_h__3_1031_, lean_object* v_h__4_1032_, lean_object* v_h__5_1033_, lean_object* v_h__6_1034_, lean_object* v_h__7_1035_, lean_object* v_h__8_1036_){
_start:
{
lean_object* v_res_1037_; 
v_res_1037_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(v_00_u03c1_1021_, v_00_u03c3_1022_, v_pat_1023_, v_inst_1024_, v_s_1025_, v_motive_1026_, v_x_1027_, v_x_1028_, v_h__1_1029_, v_h__2_1030_, v_h__3_1031_, v_h__4_1032_, v_h__5_1033_, v_h__6_1034_, v_h__7_1035_, v_h__8_1036_);
lean_dec_ref(v_s_1025_);
lean_dec(v_inst_1024_);
lean_dec(v_pat_1023_);
return v_res_1037_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___redArg(lean_object* v_x_1038_, lean_object* v_h__1_1039_, lean_object* v_h__2_1040_){
_start:
{
if (lean_obj_tag(v_x_1038_) == 0)
{
lean_object* v_currPos_1041_; lean_object* v_searcher_1042_; lean_object* v___x_1043_; 
lean_dec(v_h__2_1040_);
v_currPos_1041_ = lean_ctor_get(v_x_1038_, 0);
lean_inc(v_currPos_1041_);
v_searcher_1042_ = lean_ctor_get(v_x_1038_, 1);
lean_inc(v_searcher_1042_);
lean_dec_ref_known(v_x_1038_, 2);
v___x_1043_ = lean_apply_2(v_h__1_1039_, v_currPos_1041_, v_searcher_1042_);
return v___x_1043_;
}
else
{
lean_object* v___x_1044_; lean_object* v___x_1045_; 
lean_dec(v_h__1_1039_);
v___x_1044_ = lean_box(0);
v___x_1045_ = lean_apply_1(v_h__2_1040_, v___x_1044_);
return v___x_1045_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_1046_, lean_object* v_00_u03c3_1047_, lean_object* v_pat_1048_, lean_object* v_inst_1049_, lean_object* v_s_1050_, lean_object* v_motive_1051_, lean_object* v_x_1052_, lean_object* v_h__1_1053_, lean_object* v_h__2_1054_){
_start:
{
if (lean_obj_tag(v_x_1052_) == 0)
{
lean_object* v_currPos_1055_; lean_object* v_searcher_1056_; lean_object* v___x_1057_; 
lean_dec(v_h__2_1054_);
v_currPos_1055_ = lean_ctor_get(v_x_1052_, 0);
lean_inc(v_currPos_1055_);
v_searcher_1056_ = lean_ctor_get(v_x_1052_, 1);
lean_inc(v_searcher_1056_);
lean_dec_ref_known(v_x_1052_, 2);
v___x_1057_ = lean_apply_2(v_h__1_1053_, v_currPos_1055_, v_searcher_1056_);
return v___x_1057_;
}
else
{
lean_object* v___x_1058_; lean_object* v___x_1059_; 
lean_dec(v_h__1_1053_);
v___x_1058_ = lean_box(0);
v___x_1059_ = lean_apply_1(v_h__2_1054_, v___x_1058_);
return v___x_1059_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_1060_, lean_object* v_00_u03c3_1061_, lean_object* v_pat_1062_, lean_object* v_inst_1063_, lean_object* v_s_1064_, lean_object* v_motive_1065_, lean_object* v_x_1066_, lean_object* v_h__1_1067_, lean_object* v_h__2_1068_){
_start:
{
lean_object* v_res_1069_; 
v_res_1069_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(v_00_u03c1_1060_, v_00_u03c3_1061_, v_pat_1062_, v_inst_1063_, v_s_1064_, v_motive_1065_, v_x_1066_, v_h__1_1067_, v_h__2_1068_);
lean_dec_ref(v_s_1064_);
lean_dec(v_inst_1063_);
lean_dec(v_pat_1062_);
return v_res_1069_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(lean_object* v_00_u03c1_1070_, lean_object* v_00_u03c3_1071_, lean_object* v_inst_1072_, lean_object* v_pat_1073_, lean_object* v_inst_1074_, lean_object* v_s_1075_, lean_object* v_inst_1076_){
_start:
{
lean_object* v___x_1077_; 
v___x_1077_ = lean_box(0);
return v___x_1077_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_1078_, lean_object* v_00_u03c3_1079_, lean_object* v_inst_1080_, lean_object* v_pat_1081_, lean_object* v_inst_1082_, lean_object* v_s_1083_, lean_object* v_inst_1084_){
_start:
{
lean_object* v_res_1085_; 
v_res_1085_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(v_00_u03c1_1078_, v_00_u03c3_1079_, v_inst_1080_, v_pat_1081_, v_inst_1082_, v_s_1083_, v_inst_1084_);
lean_dec_ref(v_s_1083_);
lean_dec(v_inst_1082_);
lean_dec(v_pat_1081_);
lean_dec(v_inst_1080_);
return v_res_1085_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0(lean_object* v_toPure_1086_, lean_object* v_recur_1087_, lean_object* v_it_1088_, lean_object* v_____do__lift_1089_){
_start:
{
if (lean_obj_tag(v_____do__lift_1089_) == 0)
{
lean_object* v_a_1090_; lean_object* v___x_1091_; 
lean_dec(v_it_1088_);
lean_dec(v_recur_1087_);
v_a_1090_ = lean_ctor_get(v_____do__lift_1089_, 0);
lean_inc(v_a_1090_);
lean_dec_ref_known(v_____do__lift_1089_, 1);
v___x_1091_ = lean_apply_2(v_toPure_1086_, lean_box(0), v_a_1090_);
return v___x_1091_;
}
else
{
lean_object* v_a_1092_; lean_object* v___x_1093_; 
lean_dec(v_toPure_1086_);
v_a_1092_ = lean_ctor_get(v_____do__lift_1089_, 0);
lean_inc(v_a_1092_);
lean_dec_ref_known(v_____do__lift_1089_, 1);
v___x_1093_ = lean_apply_4(v_recur_1087_, v_it_1088_, v_a_1092_, lean_box(0), lean_box(0));
return v___x_1093_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1(lean_object* v_toPure_1094_, lean_object* v_recur_1095_, lean_object* v___y_1096_, lean_object* v_acc_1097_, lean_object* v_toBind_1098_, lean_object* v_s_1099_){
_start:
{
switch(lean_obj_tag(v_s_1099_))
{
case 0:
{
lean_object* v_it_1100_; lean_object* v_out_1101_; lean_object* v___f_1102_; lean_object* v___x_1103_; lean_object* v___x_1104_; 
v_it_1100_ = lean_ctor_get(v_s_1099_, 0);
lean_inc(v_it_1100_);
v_out_1101_ = lean_ctor_get(v_s_1099_, 1);
lean_inc(v_out_1101_);
lean_dec_ref_known(v_s_1099_, 2);
v___f_1102_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1102_, 0, v_toPure_1094_);
lean_closure_set(v___f_1102_, 1, v_recur_1095_);
lean_closure_set(v___f_1102_, 2, v_it_1100_);
v___x_1103_ = lean_apply_3(v___y_1096_, v_out_1101_, lean_box(0), v_acc_1097_);
v___x_1104_ = lean_apply_4(v_toBind_1098_, lean_box(0), lean_box(0), v___x_1103_, v___f_1102_);
return v___x_1104_;
}
case 1:
{
lean_object* v_it_1105_; lean_object* v___x_1106_; 
lean_dec(v_toBind_1098_);
lean_dec(v___y_1096_);
lean_dec(v_toPure_1094_);
v_it_1105_ = lean_ctor_get(v_s_1099_, 0);
lean_inc(v_it_1105_);
lean_dec_ref_known(v_s_1099_, 1);
v___x_1106_ = lean_apply_4(v_recur_1095_, v_it_1105_, v_acc_1097_, lean_box(0), lean_box(0));
return v___x_1106_;
}
default: 
{
lean_object* v___x_1107_; 
lean_dec(v_toBind_1098_);
lean_dec(v___y_1096_);
lean_dec(v_recur_1095_);
v___x_1107_ = lean_apply_2(v_toPure_1094_, lean_box(0), v_acc_1097_);
return v___x_1107_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2(lean_object* v_toPure_1108_, lean_object* v___y_1109_, lean_object* v_toBind_1110_, lean_object* v_inst_1111_, lean_object* v_s_1112_, lean_object* v_lift_1113_, lean_object* v_it_1114_, lean_object* v_acc_1115_, lean_object* v_hP_1116_, lean_object* v_recur_1117_){
_start:
{
lean_object* v___f_1118_; 
v___f_1118_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_1118_, 0, v_toPure_1108_);
lean_closure_set(v___f_1118_, 1, v_recur_1117_);
lean_closure_set(v___f_1118_, 2, v___y_1109_);
lean_closure_set(v___f_1118_, 3, v_acc_1115_);
lean_closure_set(v___f_1118_, 4, v_toBind_1110_);
if (lean_obj_tag(v_it_1114_) == 0)
{
lean_object* v_currPos_1119_; lean_object* v_searcher_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1178_; 
v_currPos_1119_ = lean_ctor_get(v_it_1114_, 0);
v_searcher_1120_ = lean_ctor_get(v_it_1114_, 1);
v_isSharedCheck_1178_ = !lean_is_exclusive(v_it_1114_);
if (v_isSharedCheck_1178_ == 0)
{
v___x_1122_ = v_it_1114_;
v_isShared_1123_ = v_isSharedCheck_1178_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_searcher_1120_);
lean_inc(v_currPos_1119_);
lean_dec(v_it_1114_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1178_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1124_; 
lean_inc_ref(v_s_1112_);
v___x_1124_ = lean_apply_2(v_inst_1111_, v_s_1112_, v_searcher_1120_);
switch(lean_obj_tag(v___x_1124_))
{
case 0:
{
lean_object* v_out_1125_; 
v_out_1125_ = lean_ctor_get(v___x_1124_, 1);
lean_inc(v_out_1125_);
if (lean_obj_tag(v_out_1125_) == 0)
{
lean_object* v_it_1126_; lean_object* v___x_1128_; 
lean_dec_ref_known(v_out_1125_, 2);
lean_dec_ref(v_s_1112_);
v_it_1126_ = lean_ctor_get(v___x_1124_, 0);
lean_inc(v_it_1126_);
lean_dec_ref_known(v___x_1124_, 2);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v_it_1126_);
v___x_1128_ = v___x_1122_;
goto v_reusejp_1127_;
}
else
{
lean_object* v_reuseFailAlloc_1131_; 
v_reuseFailAlloc_1131_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1131_, 0, v_currPos_1119_);
lean_ctor_set(v_reuseFailAlloc_1131_, 1, v_it_1126_);
v___x_1128_ = v_reuseFailAlloc_1131_;
goto v_reusejp_1127_;
}
v_reusejp_1127_:
{
lean_object* v___x_1129_; lean_object* v___x_1130_; 
v___x_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1129_, 0, v___x_1128_);
v___x_1130_ = lean_apply_4(v_lift_1113_, lean_box(0), lean_box(0), v___f_1118_, v___x_1129_);
return v___x_1130_;
}
}
else
{
lean_object* v_it_1132_; lean_object* v___x_1134_; uint8_t v_isShared_1135_; uint8_t v_isSharedCheck_1145_; 
v_it_1132_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1145_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1145_ == 0)
{
lean_object* v_unused_1146_; 
v_unused_1146_ = lean_ctor_get(v___x_1124_, 1);
lean_dec(v_unused_1146_);
v___x_1134_ = v___x_1124_;
v_isShared_1135_ = v_isSharedCheck_1145_;
goto v_resetjp_1133_;
}
else
{
lean_inc(v_it_1132_);
lean_dec(v___x_1124_);
v___x_1134_ = lean_box(0);
v_isShared_1135_ = v_isSharedCheck_1145_;
goto v_resetjp_1133_;
}
v_resetjp_1133_:
{
lean_object* v_endPos_1136_; lean_object* v_slice_1137_; lean_object* v_nextIt_1139_; 
v_endPos_1136_ = lean_ctor_get(v_out_1125_, 1);
lean_inc(v_endPos_1136_);
lean_dec_ref_known(v_out_1125_, 2);
v_slice_1137_ = l_String_Slice_slice_x21(v_s_1112_, v_currPos_1119_, v_endPos_1136_);
lean_dec(v_currPos_1119_);
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v_it_1132_);
lean_ctor_set(v___x_1122_, 0, v_endPos_1136_);
v_nextIt_1139_ = v___x_1122_;
goto v_reusejp_1138_;
}
else
{
lean_object* v_reuseFailAlloc_1144_; 
v_reuseFailAlloc_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1144_, 0, v_endPos_1136_);
lean_ctor_set(v_reuseFailAlloc_1144_, 1, v_it_1132_);
v_nextIt_1139_ = v_reuseFailAlloc_1144_;
goto v_reusejp_1138_;
}
v_reusejp_1138_:
{
lean_object* v___x_1141_; 
if (v_isShared_1135_ == 0)
{
lean_ctor_set(v___x_1134_, 1, v_slice_1137_);
lean_ctor_set(v___x_1134_, 0, v_nextIt_1139_);
v___x_1141_ = v___x_1134_;
goto v_reusejp_1140_;
}
else
{
lean_object* v_reuseFailAlloc_1143_; 
v_reuseFailAlloc_1143_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1143_, 0, v_nextIt_1139_);
lean_ctor_set(v_reuseFailAlloc_1143_, 1, v_slice_1137_);
v___x_1141_ = v_reuseFailAlloc_1143_;
goto v_reusejp_1140_;
}
v_reusejp_1140_:
{
lean_object* v___x_1142_; 
v___x_1142_ = lean_apply_4(v_lift_1113_, lean_box(0), lean_box(0), v___f_1118_, v___x_1141_);
return v___x_1142_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1147_; lean_object* v___x_1149_; uint8_t v_isShared_1150_; uint8_t v_isSharedCheck_1158_; 
lean_dec_ref(v_s_1112_);
v_it_1147_ = lean_ctor_get(v___x_1124_, 0);
v_isSharedCheck_1158_ = !lean_is_exclusive(v___x_1124_);
if (v_isSharedCheck_1158_ == 0)
{
v___x_1149_ = v___x_1124_;
v_isShared_1150_ = v_isSharedCheck_1158_;
goto v_resetjp_1148_;
}
else
{
lean_inc(v_it_1147_);
lean_dec(v___x_1124_);
v___x_1149_ = lean_box(0);
v_isShared_1150_ = v_isSharedCheck_1158_;
goto v_resetjp_1148_;
}
v_resetjp_1148_:
{
lean_object* v___x_1152_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 1, v_it_1147_);
v___x_1152_ = v___x_1122_;
goto v_reusejp_1151_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_currPos_1119_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_it_1147_);
v___x_1152_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1151_;
}
v_reusejp_1151_:
{
lean_object* v___x_1154_; 
if (v_isShared_1150_ == 0)
{
lean_ctor_set(v___x_1149_, 0, v___x_1152_);
v___x_1154_ = v___x_1149_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1156_; 
v_reuseFailAlloc_1156_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1156_, 0, v___x_1152_);
v___x_1154_ = v_reuseFailAlloc_1156_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; 
v___x_1155_ = lean_apply_4(v_lift_1113_, lean_box(0), lean_box(0), v___f_1118_, v___x_1154_);
return v___x_1155_;
}
}
}
}
default: 
{
lean_object* v_str_1159_; lean_object* v_startInclusive_1160_; lean_object* v_endExclusive_1161_; lean_object* v___x_1163_; uint8_t v_isShared_1164_; uint8_t v_isSharedCheck_1177_; 
lean_del_object(v___x_1122_);
v_str_1159_ = lean_ctor_get(v_s_1112_, 0);
v_startInclusive_1160_ = lean_ctor_get(v_s_1112_, 1);
v_endExclusive_1161_ = lean_ctor_get(v_s_1112_, 2);
v_isSharedCheck_1177_ = !lean_is_exclusive(v_s_1112_);
if (v_isSharedCheck_1177_ == 0)
{
v___x_1163_ = v_s_1112_;
v_isShared_1164_ = v_isSharedCheck_1177_;
goto v_resetjp_1162_;
}
else
{
lean_inc(v_endExclusive_1161_);
lean_inc(v_startInclusive_1160_);
lean_inc(v_str_1159_);
lean_dec(v_s_1112_);
v___x_1163_ = lean_box(0);
v_isShared_1164_ = v_isSharedCheck_1177_;
goto v_resetjp_1162_;
}
v_resetjp_1162_:
{
lean_object* v___x_1165_; uint8_t v___x_1166_; uint8_t v___x_1167_; 
v___x_1165_ = lean_nat_sub(v_endExclusive_1161_, v_startInclusive_1160_);
v___x_1166_ = lean_nat_dec_eq(v_currPos_1119_, v___x_1165_);
lean_dec(v___x_1165_);
v___x_1167_ = lean_bool_not(v___x_1166_);
if (v___x_1167_ == 0)
{
lean_object* v___x_1168_; lean_object* v___x_1169_; 
lean_del_object(v___x_1163_);
lean_dec(v_endExclusive_1161_);
lean_dec(v_startInclusive_1160_);
lean_dec_ref(v_str_1159_);
lean_dec(v_currPos_1119_);
v___x_1168_ = lean_box(2);
v___x_1169_ = lean_apply_4(v_lift_1113_, lean_box(0), lean_box(0), v___f_1118_, v___x_1168_);
return v___x_1169_;
}
else
{
lean_object* v___x_1170_; lean_object* v_slice_1172_; 
v___x_1170_ = lean_nat_add(v_startInclusive_1160_, v_currPos_1119_);
lean_dec(v_currPos_1119_);
lean_dec(v_startInclusive_1160_);
if (v_isShared_1164_ == 0)
{
lean_ctor_set(v___x_1163_, 1, v___x_1170_);
v_slice_1172_ = v___x_1163_;
goto v_reusejp_1171_;
}
else
{
lean_object* v_reuseFailAlloc_1176_; 
v_reuseFailAlloc_1176_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1176_, 0, v_str_1159_);
lean_ctor_set(v_reuseFailAlloc_1176_, 1, v___x_1170_);
lean_ctor_set(v_reuseFailAlloc_1176_, 2, v_endExclusive_1161_);
v_slice_1172_ = v_reuseFailAlloc_1176_;
goto v_reusejp_1171_;
}
v_reusejp_1171_:
{
lean_object* v___x_1173_; lean_object* v___x_1174_; lean_object* v___x_1175_; 
v___x_1173_ = lean_box(1);
v___x_1174_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1174_, 0, v___x_1173_);
lean_ctor_set(v___x_1174_, 1, v_slice_1172_);
v___x_1175_ = lean_apply_4(v_lift_1113_, lean_box(0), lean_box(0), v___f_1118_, v___x_1174_);
return v___x_1175_;
}
}
}
}
}
}
}
else
{
lean_object* v___x_1179_; lean_object* v___x_1180_; 
lean_dec_ref(v_s_1112_);
lean_dec(v_inst_1111_);
v___x_1179_ = lean_box(2);
v___x_1180_ = lean_apply_4(v_lift_1113_, lean_box(0), lean_box(0), v___f_1118_, v___x_1179_);
return v___x_1180_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3(lean_object* v_inst_1181_, lean_object* v_inst_1182_, lean_object* v_s_1183_, lean_object* v_lift_1184_, lean_object* v_00_u03b3_1185_, lean_object* v_Pl_1186_, lean_object* v_it_1187_, lean_object* v_init_1188_, lean_object* v___y_1189_){
_start:
{
lean_object* v_toApplicative_1190_; lean_object* v_toBind_1191_; lean_object* v_toPure_1192_; lean_object* v___f_1193_; lean_object* v___x_1194_; 
v_toApplicative_1190_ = lean_ctor_get(v_inst_1181_, 0);
lean_inc_ref(v_toApplicative_1190_);
v_toBind_1191_ = lean_ctor_get(v_inst_1181_, 1);
lean_inc(v_toBind_1191_);
lean_dec_ref(v_inst_1181_);
v_toPure_1192_ = lean_ctor_get(v_toApplicative_1190_, 1);
lean_inc(v_toPure_1192_);
lean_dec_ref(v_toApplicative_1190_);
v___f_1193_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_1193_, 0, v_toPure_1192_);
lean_closure_set(v___f_1193_, 1, v___y_1189_);
lean_closure_set(v___f_1193_, 2, v_toBind_1191_);
lean_closure_set(v___f_1193_, 3, v_inst_1182_);
lean_closure_set(v___f_1193_, 4, v_s_1183_);
lean_closure_set(v___f_1193_, 5, v_lift_1184_);
v___x_1194_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1193_, v_it_1187_, v_init_1188_, lean_box(0));
return v___x_1194_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg(lean_object* v_inst_1195_, lean_object* v_inst_1196_, lean_object* v_s_1197_){
_start:
{
lean_object* v___f_1198_; 
v___f_1198_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1198_, 0, v_inst_1196_);
lean_closure_set(v___f_1198_, 1, v_inst_1195_);
lean_closure_set(v___f_1198_, 2, v_s_1197_);
return v___f_1198_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(lean_object* v_00_u03c1_1199_, lean_object* v_00_u03c3_1200_, lean_object* v_inst_1201_, lean_object* v_pat_1202_, lean_object* v_inst_1203_, lean_object* v_n_1204_, lean_object* v_inst_1205_, lean_object* v_s_1206_){
_start:
{
lean_object* v___f_1207_; 
v___f_1207_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1207_, 0, v_inst_1205_);
lean_closure_set(v___f_1207_, 1, v_inst_1201_);
lean_closure_set(v___f_1207_, 2, v_s_1206_);
return v___f_1207_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___boxed(lean_object* v_00_u03c1_1208_, lean_object* v_00_u03c3_1209_, lean_object* v_inst_1210_, lean_object* v_pat_1211_, lean_object* v_inst_1212_, lean_object* v_n_1213_, lean_object* v_inst_1214_, lean_object* v_s_1215_){
_start:
{
lean_object* v_res_1216_; 
v_res_1216_ = l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(v_00_u03c1_1208_, v_00_u03c3_1209_, v_inst_1210_, v_pat_1211_, v_inst_1212_, v_n_1213_, v_inst_1214_, v_s_1215_);
lean_dec(v_inst_1212_);
lean_dec(v_pat_1211_);
return v_res_1216_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___redArg(lean_object* v_s_1217_, lean_object* v_inst_1218_){
_start:
{
lean_object* v___x_1219_; lean_object* v___x_1220_; lean_object* v___x_1221_; 
v___x_1219_ = lean_unsigned_to_nat(0u);
v___x_1220_ = lean_apply_1(v_inst_1218_, v_s_1217_);
v___x_1221_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1221_, 0, v___x_1219_);
lean_ctor_set(v___x_1221_, 1, v___x_1220_);
return v___x_1221_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive(lean_object* v_00_u03c1_1222_, lean_object* v_00_u03c3_1223_, lean_object* v_s_1224_, lean_object* v_pat_1225_, lean_object* v_inst_1226_){
_start:
{
lean_object* v___x_1227_; 
v___x_1227_ = l_String_Slice_splitInclusive___redArg(v_s_1224_, v_inst_1226_);
return v___x_1227_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___boxed(lean_object* v_00_u03c1_1228_, lean_object* v_00_u03c3_1229_, lean_object* v_s_1230_, lean_object* v_pat_1231_, lean_object* v_inst_1232_){
_start:
{
lean_object* v_res_1233_; 
v_res_1233_ = l_String_Slice_splitInclusive(v_00_u03c1_1228_, v_00_u03c3_1229_, v_s_1230_, v_pat_1231_, v_inst_1232_);
lean_dec(v_pat_1231_);
return v_res_1233_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___redArg(lean_object* v_s_1234_, lean_object* v_inst_1235_){
_start:
{
lean_object* v_skipPrefix_x3f_1236_; lean_object* v___x_1237_; 
v_skipPrefix_x3f_1236_ = lean_ctor_get(v_inst_1235_, 0);
lean_inc_ref(v_skipPrefix_x3f_1236_);
lean_dec_ref(v_inst_1235_);
v___x_1237_ = lean_apply_1(v_skipPrefix_x3f_1236_, v_s_1234_);
return v___x_1237_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f(lean_object* v_00_u03c1_1238_, lean_object* v_s_1239_, lean_object* v_pat_1240_, lean_object* v_inst_1241_){
_start:
{
lean_object* v_skipPrefix_x3f_1242_; lean_object* v___x_1243_; 
v_skipPrefix_x3f_1242_ = lean_ctor_get(v_inst_1241_, 0);
lean_inc_ref(v_skipPrefix_x3f_1242_);
lean_dec_ref(v_inst_1241_);
v___x_1243_ = lean_apply_1(v_skipPrefix_x3f_1242_, v_s_1239_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___boxed(lean_object* v_00_u03c1_1244_, lean_object* v_s_1245_, lean_object* v_pat_1246_, lean_object* v_inst_1247_){
_start:
{
lean_object* v_res_1248_; 
v_res_1248_ = l_String_Slice_skipPrefix_x3f(v_00_u03c1_1244_, v_s_1245_, v_pat_1246_, v_inst_1247_);
lean_dec(v_pat_1246_);
return v_res_1248_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg(lean_object* v_s_1249_, lean_object* v_pos_1250_, lean_object* v_inst_1251_){
_start:
{
lean_object* v_str_1252_; lean_object* v_startInclusive_1253_; lean_object* v_endExclusive_1254_; lean_object* v___x_1256_; uint8_t v_isShared_1257_; uint8_t v_isSharedCheck_1273_; 
v_str_1252_ = lean_ctor_get(v_s_1249_, 0);
v_startInclusive_1253_ = lean_ctor_get(v_s_1249_, 1);
v_endExclusive_1254_ = lean_ctor_get(v_s_1249_, 2);
v_isSharedCheck_1273_ = !lean_is_exclusive(v_s_1249_);
if (v_isSharedCheck_1273_ == 0)
{
v___x_1256_ = v_s_1249_;
v_isShared_1257_ = v_isSharedCheck_1273_;
goto v_resetjp_1255_;
}
else
{
lean_inc(v_endExclusive_1254_);
lean_inc(v_startInclusive_1253_);
lean_inc(v_str_1252_);
lean_dec(v_s_1249_);
v___x_1256_ = lean_box(0);
v_isShared_1257_ = v_isSharedCheck_1273_;
goto v_resetjp_1255_;
}
v_resetjp_1255_:
{
lean_object* v_skipPrefix_x3f_1258_; lean_object* v___x_1259_; lean_object* v___x_1261_; 
v_skipPrefix_x3f_1258_ = lean_ctor_get(v_inst_1251_, 0);
lean_inc_ref(v_skipPrefix_x3f_1258_);
lean_dec_ref(v_inst_1251_);
v___x_1259_ = lean_nat_add(v_startInclusive_1253_, v_pos_1250_);
lean_dec(v_startInclusive_1253_);
if (v_isShared_1257_ == 0)
{
lean_ctor_set(v___x_1256_, 1, v___x_1259_);
v___x_1261_ = v___x_1256_;
goto v_reusejp_1260_;
}
else
{
lean_object* v_reuseFailAlloc_1272_; 
v_reuseFailAlloc_1272_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1272_, 0, v_str_1252_);
lean_ctor_set(v_reuseFailAlloc_1272_, 1, v___x_1259_);
lean_ctor_set(v_reuseFailAlloc_1272_, 2, v_endExclusive_1254_);
v___x_1261_ = v_reuseFailAlloc_1272_;
goto v_reusejp_1260_;
}
v_reusejp_1260_:
{
lean_object* v___x_1262_; 
v___x_1262_ = lean_apply_1(v_skipPrefix_x3f_1258_, v___x_1261_);
if (lean_obj_tag(v___x_1262_) == 0)
{
return v___x_1262_;
}
else
{
lean_object* v_val_1263_; lean_object* v___x_1265_; uint8_t v_isShared_1266_; uint8_t v_isSharedCheck_1271_; 
v_val_1263_ = lean_ctor_get(v___x_1262_, 0);
v_isSharedCheck_1271_ = !lean_is_exclusive(v___x_1262_);
if (v_isSharedCheck_1271_ == 0)
{
v___x_1265_ = v___x_1262_;
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
else
{
lean_inc(v_val_1263_);
lean_dec(v___x_1262_);
v___x_1265_ = lean_box(0);
v_isShared_1266_ = v_isSharedCheck_1271_;
goto v_resetjp_1264_;
}
v_resetjp_1264_:
{
lean_object* v___x_1267_; lean_object* v___x_1269_; 
v___x_1267_ = lean_nat_add(v_pos_1250_, v_val_1263_);
lean_dec(v_val_1263_);
if (v_isShared_1266_ == 0)
{
lean_ctor_set(v___x_1265_, 0, v___x_1267_);
v___x_1269_ = v___x_1265_;
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg___boxed(lean_object* v_s_1274_, lean_object* v_pos_1275_, lean_object* v_inst_1276_){
_start:
{
lean_object* v_res_1277_; 
v_res_1277_ = l_String_Slice_Pos_skip_x3f___redArg(v_s_1274_, v_pos_1275_, v_inst_1276_);
lean_dec(v_pos_1275_);
return v_res_1277_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f(lean_object* v_00_u03c1_1278_, lean_object* v_s_1279_, lean_object* v_pos_1280_, lean_object* v_pat_1281_, lean_object* v_inst_1282_){
_start:
{
lean_object* v_str_1283_; lean_object* v_startInclusive_1284_; lean_object* v_endExclusive_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1304_; 
v_str_1283_ = lean_ctor_get(v_s_1279_, 0);
v_startInclusive_1284_ = lean_ctor_get(v_s_1279_, 1);
v_endExclusive_1285_ = lean_ctor_get(v_s_1279_, 2);
v_isSharedCheck_1304_ = !lean_is_exclusive(v_s_1279_);
if (v_isSharedCheck_1304_ == 0)
{
v___x_1287_ = v_s_1279_;
v_isShared_1288_ = v_isSharedCheck_1304_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_endExclusive_1285_);
lean_inc(v_startInclusive_1284_);
lean_inc(v_str_1283_);
lean_dec(v_s_1279_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1304_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v_skipPrefix_x3f_1289_; lean_object* v___x_1290_; lean_object* v___x_1292_; 
v_skipPrefix_x3f_1289_ = lean_ctor_get(v_inst_1282_, 0);
lean_inc_ref(v_skipPrefix_x3f_1289_);
lean_dec_ref(v_inst_1282_);
v___x_1290_ = lean_nat_add(v_startInclusive_1284_, v_pos_1280_);
lean_dec(v_startInclusive_1284_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 1, v___x_1290_);
v___x_1292_ = v___x_1287_;
goto v_reusejp_1291_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v_str_1283_);
lean_ctor_set(v_reuseFailAlloc_1303_, 1, v___x_1290_);
lean_ctor_set(v_reuseFailAlloc_1303_, 2, v_endExclusive_1285_);
v___x_1292_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1291_;
}
v_reusejp_1291_:
{
lean_object* v___x_1293_; 
v___x_1293_ = lean_apply_1(v_skipPrefix_x3f_1289_, v___x_1292_);
if (lean_obj_tag(v___x_1293_) == 0)
{
return v___x_1293_;
}
else
{
lean_object* v_val_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1302_; 
v_val_1294_ = lean_ctor_get(v___x_1293_, 0);
v_isSharedCheck_1302_ = !lean_is_exclusive(v___x_1293_);
if (v_isSharedCheck_1302_ == 0)
{
v___x_1296_ = v___x_1293_;
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_val_1294_);
lean_dec(v___x_1293_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1302_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = lean_nat_add(v_pos_1280_, v_val_1294_);
lean_dec(v_val_1294_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 0, v___x_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1301_; 
v_reuseFailAlloc_1301_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1301_, 0, v___x_1298_);
v___x_1300_ = v_reuseFailAlloc_1301_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
return v___x_1300_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_1305_, lean_object* v_s_1306_, lean_object* v_pos_1307_, lean_object* v_pat_1308_, lean_object* v_inst_1309_){
_start:
{
lean_object* v_res_1310_; 
v_res_1310_ = l_String_Slice_Pos_skip_x3f(v_00_u03c1_1305_, v_s_1306_, v_pos_1307_, v_pat_1308_, v_inst_1309_);
lean_dec(v_pat_1308_);
lean_dec(v_pos_1307_);
return v_res_1310_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___redArg(lean_object* v_s_1311_, lean_object* v_inst_1312_){
_start:
{
lean_object* v_skipPrefix_x3f_1313_; lean_object* v___x_1314_; 
v_skipPrefix_x3f_1313_ = lean_ctor_get(v_inst_1312_, 0);
lean_inc_ref(v_skipPrefix_x3f_1313_);
lean_dec_ref(v_inst_1312_);
lean_inc_ref(v_s_1311_);
v___x_1314_ = lean_apply_1(v_skipPrefix_x3f_1313_, v_s_1311_);
if (lean_obj_tag(v___x_1314_) == 0)
{
lean_object* v___x_1315_; 
lean_dec_ref(v_s_1311_);
v___x_1315_ = lean_box(0);
return v___x_1315_;
}
else
{
lean_object* v_val_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1334_; 
v_val_1316_ = lean_ctor_get(v___x_1314_, 0);
v_isSharedCheck_1334_ = !lean_is_exclusive(v___x_1314_);
if (v_isSharedCheck_1334_ == 0)
{
v___x_1318_ = v___x_1314_;
v_isShared_1319_ = v_isSharedCheck_1334_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_val_1316_);
lean_dec(v___x_1314_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1334_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v_str_1320_; lean_object* v_startInclusive_1321_; lean_object* v_endExclusive_1322_; lean_object* v___x_1324_; uint8_t v_isShared_1325_; uint8_t v_isSharedCheck_1333_; 
v_str_1320_ = lean_ctor_get(v_s_1311_, 0);
v_startInclusive_1321_ = lean_ctor_get(v_s_1311_, 1);
v_endExclusive_1322_ = lean_ctor_get(v_s_1311_, 2);
v_isSharedCheck_1333_ = !lean_is_exclusive(v_s_1311_);
if (v_isSharedCheck_1333_ == 0)
{
v___x_1324_ = v_s_1311_;
v_isShared_1325_ = v_isSharedCheck_1333_;
goto v_resetjp_1323_;
}
else
{
lean_inc(v_endExclusive_1322_);
lean_inc(v_startInclusive_1321_);
lean_inc(v_str_1320_);
lean_dec(v_s_1311_);
v___x_1324_ = lean_box(0);
v_isShared_1325_ = v_isSharedCheck_1333_;
goto v_resetjp_1323_;
}
v_resetjp_1323_:
{
lean_object* v___x_1326_; lean_object* v___x_1328_; 
v___x_1326_ = lean_nat_add(v_startInclusive_1321_, v_val_1316_);
lean_dec(v_val_1316_);
lean_dec(v_startInclusive_1321_);
if (v_isShared_1325_ == 0)
{
lean_ctor_set(v___x_1324_, 1, v___x_1326_);
v___x_1328_ = v___x_1324_;
goto v_reusejp_1327_;
}
else
{
lean_object* v_reuseFailAlloc_1332_; 
v_reuseFailAlloc_1332_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1332_, 0, v_str_1320_);
lean_ctor_set(v_reuseFailAlloc_1332_, 1, v___x_1326_);
lean_ctor_set(v_reuseFailAlloc_1332_, 2, v_endExclusive_1322_);
v___x_1328_ = v_reuseFailAlloc_1332_;
goto v_reusejp_1327_;
}
v_reusejp_1327_:
{
lean_object* v___x_1330_; 
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1328_);
v___x_1330_ = v___x_1318_;
goto v_reusejp_1329_;
}
else
{
lean_object* v_reuseFailAlloc_1331_; 
v_reuseFailAlloc_1331_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1331_, 0, v___x_1328_);
v___x_1330_ = v_reuseFailAlloc_1331_;
goto v_reusejp_1329_;
}
v_reusejp_1329_:
{
return v___x_1330_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f(lean_object* v_00_u03c1_1335_, lean_object* v_s_1336_, lean_object* v_pat_1337_, lean_object* v_inst_1338_){
_start:
{
lean_object* v_skipPrefix_x3f_1339_; lean_object* v___x_1340_; 
v_skipPrefix_x3f_1339_ = lean_ctor_get(v_inst_1338_, 0);
lean_inc_ref(v_skipPrefix_x3f_1339_);
lean_dec_ref(v_inst_1338_);
lean_inc_ref(v_s_1336_);
v___x_1340_ = lean_apply_1(v_skipPrefix_x3f_1339_, v_s_1336_);
if (lean_obj_tag(v___x_1340_) == 0)
{
lean_object* v___x_1341_; 
lean_dec_ref(v_s_1336_);
v___x_1341_ = lean_box(0);
return v___x_1341_;
}
else
{
lean_object* v_val_1342_; lean_object* v___x_1344_; uint8_t v_isShared_1345_; uint8_t v_isSharedCheck_1360_; 
v_val_1342_ = lean_ctor_get(v___x_1340_, 0);
v_isSharedCheck_1360_ = !lean_is_exclusive(v___x_1340_);
if (v_isSharedCheck_1360_ == 0)
{
v___x_1344_ = v___x_1340_;
v_isShared_1345_ = v_isSharedCheck_1360_;
goto v_resetjp_1343_;
}
else
{
lean_inc(v_val_1342_);
lean_dec(v___x_1340_);
v___x_1344_ = lean_box(0);
v_isShared_1345_ = v_isSharedCheck_1360_;
goto v_resetjp_1343_;
}
v_resetjp_1343_:
{
lean_object* v_str_1346_; lean_object* v_startInclusive_1347_; lean_object* v_endExclusive_1348_; lean_object* v___x_1350_; uint8_t v_isShared_1351_; uint8_t v_isSharedCheck_1359_; 
v_str_1346_ = lean_ctor_get(v_s_1336_, 0);
v_startInclusive_1347_ = lean_ctor_get(v_s_1336_, 1);
v_endExclusive_1348_ = lean_ctor_get(v_s_1336_, 2);
v_isSharedCheck_1359_ = !lean_is_exclusive(v_s_1336_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1350_ = v_s_1336_;
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
else
{
lean_inc(v_endExclusive_1348_);
lean_inc(v_startInclusive_1347_);
lean_inc(v_str_1346_);
lean_dec(v_s_1336_);
v___x_1350_ = lean_box(0);
v_isShared_1351_ = v_isSharedCheck_1359_;
goto v_resetjp_1349_;
}
v_resetjp_1349_:
{
lean_object* v___x_1352_; lean_object* v___x_1354_; 
v___x_1352_ = lean_nat_add(v_startInclusive_1347_, v_val_1342_);
lean_dec(v_val_1342_);
lean_dec(v_startInclusive_1347_);
if (v_isShared_1351_ == 0)
{
lean_ctor_set(v___x_1350_, 1, v___x_1352_);
v___x_1354_ = v___x_1350_;
goto v_reusejp_1353_;
}
else
{
lean_object* v_reuseFailAlloc_1358_; 
v_reuseFailAlloc_1358_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1358_, 0, v_str_1346_);
lean_ctor_set(v_reuseFailAlloc_1358_, 1, v___x_1352_);
lean_ctor_set(v_reuseFailAlloc_1358_, 2, v_endExclusive_1348_);
v___x_1354_ = v_reuseFailAlloc_1358_;
goto v_reusejp_1353_;
}
v_reusejp_1353_:
{
lean_object* v___x_1356_; 
if (v_isShared_1345_ == 0)
{
lean_ctor_set(v___x_1344_, 0, v___x_1354_);
v___x_1356_ = v___x_1344_;
goto v_reusejp_1355_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v___x_1354_);
v___x_1356_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1355_;
}
v_reusejp_1355_:
{
return v___x_1356_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_1361_, lean_object* v_s_1362_, lean_object* v_pat_1363_, lean_object* v_inst_1364_){
_start:
{
lean_object* v_res_1365_; 
v_res_1365_ = l_String_Slice_dropPrefix_x3f(v_00_u03c1_1361_, v_s_1362_, v_pat_1363_, v_inst_1364_);
lean_dec(v_pat_1363_);
return v_res_1365_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___redArg(lean_object* v_s_1366_, lean_object* v_inst_1367_){
_start:
{
lean_object* v_skipPrefix_x3f_1368_; lean_object* v___x_1369_; 
v_skipPrefix_x3f_1368_ = lean_ctor_get(v_inst_1367_, 0);
lean_inc_ref(v_skipPrefix_x3f_1368_);
lean_dec_ref(v_inst_1367_);
lean_inc_ref(v_s_1366_);
v___x_1369_ = lean_apply_1(v_skipPrefix_x3f_1368_, v_s_1366_);
if (lean_obj_tag(v___x_1369_) == 0)
{
return v_s_1366_;
}
else
{
lean_object* v_val_1370_; lean_object* v_str_1371_; lean_object* v_startInclusive_1372_; lean_object* v_endExclusive_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1381_; 
v_val_1370_ = lean_ctor_get(v___x_1369_, 0);
lean_inc(v_val_1370_);
lean_dec_ref_known(v___x_1369_, 1);
v_str_1371_ = lean_ctor_get(v_s_1366_, 0);
v_startInclusive_1372_ = lean_ctor_get(v_s_1366_, 1);
v_endExclusive_1373_ = lean_ctor_get(v_s_1366_, 2);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_s_1366_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1375_ = v_s_1366_;
v_isShared_1376_ = v_isSharedCheck_1381_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_endExclusive_1373_);
lean_inc(v_startInclusive_1372_);
lean_inc(v_str_1371_);
lean_dec(v_s_1366_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1381_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = lean_nat_add(v_startInclusive_1372_, v_val_1370_);
lean_dec(v_val_1370_);
lean_dec(v_startInclusive_1372_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1377_);
v___x_1379_ = v___x_1375_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_str_1371_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_endExclusive_1373_);
v___x_1379_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
return v___x_1379_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix(lean_object* v_00_u03c1_1382_, lean_object* v_s_1383_, lean_object* v_pat_1384_, lean_object* v_inst_1385_){
_start:
{
lean_object* v___x_1386_; 
v___x_1386_ = l_String_Slice_dropPrefix___redArg(v_s_1383_, v_inst_1385_);
return v___x_1386_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___boxed(lean_object* v_00_u03c1_1387_, lean_object* v_s_1388_, lean_object* v_pat_1389_, lean_object* v_inst_1390_){
_start:
{
lean_object* v_res_1391_; 
v_res_1391_ = l_String_Slice_dropPrefix(v_00_u03c1_1387_, v_s_1388_, v_pat_1389_, v_inst_1390_);
lean_dec(v_pat_1389_);
return v_res_1391_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__0(lean_object* v_x_1392_, lean_object* v_x_1393_, lean_object* v_f_1394_, lean_object* v_c_1395_){
_start:
{
lean_object* v___x_1396_; 
v___x_1396_ = lean_apply_1(v_f_1394_, v_c_1395_);
return v___x_1396_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1(lean_object* v_s_1397_, lean_object* v_inst_1398_, lean_object* v_replacement_1399_, lean_object* v_x1_1400_, lean_object* v_x2_1401_, lean_object* v_x3_1402_){
_start:
{
if (lean_obj_tag(v_x1_1400_) == 0)
{
lean_object* v_startPos_1403_; lean_object* v_endPos_1404_; lean_object* v___x_1405_; lean_object* v_str_1406_; lean_object* v_startInclusive_1407_; lean_object* v_endExclusive_1408_; lean_object* v___x_1409_; lean_object* v___x_1410_; lean_object* v___x_1411_; 
lean_dec(v_replacement_1399_);
lean_dec_ref(v_inst_1398_);
v_startPos_1403_ = lean_ctor_get(v_x1_1400_, 0);
v_endPos_1404_ = lean_ctor_get(v_x1_1400_, 1);
v___x_1405_ = l_String_Slice_slice_x21(v_s_1397_, v_startPos_1403_, v_endPos_1404_);
v_str_1406_ = lean_ctor_get(v___x_1405_, 0);
lean_inc_ref(v_str_1406_);
v_startInclusive_1407_ = lean_ctor_get(v___x_1405_, 1);
lean_inc(v_startInclusive_1407_);
v_endExclusive_1408_ = lean_ctor_get(v___x_1405_, 2);
lean_inc(v_endExclusive_1408_);
lean_dec_ref(v___x_1405_);
v___x_1409_ = lean_string_utf8_extract(v_str_1406_, v_startInclusive_1407_, v_endExclusive_1408_);
lean_dec(v_endExclusive_1408_);
lean_dec(v_startInclusive_1407_);
lean_dec_ref(v_str_1406_);
v___x_1410_ = lean_string_append(v_x3_1402_, v___x_1409_);
lean_dec_ref(v___x_1409_);
v___x_1411_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1411_, 0, v___x_1410_);
return v___x_1411_;
}
else
{
lean_object* v___x_1412_; lean_object* v_str_1413_; lean_object* v_startInclusive_1414_; lean_object* v_endExclusive_1415_; lean_object* v___x_1416_; lean_object* v___x_1417_; lean_object* v___x_1418_; 
lean_dec_ref(v_s_1397_);
v___x_1412_ = lean_apply_1(v_inst_1398_, v_replacement_1399_);
v_str_1413_ = lean_ctor_get(v___x_1412_, 0);
lean_inc_ref(v_str_1413_);
v_startInclusive_1414_ = lean_ctor_get(v___x_1412_, 1);
lean_inc(v_startInclusive_1414_);
v_endExclusive_1415_ = lean_ctor_get(v___x_1412_, 2);
lean_inc(v_endExclusive_1415_);
lean_dec_ref(v___x_1412_);
v___x_1416_ = lean_string_utf8_extract(v_str_1413_, v_startInclusive_1414_, v_endExclusive_1415_);
lean_dec(v_endExclusive_1415_);
lean_dec(v_startInclusive_1414_);
lean_dec_ref(v_str_1413_);
v___x_1417_ = lean_string_append(v_x3_1402_, v___x_1416_);
lean_dec_ref(v___x_1416_);
v___x_1418_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1418_, 0, v___x_1417_);
return v___x_1418_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1___boxed(lean_object* v_s_1419_, lean_object* v_inst_1420_, lean_object* v_replacement_1421_, lean_object* v_x1_1422_, lean_object* v_x2_1423_, lean_object* v_x3_1424_){
_start:
{
lean_object* v_res_1425_; 
v_res_1425_ = l_String_Slice_replace___redArg___lam__1(v_s_1419_, v_inst_1420_, v_replacement_1421_, v_x1_1422_, v_x2_1423_, v_x3_1424_);
lean_dec_ref(v_x1_1422_);
return v_res_1425_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg(lean_object* v_inst_1428_, lean_object* v_inst_1429_, lean_object* v_s_1430_, lean_object* v_inst_1431_, lean_object* v_replacement_1432_){
_start:
{
lean_object* v___f_1433_; lean_object* v___f_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; lean_object* v___x_1437_; 
v___f_1433_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1430_, 2);
v___f_1434_ = lean_alloc_closure((void*)(l_String_Slice_replace___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1434_, 0, v_s_1430_);
lean_closure_set(v___f_1434_, 1, v_inst_1429_);
lean_closure_set(v___f_1434_, 2, v_replacement_1432_);
v___x_1435_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
v___x_1436_ = lean_apply_1(v_inst_1431_, v_s_1430_);
v___x_1437_ = lean_apply_7(v_inst_1428_, v_s_1430_, v___f_1433_, lean_box(0), lean_box(0), v___x_1436_, v___x_1435_, v___f_1434_);
return v___x_1437_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace(lean_object* v_00_u03c1_1438_, lean_object* v_00_u03c3_1439_, lean_object* v_inst_1440_, lean_object* v_inst_1441_, lean_object* v_00_u03b1_1442_, lean_object* v_inst_1443_, lean_object* v_s_1444_, lean_object* v_pattern_1445_, lean_object* v_inst_1446_, lean_object* v_replacement_1447_){
_start:
{
lean_object* v___x_1448_; 
v___x_1448_ = l_String_Slice_replace___redArg(v_inst_1441_, v_inst_1443_, v_s_1444_, v_inst_1446_, v_replacement_1447_);
return v___x_1448_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___boxed(lean_object* v_00_u03c1_1449_, lean_object* v_00_u03c3_1450_, lean_object* v_inst_1451_, lean_object* v_inst_1452_, lean_object* v_00_u03b1_1453_, lean_object* v_inst_1454_, lean_object* v_s_1455_, lean_object* v_pattern_1456_, lean_object* v_inst_1457_, lean_object* v_replacement_1458_){
_start:
{
lean_object* v_res_1459_; 
v_res_1459_ = l_String_Slice_replace(v_00_u03c1_1449_, v_00_u03c3_1450_, v_inst_1451_, v_inst_1452_, v_00_u03b1_1453_, v_inst_1454_, v_s_1455_, v_pattern_1456_, v_inst_1457_, v_replacement_1458_);
lean_dec(v_pattern_1456_);
lean_dec(v_inst_1451_);
return v_res_1459_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object* v_s_1460_, lean_object* v_n_1461_){
_start:
{
lean_object* v_str_1462_; lean_object* v_startInclusive_1463_; lean_object* v_endExclusive_1464_; lean_object* v___x_1465_; lean_object* v___x_1466_; lean_object* v___x_1468_; uint8_t v_isShared_1469_; uint8_t v_isSharedCheck_1474_; 
v_str_1462_ = lean_ctor_get(v_s_1460_, 0);
lean_inc_ref(v_str_1462_);
v_startInclusive_1463_ = lean_ctor_get(v_s_1460_, 1);
lean_inc(v_startInclusive_1463_);
v_endExclusive_1464_ = lean_ctor_get(v_s_1460_, 2);
lean_inc(v_endExclusive_1464_);
v___x_1465_ = lean_unsigned_to_nat(0u);
v___x_1466_ = l_String_Slice_Pos_nextn(v_s_1460_, v___x_1465_, v_n_1461_);
v_isSharedCheck_1474_ = !lean_is_exclusive(v_s_1460_);
if (v_isSharedCheck_1474_ == 0)
{
lean_object* v_unused_1475_; lean_object* v_unused_1476_; lean_object* v_unused_1477_; 
v_unused_1475_ = lean_ctor_get(v_s_1460_, 2);
lean_dec(v_unused_1475_);
v_unused_1476_ = lean_ctor_get(v_s_1460_, 1);
lean_dec(v_unused_1476_);
v_unused_1477_ = lean_ctor_get(v_s_1460_, 0);
lean_dec(v_unused_1477_);
v___x_1468_ = v_s_1460_;
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
else
{
lean_dec(v_s_1460_);
v___x_1468_ = lean_box(0);
v_isShared_1469_ = v_isSharedCheck_1474_;
goto v_resetjp_1467_;
}
v_resetjp_1467_:
{
lean_object* v___x_1470_; lean_object* v___x_1472_; 
v___x_1470_ = lean_nat_add(v_startInclusive_1463_, v___x_1466_);
lean_dec(v___x_1466_);
lean_dec(v_startInclusive_1463_);
if (v_isShared_1469_ == 0)
{
lean_ctor_set(v___x_1468_, 1, v___x_1470_);
v___x_1472_ = v___x_1468_;
goto v_reusejp_1471_;
}
else
{
lean_object* v_reuseFailAlloc_1473_; 
v_reuseFailAlloc_1473_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1473_, 0, v_str_1462_);
lean_ctor_set(v_reuseFailAlloc_1473_, 1, v___x_1470_);
lean_ctor_set(v_reuseFailAlloc_1473_, 2, v_endExclusive_1464_);
v___x_1472_ = v_reuseFailAlloc_1473_;
goto v_reusejp_1471_;
}
v_reusejp_1471_:
{
return v___x_1472_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object* v_s_1478_, lean_object* v_pos_1479_, lean_object* v_inst_1480_){
_start:
{
lean_object* v_str_1481_; lean_object* v_startInclusive_1482_; lean_object* v_endExclusive_1483_; lean_object* v_skipPrefix_x3f_1484_; lean_object* v___x_1485_; lean_object* v___x_1486_; lean_object* v___x_1487_; 
v_str_1481_ = lean_ctor_get(v_s_1478_, 0);
v_startInclusive_1482_ = lean_ctor_get(v_s_1478_, 1);
v_endExclusive_1483_ = lean_ctor_get(v_s_1478_, 2);
v_skipPrefix_x3f_1484_ = lean_ctor_get(v_inst_1480_, 0);
v___x_1485_ = lean_nat_add(v_startInclusive_1482_, v_pos_1479_);
lean_inc(v_endExclusive_1483_);
lean_inc_ref(v_str_1481_);
v___x_1486_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1486_, 0, v_str_1481_);
lean_ctor_set(v___x_1486_, 1, v___x_1485_);
lean_ctor_set(v___x_1486_, 2, v_endExclusive_1483_);
lean_inc_ref(v_skipPrefix_x3f_1484_);
v___x_1487_ = lean_apply_1(v_skipPrefix_x3f_1484_, v___x_1486_);
if (lean_obj_tag(v___x_1487_) == 0)
{
lean_dec_ref(v_inst_1480_);
return v_pos_1479_;
}
else
{
lean_object* v_val_1488_; lean_object* v___x_1489_; uint8_t v___x_1490_; 
v_val_1488_ = lean_ctor_get(v___x_1487_, 0);
lean_inc(v_val_1488_);
lean_dec_ref_known(v___x_1487_, 1);
v___x_1489_ = lean_nat_add(v_pos_1479_, v_val_1488_);
lean_dec(v_val_1488_);
v___x_1490_ = lean_nat_dec_lt(v_pos_1479_, v___x_1489_);
if (v___x_1490_ == 0)
{
lean_dec(v___x_1489_);
lean_dec_ref(v_inst_1480_);
return v_pos_1479_;
}
else
{
lean_dec(v_pos_1479_);
v_pos_1479_ = v___x_1489_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg___boxed(lean_object* v_s_1492_, lean_object* v_pos_1493_, lean_object* v_inst_1494_){
_start:
{
lean_object* v_res_1495_; 
v_res_1495_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1492_, v_pos_1493_, v_inst_1494_);
lean_dec_ref(v_s_1492_);
return v_res_1495_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile(lean_object* v_00_u03c1_1496_, lean_object* v_s_1497_, lean_object* v_pos_1498_, lean_object* v_pat_1499_, lean_object* v_inst_1500_){
_start:
{
lean_object* v___x_1501_; 
v___x_1501_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1497_, v_pos_1498_, v_inst_1500_);
return v___x_1501_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___boxed(lean_object* v_00_u03c1_1502_, lean_object* v_s_1503_, lean_object* v_pos_1504_, lean_object* v_pat_1505_, lean_object* v_inst_1506_){
_start:
{
lean_object* v_res_1507_; 
v_res_1507_ = l_String_Slice_Pos_skipWhile(v_00_u03c1_1502_, v_s_1503_, v_pos_1504_, v_pat_1505_, v_inst_1506_);
lean_dec(v_pat_1505_);
lean_dec_ref(v_s_1503_);
return v_res_1507_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object* v_x_1508_, lean_object* v_h__1_1509_, lean_object* v_h__2_1510_){
_start:
{
if (lean_obj_tag(v_x_1508_) == 0)
{
lean_object* v___x_1511_; lean_object* v___x_1512_; 
lean_dec(v_h__1_1509_);
v___x_1511_ = lean_box(0);
v___x_1512_ = lean_apply_1(v_h__2_1510_, v___x_1511_);
return v___x_1512_;
}
else
{
lean_object* v_val_1513_; lean_object* v___x_1514_; 
lean_dec(v_h__2_1510_);
v_val_1513_ = lean_ctor_get(v_x_1508_, 0);
lean_inc(v_val_1513_);
lean_dec_ref_known(v_x_1508_, 1);
v___x_1514_ = lean_apply_1(v_h__1_1509_, v_val_1513_);
return v___x_1514_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object* v_s_1515_, lean_object* v_motive_1516_, lean_object* v_x_1517_, lean_object* v_h__1_1518_, lean_object* v_h__2_1519_){
_start:
{
if (lean_obj_tag(v_x_1517_) == 0)
{
lean_object* v___x_1520_; lean_object* v___x_1521_; 
lean_dec(v_h__1_1518_);
v___x_1520_ = lean_box(0);
v___x_1521_ = lean_apply_1(v_h__2_1519_, v___x_1520_);
return v___x_1521_;
}
else
{
lean_object* v_val_1522_; lean_object* v___x_1523_; 
lean_dec(v_h__2_1519_);
v_val_1522_ = lean_ctor_get(v_x_1517_, 0);
lean_inc(v_val_1522_);
lean_dec_ref_known(v_x_1517_, 1);
v___x_1523_ = lean_apply_1(v_h__1_1518_, v_val_1522_);
return v___x_1523_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object* v_s_1524_, lean_object* v_motive_1525_, lean_object* v_x_1526_, lean_object* v_h__1_1527_, lean_object* v_h__2_1528_){
_start:
{
lean_object* v_res_1529_; 
v_res_1529_ = l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_1524_, v_motive_1525_, v_x_1526_, v_h__1_1527_, v_h__2_1528_);
lean_dec_ref(v_s_1524_);
return v_res_1529_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg(lean_object* v_s_1530_, lean_object* v_inst_1531_){
_start:
{
lean_object* v___x_1532_; lean_object* v___x_1533_; 
v___x_1532_ = lean_unsigned_to_nat(0u);
v___x_1533_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1530_, v___x_1532_, v_inst_1531_);
return v___x_1533_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg___boxed(lean_object* v_s_1534_, lean_object* v_inst_1535_){
_start:
{
lean_object* v_res_1536_; 
v_res_1536_ = l_String_Slice_skipPrefixWhile___redArg(v_s_1534_, v_inst_1535_);
lean_dec_ref(v_s_1534_);
return v_res_1536_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile(lean_object* v_00_u03c1_1537_, lean_object* v_s_1538_, lean_object* v_pat_1539_, lean_object* v_inst_1540_){
_start:
{
lean_object* v___x_1541_; lean_object* v___x_1542_; 
v___x_1541_ = lean_unsigned_to_nat(0u);
v___x_1542_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1538_, v___x_1541_, v_inst_1540_);
return v___x_1542_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___boxed(lean_object* v_00_u03c1_1543_, lean_object* v_s_1544_, lean_object* v_pat_1545_, lean_object* v_inst_1546_){
_start:
{
lean_object* v_res_1547_; 
v_res_1547_ = l_String_Slice_skipPrefixWhile(v_00_u03c1_1543_, v_s_1544_, v_pat_1545_, v_inst_1546_);
lean_dec(v_pat_1545_);
lean_dec_ref(v_s_1544_);
return v_res_1547_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg(lean_object* v_s_1548_, lean_object* v_inst_1549_){
_start:
{
lean_object* v_str_1550_; lean_object* v_startInclusive_1551_; lean_object* v_endExclusive_1552_; lean_object* v___x_1553_; lean_object* v___x_1554_; lean_object* v___x_1556_; uint8_t v_isShared_1557_; uint8_t v_isSharedCheck_1562_; 
v_str_1550_ = lean_ctor_get(v_s_1548_, 0);
lean_inc_ref(v_str_1550_);
v_startInclusive_1551_ = lean_ctor_get(v_s_1548_, 1);
lean_inc(v_startInclusive_1551_);
v_endExclusive_1552_ = lean_ctor_get(v_s_1548_, 2);
lean_inc(v_endExclusive_1552_);
v___x_1553_ = lean_unsigned_to_nat(0u);
v___x_1554_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1548_, v___x_1553_, v_inst_1549_);
v_isSharedCheck_1562_ = !lean_is_exclusive(v_s_1548_);
if (v_isSharedCheck_1562_ == 0)
{
lean_object* v_unused_1563_; lean_object* v_unused_1564_; lean_object* v_unused_1565_; 
v_unused_1563_ = lean_ctor_get(v_s_1548_, 2);
lean_dec(v_unused_1563_);
v_unused_1564_ = lean_ctor_get(v_s_1548_, 1);
lean_dec(v_unused_1564_);
v_unused_1565_ = lean_ctor_get(v_s_1548_, 0);
lean_dec(v_unused_1565_);
v___x_1556_ = v_s_1548_;
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
else
{
lean_dec(v_s_1548_);
v___x_1556_ = lean_box(0);
v_isShared_1557_ = v_isSharedCheck_1562_;
goto v_resetjp_1555_;
}
v_resetjp_1555_:
{
lean_object* v___x_1558_; lean_object* v___x_1560_; 
v___x_1558_ = lean_nat_add(v_startInclusive_1551_, v___x_1554_);
lean_dec(v___x_1554_);
lean_dec(v_startInclusive_1551_);
if (v_isShared_1557_ == 0)
{
lean_ctor_set(v___x_1556_, 1, v___x_1558_);
v___x_1560_ = v___x_1556_;
goto v_reusejp_1559_;
}
else
{
lean_object* v_reuseFailAlloc_1561_; 
v_reuseFailAlloc_1561_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1561_, 0, v_str_1550_);
lean_ctor_set(v_reuseFailAlloc_1561_, 1, v___x_1558_);
lean_ctor_set(v_reuseFailAlloc_1561_, 2, v_endExclusive_1552_);
v___x_1560_ = v_reuseFailAlloc_1561_;
goto v_reusejp_1559_;
}
v_reusejp_1559_:
{
return v___x_1560_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile(lean_object* v_00_u03c1_1566_, lean_object* v_s_1567_, lean_object* v_pat_1568_, lean_object* v_inst_1569_){
_start:
{
lean_object* v_str_1570_; lean_object* v_startInclusive_1571_; lean_object* v_endExclusive_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1582_; 
v_str_1570_ = lean_ctor_get(v_s_1567_, 0);
lean_inc_ref(v_str_1570_);
v_startInclusive_1571_ = lean_ctor_get(v_s_1567_, 1);
lean_inc(v_startInclusive_1571_);
v_endExclusive_1572_ = lean_ctor_get(v_s_1567_, 2);
lean_inc(v_endExclusive_1572_);
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1567_, v___x_1573_, v_inst_1569_);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_s_1567_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; lean_object* v_unused_1584_; lean_object* v_unused_1585_; 
v_unused_1583_ = lean_ctor_get(v_s_1567_, 2);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_s_1567_, 1);
lean_dec(v_unused_1584_);
v_unused_1585_ = lean_ctor_get(v_s_1567_, 0);
lean_dec(v_unused_1585_);
v___x_1576_ = v_s_1567_;
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v_s_1567_);
v___x_1576_ = lean_box(0);
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
v_resetjp_1575_:
{
lean_object* v___x_1578_; lean_object* v___x_1580_; 
v___x_1578_ = lean_nat_add(v_startInclusive_1571_, v___x_1574_);
lean_dec(v___x_1574_);
lean_dec(v_startInclusive_1571_);
if (v_isShared_1577_ == 0)
{
lean_ctor_set(v___x_1576_, 1, v___x_1578_);
v___x_1580_ = v___x_1576_;
goto v_reusejp_1579_;
}
else
{
lean_object* v_reuseFailAlloc_1581_; 
v_reuseFailAlloc_1581_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1581_, 0, v_str_1570_);
lean_ctor_set(v_reuseFailAlloc_1581_, 1, v___x_1578_);
lean_ctor_set(v_reuseFailAlloc_1581_, 2, v_endExclusive_1572_);
v___x_1580_ = v_reuseFailAlloc_1581_;
goto v_reusejp_1579_;
}
v_reusejp_1579_:
{
return v___x_1580_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___boxed(lean_object* v_00_u03c1_1586_, lean_object* v_s_1587_, lean_object* v_pat_1588_, lean_object* v_inst_1589_){
_start:
{
lean_object* v_res_1590_; 
v_res_1590_ = l_String_Slice_dropWhile(v_00_u03c1_1586_, v_s_1587_, v_pat_1588_, v_inst_1589_);
lean_dec(v_pat_1588_);
return v_res_1590_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiStart___closed__1(void){
_start:
{
lean_object* v___x_1592_; lean_object* v___x_1593_; 
v___x_1592_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_1593_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1592_);
return v___x_1593_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart(lean_object* v_s_1594_){
_start:
{
lean_object* v___x_1595_; lean_object* v_str_1596_; lean_object* v_startInclusive_1597_; lean_object* v_endExclusive_1598_; lean_object* v___x_1599_; lean_object* v___x_1600_; lean_object* v___x_1602_; uint8_t v_isShared_1603_; uint8_t v_isSharedCheck_1608_; 
v___x_1595_ = lean_obj_once(&l_String_Slice_trimAsciiStart___closed__1, &l_String_Slice_trimAsciiStart___closed__1_once, _init_l_String_Slice_trimAsciiStart___closed__1);
v_str_1596_ = lean_ctor_get(v_s_1594_, 0);
lean_inc_ref(v_str_1596_);
v_startInclusive_1597_ = lean_ctor_get(v_s_1594_, 1);
lean_inc(v_startInclusive_1597_);
v_endExclusive_1598_ = lean_ctor_get(v_s_1594_, 2);
lean_inc(v_endExclusive_1598_);
v___x_1599_ = lean_unsigned_to_nat(0u);
v___x_1600_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1594_, v___x_1599_, v___x_1595_);
v_isSharedCheck_1608_ = !lean_is_exclusive(v_s_1594_);
if (v_isSharedCheck_1608_ == 0)
{
lean_object* v_unused_1609_; lean_object* v_unused_1610_; lean_object* v_unused_1611_; 
v_unused_1609_ = lean_ctor_get(v_s_1594_, 2);
lean_dec(v_unused_1609_);
v_unused_1610_ = lean_ctor_get(v_s_1594_, 1);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_s_1594_, 0);
lean_dec(v_unused_1611_);
v___x_1602_ = v_s_1594_;
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
else
{
lean_dec(v_s_1594_);
v___x_1602_ = lean_box(0);
v_isShared_1603_ = v_isSharedCheck_1608_;
goto v_resetjp_1601_;
}
v_resetjp_1601_:
{
lean_object* v___x_1604_; lean_object* v___x_1606_; 
v___x_1604_ = lean_nat_add(v_startInclusive_1597_, v___x_1600_);
lean_dec(v___x_1600_);
lean_dec(v_startInclusive_1597_);
if (v_isShared_1603_ == 0)
{
lean_ctor_set(v___x_1602_, 1, v___x_1604_);
v___x_1606_ = v___x_1602_;
goto v_reusejp_1605_;
}
else
{
lean_object* v_reuseFailAlloc_1607_; 
v_reuseFailAlloc_1607_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1607_, 0, v_str_1596_);
lean_ctor_set(v_reuseFailAlloc_1607_, 1, v___x_1604_);
lean_ctor_set(v_reuseFailAlloc_1607_, 2, v_endExclusive_1598_);
v___x_1606_ = v_reuseFailAlloc_1607_;
goto v_reusejp_1605_;
}
v_reusejp_1605_:
{
return v___x_1606_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object* v_s_1612_, lean_object* v_n_1613_){
_start:
{
lean_object* v_str_1614_; lean_object* v_startInclusive_1615_; lean_object* v___x_1616_; lean_object* v___x_1617_; lean_object* v___x_1619_; uint8_t v_isShared_1620_; uint8_t v_isSharedCheck_1625_; 
v_str_1614_ = lean_ctor_get(v_s_1612_, 0);
lean_inc_ref(v_str_1614_);
v_startInclusive_1615_ = lean_ctor_get(v_s_1612_, 1);
lean_inc(v_startInclusive_1615_);
v___x_1616_ = lean_unsigned_to_nat(0u);
v___x_1617_ = l_String_Slice_Pos_nextn(v_s_1612_, v___x_1616_, v_n_1613_);
v_isSharedCheck_1625_ = !lean_is_exclusive(v_s_1612_);
if (v_isSharedCheck_1625_ == 0)
{
lean_object* v_unused_1626_; lean_object* v_unused_1627_; lean_object* v_unused_1628_; 
v_unused_1626_ = lean_ctor_get(v_s_1612_, 2);
lean_dec(v_unused_1626_);
v_unused_1627_ = lean_ctor_get(v_s_1612_, 1);
lean_dec(v_unused_1627_);
v_unused_1628_ = lean_ctor_get(v_s_1612_, 0);
lean_dec(v_unused_1628_);
v___x_1619_ = v_s_1612_;
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
else
{
lean_dec(v_s_1612_);
v___x_1619_ = lean_box(0);
v_isShared_1620_ = v_isSharedCheck_1625_;
goto v_resetjp_1618_;
}
v_resetjp_1618_:
{
lean_object* v___x_1621_; lean_object* v___x_1623_; 
v___x_1621_ = lean_nat_add(v_startInclusive_1615_, v___x_1617_);
lean_dec(v___x_1617_);
if (v_isShared_1620_ == 0)
{
lean_ctor_set(v___x_1619_, 2, v___x_1621_);
v___x_1623_ = v___x_1619_;
goto v_reusejp_1622_;
}
else
{
lean_object* v_reuseFailAlloc_1624_; 
v_reuseFailAlloc_1624_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1624_, 0, v_str_1614_);
lean_ctor_set(v_reuseFailAlloc_1624_, 1, v_startInclusive_1615_);
lean_ctor_set(v_reuseFailAlloc_1624_, 2, v___x_1621_);
v___x_1623_ = v_reuseFailAlloc_1624_;
goto v_reusejp_1622_;
}
v_reusejp_1622_:
{
return v___x_1623_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___redArg(lean_object* v_s_1629_, lean_object* v_inst_1630_){
_start:
{
lean_object* v_str_1631_; lean_object* v_startInclusive_1632_; lean_object* v___x_1633_; lean_object* v___x_1634_; lean_object* v___x_1636_; uint8_t v_isShared_1637_; uint8_t v_isSharedCheck_1642_; 
v_str_1631_ = lean_ctor_get(v_s_1629_, 0);
lean_inc_ref(v_str_1631_);
v_startInclusive_1632_ = lean_ctor_get(v_s_1629_, 1);
lean_inc(v_startInclusive_1632_);
v___x_1633_ = lean_unsigned_to_nat(0u);
v___x_1634_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1629_, v___x_1633_, v_inst_1630_);
v_isSharedCheck_1642_ = !lean_is_exclusive(v_s_1629_);
if (v_isSharedCheck_1642_ == 0)
{
lean_object* v_unused_1643_; lean_object* v_unused_1644_; lean_object* v_unused_1645_; 
v_unused_1643_ = lean_ctor_get(v_s_1629_, 2);
lean_dec(v_unused_1643_);
v_unused_1644_ = lean_ctor_get(v_s_1629_, 1);
lean_dec(v_unused_1644_);
v_unused_1645_ = lean_ctor_get(v_s_1629_, 0);
lean_dec(v_unused_1645_);
v___x_1636_ = v_s_1629_;
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
else
{
lean_dec(v_s_1629_);
v___x_1636_ = lean_box(0);
v_isShared_1637_ = v_isSharedCheck_1642_;
goto v_resetjp_1635_;
}
v_resetjp_1635_:
{
lean_object* v___x_1638_; lean_object* v___x_1640_; 
v___x_1638_ = lean_nat_add(v_startInclusive_1632_, v___x_1634_);
lean_dec(v___x_1634_);
if (v_isShared_1637_ == 0)
{
lean_ctor_set(v___x_1636_, 2, v___x_1638_);
v___x_1640_ = v___x_1636_;
goto v_reusejp_1639_;
}
else
{
lean_object* v_reuseFailAlloc_1641_; 
v_reuseFailAlloc_1641_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1641_, 0, v_str_1631_);
lean_ctor_set(v_reuseFailAlloc_1641_, 1, v_startInclusive_1632_);
lean_ctor_set(v_reuseFailAlloc_1641_, 2, v___x_1638_);
v___x_1640_ = v_reuseFailAlloc_1641_;
goto v_reusejp_1639_;
}
v_reusejp_1639_:
{
return v___x_1640_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile(lean_object* v_00_u03c1_1646_, lean_object* v_s_1647_, lean_object* v_pat_1648_, lean_object* v_inst_1649_){
_start:
{
lean_object* v_str_1650_; lean_object* v_startInclusive_1651_; lean_object* v___x_1652_; lean_object* v___x_1653_; lean_object* v___x_1655_; uint8_t v_isShared_1656_; uint8_t v_isSharedCheck_1661_; 
v_str_1650_ = lean_ctor_get(v_s_1647_, 0);
lean_inc_ref(v_str_1650_);
v_startInclusive_1651_ = lean_ctor_get(v_s_1647_, 1);
lean_inc(v_startInclusive_1651_);
v___x_1652_ = lean_unsigned_to_nat(0u);
v___x_1653_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1647_, v___x_1652_, v_inst_1649_);
v_isSharedCheck_1661_ = !lean_is_exclusive(v_s_1647_);
if (v_isSharedCheck_1661_ == 0)
{
lean_object* v_unused_1662_; lean_object* v_unused_1663_; lean_object* v_unused_1664_; 
v_unused_1662_ = lean_ctor_get(v_s_1647_, 2);
lean_dec(v_unused_1662_);
v_unused_1663_ = lean_ctor_get(v_s_1647_, 1);
lean_dec(v_unused_1663_);
v_unused_1664_ = lean_ctor_get(v_s_1647_, 0);
lean_dec(v_unused_1664_);
v___x_1655_ = v_s_1647_;
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
else
{
lean_dec(v_s_1647_);
v___x_1655_ = lean_box(0);
v_isShared_1656_ = v_isSharedCheck_1661_;
goto v_resetjp_1654_;
}
v_resetjp_1654_:
{
lean_object* v___x_1657_; lean_object* v___x_1659_; 
v___x_1657_ = lean_nat_add(v_startInclusive_1651_, v___x_1653_);
lean_dec(v___x_1653_);
if (v_isShared_1656_ == 0)
{
lean_ctor_set(v___x_1655_, 2, v___x_1657_);
v___x_1659_ = v___x_1655_;
goto v_reusejp_1658_;
}
else
{
lean_object* v_reuseFailAlloc_1660_; 
v_reuseFailAlloc_1660_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1660_, 0, v_str_1650_);
lean_ctor_set(v_reuseFailAlloc_1660_, 1, v_startInclusive_1651_);
lean_ctor_set(v_reuseFailAlloc_1660_, 2, v___x_1657_);
v___x_1659_ = v_reuseFailAlloc_1660_;
goto v_reusejp_1658_;
}
v_reusejp_1658_:
{
return v___x_1659_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___boxed(lean_object* v_00_u03c1_1665_, lean_object* v_s_1666_, lean_object* v_pat_1667_, lean_object* v_inst_1668_){
_start:
{
lean_object* v_res_1669_; 
v_res_1669_ = l_String_Slice_takeWhile(v_00_u03c1_1665_, v_s_1666_, v_pat_1667_, v_inst_1668_);
lean_dec(v_pat_1667_);
return v_res_1669_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1(lean_object* v___x_1670_, lean_object* v_x1_1671_, lean_object* v_x2_1672_, lean_object* v_x3_1673_){
_start:
{
if (lean_obj_tag(v_x1_1671_) == 0)
{
lean_object* v___x_1674_; 
v___x_1674_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1674_, 0, v___x_1670_);
return v___x_1674_;
}
else
{
lean_object* v_startPos_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; 
lean_dec(v___x_1670_);
v_startPos_1675_ = lean_ctor_get(v_x1_1671_, 0);
lean_inc(v_startPos_1675_);
v___x_1676_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1676_, 0, v_startPos_1675_);
v___x_1677_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1677_, 0, v___x_1676_);
return v___x_1677_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1___boxed(lean_object* v___x_1678_, lean_object* v_x1_1679_, lean_object* v_x2_1680_, lean_object* v_x3_1681_){
_start:
{
lean_object* v_res_1682_; 
v_res_1682_ = l_String_Slice_find_x3f___redArg___lam__1(v___x_1678_, v_x1_1679_, v_x2_1680_, v_x3_1681_);
lean_dec(v_x3_1681_);
lean_dec_ref(v_x1_1679_);
return v_res_1682_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg(lean_object* v_inst_1685_, lean_object* v_s_1686_, lean_object* v_inst_1687_){
_start:
{
lean_object* v___f_1688_; lean_object* v_searcher_1689_; lean_object* v___x_1690_; lean_object* v___f_1691_; lean_object* v___x_1692_; 
v___f_1688_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1686_);
v_searcher_1689_ = lean_apply_1(v_inst_1687_, v_s_1686_);
v___x_1690_ = lean_box(0);
v___f_1691_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1692_ = lean_apply_7(v_inst_1685_, v_s_1686_, v___f_1688_, lean_box(0), lean_box(0), v_searcher_1689_, v___x_1690_, v___f_1691_);
return v___x_1692_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f(lean_object* v_00_u03c1_1693_, lean_object* v_00_u03c3_1694_, lean_object* v_inst_1695_, lean_object* v_inst_1696_, lean_object* v_s_1697_, lean_object* v_pat_1698_, lean_object* v_inst_1699_){
_start:
{
lean_object* v___f_1700_; lean_object* v_searcher_1701_; lean_object* v___x_1702_; lean_object* v___f_1703_; lean_object* v___x_1704_; 
v___f_1700_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1697_);
v_searcher_1701_ = lean_apply_1(v_inst_1699_, v_s_1697_);
v___x_1702_ = lean_box(0);
v___f_1703_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1704_ = lean_apply_7(v_inst_1696_, v_s_1697_, v___f_1700_, lean_box(0), lean_box(0), v_searcher_1701_, v___x_1702_, v___f_1703_);
return v___x_1704_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___boxed(lean_object* v_00_u03c1_1705_, lean_object* v_00_u03c3_1706_, lean_object* v_inst_1707_, lean_object* v_inst_1708_, lean_object* v_s_1709_, lean_object* v_pat_1710_, lean_object* v_inst_1711_){
_start:
{
lean_object* v_res_1712_; 
v_res_1712_ = l_String_Slice_find_x3f(v_00_u03c1_1705_, v_00_u03c3_1706_, v_inst_1707_, v_inst_1708_, v_s_1709_, v_pat_1710_, v_inst_1711_);
lean_dec(v_pat_1710_);
lean_dec(v_inst_1707_);
return v_res_1712_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___redArg(lean_object* v_inst_1713_, lean_object* v_s_1714_, lean_object* v_inst_1715_){
_start:
{
lean_object* v___f_1716_; lean_object* v_searcher_1717_; lean_object* v___x_1718_; lean_object* v___f_1719_; lean_object* v___x_1720_; 
v___f_1716_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1714_, 2);
v_searcher_1717_ = lean_apply_1(v_inst_1715_, v_s_1714_);
v___x_1718_ = lean_box(0);
v___f_1719_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1720_ = lean_apply_7(v_inst_1713_, v_s_1714_, v___f_1716_, lean_box(0), lean_box(0), v_searcher_1717_, v___x_1718_, v___f_1719_);
if (lean_obj_tag(v___x_1720_) == 0)
{
lean_object* v_startInclusive_1721_; lean_object* v_endExclusive_1722_; lean_object* v___x_1723_; 
v_startInclusive_1721_ = lean_ctor_get(v_s_1714_, 1);
lean_inc(v_startInclusive_1721_);
v_endExclusive_1722_ = lean_ctor_get(v_s_1714_, 2);
lean_inc(v_endExclusive_1722_);
lean_dec_ref(v_s_1714_);
v___x_1723_ = lean_nat_sub(v_endExclusive_1722_, v_startInclusive_1721_);
lean_dec(v_startInclusive_1721_);
lean_dec(v_endExclusive_1722_);
return v___x_1723_;
}
else
{
lean_object* v_val_1724_; 
lean_dec_ref(v_s_1714_);
v_val_1724_ = lean_ctor_get(v___x_1720_, 0);
lean_inc(v_val_1724_);
lean_dec_ref_known(v___x_1720_, 1);
return v_val_1724_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find(lean_object* v_00_u03c1_1725_, lean_object* v_00_u03c3_1726_, lean_object* v_inst_1727_, lean_object* v_inst_1728_, lean_object* v_s_1729_, lean_object* v_pat_1730_, lean_object* v_inst_1731_){
_start:
{
lean_object* v___f_1732_; lean_object* v_searcher_1733_; lean_object* v___x_1734_; lean_object* v___f_1735_; lean_object* v___x_1736_; 
v___f_1732_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1729_, 2);
v_searcher_1733_ = lean_apply_1(v_inst_1731_, v_s_1729_);
v___x_1734_ = lean_box(0);
v___f_1735_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1736_ = lean_apply_7(v_inst_1728_, v_s_1729_, v___f_1732_, lean_box(0), lean_box(0), v_searcher_1733_, v___x_1734_, v___f_1735_);
if (lean_obj_tag(v___x_1736_) == 0)
{
lean_object* v_startInclusive_1737_; lean_object* v_endExclusive_1738_; lean_object* v___x_1739_; 
v_startInclusive_1737_ = lean_ctor_get(v_s_1729_, 1);
lean_inc(v_startInclusive_1737_);
v_endExclusive_1738_ = lean_ctor_get(v_s_1729_, 2);
lean_inc(v_endExclusive_1738_);
lean_dec_ref(v_s_1729_);
v___x_1739_ = lean_nat_sub(v_endExclusive_1738_, v_startInclusive_1737_);
lean_dec(v_startInclusive_1737_);
lean_dec(v_endExclusive_1738_);
return v___x_1739_;
}
else
{
lean_object* v_val_1740_; 
lean_dec_ref(v_s_1729_);
v_val_1740_ = lean_ctor_get(v___x_1736_, 0);
lean_inc(v_val_1740_);
lean_dec_ref_known(v___x_1736_, 1);
return v_val_1740_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___boxed(lean_object* v_00_u03c1_1741_, lean_object* v_00_u03c3_1742_, lean_object* v_inst_1743_, lean_object* v_inst_1744_, lean_object* v_s_1745_, lean_object* v_pat_1746_, lean_object* v_inst_1747_){
_start:
{
lean_object* v_res_1748_; 
v_res_1748_ = l_String_Slice_find(v_00_u03c1_1741_, v_00_u03c3_1742_, v_inst_1743_, v_inst_1744_, v_s_1745_, v_pat_1746_, v_inst_1747_);
lean_dec(v_pat_1746_);
lean_dec(v_inst_1743_);
return v_res_1748_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1(uint8_t v___x_1752_, lean_object* v_x1_1753_, lean_object* v_x2_1754_, uint8_t v_x3_1755_){
_start:
{
if (lean_obj_tag(v_x1_1753_) == 1)
{
lean_object* v___x_1756_; 
v___x_1756_ = ((lean_object*)(l_String_Slice_contains___redArg___lam__1___closed__0));
return v___x_1756_;
}
else
{
lean_object* v___x_1757_; lean_object* v___x_1758_; 
v___x_1757_ = lean_box(v___x_1752_);
v___x_1758_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1758_, 0, v___x_1757_);
return v___x_1758_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1___boxed(lean_object* v___x_1759_, lean_object* v_x1_1760_, lean_object* v_x2_1761_, lean_object* v_x3_1762_){
_start:
{
uint8_t v___x_86__boxed_1763_; uint8_t v_x3_89__boxed_1764_; lean_object* v_res_1765_; 
v___x_86__boxed_1763_ = lean_unbox(v___x_1759_);
v_x3_89__boxed_1764_ = lean_unbox(v_x3_1762_);
v_res_1765_ = l_String_Slice_contains___redArg___lam__1(v___x_86__boxed_1763_, v_x1_1760_, v_x2_1761_, v_x3_89__boxed_1764_);
lean_dec_ref(v_x1_1760_);
return v_res_1765_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___redArg(lean_object* v_inst_1769_, lean_object* v_s_1770_, lean_object* v_inst_1771_){
_start:
{
lean_object* v___f_1772_; lean_object* v_searcher_1773_; uint8_t v___x_1774_; lean_object* v___f_1775_; lean_object* v___x_1776_; lean_object* v___x_1777_; uint8_t v___x_1778_; 
v___f_1772_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1770_);
v_searcher_1773_ = lean_apply_1(v_inst_1771_, v_s_1770_);
v___x_1774_ = 0;
v___f_1775_ = ((lean_object*)(l_String_Slice_contains___redArg___closed__0));
v___x_1776_ = lean_box(v___x_1774_);
v___x_1777_ = lean_apply_7(v_inst_1769_, v_s_1770_, v___f_1772_, lean_box(0), lean_box(0), v_searcher_1773_, v___x_1776_, v___f_1775_);
v___x_1778_ = lean_unbox(v___x_1777_);
return v___x_1778_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___boxed(lean_object* v_inst_1779_, lean_object* v_s_1780_, lean_object* v_inst_1781_){
_start:
{
uint8_t v_res_1782_; lean_object* v_r_1783_; 
v_res_1782_ = l_String_Slice_contains___redArg(v_inst_1779_, v_s_1780_, v_inst_1781_);
v_r_1783_ = lean_box(v_res_1782_);
return v_r_1783_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains(lean_object* v_00_u03c1_1784_, lean_object* v_00_u03c3_1785_, lean_object* v_inst_1786_, lean_object* v_inst_1787_, lean_object* v_s_1788_, lean_object* v_pat_1789_, lean_object* v_inst_1790_){
_start:
{
uint8_t v___x_1791_; 
v___x_1791_ = l_String_Slice_contains___redArg(v_inst_1787_, v_s_1788_, v_inst_1790_);
return v___x_1791_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___boxed(lean_object* v_00_u03c1_1792_, lean_object* v_00_u03c3_1793_, lean_object* v_inst_1794_, lean_object* v_inst_1795_, lean_object* v_s_1796_, lean_object* v_pat_1797_, lean_object* v_inst_1798_){
_start:
{
uint8_t v_res_1799_; lean_object* v_r_1800_; 
v_res_1799_ = l_String_Slice_contains(v_00_u03c1_1792_, v_00_u03c3_1793_, v_inst_1794_, v_inst_1795_, v_s_1796_, v_pat_1797_, v_inst_1798_);
lean_dec(v_pat_1797_);
lean_dec(v_inst_1794_);
v_r_1800_ = lean_box(v_res_1799_);
return v_r_1800_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any___redArg(lean_object* v_inst_1801_, lean_object* v_s_1802_, lean_object* v_inst_1803_){
_start:
{
uint8_t v___x_1804_; 
v___x_1804_ = l_String_Slice_contains___redArg(v_inst_1801_, v_s_1802_, v_inst_1803_);
return v___x_1804_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___redArg___boxed(lean_object* v_inst_1805_, lean_object* v_s_1806_, lean_object* v_inst_1807_){
_start:
{
uint8_t v_res_1808_; lean_object* v_r_1809_; 
v_res_1808_ = l_String_Slice_any___redArg(v_inst_1805_, v_s_1806_, v_inst_1807_);
v_r_1809_ = lean_box(v_res_1808_);
return v_r_1809_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any(lean_object* v_00_u03c1_1810_, lean_object* v_00_u03c3_1811_, lean_object* v_inst_1812_, lean_object* v_inst_1813_, lean_object* v_s_1814_, lean_object* v_pat_1815_, lean_object* v_inst_1816_){
_start:
{
uint8_t v___x_1817_; 
v___x_1817_ = l_String_Slice_contains___redArg(v_inst_1813_, v_s_1814_, v_inst_1816_);
return v___x_1817_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___boxed(lean_object* v_00_u03c1_1818_, lean_object* v_00_u03c3_1819_, lean_object* v_inst_1820_, lean_object* v_inst_1821_, lean_object* v_s_1822_, lean_object* v_pat_1823_, lean_object* v_inst_1824_){
_start:
{
uint8_t v_res_1825_; lean_object* v_r_1826_; 
v_res_1825_ = l_String_Slice_any(v_00_u03c1_1818_, v_00_u03c3_1819_, v_inst_1820_, v_inst_1821_, v_s_1822_, v_pat_1823_, v_inst_1824_);
lean_dec(v_pat_1823_);
lean_dec(v_inst_1820_);
v_r_1826_ = lean_box(v_res_1825_);
return v_r_1826_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all___redArg(lean_object* v_s_1827_, lean_object* v_inst_1828_){
_start:
{
lean_object* v_startInclusive_1829_; lean_object* v_endExclusive_1830_; lean_object* v___x_1831_; lean_object* v___x_1832_; lean_object* v___x_1833_; uint8_t v___x_1834_; 
v_startInclusive_1829_ = lean_ctor_get(v_s_1827_, 1);
v_endExclusive_1830_ = lean_ctor_get(v_s_1827_, 2);
v___x_1831_ = lean_unsigned_to_nat(0u);
v___x_1832_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1827_, v___x_1831_, v_inst_1828_);
v___x_1833_ = lean_nat_sub(v_endExclusive_1830_, v_startInclusive_1829_);
v___x_1834_ = lean_nat_dec_eq(v___x_1832_, v___x_1833_);
lean_dec(v___x_1833_);
lean_dec(v___x_1832_);
return v___x_1834_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___redArg___boxed(lean_object* v_s_1835_, lean_object* v_inst_1836_){
_start:
{
uint8_t v_res_1837_; lean_object* v_r_1838_; 
v_res_1837_ = l_String_Slice_all___redArg(v_s_1835_, v_inst_1836_);
lean_dec_ref(v_s_1835_);
v_r_1838_ = lean_box(v_res_1837_);
return v_r_1838_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all(lean_object* v_00_u03c1_1839_, lean_object* v_s_1840_, lean_object* v_pat_1841_, lean_object* v_inst_1842_){
_start:
{
lean_object* v_startInclusive_1843_; lean_object* v_endExclusive_1844_; lean_object* v___x_1845_; lean_object* v___x_1846_; lean_object* v___x_1847_; uint8_t v___x_1848_; 
v_startInclusive_1843_ = lean_ctor_get(v_s_1840_, 1);
v_endExclusive_1844_ = lean_ctor_get(v_s_1840_, 2);
v___x_1845_ = lean_unsigned_to_nat(0u);
v___x_1846_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1840_, v___x_1845_, v_inst_1842_);
v___x_1847_ = lean_nat_sub(v_endExclusive_1844_, v_startInclusive_1843_);
v___x_1848_ = lean_nat_dec_eq(v___x_1846_, v___x_1847_);
lean_dec(v___x_1847_);
lean_dec(v___x_1846_);
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
lean_dec_ref_known(v_t_1896_, 2);
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
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default(lean_object* v_00_u03c3_1969_, lean_object* v_00_u03c1_1970_, lean_object* v_pat_1971_, lean_object* v_s_1972_, lean_object* v_inst_1973_){
_start:
{
lean_object* v___x_1974_; 
v___x_1974_ = lean_box(1);
return v___x_1974_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___boxed(lean_object* v_00_u03c3_1975_, lean_object* v_00_u03c1_1976_, lean_object* v_pat_1977_, lean_object* v_s_1978_, lean_object* v_inst_1979_){
_start:
{
lean_object* v_res_1980_; 
v_res_1980_ = l_String_Slice_instInhabitedRevSplitIterator_default(v_00_u03c3_1975_, v_00_u03c1_1976_, v_pat_1977_, v_s_1978_, v_inst_1979_);
lean_dec(v_inst_1979_);
lean_dec_ref(v_s_1978_);
lean_dec(v_pat_1977_);
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
lean_dec_ref_known(v_out_2003_, 2);
lean_dec_ref(v_s_1994_);
v_it_2004_ = lean_ctor_get(v___x_2002_, 0);
lean_inc(v_it_2004_);
lean_dec_ref_known(v___x_2002_, 2);
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
lean_dec_ref_known(v_out_2003_, 2);
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
lean_dec_ref_known(v_x_2101_, 2);
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
lean_dec_ref_known(v_x_2116_, 2);
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
lean_dec_ref_known(v_x_2135_, 2);
v_out_2148_ = lean_ctor_get(v_x_2136_, 1);
lean_inc(v_out_2148_);
lean_dec_ref_known(v_x_2136_, 2);
v_currPos_2149_ = lean_ctor_get(v_it_2145_, 0);
lean_inc(v_currPos_2149_);
v_searcher_2150_ = lean_ctor_get(v_it_2145_, 1);
lean_inc(v_searcher_2150_);
lean_dec_ref_known(v_it_2145_, 2);
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
lean_dec_ref_known(v_x_2135_, 2);
v_out_2154_ = lean_ctor_get(v_x_2136_, 1);
lean_inc(v_out_2154_);
lean_dec_ref_known(v_x_2136_, 2);
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
lean_dec_ref_known(v_x_2136_, 1);
if (lean_obj_tag(v_it_2156_) == 0)
{
lean_object* v_currPos_2157_; lean_object* v_searcher_2158_; lean_object* v_currPos_2159_; lean_object* v_searcher_2160_; lean_object* v___x_2161_; 
lean_dec(v_h__4_2140_);
v_currPos_2157_ = lean_ctor_get(v_x_2135_, 0);
lean_inc(v_currPos_2157_);
v_searcher_2158_ = lean_ctor_get(v_x_2135_, 1);
lean_inc(v_searcher_2158_);
lean_dec_ref_known(v_x_2135_, 2);
v_currPos_2159_ = lean_ctor_get(v_it_2156_, 0);
lean_inc(v_currPos_2159_);
v_searcher_2160_ = lean_ctor_get(v_it_2156_, 1);
lean_inc(v_searcher_2160_);
lean_dec_ref_known(v_it_2156_, 2);
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
lean_dec_ref_known(v_x_2135_, 2);
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
lean_dec_ref_known(v_x_2135_, 2);
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
lean_dec_ref_known(v_x_2136_, 2);
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
lean_dec_ref_known(v_x_2136_, 1);
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
lean_dec_ref_known(v_x_2182_, 2);
v_out_2195_ = lean_ctor_get(v_x_2183_, 1);
lean_inc(v_out_2195_);
lean_dec_ref_known(v_x_2183_, 2);
v_currPos_2196_ = lean_ctor_get(v_it_2192_, 0);
lean_inc(v_currPos_2196_);
v_searcher_2197_ = lean_ctor_get(v_it_2192_, 1);
lean_inc(v_searcher_2197_);
lean_dec_ref_known(v_it_2192_, 2);
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
lean_dec_ref_known(v_x_2182_, 2);
v_out_2201_ = lean_ctor_get(v_x_2183_, 1);
lean_inc(v_out_2201_);
lean_dec_ref_known(v_x_2183_, 2);
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
lean_dec_ref_known(v_x_2183_, 1);
if (lean_obj_tag(v_it_2203_) == 0)
{
lean_object* v_currPos_2204_; lean_object* v_searcher_2205_; lean_object* v_currPos_2206_; lean_object* v_searcher_2207_; lean_object* v___x_2208_; 
lean_dec(v_h__4_2187_);
v_currPos_2204_ = lean_ctor_get(v_x_2182_, 0);
lean_inc(v_currPos_2204_);
v_searcher_2205_ = lean_ctor_get(v_x_2182_, 1);
lean_inc(v_searcher_2205_);
lean_dec_ref_known(v_x_2182_, 2);
v_currPos_2206_ = lean_ctor_get(v_it_2203_, 0);
lean_inc(v_currPos_2206_);
v_searcher_2207_ = lean_ctor_get(v_it_2203_, 1);
lean_inc(v_searcher_2207_);
lean_dec_ref_known(v_it_2203_, 2);
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
lean_dec_ref_known(v_x_2182_, 2);
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
lean_dec_ref_known(v_x_2182_, 2);
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
lean_dec_ref_known(v_x_2183_, 2);
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
lean_dec_ref_known(v_x_2183_, 1);
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
lean_dec_ref_known(v_x_2240_, 2);
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
lean_dec_ref_known(v_x_2254_, 2);
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
lean_dec_ref_known(v_____do__lift_2291_, 1);
v___x_2293_ = lean_apply_2(v_toPure_2288_, lean_box(0), v_a_2292_);
return v___x_2293_;
}
else
{
lean_object* v_a_2294_; lean_object* v___x_2295_; 
lean_dec(v_toPure_2288_);
v_a_2294_ = lean_ctor_get(v_____do__lift_2291_, 0);
lean_inc(v_a_2294_);
lean_dec_ref_known(v_____do__lift_2291_, 1);
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
lean_dec_ref_known(v_s_2301_, 2);
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
lean_dec_ref_known(v_s_2301_, 1);
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
lean_dec_ref_known(v_out_2328_, 2);
lean_dec_ref(v_s_2314_);
v_it_2329_ = lean_ctor_get(v___x_2327_, 0);
lean_inc(v_it_2329_);
lean_dec_ref_known(v___x_2327_, 2);
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
lean_dec_ref_known(v_out_2328_, 2);
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
lean_object* v_str_2471_; lean_object* v_startInclusive_2472_; lean_object* v___x_2474_; uint8_t v_isShared_2475_; uint8_t v_isSharedCheck_2490_; 
v_str_2471_ = lean_ctor_get(v_s_2468_, 0);
v_startInclusive_2472_ = lean_ctor_get(v_s_2468_, 1);
v_isSharedCheck_2490_ = !lean_is_exclusive(v_s_2468_);
if (v_isSharedCheck_2490_ == 0)
{
lean_object* v_unused_2491_; 
v_unused_2491_ = lean_ctor_get(v_s_2468_, 2);
lean_dec(v_unused_2491_);
v___x_2474_ = v_s_2468_;
v_isShared_2475_ = v_isSharedCheck_2490_;
goto v_resetjp_2473_;
}
else
{
lean_inc(v_startInclusive_2472_);
lean_inc(v_str_2471_);
lean_dec(v_s_2468_);
v___x_2474_ = lean_box(0);
v_isShared_2475_ = v_isSharedCheck_2490_;
goto v_resetjp_2473_;
}
v_resetjp_2473_:
{
lean_object* v_skipSuffix_x3f_2476_; lean_object* v___x_2477_; lean_object* v___x_2479_; 
v_skipSuffix_x3f_2476_ = lean_ctor_get(v_inst_2470_, 0);
lean_inc_ref(v_skipSuffix_x3f_2476_);
lean_dec_ref(v_inst_2470_);
v___x_2477_ = lean_nat_add(v_startInclusive_2472_, v_pos_2469_);
if (v_isShared_2475_ == 0)
{
lean_ctor_set(v___x_2474_, 2, v___x_2477_);
v___x_2479_ = v___x_2474_;
goto v_reusejp_2478_;
}
else
{
lean_object* v_reuseFailAlloc_2489_; 
v_reuseFailAlloc_2489_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2489_, 0, v_str_2471_);
lean_ctor_set(v_reuseFailAlloc_2489_, 1, v_startInclusive_2472_);
lean_ctor_set(v_reuseFailAlloc_2489_, 2, v___x_2477_);
v___x_2479_ = v_reuseFailAlloc_2489_;
goto v_reusejp_2478_;
}
v_reusejp_2478_:
{
lean_object* v___x_2480_; 
v___x_2480_ = lean_apply_1(v_skipSuffix_x3f_2476_, v___x_2479_);
if (lean_obj_tag(v___x_2480_) == 0)
{
return v___x_2480_;
}
else
{
lean_object* v_val_2481_; lean_object* v___x_2483_; uint8_t v_isShared_2484_; uint8_t v_isSharedCheck_2488_; 
v_val_2481_ = lean_ctor_get(v___x_2480_, 0);
v_isSharedCheck_2488_ = !lean_is_exclusive(v___x_2480_);
if (v_isSharedCheck_2488_ == 0)
{
v___x_2483_ = v___x_2480_;
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
else
{
lean_inc(v_val_2481_);
lean_dec(v___x_2480_);
v___x_2483_ = lean_box(0);
v_isShared_2484_ = v_isSharedCheck_2488_;
goto v_resetjp_2482_;
}
v_resetjp_2482_:
{
lean_object* v___x_2486_; 
if (v_isShared_2484_ == 0)
{
v___x_2486_ = v___x_2483_;
goto v_reusejp_2485_;
}
else
{
lean_object* v_reuseFailAlloc_2487_; 
v_reuseFailAlloc_2487_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2487_, 0, v_val_2481_);
v___x_2486_ = v_reuseFailAlloc_2487_;
goto v_reusejp_2485_;
}
v_reusejp_2485_:
{
return v___x_2486_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg___boxed(lean_object* v_s_2492_, lean_object* v_pos_2493_, lean_object* v_inst_2494_){
_start:
{
lean_object* v_res_2495_; 
v_res_2495_ = l_String_Slice_Pos_revSkip_x3f___redArg(v_s_2492_, v_pos_2493_, v_inst_2494_);
lean_dec(v_pos_2493_);
return v_res_2495_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f(lean_object* v_00_u03c1_2496_, lean_object* v_s_2497_, lean_object* v_pos_2498_, lean_object* v_pat_2499_, lean_object* v_inst_2500_){
_start:
{
lean_object* v_str_2501_; lean_object* v_startInclusive_2502_; lean_object* v___x_2504_; uint8_t v_isShared_2505_; uint8_t v_isSharedCheck_2520_; 
v_str_2501_ = lean_ctor_get(v_s_2497_, 0);
v_startInclusive_2502_ = lean_ctor_get(v_s_2497_, 1);
v_isSharedCheck_2520_ = !lean_is_exclusive(v_s_2497_);
if (v_isSharedCheck_2520_ == 0)
{
lean_object* v_unused_2521_; 
v_unused_2521_ = lean_ctor_get(v_s_2497_, 2);
lean_dec(v_unused_2521_);
v___x_2504_ = v_s_2497_;
v_isShared_2505_ = v_isSharedCheck_2520_;
goto v_resetjp_2503_;
}
else
{
lean_inc(v_startInclusive_2502_);
lean_inc(v_str_2501_);
lean_dec(v_s_2497_);
v___x_2504_ = lean_box(0);
v_isShared_2505_ = v_isSharedCheck_2520_;
goto v_resetjp_2503_;
}
v_resetjp_2503_:
{
lean_object* v_skipSuffix_x3f_2506_; lean_object* v___x_2507_; lean_object* v___x_2509_; 
v_skipSuffix_x3f_2506_ = lean_ctor_get(v_inst_2500_, 0);
lean_inc_ref(v_skipSuffix_x3f_2506_);
lean_dec_ref(v_inst_2500_);
v___x_2507_ = lean_nat_add(v_startInclusive_2502_, v_pos_2498_);
if (v_isShared_2505_ == 0)
{
lean_ctor_set(v___x_2504_, 2, v___x_2507_);
v___x_2509_ = v___x_2504_;
goto v_reusejp_2508_;
}
else
{
lean_object* v_reuseFailAlloc_2519_; 
v_reuseFailAlloc_2519_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2519_, 0, v_str_2501_);
lean_ctor_set(v_reuseFailAlloc_2519_, 1, v_startInclusive_2502_);
lean_ctor_set(v_reuseFailAlloc_2519_, 2, v___x_2507_);
v___x_2509_ = v_reuseFailAlloc_2519_;
goto v_reusejp_2508_;
}
v_reusejp_2508_:
{
lean_object* v___x_2510_; 
v___x_2510_ = lean_apply_1(v_skipSuffix_x3f_2506_, v___x_2509_);
if (lean_obj_tag(v___x_2510_) == 0)
{
return v___x_2510_;
}
else
{
lean_object* v_val_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2518_; 
v_val_2511_ = lean_ctor_get(v___x_2510_, 0);
v_isSharedCheck_2518_ = !lean_is_exclusive(v___x_2510_);
if (v_isSharedCheck_2518_ == 0)
{
v___x_2513_ = v___x_2510_;
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_val_2511_);
lean_dec(v___x_2510_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2518_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v___x_2516_; 
if (v_isShared_2514_ == 0)
{
v___x_2516_ = v___x_2513_;
goto v_reusejp_2515_;
}
else
{
lean_object* v_reuseFailAlloc_2517_; 
v_reuseFailAlloc_2517_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2517_, 0, v_val_2511_);
v___x_2516_ = v_reuseFailAlloc_2517_;
goto v_reusejp_2515_;
}
v_reusejp_2515_:
{
return v___x_2516_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_2522_, lean_object* v_s_2523_, lean_object* v_pos_2524_, lean_object* v_pat_2525_, lean_object* v_inst_2526_){
_start:
{
lean_object* v_res_2527_; 
v_res_2527_ = l_String_Slice_Pos_revSkip_x3f(v_00_u03c1_2522_, v_s_2523_, v_pos_2524_, v_pat_2525_, v_inst_2526_);
lean_dec(v_pat_2525_);
lean_dec(v_pos_2524_);
return v_res_2527_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___redArg(lean_object* v_s_2528_, lean_object* v_inst_2529_){
_start:
{
lean_object* v_skipSuffix_x3f_2530_; lean_object* v___x_2531_; 
v_skipSuffix_x3f_2530_ = lean_ctor_get(v_inst_2529_, 0);
lean_inc_ref(v_skipSuffix_x3f_2530_);
lean_dec_ref(v_inst_2529_);
lean_inc_ref(v_s_2528_);
v___x_2531_ = lean_apply_1(v_skipSuffix_x3f_2530_, v_s_2528_);
if (lean_obj_tag(v___x_2531_) == 0)
{
lean_object* v___x_2532_; 
lean_dec_ref(v_s_2528_);
v___x_2532_ = lean_box(0);
return v___x_2532_;
}
else
{
lean_object* v_val_2533_; lean_object* v___x_2535_; uint8_t v_isShared_2536_; uint8_t v_isSharedCheck_2551_; 
v_val_2533_ = lean_ctor_get(v___x_2531_, 0);
v_isSharedCheck_2551_ = !lean_is_exclusive(v___x_2531_);
if (v_isSharedCheck_2551_ == 0)
{
v___x_2535_ = v___x_2531_;
v_isShared_2536_ = v_isSharedCheck_2551_;
goto v_resetjp_2534_;
}
else
{
lean_inc(v_val_2533_);
lean_dec(v___x_2531_);
v___x_2535_ = lean_box(0);
v_isShared_2536_ = v_isSharedCheck_2551_;
goto v_resetjp_2534_;
}
v_resetjp_2534_:
{
lean_object* v_str_2537_; lean_object* v_startInclusive_2538_; lean_object* v___x_2540_; uint8_t v_isShared_2541_; uint8_t v_isSharedCheck_2549_; 
v_str_2537_ = lean_ctor_get(v_s_2528_, 0);
v_startInclusive_2538_ = lean_ctor_get(v_s_2528_, 1);
v_isSharedCheck_2549_ = !lean_is_exclusive(v_s_2528_);
if (v_isSharedCheck_2549_ == 0)
{
lean_object* v_unused_2550_; 
v_unused_2550_ = lean_ctor_get(v_s_2528_, 2);
lean_dec(v_unused_2550_);
v___x_2540_ = v_s_2528_;
v_isShared_2541_ = v_isSharedCheck_2549_;
goto v_resetjp_2539_;
}
else
{
lean_inc(v_startInclusive_2538_);
lean_inc(v_str_2537_);
lean_dec(v_s_2528_);
v___x_2540_ = lean_box(0);
v_isShared_2541_ = v_isSharedCheck_2549_;
goto v_resetjp_2539_;
}
v_resetjp_2539_:
{
lean_object* v___x_2542_; lean_object* v___x_2544_; 
v___x_2542_ = lean_nat_add(v_startInclusive_2538_, v_val_2533_);
lean_dec(v_val_2533_);
if (v_isShared_2541_ == 0)
{
lean_ctor_set(v___x_2540_, 2, v___x_2542_);
v___x_2544_ = v___x_2540_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2548_; 
v_reuseFailAlloc_2548_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2548_, 0, v_str_2537_);
lean_ctor_set(v_reuseFailAlloc_2548_, 1, v_startInclusive_2538_);
lean_ctor_set(v_reuseFailAlloc_2548_, 2, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2548_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2546_; 
if (v_isShared_2536_ == 0)
{
lean_ctor_set(v___x_2535_, 0, v___x_2544_);
v___x_2546_ = v___x_2535_;
goto v_reusejp_2545_;
}
else
{
lean_object* v_reuseFailAlloc_2547_; 
v_reuseFailAlloc_2547_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2547_, 0, v___x_2544_);
v___x_2546_ = v_reuseFailAlloc_2547_;
goto v_reusejp_2545_;
}
v_reusejp_2545_:
{
return v___x_2546_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f(lean_object* v_00_u03c1_2552_, lean_object* v_s_2553_, lean_object* v_pat_2554_, lean_object* v_inst_2555_){
_start:
{
lean_object* v_skipSuffix_x3f_2556_; lean_object* v___x_2557_; 
v_skipSuffix_x3f_2556_ = lean_ctor_get(v_inst_2555_, 0);
lean_inc_ref(v_skipSuffix_x3f_2556_);
lean_dec_ref(v_inst_2555_);
lean_inc_ref(v_s_2553_);
v___x_2557_ = lean_apply_1(v_skipSuffix_x3f_2556_, v_s_2553_);
if (lean_obj_tag(v___x_2557_) == 0)
{
lean_object* v___x_2558_; 
lean_dec_ref(v_s_2553_);
v___x_2558_ = lean_box(0);
return v___x_2558_;
}
else
{
lean_object* v_val_2559_; lean_object* v___x_2561_; uint8_t v_isShared_2562_; uint8_t v_isSharedCheck_2577_; 
v_val_2559_ = lean_ctor_get(v___x_2557_, 0);
v_isSharedCheck_2577_ = !lean_is_exclusive(v___x_2557_);
if (v_isSharedCheck_2577_ == 0)
{
v___x_2561_ = v___x_2557_;
v_isShared_2562_ = v_isSharedCheck_2577_;
goto v_resetjp_2560_;
}
else
{
lean_inc(v_val_2559_);
lean_dec(v___x_2557_);
v___x_2561_ = lean_box(0);
v_isShared_2562_ = v_isSharedCheck_2577_;
goto v_resetjp_2560_;
}
v_resetjp_2560_:
{
lean_object* v_str_2563_; lean_object* v_startInclusive_2564_; lean_object* v___x_2566_; uint8_t v_isShared_2567_; uint8_t v_isSharedCheck_2575_; 
v_str_2563_ = lean_ctor_get(v_s_2553_, 0);
v_startInclusive_2564_ = lean_ctor_get(v_s_2553_, 1);
v_isSharedCheck_2575_ = !lean_is_exclusive(v_s_2553_);
if (v_isSharedCheck_2575_ == 0)
{
lean_object* v_unused_2576_; 
v_unused_2576_ = lean_ctor_get(v_s_2553_, 2);
lean_dec(v_unused_2576_);
v___x_2566_ = v_s_2553_;
v_isShared_2567_ = v_isSharedCheck_2575_;
goto v_resetjp_2565_;
}
else
{
lean_inc(v_startInclusive_2564_);
lean_inc(v_str_2563_);
lean_dec(v_s_2553_);
v___x_2566_ = lean_box(0);
v_isShared_2567_ = v_isSharedCheck_2575_;
goto v_resetjp_2565_;
}
v_resetjp_2565_:
{
lean_object* v___x_2568_; lean_object* v___x_2570_; 
v___x_2568_ = lean_nat_add(v_startInclusive_2564_, v_val_2559_);
lean_dec(v_val_2559_);
if (v_isShared_2567_ == 0)
{
lean_ctor_set(v___x_2566_, 2, v___x_2568_);
v___x_2570_ = v___x_2566_;
goto v_reusejp_2569_;
}
else
{
lean_object* v_reuseFailAlloc_2574_; 
v_reuseFailAlloc_2574_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2574_, 0, v_str_2563_);
lean_ctor_set(v_reuseFailAlloc_2574_, 1, v_startInclusive_2564_);
lean_ctor_set(v_reuseFailAlloc_2574_, 2, v___x_2568_);
v___x_2570_ = v_reuseFailAlloc_2574_;
goto v_reusejp_2569_;
}
v_reusejp_2569_:
{
lean_object* v___x_2572_; 
if (v_isShared_2562_ == 0)
{
lean_ctor_set(v___x_2561_, 0, v___x_2570_);
v___x_2572_ = v___x_2561_;
goto v_reusejp_2571_;
}
else
{
lean_object* v_reuseFailAlloc_2573_; 
v_reuseFailAlloc_2573_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2573_, 0, v___x_2570_);
v___x_2572_ = v_reuseFailAlloc_2573_;
goto v_reusejp_2571_;
}
v_reusejp_2571_:
{
return v___x_2572_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_2578_, lean_object* v_s_2579_, lean_object* v_pat_2580_, lean_object* v_inst_2581_){
_start:
{
lean_object* v_res_2582_; 
v_res_2582_ = l_String_Slice_dropSuffix_x3f(v_00_u03c1_2578_, v_s_2579_, v_pat_2580_, v_inst_2581_);
lean_dec(v_pat_2580_);
return v_res_2582_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___redArg(lean_object* v_s_2583_, lean_object* v_inst_2584_){
_start:
{
lean_object* v_skipSuffix_x3f_2585_; lean_object* v___x_2586_; 
v_skipSuffix_x3f_2585_ = lean_ctor_get(v_inst_2584_, 0);
lean_inc_ref(v_skipSuffix_x3f_2585_);
lean_dec_ref(v_inst_2584_);
lean_inc_ref(v_s_2583_);
v___x_2586_ = lean_apply_1(v_skipSuffix_x3f_2585_, v_s_2583_);
if (lean_obj_tag(v___x_2586_) == 0)
{
return v_s_2583_;
}
else
{
lean_object* v_val_2587_; lean_object* v_str_2588_; lean_object* v_startInclusive_2589_; lean_object* v___x_2591_; uint8_t v_isShared_2592_; uint8_t v_isSharedCheck_2597_; 
v_val_2587_ = lean_ctor_get(v___x_2586_, 0);
lean_inc(v_val_2587_);
lean_dec_ref_known(v___x_2586_, 1);
v_str_2588_ = lean_ctor_get(v_s_2583_, 0);
v_startInclusive_2589_ = lean_ctor_get(v_s_2583_, 1);
v_isSharedCheck_2597_ = !lean_is_exclusive(v_s_2583_);
if (v_isSharedCheck_2597_ == 0)
{
lean_object* v_unused_2598_; 
v_unused_2598_ = lean_ctor_get(v_s_2583_, 2);
lean_dec(v_unused_2598_);
v___x_2591_ = v_s_2583_;
v_isShared_2592_ = v_isSharedCheck_2597_;
goto v_resetjp_2590_;
}
else
{
lean_inc(v_startInclusive_2589_);
lean_inc(v_str_2588_);
lean_dec(v_s_2583_);
v___x_2591_ = lean_box(0);
v_isShared_2592_ = v_isSharedCheck_2597_;
goto v_resetjp_2590_;
}
v_resetjp_2590_:
{
lean_object* v___x_2593_; lean_object* v___x_2595_; 
v___x_2593_ = lean_nat_add(v_startInclusive_2589_, v_val_2587_);
lean_dec(v_val_2587_);
if (v_isShared_2592_ == 0)
{
lean_ctor_set(v___x_2591_, 2, v___x_2593_);
v___x_2595_ = v___x_2591_;
goto v_reusejp_2594_;
}
else
{
lean_object* v_reuseFailAlloc_2596_; 
v_reuseFailAlloc_2596_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2596_, 0, v_str_2588_);
lean_ctor_set(v_reuseFailAlloc_2596_, 1, v_startInclusive_2589_);
lean_ctor_set(v_reuseFailAlloc_2596_, 2, v___x_2593_);
v___x_2595_ = v_reuseFailAlloc_2596_;
goto v_reusejp_2594_;
}
v_reusejp_2594_:
{
return v___x_2595_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix(lean_object* v_00_u03c1_2599_, lean_object* v_s_2600_, lean_object* v_pat_2601_, lean_object* v_inst_2602_){
_start:
{
lean_object* v___x_2603_; 
v___x_2603_ = l_String_Slice_dropSuffix___redArg(v_s_2600_, v_inst_2602_);
return v___x_2603_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___boxed(lean_object* v_00_u03c1_2604_, lean_object* v_s_2605_, lean_object* v_pat_2606_, lean_object* v_inst_2607_){
_start:
{
lean_object* v_res_2608_; 
v_res_2608_ = l_String_Slice_dropSuffix(v_00_u03c1_2604_, v_s_2605_, v_pat_2606_, v_inst_2607_);
lean_dec(v_pat_2606_);
return v_res_2608_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object* v_s_2609_, lean_object* v_n_2610_){
_start:
{
lean_object* v_str_2611_; lean_object* v_startInclusive_2612_; lean_object* v_endExclusive_2613_; lean_object* v___x_2614_; lean_object* v___x_2615_; lean_object* v___x_2617_; uint8_t v_isShared_2618_; uint8_t v_isSharedCheck_2623_; 
v_str_2611_ = lean_ctor_get(v_s_2609_, 0);
lean_inc_ref(v_str_2611_);
v_startInclusive_2612_ = lean_ctor_get(v_s_2609_, 1);
lean_inc(v_startInclusive_2612_);
v_endExclusive_2613_ = lean_ctor_get(v_s_2609_, 2);
v___x_2614_ = lean_nat_sub(v_endExclusive_2613_, v_startInclusive_2612_);
v___x_2615_ = l_String_Slice_Pos_prevn(v_s_2609_, v___x_2614_, v_n_2610_);
v_isSharedCheck_2623_ = !lean_is_exclusive(v_s_2609_);
if (v_isSharedCheck_2623_ == 0)
{
lean_object* v_unused_2624_; lean_object* v_unused_2625_; lean_object* v_unused_2626_; 
v_unused_2624_ = lean_ctor_get(v_s_2609_, 2);
lean_dec(v_unused_2624_);
v_unused_2625_ = lean_ctor_get(v_s_2609_, 1);
lean_dec(v_unused_2625_);
v_unused_2626_ = lean_ctor_get(v_s_2609_, 0);
lean_dec(v_unused_2626_);
v___x_2617_ = v_s_2609_;
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
else
{
lean_dec(v_s_2609_);
v___x_2617_ = lean_box(0);
v_isShared_2618_ = v_isSharedCheck_2623_;
goto v_resetjp_2616_;
}
v_resetjp_2616_:
{
lean_object* v___x_2619_; lean_object* v___x_2621_; 
v___x_2619_ = lean_nat_add(v_startInclusive_2612_, v___x_2615_);
lean_dec(v___x_2615_);
if (v_isShared_2618_ == 0)
{
lean_ctor_set(v___x_2617_, 2, v___x_2619_);
v___x_2621_ = v___x_2617_;
goto v_reusejp_2620_;
}
else
{
lean_object* v_reuseFailAlloc_2622_; 
v_reuseFailAlloc_2622_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2622_, 0, v_str_2611_);
lean_ctor_set(v_reuseFailAlloc_2622_, 1, v_startInclusive_2612_);
lean_ctor_set(v_reuseFailAlloc_2622_, 2, v___x_2619_);
v___x_2621_ = v_reuseFailAlloc_2622_;
goto v_reusejp_2620_;
}
v_reusejp_2620_:
{
return v___x_2621_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object* v_s_2627_, lean_object* v_pos_2628_, lean_object* v_inst_2629_){
_start:
{
lean_object* v_str_2630_; lean_object* v_startInclusive_2631_; lean_object* v_skipSuffix_x3f_2632_; lean_object* v___x_2633_; lean_object* v___x_2634_; lean_object* v___x_2635_; 
v_str_2630_ = lean_ctor_get(v_s_2627_, 0);
v_startInclusive_2631_ = lean_ctor_get(v_s_2627_, 1);
v_skipSuffix_x3f_2632_ = lean_ctor_get(v_inst_2629_, 0);
v___x_2633_ = lean_nat_add(v_startInclusive_2631_, v_pos_2628_);
lean_inc(v_startInclusive_2631_);
lean_inc_ref(v_str_2630_);
v___x_2634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2634_, 0, v_str_2630_);
lean_ctor_set(v___x_2634_, 1, v_startInclusive_2631_);
lean_ctor_set(v___x_2634_, 2, v___x_2633_);
lean_inc_ref(v_skipSuffix_x3f_2632_);
v___x_2635_ = lean_apply_1(v_skipSuffix_x3f_2632_, v___x_2634_);
if (lean_obj_tag(v___x_2635_) == 0)
{
lean_dec_ref(v_inst_2629_);
return v_pos_2628_;
}
else
{
lean_object* v_val_2636_; uint8_t v___x_2637_; 
v_val_2636_ = lean_ctor_get(v___x_2635_, 0);
lean_inc(v_val_2636_);
lean_dec_ref_known(v___x_2635_, 1);
v___x_2637_ = lean_nat_dec_lt(v_val_2636_, v_pos_2628_);
if (v___x_2637_ == 0)
{
lean_dec(v_val_2636_);
lean_dec_ref(v_inst_2629_);
return v_pos_2628_;
}
else
{
lean_dec(v_pos_2628_);
v_pos_2628_ = v_val_2636_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg___boxed(lean_object* v_s_2639_, lean_object* v_pos_2640_, lean_object* v_inst_2641_){
_start:
{
lean_object* v_res_2642_; 
v_res_2642_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2639_, v_pos_2640_, v_inst_2641_);
lean_dec_ref(v_s_2639_);
return v_res_2642_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile(lean_object* v_00_u03c1_2643_, lean_object* v_s_2644_, lean_object* v_pos_2645_, lean_object* v_pat_2646_, lean_object* v_inst_2647_){
_start:
{
lean_object* v___x_2648_; 
v___x_2648_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2644_, v_pos_2645_, v_inst_2647_);
return v___x_2648_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_2649_, lean_object* v_s_2650_, lean_object* v_pos_2651_, lean_object* v_pat_2652_, lean_object* v_inst_2653_){
_start:
{
lean_object* v_res_2654_; 
v_res_2654_ = l_String_Slice_Pos_revSkipWhile(v_00_u03c1_2649_, v_s_2650_, v_pos_2651_, v_pat_2652_, v_inst_2653_);
lean_dec(v_pat_2652_);
lean_dec_ref(v_s_2650_);
return v_res_2654_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg(lean_object* v_s_2655_, lean_object* v_inst_2656_){
_start:
{
lean_object* v_startInclusive_2657_; lean_object* v_endExclusive_2658_; lean_object* v___x_2659_; lean_object* v___x_2660_; 
v_startInclusive_2657_ = lean_ctor_get(v_s_2655_, 1);
v_endExclusive_2658_ = lean_ctor_get(v_s_2655_, 2);
v___x_2659_ = lean_nat_sub(v_endExclusive_2658_, v_startInclusive_2657_);
v___x_2660_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2655_, v___x_2659_, v_inst_2656_);
return v___x_2660_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg___boxed(lean_object* v_s_2661_, lean_object* v_inst_2662_){
_start:
{
lean_object* v_res_2663_; 
v_res_2663_ = l_String_Slice_skipSuffixWhile___redArg(v_s_2661_, v_inst_2662_);
lean_dec_ref(v_s_2661_);
return v_res_2663_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile(lean_object* v_00_u03c1_2664_, lean_object* v_s_2665_, lean_object* v_pat_2666_, lean_object* v_inst_2667_){
_start:
{
lean_object* v_startInclusive_2668_; lean_object* v_endExclusive_2669_; lean_object* v___x_2670_; lean_object* v___x_2671_; 
v_startInclusive_2668_ = lean_ctor_get(v_s_2665_, 1);
v_endExclusive_2669_ = lean_ctor_get(v_s_2665_, 2);
v___x_2670_ = lean_nat_sub(v_endExclusive_2669_, v_startInclusive_2668_);
v___x_2671_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2665_, v___x_2670_, v_inst_2667_);
return v___x_2671_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___boxed(lean_object* v_00_u03c1_2672_, lean_object* v_s_2673_, lean_object* v_pat_2674_, lean_object* v_inst_2675_){
_start:
{
lean_object* v_res_2676_; 
v_res_2676_ = l_String_Slice_skipSuffixWhile(v_00_u03c1_2672_, v_s_2673_, v_pat_2674_, v_inst_2675_);
lean_dec(v_pat_2674_);
lean_dec_ref(v_s_2673_);
return v_res_2676_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_revAll___redArg(lean_object* v_s_2677_, lean_object* v_inst_2678_){
_start:
{
lean_object* v_startInclusive_2679_; lean_object* v_endExclusive_2680_; lean_object* v___x_2681_; lean_object* v___x_2682_; lean_object* v___x_2683_; uint8_t v___x_2684_; 
v_startInclusive_2679_ = lean_ctor_get(v_s_2677_, 1);
v_endExclusive_2680_ = lean_ctor_get(v_s_2677_, 2);
v___x_2681_ = lean_nat_sub(v_endExclusive_2680_, v_startInclusive_2679_);
v___x_2682_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2677_, v___x_2681_, v_inst_2678_);
v___x_2683_ = lean_unsigned_to_nat(0u);
v___x_2684_ = lean_nat_dec_eq(v___x_2682_, v___x_2683_);
lean_dec(v___x_2682_);
return v___x_2684_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___redArg___boxed(lean_object* v_s_2685_, lean_object* v_inst_2686_){
_start:
{
uint8_t v_res_2687_; lean_object* v_r_2688_; 
v_res_2687_ = l_String_Slice_revAll___redArg(v_s_2685_, v_inst_2686_);
lean_dec_ref(v_s_2685_);
v_r_2688_ = lean_box(v_res_2687_);
return v_r_2688_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_revAll(lean_object* v_00_u03c1_2689_, lean_object* v_s_2690_, lean_object* v_pat_2691_, lean_object* v_inst_2692_){
_start:
{
lean_object* v_startInclusive_2693_; lean_object* v_endExclusive_2694_; lean_object* v___x_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; uint8_t v___x_2698_; 
v_startInclusive_2693_ = lean_ctor_get(v_s_2690_, 1);
v_endExclusive_2694_ = lean_ctor_get(v_s_2690_, 2);
v___x_2695_ = lean_nat_sub(v_endExclusive_2694_, v_startInclusive_2693_);
v___x_2696_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2690_, v___x_2695_, v_inst_2692_);
v___x_2697_ = lean_unsigned_to_nat(0u);
v___x_2698_ = lean_nat_dec_eq(v___x_2696_, v___x_2697_);
lean_dec(v___x_2696_);
return v___x_2698_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___boxed(lean_object* v_00_u03c1_2699_, lean_object* v_s_2700_, lean_object* v_pat_2701_, lean_object* v_inst_2702_){
_start:
{
uint8_t v_res_2703_; lean_object* v_r_2704_; 
v_res_2703_ = l_String_Slice_revAll(v_00_u03c1_2699_, v_s_2700_, v_pat_2701_, v_inst_2702_);
lean_dec(v_pat_2701_);
lean_dec_ref(v_s_2700_);
v_r_2704_ = lean_box(v_res_2703_);
return v_r_2704_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object* v_s_2705_, lean_object* v_inst_2706_){
_start:
{
lean_object* v_str_2707_; lean_object* v_startInclusive_2708_; lean_object* v_endExclusive_2709_; lean_object* v___x_2710_; lean_object* v___x_2711_; lean_object* v___x_2713_; uint8_t v_isShared_2714_; uint8_t v_isSharedCheck_2719_; 
v_str_2707_ = lean_ctor_get(v_s_2705_, 0);
lean_inc_ref(v_str_2707_);
v_startInclusive_2708_ = lean_ctor_get(v_s_2705_, 1);
lean_inc(v_startInclusive_2708_);
v_endExclusive_2709_ = lean_ctor_get(v_s_2705_, 2);
v___x_2710_ = lean_nat_sub(v_endExclusive_2709_, v_startInclusive_2708_);
v___x_2711_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2705_, v___x_2710_, v_inst_2706_);
v_isSharedCheck_2719_ = !lean_is_exclusive(v_s_2705_);
if (v_isSharedCheck_2719_ == 0)
{
lean_object* v_unused_2720_; lean_object* v_unused_2721_; lean_object* v_unused_2722_; 
v_unused_2720_ = lean_ctor_get(v_s_2705_, 2);
lean_dec(v_unused_2720_);
v_unused_2721_ = lean_ctor_get(v_s_2705_, 1);
lean_dec(v_unused_2721_);
v_unused_2722_ = lean_ctor_get(v_s_2705_, 0);
lean_dec(v_unused_2722_);
v___x_2713_ = v_s_2705_;
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
else
{
lean_dec(v_s_2705_);
v___x_2713_ = lean_box(0);
v_isShared_2714_ = v_isSharedCheck_2719_;
goto v_resetjp_2712_;
}
v_resetjp_2712_:
{
lean_object* v___x_2715_; lean_object* v___x_2717_; 
v___x_2715_ = lean_nat_add(v_startInclusive_2708_, v___x_2711_);
lean_dec(v___x_2711_);
if (v_isShared_2714_ == 0)
{
lean_ctor_set(v___x_2713_, 2, v___x_2715_);
v___x_2717_ = v___x_2713_;
goto v_reusejp_2716_;
}
else
{
lean_object* v_reuseFailAlloc_2718_; 
v_reuseFailAlloc_2718_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2718_, 0, v_str_2707_);
lean_ctor_set(v_reuseFailAlloc_2718_, 1, v_startInclusive_2708_);
lean_ctor_set(v_reuseFailAlloc_2718_, 2, v___x_2715_);
v___x_2717_ = v_reuseFailAlloc_2718_;
goto v_reusejp_2716_;
}
v_reusejp_2716_:
{
return v___x_2717_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object* v_00_u03c1_2723_, lean_object* v_s_2724_, lean_object* v_pat_2725_, lean_object* v_inst_2726_){
_start:
{
lean_object* v_str_2727_; lean_object* v_startInclusive_2728_; lean_object* v_endExclusive_2729_; lean_object* v___x_2730_; lean_object* v___x_2731_; lean_object* v___x_2733_; uint8_t v_isShared_2734_; uint8_t v_isSharedCheck_2739_; 
v_str_2727_ = lean_ctor_get(v_s_2724_, 0);
lean_inc_ref(v_str_2727_);
v_startInclusive_2728_ = lean_ctor_get(v_s_2724_, 1);
lean_inc(v_startInclusive_2728_);
v_endExclusive_2729_ = lean_ctor_get(v_s_2724_, 2);
v___x_2730_ = lean_nat_sub(v_endExclusive_2729_, v_startInclusive_2728_);
v___x_2731_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2724_, v___x_2730_, v_inst_2726_);
v_isSharedCheck_2739_ = !lean_is_exclusive(v_s_2724_);
if (v_isSharedCheck_2739_ == 0)
{
lean_object* v_unused_2740_; lean_object* v_unused_2741_; lean_object* v_unused_2742_; 
v_unused_2740_ = lean_ctor_get(v_s_2724_, 2);
lean_dec(v_unused_2740_);
v_unused_2741_ = lean_ctor_get(v_s_2724_, 1);
lean_dec(v_unused_2741_);
v_unused_2742_ = lean_ctor_get(v_s_2724_, 0);
lean_dec(v_unused_2742_);
v___x_2733_ = v_s_2724_;
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
else
{
lean_dec(v_s_2724_);
v___x_2733_ = lean_box(0);
v_isShared_2734_ = v_isSharedCheck_2739_;
goto v_resetjp_2732_;
}
v_resetjp_2732_:
{
lean_object* v___x_2735_; lean_object* v___x_2737_; 
v___x_2735_ = lean_nat_add(v_startInclusive_2728_, v___x_2731_);
lean_dec(v___x_2731_);
if (v_isShared_2734_ == 0)
{
lean_ctor_set(v___x_2733_, 2, v___x_2735_);
v___x_2737_ = v___x_2733_;
goto v_reusejp_2736_;
}
else
{
lean_object* v_reuseFailAlloc_2738_; 
v_reuseFailAlloc_2738_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2738_, 0, v_str_2727_);
lean_ctor_set(v_reuseFailAlloc_2738_, 1, v_startInclusive_2728_);
lean_ctor_set(v_reuseFailAlloc_2738_, 2, v___x_2735_);
v___x_2737_ = v_reuseFailAlloc_2738_;
goto v_reusejp_2736_;
}
v_reusejp_2736_:
{
return v___x_2737_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object* v_00_u03c1_2743_, lean_object* v_s_2744_, lean_object* v_pat_2745_, lean_object* v_inst_2746_){
_start:
{
lean_object* v_res_2747_; 
v_res_2747_ = l_String_Slice_dropEndWhile(v_00_u03c1_2743_, v_s_2744_, v_pat_2745_, v_inst_2746_);
lean_dec(v_pat_2745_);
return v_res_2747_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiEnd___closed__0(void){
_start:
{
lean_object* v___x_2748_; lean_object* v___x_2749_; 
v___x_2748_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_2749_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_2748_);
return v___x_2749_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object* v_s_2750_){
_start:
{
lean_object* v___x_2751_; lean_object* v_str_2752_; lean_object* v_startInclusive_2753_; lean_object* v_endExclusive_2754_; lean_object* v___x_2755_; lean_object* v___x_2756_; lean_object* v___x_2758_; uint8_t v_isShared_2759_; uint8_t v_isSharedCheck_2764_; 
v___x_2751_ = lean_obj_once(&l_String_Slice_trimAsciiEnd___closed__0, &l_String_Slice_trimAsciiEnd___closed__0_once, _init_l_String_Slice_trimAsciiEnd___closed__0);
v_str_2752_ = lean_ctor_get(v_s_2750_, 0);
lean_inc_ref(v_str_2752_);
v_startInclusive_2753_ = lean_ctor_get(v_s_2750_, 1);
lean_inc(v_startInclusive_2753_);
v_endExclusive_2754_ = lean_ctor_get(v_s_2750_, 2);
v___x_2755_ = lean_nat_sub(v_endExclusive_2754_, v_startInclusive_2753_);
v___x_2756_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2750_, v___x_2755_, v___x_2751_);
v_isSharedCheck_2764_ = !lean_is_exclusive(v_s_2750_);
if (v_isSharedCheck_2764_ == 0)
{
lean_object* v_unused_2765_; lean_object* v_unused_2766_; lean_object* v_unused_2767_; 
v_unused_2765_ = lean_ctor_get(v_s_2750_, 2);
lean_dec(v_unused_2765_);
v_unused_2766_ = lean_ctor_get(v_s_2750_, 1);
lean_dec(v_unused_2766_);
v_unused_2767_ = lean_ctor_get(v_s_2750_, 0);
lean_dec(v_unused_2767_);
v___x_2758_ = v_s_2750_;
v_isShared_2759_ = v_isSharedCheck_2764_;
goto v_resetjp_2757_;
}
else
{
lean_dec(v_s_2750_);
v___x_2758_ = lean_box(0);
v_isShared_2759_ = v_isSharedCheck_2764_;
goto v_resetjp_2757_;
}
v_resetjp_2757_:
{
lean_object* v___x_2760_; lean_object* v___x_2762_; 
v___x_2760_ = lean_nat_add(v_startInclusive_2753_, v___x_2756_);
lean_dec(v___x_2756_);
if (v_isShared_2759_ == 0)
{
lean_ctor_set(v___x_2758_, 2, v___x_2760_);
v___x_2762_ = v___x_2758_;
goto v_reusejp_2761_;
}
else
{
lean_object* v_reuseFailAlloc_2763_; 
v_reuseFailAlloc_2763_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2763_, 0, v_str_2752_);
lean_ctor_set(v_reuseFailAlloc_2763_, 1, v_startInclusive_2753_);
lean_ctor_set(v_reuseFailAlloc_2763_, 2, v___x_2760_);
v___x_2762_ = v_reuseFailAlloc_2763_;
goto v_reusejp_2761_;
}
v_reusejp_2761_:
{
return v___x_2762_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object* v_s_2768_, lean_object* v_n_2769_){
_start:
{
lean_object* v_str_2770_; lean_object* v_startInclusive_2771_; lean_object* v_endExclusive_2772_; lean_object* v___x_2773_; lean_object* v___x_2774_; lean_object* v___x_2776_; uint8_t v_isShared_2777_; uint8_t v_isSharedCheck_2782_; 
v_str_2770_ = lean_ctor_get(v_s_2768_, 0);
lean_inc_ref(v_str_2770_);
v_startInclusive_2771_ = lean_ctor_get(v_s_2768_, 1);
lean_inc(v_startInclusive_2771_);
v_endExclusive_2772_ = lean_ctor_get(v_s_2768_, 2);
lean_inc(v_endExclusive_2772_);
v___x_2773_ = lean_nat_sub(v_endExclusive_2772_, v_startInclusive_2771_);
v___x_2774_ = l_String_Slice_Pos_prevn(v_s_2768_, v___x_2773_, v_n_2769_);
v_isSharedCheck_2782_ = !lean_is_exclusive(v_s_2768_);
if (v_isSharedCheck_2782_ == 0)
{
lean_object* v_unused_2783_; lean_object* v_unused_2784_; lean_object* v_unused_2785_; 
v_unused_2783_ = lean_ctor_get(v_s_2768_, 2);
lean_dec(v_unused_2783_);
v_unused_2784_ = lean_ctor_get(v_s_2768_, 1);
lean_dec(v_unused_2784_);
v_unused_2785_ = lean_ctor_get(v_s_2768_, 0);
lean_dec(v_unused_2785_);
v___x_2776_ = v_s_2768_;
v_isShared_2777_ = v_isSharedCheck_2782_;
goto v_resetjp_2775_;
}
else
{
lean_dec(v_s_2768_);
v___x_2776_ = lean_box(0);
v_isShared_2777_ = v_isSharedCheck_2782_;
goto v_resetjp_2775_;
}
v_resetjp_2775_:
{
lean_object* v___x_2778_; lean_object* v___x_2780_; 
v___x_2778_ = lean_nat_add(v_startInclusive_2771_, v___x_2774_);
lean_dec(v___x_2774_);
lean_dec(v_startInclusive_2771_);
if (v_isShared_2777_ == 0)
{
lean_ctor_set(v___x_2776_, 1, v___x_2778_);
v___x_2780_ = v___x_2776_;
goto v_reusejp_2779_;
}
else
{
lean_object* v_reuseFailAlloc_2781_; 
v_reuseFailAlloc_2781_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2781_, 0, v_str_2770_);
lean_ctor_set(v_reuseFailAlloc_2781_, 1, v___x_2778_);
lean_ctor_set(v_reuseFailAlloc_2781_, 2, v_endExclusive_2772_);
v___x_2780_ = v_reuseFailAlloc_2781_;
goto v_reusejp_2779_;
}
v_reusejp_2779_:
{
return v___x_2780_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___redArg(lean_object* v_s_2786_, lean_object* v_inst_2787_){
_start:
{
lean_object* v_str_2788_; lean_object* v_startInclusive_2789_; lean_object* v_endExclusive_2790_; lean_object* v___x_2791_; lean_object* v___x_2792_; lean_object* v___x_2794_; uint8_t v_isShared_2795_; uint8_t v_isSharedCheck_2800_; 
v_str_2788_ = lean_ctor_get(v_s_2786_, 0);
lean_inc_ref(v_str_2788_);
v_startInclusive_2789_ = lean_ctor_get(v_s_2786_, 1);
lean_inc(v_startInclusive_2789_);
v_endExclusive_2790_ = lean_ctor_get(v_s_2786_, 2);
lean_inc(v_endExclusive_2790_);
v___x_2791_ = lean_nat_sub(v_endExclusive_2790_, v_startInclusive_2789_);
v___x_2792_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2786_, v___x_2791_, v_inst_2787_);
v_isSharedCheck_2800_ = !lean_is_exclusive(v_s_2786_);
if (v_isSharedCheck_2800_ == 0)
{
lean_object* v_unused_2801_; lean_object* v_unused_2802_; lean_object* v_unused_2803_; 
v_unused_2801_ = lean_ctor_get(v_s_2786_, 2);
lean_dec(v_unused_2801_);
v_unused_2802_ = lean_ctor_get(v_s_2786_, 1);
lean_dec(v_unused_2802_);
v_unused_2803_ = lean_ctor_get(v_s_2786_, 0);
lean_dec(v_unused_2803_);
v___x_2794_ = v_s_2786_;
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
else
{
lean_dec(v_s_2786_);
v___x_2794_ = lean_box(0);
v_isShared_2795_ = v_isSharedCheck_2800_;
goto v_resetjp_2793_;
}
v_resetjp_2793_:
{
lean_object* v___x_2796_; lean_object* v___x_2798_; 
v___x_2796_ = lean_nat_add(v_startInclusive_2789_, v___x_2792_);
lean_dec(v___x_2792_);
lean_dec(v_startInclusive_2789_);
if (v_isShared_2795_ == 0)
{
lean_ctor_set(v___x_2794_, 1, v___x_2796_);
v___x_2798_ = v___x_2794_;
goto v_reusejp_2797_;
}
else
{
lean_object* v_reuseFailAlloc_2799_; 
v_reuseFailAlloc_2799_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2799_, 0, v_str_2788_);
lean_ctor_set(v_reuseFailAlloc_2799_, 1, v___x_2796_);
lean_ctor_set(v_reuseFailAlloc_2799_, 2, v_endExclusive_2790_);
v___x_2798_ = v_reuseFailAlloc_2799_;
goto v_reusejp_2797_;
}
v_reusejp_2797_:
{
return v___x_2798_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile(lean_object* v_00_u03c1_2804_, lean_object* v_s_2805_, lean_object* v_pat_2806_, lean_object* v_inst_2807_){
_start:
{
lean_object* v_str_2808_; lean_object* v_startInclusive_2809_; lean_object* v_endExclusive_2810_; lean_object* v___x_2811_; lean_object* v___x_2812_; lean_object* v___x_2814_; uint8_t v_isShared_2815_; uint8_t v_isSharedCheck_2820_; 
v_str_2808_ = lean_ctor_get(v_s_2805_, 0);
lean_inc_ref(v_str_2808_);
v_startInclusive_2809_ = lean_ctor_get(v_s_2805_, 1);
lean_inc(v_startInclusive_2809_);
v_endExclusive_2810_ = lean_ctor_get(v_s_2805_, 2);
lean_inc(v_endExclusive_2810_);
v___x_2811_ = lean_nat_sub(v_endExclusive_2810_, v_startInclusive_2809_);
v___x_2812_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2805_, v___x_2811_, v_inst_2807_);
v_isSharedCheck_2820_ = !lean_is_exclusive(v_s_2805_);
if (v_isSharedCheck_2820_ == 0)
{
lean_object* v_unused_2821_; lean_object* v_unused_2822_; lean_object* v_unused_2823_; 
v_unused_2821_ = lean_ctor_get(v_s_2805_, 2);
lean_dec(v_unused_2821_);
v_unused_2822_ = lean_ctor_get(v_s_2805_, 1);
lean_dec(v_unused_2822_);
v_unused_2823_ = lean_ctor_get(v_s_2805_, 0);
lean_dec(v_unused_2823_);
v___x_2814_ = v_s_2805_;
v_isShared_2815_ = v_isSharedCheck_2820_;
goto v_resetjp_2813_;
}
else
{
lean_dec(v_s_2805_);
v___x_2814_ = lean_box(0);
v_isShared_2815_ = v_isSharedCheck_2820_;
goto v_resetjp_2813_;
}
v_resetjp_2813_:
{
lean_object* v___x_2816_; lean_object* v___x_2818_; 
v___x_2816_ = lean_nat_add(v_startInclusive_2809_, v___x_2812_);
lean_dec(v___x_2812_);
lean_dec(v_startInclusive_2809_);
if (v_isShared_2815_ == 0)
{
lean_ctor_set(v___x_2814_, 1, v___x_2816_);
v___x_2818_ = v___x_2814_;
goto v_reusejp_2817_;
}
else
{
lean_object* v_reuseFailAlloc_2819_; 
v_reuseFailAlloc_2819_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2819_, 0, v_str_2808_);
lean_ctor_set(v_reuseFailAlloc_2819_, 1, v___x_2816_);
lean_ctor_set(v_reuseFailAlloc_2819_, 2, v_endExclusive_2810_);
v___x_2818_ = v_reuseFailAlloc_2819_;
goto v_reusejp_2817_;
}
v_reusejp_2817_:
{
return v___x_2818_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___boxed(lean_object* v_00_u03c1_2824_, lean_object* v_s_2825_, lean_object* v_pat_2826_, lean_object* v_inst_2827_){
_start:
{
lean_object* v_res_2828_; 
v_res_2828_ = l_String_Slice_takeEndWhile(v_00_u03c1_2824_, v_s_2825_, v_pat_2826_, v_inst_2827_);
lean_dec(v_pat_2826_);
return v_res_2828_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___redArg(lean_object* v_inst_2829_, lean_object* v_s_2830_, lean_object* v_inst_2831_){
_start:
{
lean_object* v___f_2832_; lean_object* v_searcher_2833_; lean_object* v___x_2834_; lean_object* v___f_2835_; lean_object* v___x_2836_; 
v___f_2832_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_2830_);
v_searcher_2833_ = lean_apply_1(v_inst_2831_, v_s_2830_);
v___x_2834_ = lean_box(0);
v___f_2835_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_2836_ = lean_apply_7(v_inst_2829_, v_s_2830_, v___f_2832_, lean_box(0), lean_box(0), v_searcher_2833_, v___x_2834_, v___f_2835_);
return v___x_2836_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f(lean_object* v_00_u03c3_2837_, lean_object* v_inst_2838_, lean_object* v_inst_2839_, lean_object* v_00_u03c1_2840_, lean_object* v_s_2841_, lean_object* v_pat_2842_, lean_object* v_inst_2843_){
_start:
{
lean_object* v___x_2844_; 
v___x_2844_ = l_String_Slice_revFind_x3f___redArg(v_inst_2839_, v_s_2841_, v_inst_2843_);
return v___x_2844_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___boxed(lean_object* v_00_u03c3_2845_, lean_object* v_inst_2846_, lean_object* v_inst_2847_, lean_object* v_00_u03c1_2848_, lean_object* v_s_2849_, lean_object* v_pat_2850_, lean_object* v_inst_2851_){
_start:
{
lean_object* v_res_2852_; 
v_res_2852_ = l_String_Slice_revFind_x3f(v_00_u03c3_2845_, v_inst_2846_, v_inst_2847_, v_00_u03c1_2848_, v_s_2849_, v_pat_2850_, v_inst_2851_);
lean_dec(v_pat_2850_);
lean_dec(v_inst_2846_);
return v_res_2852_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(lean_object* v_s_2853_, lean_object* v_pos_2854_){
_start:
{
lean_object* v_str_2855_; lean_object* v_startInclusive_2856_; lean_object* v_endExclusive_2857_; lean_object* v___x_2858_; uint8_t v___y_2866_; lean_object* v___x_2867_; lean_object* v___x_2868_; uint8_t v___x_2869_; 
v_str_2855_ = lean_ctor_get(v_s_2853_, 0);
v_startInclusive_2856_ = lean_ctor_get(v_s_2853_, 1);
v_endExclusive_2857_ = lean_ctor_get(v_s_2853_, 2);
v___x_2858_ = lean_nat_add(v_startInclusive_2856_, v_pos_2854_);
v___x_2867_ = lean_unsigned_to_nat(0u);
v___x_2868_ = lean_nat_sub(v_endExclusive_2857_, v___x_2858_);
v___x_2869_ = lean_nat_dec_eq(v___x_2867_, v___x_2868_);
lean_dec(v___x_2868_);
if (v___x_2869_ == 0)
{
uint32_t v___x_2870_; uint8_t v___y_2872_; uint32_t v___x_2877_; uint8_t v___x_2878_; 
v___x_2870_ = lean_string_utf8_get_fast(v_str_2855_, v___x_2858_);
v___x_2877_ = 32;
v___x_2878_ = lean_uint32_dec_eq(v___x_2870_, v___x_2877_);
if (v___x_2878_ == 0)
{
uint32_t v___x_2879_; uint8_t v___x_2880_; 
v___x_2879_ = 9;
v___x_2880_ = lean_uint32_dec_eq(v___x_2870_, v___x_2879_);
v___y_2872_ = v___x_2880_;
goto v___jp_2871_;
}
else
{
v___y_2872_ = v___x_2878_;
goto v___jp_2871_;
}
v___jp_2871_:
{
if (v___y_2872_ == 0)
{
uint32_t v___x_2873_; uint8_t v___x_2874_; 
v___x_2873_ = 13;
v___x_2874_ = lean_uint32_dec_eq(v___x_2870_, v___x_2873_);
if (v___x_2874_ == 0)
{
uint32_t v___x_2875_; uint8_t v___x_2876_; 
v___x_2875_ = 10;
v___x_2876_ = lean_uint32_dec_eq(v___x_2870_, v___x_2875_);
v___y_2866_ = v___x_2876_;
goto v___jp_2865_;
}
else
{
v___y_2866_ = v___x_2874_;
goto v___jp_2865_;
}
}
else
{
goto v___jp_2859_;
}
}
}
else
{
lean_dec(v___x_2858_);
return v_pos_2854_;
}
v___jp_2859_:
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; uint8_t v___x_2863_; 
v___x_2860_ = lean_string_utf8_next_fast(v_str_2855_, v___x_2858_);
v___x_2861_ = lean_nat_sub(v___x_2860_, v___x_2858_);
lean_dec(v___x_2858_);
v___x_2862_ = lean_nat_add(v_pos_2854_, v___x_2861_);
lean_dec(v___x_2861_);
v___x_2863_ = lean_nat_dec_lt(v_pos_2854_, v___x_2862_);
if (v___x_2863_ == 0)
{
lean_dec(v___x_2862_);
return v_pos_2854_;
}
else
{
lean_dec(v_pos_2854_);
v_pos_2854_ = v___x_2862_;
goto _start;
}
}
v___jp_2865_:
{
if (v___y_2866_ == 0)
{
lean_dec(v___x_2858_);
return v_pos_2854_;
}
else
{
goto v___jp_2859_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0___boxed(lean_object* v_s_2881_, lean_object* v_pos_2882_){
_start:
{
lean_object* v_res_2883_; 
v_res_2883_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2881_, v_pos_2882_);
lean_dec_ref(v_s_2881_);
return v_res_2883_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(lean_object* v_s_2884_, lean_object* v_pos_2885_){
_start:
{
lean_object* v_str_2886_; lean_object* v_startInclusive_2887_; lean_object* v___x_2888_; lean_object* v___x_2889_; lean_object* v___x_2890_; uint8_t v___x_2891_; 
v_str_2886_ = lean_ctor_get(v_s_2884_, 0);
v_startInclusive_2887_ = lean_ctor_get(v_s_2884_, 1);
v___x_2888_ = lean_nat_add(v_startInclusive_2887_, v_pos_2885_);
v___x_2889_ = lean_nat_sub(v___x_2888_, v_startInclusive_2887_);
v___x_2890_ = lean_unsigned_to_nat(0u);
v___x_2891_ = lean_nat_dec_eq(v___x_2889_, v___x_2890_);
if (v___x_2891_ == 0)
{
lean_object* v___x_2892_; lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; uint8_t v___y_2900_; lean_object* v___x_2901_; uint32_t v___x_2902_; uint8_t v___y_2904_; uint32_t v___x_2909_; uint8_t v___x_2910_; 
lean_inc(v_startInclusive_2887_);
lean_inc_ref(v_str_2886_);
v___x_2892_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2892_, 0, v_str_2886_);
lean_ctor_set(v___x_2892_, 1, v_startInclusive_2887_);
lean_ctor_set(v___x_2892_, 2, v___x_2888_);
v___x_2893_ = lean_unsigned_to_nat(1u);
v___x_2894_ = lean_nat_sub(v___x_2889_, v___x_2893_);
lean_dec(v___x_2889_);
v___x_2895_ = l_String_Slice_posLE(v___x_2892_, v___x_2894_);
lean_dec_ref_known(v___x_2892_, 3);
v___x_2901_ = lean_nat_add(v_startInclusive_2887_, v___x_2895_);
v___x_2902_ = lean_string_utf8_get_fast(v_str_2886_, v___x_2901_);
lean_dec(v___x_2901_);
v___x_2909_ = 32;
v___x_2910_ = lean_uint32_dec_eq(v___x_2902_, v___x_2909_);
if (v___x_2910_ == 0)
{
uint32_t v___x_2911_; uint8_t v___x_2912_; 
v___x_2911_ = 9;
v___x_2912_ = lean_uint32_dec_eq(v___x_2902_, v___x_2911_);
v___y_2904_ = v___x_2912_;
goto v___jp_2903_;
}
else
{
v___y_2904_ = v___x_2910_;
goto v___jp_2903_;
}
v___jp_2896_:
{
uint8_t v___x_2897_; 
v___x_2897_ = lean_nat_dec_lt(v___x_2895_, v_pos_2885_);
if (v___x_2897_ == 0)
{
lean_dec(v___x_2895_);
return v_pos_2885_;
}
else
{
lean_dec(v_pos_2885_);
v_pos_2885_ = v___x_2895_;
goto _start;
}
}
v___jp_2899_:
{
if (v___y_2900_ == 0)
{
lean_dec(v___x_2895_);
return v_pos_2885_;
}
else
{
goto v___jp_2896_;
}
}
v___jp_2903_:
{
if (v___y_2904_ == 0)
{
uint32_t v___x_2905_; uint8_t v___x_2906_; 
v___x_2905_ = 13;
v___x_2906_ = lean_uint32_dec_eq(v___x_2902_, v___x_2905_);
if (v___x_2906_ == 0)
{
uint32_t v___x_2907_; uint8_t v___x_2908_; 
v___x_2907_ = 10;
v___x_2908_ = lean_uint32_dec_eq(v___x_2902_, v___x_2907_);
v___y_2900_ = v___x_2908_;
goto v___jp_2899_;
}
else
{
v___y_2900_ = v___x_2906_;
goto v___jp_2899_;
}
}
else
{
goto v___jp_2896_;
}
}
}
else
{
lean_dec(v___x_2889_);
lean_dec(v___x_2888_);
return v_pos_2885_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1___boxed(lean_object* v_s_2913_, lean_object* v_pos_2914_){
_start:
{
lean_object* v_res_2915_; 
v_res_2915_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v_s_2913_, v_pos_2914_);
lean_dec_ref(v_s_2913_);
return v_res_2915_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAscii(lean_object* v_s_2916_){
_start:
{
lean_object* v_str_2917_; lean_object* v_startInclusive_2918_; lean_object* v_endExclusive_2919_; lean_object* v___x_2920_; lean_object* v___x_2921_; lean_object* v___x_2923_; uint8_t v_isShared_2924_; uint8_t v_isSharedCheck_2933_; 
v_str_2917_ = lean_ctor_get(v_s_2916_, 0);
lean_inc_ref(v_str_2917_);
v_startInclusive_2918_ = lean_ctor_get(v_s_2916_, 1);
lean_inc(v_startInclusive_2918_);
v_endExclusive_2919_ = lean_ctor_get(v_s_2916_, 2);
lean_inc(v_endExclusive_2919_);
v___x_2920_ = lean_unsigned_to_nat(0u);
v___x_2921_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2916_, v___x_2920_);
v_isSharedCheck_2933_ = !lean_is_exclusive(v_s_2916_);
if (v_isSharedCheck_2933_ == 0)
{
lean_object* v_unused_2934_; lean_object* v_unused_2935_; lean_object* v_unused_2936_; 
v_unused_2934_ = lean_ctor_get(v_s_2916_, 2);
lean_dec(v_unused_2934_);
v_unused_2935_ = lean_ctor_get(v_s_2916_, 1);
lean_dec(v_unused_2935_);
v_unused_2936_ = lean_ctor_get(v_s_2916_, 0);
lean_dec(v_unused_2936_);
v___x_2923_ = v_s_2916_;
v_isShared_2924_ = v_isSharedCheck_2933_;
goto v_resetjp_2922_;
}
else
{
lean_dec(v_s_2916_);
v___x_2923_ = lean_box(0);
v_isShared_2924_ = v_isSharedCheck_2933_;
goto v_resetjp_2922_;
}
v_resetjp_2922_:
{
lean_object* v___x_2925_; lean_object* v___x_2927_; 
v___x_2925_ = lean_nat_add(v_startInclusive_2918_, v___x_2921_);
lean_dec(v___x_2921_);
lean_dec(v_startInclusive_2918_);
lean_inc(v_endExclusive_2919_);
lean_inc(v___x_2925_);
lean_inc_ref(v_str_2917_);
if (v_isShared_2924_ == 0)
{
lean_ctor_set(v___x_2923_, 1, v___x_2925_);
v___x_2927_ = v___x_2923_;
goto v_reusejp_2926_;
}
else
{
lean_object* v_reuseFailAlloc_2932_; 
v_reuseFailAlloc_2932_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2932_, 0, v_str_2917_);
lean_ctor_set(v_reuseFailAlloc_2932_, 1, v___x_2925_);
lean_ctor_set(v_reuseFailAlloc_2932_, 2, v_endExclusive_2919_);
v___x_2927_ = v_reuseFailAlloc_2932_;
goto v_reusejp_2926_;
}
v_reusejp_2926_:
{
lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2931_; 
v___x_2928_ = lean_nat_sub(v_endExclusive_2919_, v___x_2925_);
lean_dec(v_endExclusive_2919_);
v___x_2929_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v___x_2927_, v___x_2928_);
lean_dec_ref(v___x_2927_);
v___x_2930_ = lean_nat_add(v___x_2925_, v___x_2929_);
lean_dec(v___x_2929_);
v___x_2931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2931_, 0, v_str_2917_);
lean_ctor_set(v___x_2931_, 1, v___x_2925_);
lean_ctor_set(v___x_2931_, 2, v___x_2930_);
return v___x_2931_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(lean_object* v_s1_2937_, lean_object* v_s1Curr_2938_, lean_object* v_s2_2939_, lean_object* v_s2Curr_2940_){
_start:
{
uint8_t v___y_2942_; uint8_t v___y_2943_; uint8_t v___y_2950_; uint8_t v___y_2951_; uint8_t v___y_2952_; lean_object* v_str_2955_; lean_object* v_startInclusive_2956_; lean_object* v_endExclusive_2957_; lean_object* v___x_2958_; uint8_t v___x_2965_; 
v_str_2955_ = lean_ctor_get(v_s1_2937_, 0);
v_startInclusive_2956_ = lean_ctor_get(v_s1_2937_, 1);
v_endExclusive_2957_ = lean_ctor_get(v_s1_2937_, 2);
v___x_2958_ = lean_nat_sub(v_endExclusive_2957_, v_startInclusive_2956_);
v___x_2965_ = lean_nat_dec_lt(v_s1Curr_2938_, v___x_2958_);
if (v___x_2965_ == 0)
{
goto v___jp_2959_;
}
else
{
lean_object* v_str_2966_; lean_object* v_startInclusive_2967_; lean_object* v_endExclusive_2968_; uint8_t v___y_2970_; lean_object* v___x_2977_; uint8_t v___x_2978_; 
v_str_2966_ = lean_ctor_get(v_s2_2939_, 0);
v_startInclusive_2967_ = lean_ctor_get(v_s2_2939_, 1);
v_endExclusive_2968_ = lean_ctor_get(v_s2_2939_, 2);
v___x_2977_ = lean_nat_sub(v_endExclusive_2968_, v_startInclusive_2967_);
v___x_2978_ = lean_nat_dec_lt(v_s2Curr_2940_, v___x_2977_);
lean_dec(v___x_2977_);
if (v___x_2978_ == 0)
{
goto v___jp_2959_;
}
else
{
lean_object* v___x_2979_; uint8_t v___x_2980_; uint8_t v___y_2982_; uint8_t v___x_2985_; uint8_t v___x_2986_; 
lean_dec(v___x_2958_);
v___x_2979_ = lean_nat_add(v_startInclusive_2956_, v_s1Curr_2938_);
v___x_2980_ = lean_string_get_byte_fast(v_str_2955_, v___x_2979_);
v___x_2985_ = 65;
v___x_2986_ = lean_uint8_dec_le(v___x_2985_, v___x_2980_);
if (v___x_2986_ == 0)
{
v___y_2982_ = v___x_2986_;
goto v___jp_2981_;
}
else
{
uint8_t v___x_2987_; uint8_t v___x_2988_; 
v___x_2987_ = 90;
v___x_2988_ = lean_uint8_dec_le(v___x_2980_, v___x_2987_);
v___y_2982_ = v___x_2988_;
goto v___jp_2981_;
}
v___jp_2981_:
{
if (v___y_2982_ == 0)
{
v___y_2970_ = v___x_2980_;
goto v___jp_2969_;
}
else
{
uint8_t v___x_2983_; uint8_t v___x_2984_; 
v___x_2983_ = 32;
v___x_2984_ = lean_uint8_add(v___x_2980_, v___x_2983_);
v___y_2970_ = v___x_2984_;
goto v___jp_2969_;
}
}
}
v___jp_2969_:
{
lean_object* v___x_2971_; uint8_t v___x_2972_; uint8_t v___x_2973_; uint8_t v___x_2974_; 
v___x_2971_ = lean_nat_add(v_startInclusive_2967_, v_s2Curr_2940_);
v___x_2972_ = lean_string_get_byte_fast(v_str_2966_, v___x_2971_);
v___x_2973_ = 65;
v___x_2974_ = lean_uint8_dec_le(v___x_2973_, v___x_2972_);
if (v___x_2974_ == 0)
{
v___y_2950_ = v___y_2970_;
v___y_2951_ = v___x_2972_;
v___y_2952_ = v___x_2974_;
goto v___jp_2949_;
}
else
{
uint8_t v___x_2975_; uint8_t v___x_2976_; 
v___x_2975_ = 90;
v___x_2976_ = lean_uint8_dec_le(v___x_2972_, v___x_2975_);
v___y_2950_ = v___y_2970_;
v___y_2951_ = v___x_2972_;
v___y_2952_ = v___x_2976_;
goto v___jp_2949_;
}
}
}
v___jp_2941_:
{
uint8_t v___x_2944_; 
v___x_2944_ = lean_uint8_dec_eq(v___y_2942_, v___y_2943_);
if (v___x_2944_ == 0)
{
lean_dec(v_s2Curr_2940_);
lean_dec(v_s1Curr_2938_);
return v___x_2944_;
}
else
{
lean_object* v___x_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; 
v___x_2945_ = lean_unsigned_to_nat(1u);
v___x_2946_ = lean_nat_add(v_s1Curr_2938_, v___x_2945_);
lean_dec(v_s1Curr_2938_);
v___x_2947_ = lean_nat_add(v_s2Curr_2940_, v___x_2945_);
lean_dec(v_s2Curr_2940_);
v_s1Curr_2938_ = v___x_2946_;
v_s2Curr_2940_ = v___x_2947_;
goto _start;
}
}
v___jp_2949_:
{
if (v___y_2952_ == 0)
{
v___y_2942_ = v___y_2950_;
v___y_2943_ = v___y_2951_;
goto v___jp_2941_;
}
else
{
uint8_t v___x_2953_; uint8_t v___x_2954_; 
v___x_2953_ = 32;
v___x_2954_ = lean_uint8_add(v___y_2951_, v___x_2953_);
v___y_2942_ = v___y_2950_;
v___y_2943_ = v___x_2954_;
goto v___jp_2941_;
}
}
v___jp_2959_:
{
uint8_t v___x_2960_; 
v___x_2960_ = lean_nat_dec_eq(v_s1Curr_2938_, v___x_2958_);
lean_dec(v___x_2958_);
lean_dec(v_s1Curr_2938_);
if (v___x_2960_ == 0)
{
lean_dec(v_s2Curr_2940_);
return v___x_2960_;
}
else
{
lean_object* v_startInclusive_2961_; lean_object* v_endExclusive_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v_startInclusive_2961_ = lean_ctor_get(v_s2_2939_, 1);
v_endExclusive_2962_ = lean_ctor_get(v_s2_2939_, 2);
v___x_2963_ = lean_nat_sub(v_endExclusive_2962_, v_startInclusive_2961_);
v___x_2964_ = lean_nat_dec_eq(v_s2Curr_2940_, v___x_2963_);
lean_dec(v___x_2963_);
lean_dec(v_s2Curr_2940_);
return v___x_2964_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object* v_s1_2989_, lean_object* v_s1Curr_2990_, lean_object* v_s2_2991_, lean_object* v_s2Curr_2992_){
_start:
{
uint8_t v_res_2993_; lean_object* v_r_2994_; 
v_res_2993_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_2989_, v_s1Curr_2990_, v_s2_2991_, v_s2Curr_2992_);
lean_dec_ref(v_s2_2991_);
lean_dec_ref(v_s1_2989_);
v_r_2994_ = lean_box(v_res_2993_);
return v_r_2994_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object* v_s1_2995_, lean_object* v_s2_2996_){
_start:
{
lean_object* v_startInclusive_2997_; lean_object* v_endExclusive_2998_; lean_object* v_startInclusive_2999_; lean_object* v_endExclusive_3000_; lean_object* v___x_3001_; lean_object* v___x_3002_; uint8_t v___x_3003_; 
v_startInclusive_2997_ = lean_ctor_get(v_s1_2995_, 1);
v_endExclusive_2998_ = lean_ctor_get(v_s1_2995_, 2);
v_startInclusive_2999_ = lean_ctor_get(v_s2_2996_, 1);
v_endExclusive_3000_ = lean_ctor_get(v_s2_2996_, 2);
v___x_3001_ = lean_nat_sub(v_endExclusive_2998_, v_startInclusive_2997_);
v___x_3002_ = lean_nat_sub(v_endExclusive_3000_, v_startInclusive_2999_);
v___x_3003_ = lean_nat_dec_eq(v___x_3001_, v___x_3002_);
lean_dec(v___x_3002_);
lean_dec(v___x_3001_);
if (v___x_3003_ == 0)
{
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; uint8_t v___x_3005_; 
v___x_3004_ = lean_unsigned_to_nat(0u);
v___x_3005_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_2995_, v___x_3004_, v_s2_2996_, v___x_3004_);
return v___x_3005_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object* v_s1_3006_, lean_object* v_s2_3007_){
_start:
{
uint8_t v_res_3008_; lean_object* v_r_3009_; 
v_res_3008_ = l_String_Slice_eqIgnoreAsciiCase(v_s1_3006_, v_s2_3007_);
lean_dec_ref(v_s2_3007_);
lean_dec_ref(v_s1_3006_);
v_r_3009_ = lean_box(v_res_3008_);
return v_r_3009_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines_lineMap(lean_object* v_s_3010_){
_start:
{
lean_object* v_str_3011_; lean_object* v_startInclusive_3012_; lean_object* v_endExclusive_3013_; lean_object* v___x_3014_; lean_object* v___x_3015_; uint8_t v___x_3016_; 
v_str_3011_ = lean_ctor_get(v_s_3010_, 0);
v_startInclusive_3012_ = lean_ctor_get(v_s_3010_, 1);
v_endExclusive_3013_ = lean_ctor_get(v_s_3010_, 2);
v___x_3014_ = lean_nat_sub(v_endExclusive_3013_, v_startInclusive_3012_);
v___x_3015_ = lean_unsigned_to_nat(0u);
v___x_3016_ = lean_nat_dec_eq(v___x_3014_, v___x_3015_);
if (v___x_3016_ == 0)
{
uint32_t v___x_3017_; lean_object* v___x_3018_; lean_object* v___x_3019_; lean_object* v___x_3020_; lean_object* v___x_3021_; uint32_t v___x_3022_; uint8_t v___x_3023_; 
v___x_3017_ = 10;
v___x_3018_ = lean_unsigned_to_nat(1u);
v___x_3019_ = lean_nat_sub(v___x_3014_, v___x_3018_);
lean_dec(v___x_3014_);
v___x_3020_ = l_String_Slice_posLE(v_s_3010_, v___x_3019_);
v___x_3021_ = lean_nat_add(v_startInclusive_3012_, v___x_3020_);
lean_dec(v___x_3020_);
v___x_3022_ = lean_string_utf8_get_fast(v_str_3011_, v___x_3021_);
v___x_3023_ = lean_uint32_dec_eq(v___x_3022_, v___x_3017_);
if (v___x_3023_ == 0)
{
lean_dec(v___x_3021_);
return v_s_3010_;
}
else
{
lean_object* v___x_3025_; uint8_t v_isShared_3026_; uint8_t v_isSharedCheck_3039_; 
lean_inc(v_startInclusive_3012_);
lean_inc_ref(v_str_3011_);
v_isSharedCheck_3039_ = !lean_is_exclusive(v_s_3010_);
if (v_isSharedCheck_3039_ == 0)
{
lean_object* v_unused_3040_; lean_object* v_unused_3041_; lean_object* v_unused_3042_; 
v_unused_3040_ = lean_ctor_get(v_s_3010_, 2);
lean_dec(v_unused_3040_);
v_unused_3041_ = lean_ctor_get(v_s_3010_, 1);
lean_dec(v_unused_3041_);
v_unused_3042_ = lean_ctor_get(v_s_3010_, 0);
lean_dec(v_unused_3042_);
v___x_3025_ = v_s_3010_;
v_isShared_3026_ = v_isSharedCheck_3039_;
goto v_resetjp_3024_;
}
else
{
lean_dec(v_s_3010_);
v___x_3025_ = lean_box(0);
v_isShared_3026_ = v_isSharedCheck_3039_;
goto v_resetjp_3024_;
}
v_resetjp_3024_:
{
lean_object* v___x_3028_; 
lean_inc(v___x_3021_);
lean_inc(v_startInclusive_3012_);
lean_inc_ref(v_str_3011_);
if (v_isShared_3026_ == 0)
{
lean_ctor_set(v___x_3025_, 2, v___x_3021_);
v___x_3028_ = v___x_3025_;
goto v_reusejp_3027_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v_str_3011_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_startInclusive_3012_);
lean_ctor_set(v_reuseFailAlloc_3038_, 2, v___x_3021_);
v___x_3028_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3027_;
}
v_reusejp_3027_:
{
lean_object* v___x_3029_; uint8_t v___x_3030_; 
v___x_3029_ = lean_nat_sub(v___x_3021_, v_startInclusive_3012_);
lean_dec(v___x_3021_);
v___x_3030_ = lean_nat_dec_eq(v___x_3029_, v___x_3015_);
if (v___x_3030_ == 0)
{
uint32_t v___x_3031_; lean_object* v___x_3032_; lean_object* v___x_3033_; lean_object* v___x_3034_; uint32_t v___x_3035_; uint8_t v___x_3036_; 
v___x_3031_ = 13;
v___x_3032_ = lean_nat_sub(v___x_3029_, v___x_3018_);
lean_dec(v___x_3029_);
v___x_3033_ = l_String_Slice_posLE(v___x_3028_, v___x_3032_);
v___x_3034_ = lean_nat_add(v_startInclusive_3012_, v___x_3033_);
lean_dec(v___x_3033_);
v___x_3035_ = lean_string_utf8_get_fast(v_str_3011_, v___x_3034_);
v___x_3036_ = lean_uint32_dec_eq(v___x_3035_, v___x_3031_);
if (v___x_3036_ == 0)
{
lean_dec(v___x_3034_);
lean_dec(v_startInclusive_3012_);
lean_dec_ref(v_str_3011_);
return v___x_3028_;
}
else
{
lean_object* v___x_3037_; 
lean_dec_ref(v___x_3028_);
v___x_3037_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3037_, 0, v_str_3011_);
lean_ctor_set(v___x_3037_, 1, v_startInclusive_3012_);
lean_ctor_set(v___x_3037_, 2, v___x_3034_);
return v___x_3037_;
}
}
else
{
lean_dec(v___x_3029_);
lean_dec(v_startInclusive_3012_);
lean_dec_ref(v_str_3011_);
return v___x_3028_;
}
}
}
}
}
else
{
lean_dec(v___x_3014_);
return v_s_3010_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(lean_object* v_s_3045_){
_start:
{
lean_object* v___x_3046_; 
v___x_3046_ = ((lean_object*)(l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0));
return v___x_3046_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(lean_object* v_s_3047_){
_start:
{
lean_object* v_res_3048_; 
v_res_3048_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_3047_);
lean_dec_ref(v_s_3047_);
return v_res_3048_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines(lean_object* v_s_3049_){
_start:
{
lean_object* v___x_3050_; 
v___x_3050_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_3049_);
return v___x_3050_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines___boxed(lean_object* v_s_3051_){
_start:
{
lean_object* v_res_3052_; 
v_res_3052_ = l_String_Slice_lines(v_s_3051_);
lean_dec_ref(v_s_3051_);
return v_res_3052_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(lean_object* v_s_3053_, lean_object* v_a_3054_, lean_object* v_b_3055_){
_start:
{
lean_object* v_str_3056_; lean_object* v_startInclusive_3057_; lean_object* v_endExclusive_3058_; lean_object* v___x_3059_; uint8_t v_lastWasDigit_3060_; 
v_str_3056_ = lean_ctor_get(v_s_3053_, 0);
v_startInclusive_3057_ = lean_ctor_get(v_s_3053_, 1);
v_endExclusive_3058_ = lean_ctor_get(v_s_3053_, 2);
v___x_3059_ = lean_nat_sub(v_endExclusive_3058_, v_startInclusive_3057_);
v_lastWasDigit_3060_ = lean_nat_dec_eq(v_a_3054_, v___x_3059_);
lean_dec(v___x_3059_);
if (v_lastWasDigit_3060_ == 0)
{
lean_object* v_snd_3061_; lean_object* v___x_3063_; uint8_t v_isShared_3064_; uint8_t v_isSharedCheck_3096_; 
v_snd_3061_ = lean_ctor_get(v_b_3055_, 1);
v_isSharedCheck_3096_ = !lean_is_exclusive(v_b_3055_);
if (v_isSharedCheck_3096_ == 0)
{
lean_object* v_unused_3097_; 
v_unused_3097_ = lean_ctor_get(v_b_3055_, 0);
lean_dec(v_unused_3097_);
v___x_3063_ = v_b_3055_;
v_isShared_3064_ = v_isSharedCheck_3096_;
goto v_resetjp_3062_;
}
else
{
lean_inc(v_snd_3061_);
lean_dec(v_b_3055_);
v___x_3063_ = lean_box(0);
v_isShared_3064_ = v_isSharedCheck_3096_;
goto v_resetjp_3062_;
}
v_resetjp_3062_:
{
lean_object* v___x_3065_; lean_object* v___x_3066_; lean_object* v___x_3067_; lean_object* v___x_3068_; uint8_t v___y_3070_; uint32_t v___x_3081_; uint32_t v___x_3082_; uint8_t v___x_3083_; 
v___x_3065_ = lean_box(0);
v___x_3066_ = lean_nat_add(v_startInclusive_3057_, v_a_3054_);
lean_dec(v_a_3054_);
v___x_3067_ = lean_string_utf8_next_fast(v_str_3056_, v___x_3066_);
v___x_3068_ = lean_nat_sub(v___x_3067_, v_startInclusive_3057_);
v___x_3081_ = lean_string_utf8_get_fast(v_str_3056_, v___x_3066_);
lean_dec(v___x_3066_);
v___x_3082_ = 95;
v___x_3083_ = lean_uint32_dec_eq(v___x_3081_, v___x_3082_);
if (v___x_3083_ == 0)
{
uint32_t v___x_3084_; uint8_t v___x_3085_; 
v___x_3084_ = 48;
v___x_3085_ = lean_uint32_dec_le(v___x_3084_, v___x_3081_);
if (v___x_3085_ == 0)
{
v___y_3070_ = v___x_3085_;
goto v___jp_3069_;
}
else
{
uint32_t v___x_3086_; uint8_t v___x_3087_; 
v___x_3086_ = 57;
v___x_3087_ = lean_uint32_dec_le(v___x_3081_, v___x_3086_);
v___y_3070_ = v___x_3087_;
goto v___jp_3069_;
}
}
else
{
uint8_t v___x_3088_; uint8_t v___x_3089_; 
lean_del_object(v___x_3063_);
v___x_3088_ = lean_unbox(v_snd_3061_);
v___x_3089_ = lean_bool_not(v___x_3088_);
if (v___x_3089_ == 0)
{
lean_object* v___x_3090_; lean_object* v___x_3091_; 
lean_dec(v_snd_3061_);
v___x_3090_ = lean_box(v_lastWasDigit_3060_);
v___x_3091_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3091_, 0, v___x_3065_);
lean_ctor_set(v___x_3091_, 1, v___x_3090_);
v_a_3054_ = v___x_3068_;
v_b_3055_ = v___x_3091_;
goto _start;
}
else
{
lean_object* v___x_3093_; lean_object* v___x_3094_; lean_object* v___x_3095_; 
lean_dec(v___x_3068_);
v___x_3093_ = lean_box(v_lastWasDigit_3060_);
v___x_3094_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3094_, 0, v___x_3093_);
v___x_3095_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3095_, 0, v___x_3094_);
lean_ctor_set(v___x_3095_, 1, v_snd_3061_);
return v___x_3095_;
}
}
v___jp_3069_:
{
if (v___y_3070_ == 0)
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3074_; 
lean_dec(v___x_3068_);
v___x_3071_ = lean_box(v_lastWasDigit_3060_);
v___x_3072_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3072_, 0, v___x_3071_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 0, v___x_3072_);
v___x_3074_ = v___x_3063_;
goto v_reusejp_3073_;
}
else
{
lean_object* v_reuseFailAlloc_3075_; 
v_reuseFailAlloc_3075_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3075_, 0, v___x_3072_);
lean_ctor_set(v_reuseFailAlloc_3075_, 1, v_snd_3061_);
v___x_3074_ = v_reuseFailAlloc_3075_;
goto v_reusejp_3073_;
}
v_reusejp_3073_:
{
return v___x_3074_;
}
}
else
{
lean_object* v___x_3076_; lean_object* v___x_3078_; 
lean_dec(v_snd_3061_);
v___x_3076_ = lean_box(v___y_3070_);
if (v_isShared_3064_ == 0)
{
lean_ctor_set(v___x_3063_, 1, v___x_3076_);
lean_ctor_set(v___x_3063_, 0, v___x_3065_);
v___x_3078_ = v___x_3063_;
goto v_reusejp_3077_;
}
else
{
lean_object* v_reuseFailAlloc_3080_; 
v_reuseFailAlloc_3080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3080_, 0, v___x_3065_);
lean_ctor_set(v_reuseFailAlloc_3080_, 1, v___x_3076_);
v___x_3078_ = v_reuseFailAlloc_3080_;
goto v_reusejp_3077_;
}
v_reusejp_3077_:
{
v_a_3054_ = v___x_3068_;
v_b_3055_ = v___x_3078_;
goto _start;
}
}
}
}
}
else
{
lean_dec(v_a_3054_);
return v_b_3055_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg___boxed(lean_object* v_s_3098_, lean_object* v_a_3099_, lean_object* v_b_3100_){
_start:
{
lean_object* v_res_3101_; 
v_res_3101_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3098_, v_a_3099_, v_b_3100_);
lean_dec_ref(v_s_3098_);
return v_res_3101_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isNat(lean_object* v_s_3106_){
_start:
{
lean_object* v___x_3107_; lean_object* v___x_3108_; lean_object* v___x_3109_; lean_object* v_fst_3110_; 
v___x_3107_ = ((lean_object*)(l_String_Slice_isNat___closed__0));
v___x_3108_ = l_String_Slice_positions(v_s_3106_);
v___x_3109_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3106_, v___x_3108_, v___x_3107_);
v_fst_3110_ = lean_ctor_get(v___x_3109_, 0);
lean_inc(v_fst_3110_);
if (lean_obj_tag(v_fst_3110_) == 0)
{
lean_object* v_snd_3111_; uint8_t v___x_3112_; 
v_snd_3111_ = lean_ctor_get(v___x_3109_, 1);
lean_inc(v_snd_3111_);
lean_dec_ref(v___x_3109_);
v___x_3112_ = lean_unbox(v_snd_3111_);
lean_dec(v_snd_3111_);
return v___x_3112_;
}
else
{
lean_object* v_val_3113_; uint8_t v___x_3114_; 
lean_dec_ref(v___x_3109_);
v_val_3113_ = lean_ctor_get(v_fst_3110_, 0);
lean_inc(v_val_3113_);
lean_dec_ref_known(v_fst_3110_, 1);
v___x_3114_ = lean_unbox(v_val_3113_);
lean_dec(v_val_3113_);
return v___x_3114_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object* v_s_3115_){
_start:
{
uint8_t v_res_3116_; lean_object* v_r_3117_; 
v_res_3116_ = l_String_Slice_isNat(v_s_3115_);
lean_dec_ref(v_s_3115_);
v_r_3117_ = lean_box(v_res_3116_);
return v_r_3117_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(lean_object* v_s_3118_, lean_object* v_inst_3119_, lean_object* v_R_3120_, lean_object* v_a_3121_, lean_object* v_b_3122_, lean_object* v_c_3123_){
_start:
{
lean_object* v___x_3124_; 
v___x_3124_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3118_, v_a_3121_, v_b_3122_);
return v___x_3124_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___boxed(lean_object* v_s_3125_, lean_object* v_inst_3126_, lean_object* v_R_3127_, lean_object* v_a_3128_, lean_object* v_b_3129_, lean_object* v_c_3130_){
_start:
{
lean_object* v_res_3131_; 
v_res_3131_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(v_s_3125_, v_inst_3126_, v_R_3127_, v_a_3128_, v_b_3129_, v_c_3130_);
lean_dec_ref(v_s_3125_);
return v_res_3131_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object* v_s_3132_, lean_object* v_a_3133_, lean_object* v_b_3134_){
_start:
{
lean_object* v_str_3135_; lean_object* v_startInclusive_3136_; lean_object* v_endExclusive_3137_; lean_object* v___x_3138_; uint8_t v___x_3139_; 
v_str_3135_ = lean_ctor_get(v_s_3132_, 0);
v_startInclusive_3136_ = lean_ctor_get(v_s_3132_, 1);
v_endExclusive_3137_ = lean_ctor_get(v_s_3132_, 2);
v___x_3138_ = lean_nat_sub(v_endExclusive_3137_, v_startInclusive_3136_);
v___x_3139_ = lean_nat_dec_eq(v_a_3133_, v___x_3138_);
lean_dec(v___x_3138_);
if (v___x_3139_ == 0)
{
lean_object* v___x_3140_; lean_object* v___x_3141_; lean_object* v___x_3142_; uint32_t v___x_3143_; uint32_t v___x_3144_; uint8_t v___x_3145_; 
v___x_3140_ = lean_nat_add(v_startInclusive_3136_, v_a_3133_);
lean_dec(v_a_3133_);
v___x_3141_ = lean_string_utf8_next_fast(v_str_3135_, v___x_3140_);
v___x_3142_ = lean_nat_sub(v___x_3141_, v_startInclusive_3136_);
v___x_3143_ = lean_string_utf8_get_fast(v_str_3135_, v___x_3140_);
lean_dec(v___x_3140_);
v___x_3144_ = 95;
v___x_3145_ = lean_uint32_dec_eq(v___x_3143_, v___x_3144_);
if (v___x_3145_ == 0)
{
lean_object* v___x_3146_; lean_object* v___x_3147_; lean_object* v___x_3148_; lean_object* v___x_3149_; lean_object* v___x_3150_; lean_object* v___x_3151_; 
v___x_3146_ = lean_unsigned_to_nat(10u);
v___x_3147_ = lean_nat_mul(v_b_3134_, v___x_3146_);
lean_dec(v_b_3134_);
v___x_3148_ = lean_uint32_to_nat(v___x_3143_);
v___x_3149_ = lean_unsigned_to_nat(48u);
v___x_3150_ = lean_nat_sub(v___x_3148_, v___x_3149_);
lean_dec(v___x_3148_);
v___x_3151_ = lean_nat_add(v___x_3147_, v___x_3150_);
lean_dec(v___x_3150_);
lean_dec(v___x_3147_);
v_a_3133_ = v___x_3142_;
v_b_3134_ = v___x_3151_;
goto _start;
}
else
{
v_a_3133_ = v___x_3142_;
goto _start;
}
}
else
{
lean_dec(v_a_3133_);
return v_b_3134_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object* v_s_3154_, lean_object* v_a_3155_, lean_object* v_b_3156_){
_start:
{
lean_object* v_res_3157_; 
v_res_3157_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3154_, v_a_3155_, v_b_3156_);
lean_dec_ref(v_s_3154_);
return v_res_3157_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object* v_s_3158_){
_start:
{
uint8_t v___x_3159_; 
v___x_3159_ = l_String_Slice_isNat(v_s_3158_);
if (v___x_3159_ == 0)
{
lean_object* v___x_3160_; 
v___x_3160_ = lean_box(0);
return v___x_3160_;
}
else
{
lean_object* v___x_3161_; lean_object* v___x_3162_; lean_object* v___x_3163_; lean_object* v___x_3164_; 
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = l_String_Slice_positions(v_s_3158_);
v___x_3163_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3158_, v___x_3162_, v___x_3161_);
v___x_3164_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3164_, 0, v___x_3163_);
return v___x_3164_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object* v_s_3165_){
_start:
{
lean_object* v_res_3166_; 
v_res_3166_ = l_String_Slice_toNat_x3f(v_s_3165_);
lean_dec_ref(v_s_3165_);
return v_res_3166_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object* v_s_3167_, lean_object* v_inst_3168_, lean_object* v_R_3169_, lean_object* v_a_3170_, lean_object* v_b_3171_, lean_object* v_c_3172_){
_start:
{
lean_object* v___x_3173_; 
v___x_3173_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3167_, v_a_3170_, v_b_3171_);
return v___x_3173_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object* v_s_3174_, lean_object* v_inst_3175_, lean_object* v_R_3176_, lean_object* v_a_3177_, lean_object* v_b_3178_, lean_object* v_c_3179_){
_start:
{
lean_object* v_res_3180_; 
v_res_3180_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(v_s_3174_, v_inst_3175_, v_R_3176_, v_a_3177_, v_b_3178_, v_c_3179_);
lean_dec_ref(v_s_3174_);
return v_res_3180_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_toNat_x21_spec__0(lean_object* v_msg_3181_){
_start:
{
lean_object* v___x_3182_; lean_object* v___x_3183_; 
v___x_3182_ = lean_unsigned_to_nat(0u);
v___x_3183_ = lean_panic_fn_borrowed(v___x_3182_, v_msg_3181_);
return v___x_3183_;
}
}
static lean_object* _init_l_String_Slice_toNat_x21___closed__3(void){
_start:
{
lean_object* v___x_3187_; lean_object* v___x_3188_; lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; lean_object* v___x_3192_; 
v___x_3187_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__2));
v___x_3188_ = lean_unsigned_to_nat(4u);
v___x_3189_ = lean_unsigned_to_nat(1040u);
v___x_3190_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__1));
v___x_3191_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__0));
v___x_3192_ = l_mkPanicMessageWithDecl(v___x_3191_, v___x_3190_, v___x_3189_, v___x_3188_, v___x_3187_);
return v___x_3192_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21(lean_object* v_s_3193_){
_start:
{
uint8_t v___x_3194_; 
v___x_3194_ = l_String_Slice_isNat(v_s_3193_);
if (v___x_3194_ == 0)
{
lean_object* v___x_3195_; lean_object* v___x_3196_; 
v___x_3195_ = lean_obj_once(&l_String_Slice_toNat_x21___closed__3, &l_String_Slice_toNat_x21___closed__3_once, _init_l_String_Slice_toNat_x21___closed__3);
v___x_3196_ = l_panic___at___00String_Slice_toNat_x21_spec__0(v___x_3195_);
return v___x_3196_;
}
else
{
lean_object* v___x_3197_; lean_object* v___x_3198_; lean_object* v___x_3199_; 
v___x_3197_ = lean_unsigned_to_nat(0u);
v___x_3198_ = l_String_Slice_positions(v_s_3193_);
v___x_3199_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3193_, v___x_3198_, v___x_3197_);
return v___x_3199_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21___boxed(lean_object* v_s_3200_){
_start:
{
lean_object* v_res_3201_; 
v_res_3201_ = l_String_Slice_toNat_x21(v_s_3200_);
lean_dec_ref(v_s_3200_);
return v_res_3201_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object* v_s_3202_){
_start:
{
lean_object* v___x_3203_; lean_object* v___x_3204_; 
v___x_3203_ = lean_unsigned_to_nat(0u);
v___x_3204_ = l_String_Slice_Pos_get_x3f(v_s_3202_, v___x_3203_);
return v___x_3204_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object* v_s_3205_){
_start:
{
lean_object* v_res_3206_; 
v_res_3206_ = l_String_Slice_front_x3f(v_s_3205_);
lean_dec_ref(v_s_3205_);
return v_res_3206_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_front(lean_object* v_s_3207_){
_start:
{
lean_object* v___x_3208_; lean_object* v___x_3209_; 
v___x_3208_ = lean_unsigned_to_nat(0u);
v___x_3209_ = l_String_Slice_Pos_get_x3f(v_s_3207_, v___x_3208_);
if (lean_obj_tag(v___x_3209_) == 0)
{
uint32_t v___x_3210_; 
v___x_3210_ = 65;
return v___x_3210_;
}
else
{
lean_object* v_val_3211_; uint32_t v___x_3212_; 
v_val_3211_ = lean_ctor_get(v___x_3209_, 0);
lean_inc(v_val_3211_);
lean_dec_ref_known(v___x_3209_, 1);
v___x_3212_ = lean_unbox_uint32(v_val_3211_);
lean_dec(v_val_3211_);
return v___x_3212_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object* v_s_3213_){
_start:
{
uint32_t v_res_3214_; lean_object* v_r_3215_; 
v_res_3214_ = l_String_Slice_front(v_s_3213_);
lean_dec_ref(v_s_3213_);
v_r_3215_ = lean_box_uint32(v_res_3214_);
return v_r_3215_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isInt(lean_object* v_s_3216_){
_start:
{
lean_object* v_str_3217_; lean_object* v_startInclusive_3218_; lean_object* v_endExclusive_3219_; lean_object* v___x_3220_; lean_object* v___x_3221_; uint8_t v___x_3222_; 
v_str_3217_ = lean_ctor_get(v_s_3216_, 0);
v_startInclusive_3218_ = lean_ctor_get(v_s_3216_, 1);
v_endExclusive_3219_ = lean_ctor_get(v_s_3216_, 2);
v___x_3220_ = lean_unsigned_to_nat(0u);
v___x_3221_ = lean_nat_sub(v_endExclusive_3219_, v_startInclusive_3218_);
v___x_3222_ = lean_nat_dec_eq(v___x_3220_, v___x_3221_);
lean_dec(v___x_3221_);
if (v___x_3222_ == 0)
{
uint32_t v___x_3223_; uint32_t v___x_3224_; uint8_t v___x_3225_; 
v___x_3223_ = 45;
v___x_3224_ = lean_string_utf8_get_fast(v_str_3217_, v_startInclusive_3218_);
v___x_3225_ = lean_uint32_dec_eq(v___x_3224_, v___x_3223_);
if (v___x_3225_ == 0)
{
uint8_t v___x_3226_; 
v___x_3226_ = l_String_Slice_isNat(v_s_3216_);
lean_dec_ref(v_s_3216_);
return v___x_3226_;
}
else
{
lean_object* v___x_3228_; uint8_t v_isShared_3229_; uint8_t v_isSharedCheck_3237_; 
lean_inc(v_endExclusive_3219_);
lean_inc(v_startInclusive_3218_);
lean_inc_ref(v_str_3217_);
v_isSharedCheck_3237_ = !lean_is_exclusive(v_s_3216_);
if (v_isSharedCheck_3237_ == 0)
{
lean_object* v_unused_3238_; lean_object* v_unused_3239_; lean_object* v_unused_3240_; 
v_unused_3238_ = lean_ctor_get(v_s_3216_, 2);
lean_dec(v_unused_3238_);
v_unused_3239_ = lean_ctor_get(v_s_3216_, 1);
lean_dec(v_unused_3239_);
v_unused_3240_ = lean_ctor_get(v_s_3216_, 0);
lean_dec(v_unused_3240_);
v___x_3228_ = v_s_3216_;
v_isShared_3229_ = v_isSharedCheck_3237_;
goto v_resetjp_3227_;
}
else
{
lean_dec(v_s_3216_);
v___x_3228_ = lean_box(0);
v_isShared_3229_ = v_isSharedCheck_3237_;
goto v_resetjp_3227_;
}
v_resetjp_3227_:
{
lean_object* v___x_3230_; lean_object* v___x_3231_; lean_object* v___x_3232_; lean_object* v___x_3234_; 
v___x_3230_ = lean_string_utf8_next_fast(v_str_3217_, v_startInclusive_3218_);
v___x_3231_ = lean_nat_sub(v___x_3230_, v_startInclusive_3218_);
v___x_3232_ = lean_nat_add(v_startInclusive_3218_, v___x_3231_);
lean_dec(v___x_3231_);
lean_dec(v_startInclusive_3218_);
if (v_isShared_3229_ == 0)
{
lean_ctor_set(v___x_3228_, 1, v___x_3232_);
v___x_3234_ = v___x_3228_;
goto v_reusejp_3233_;
}
else
{
lean_object* v_reuseFailAlloc_3236_; 
v_reuseFailAlloc_3236_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3236_, 0, v_str_3217_);
lean_ctor_set(v_reuseFailAlloc_3236_, 1, v___x_3232_);
lean_ctor_set(v_reuseFailAlloc_3236_, 2, v_endExclusive_3219_);
v___x_3234_ = v_reuseFailAlloc_3236_;
goto v_reusejp_3233_;
}
v_reusejp_3233_:
{
uint8_t v___x_3235_; 
v___x_3235_ = l_String_Slice_isNat(v___x_3234_);
lean_dec_ref(v___x_3234_);
return v___x_3235_;
}
}
}
}
else
{
uint8_t v___x_3241_; 
v___x_3241_ = l_String_Slice_isNat(v_s_3216_);
lean_dec_ref(v_s_3216_);
return v___x_3241_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object* v_s_3242_){
_start:
{
uint8_t v_res_3243_; lean_object* v_r_3244_; 
v_res_3243_ = l_String_Slice_isInt(v_s_3242_);
v_r_3244_ = lean_box(v_res_3243_);
return v_r_3244_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x3f(lean_object* v_s_3245_){
_start:
{
lean_object* v_str_3258_; lean_object* v_startInclusive_3259_; lean_object* v_endExclusive_3260_; lean_object* v___x_3261_; lean_object* v___x_3262_; uint8_t v___x_3263_; 
v_str_3258_ = lean_ctor_get(v_s_3245_, 0);
v_startInclusive_3259_ = lean_ctor_get(v_s_3245_, 1);
v_endExclusive_3260_ = lean_ctor_get(v_s_3245_, 2);
v___x_3261_ = lean_unsigned_to_nat(0u);
v___x_3262_ = lean_nat_sub(v_endExclusive_3260_, v_startInclusive_3259_);
v___x_3263_ = lean_nat_dec_eq(v___x_3261_, v___x_3262_);
lean_dec(v___x_3262_);
if (v___x_3263_ == 0)
{
uint32_t v___x_3264_; uint32_t v___x_3265_; uint8_t v___x_3266_; 
v___x_3264_ = 45;
v___x_3265_ = lean_string_utf8_get_fast(v_str_3258_, v_startInclusive_3259_);
v___x_3266_ = lean_uint32_dec_eq(v___x_3265_, v___x_3264_);
if (v___x_3266_ == 0)
{
goto v___jp_3246_;
}
else
{
lean_object* v___x_3268_; uint8_t v_isShared_3269_; uint8_t v_isSharedCheck_3287_; 
lean_inc(v_endExclusive_3260_);
lean_inc(v_startInclusive_3259_);
lean_inc_ref(v_str_3258_);
v_isSharedCheck_3287_ = !lean_is_exclusive(v_s_3245_);
if (v_isSharedCheck_3287_ == 0)
{
lean_object* v_unused_3288_; lean_object* v_unused_3289_; lean_object* v_unused_3290_; 
v_unused_3288_ = lean_ctor_get(v_s_3245_, 2);
lean_dec(v_unused_3288_);
v_unused_3289_ = lean_ctor_get(v_s_3245_, 1);
lean_dec(v_unused_3289_);
v_unused_3290_ = lean_ctor_get(v_s_3245_, 0);
lean_dec(v_unused_3290_);
v___x_3268_ = v_s_3245_;
v_isShared_3269_ = v_isSharedCheck_3287_;
goto v_resetjp_3267_;
}
else
{
lean_dec(v_s_3245_);
v___x_3268_ = lean_box(0);
v_isShared_3269_ = v_isSharedCheck_3287_;
goto v_resetjp_3267_;
}
v_resetjp_3267_:
{
lean_object* v___x_3270_; lean_object* v___x_3271_; lean_object* v___x_3272_; lean_object* v___x_3274_; 
v___x_3270_ = lean_string_utf8_next_fast(v_str_3258_, v_startInclusive_3259_);
v___x_3271_ = lean_nat_sub(v___x_3270_, v_startInclusive_3259_);
v___x_3272_ = lean_nat_add(v_startInclusive_3259_, v___x_3271_);
lean_dec(v___x_3271_);
lean_dec(v_startInclusive_3259_);
if (v_isShared_3269_ == 0)
{
lean_ctor_set(v___x_3268_, 1, v___x_3272_);
v___x_3274_ = v___x_3268_;
goto v_reusejp_3273_;
}
else
{
lean_object* v_reuseFailAlloc_3286_; 
v_reuseFailAlloc_3286_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3286_, 0, v_str_3258_);
lean_ctor_set(v_reuseFailAlloc_3286_, 1, v___x_3272_);
lean_ctor_set(v_reuseFailAlloc_3286_, 2, v_endExclusive_3260_);
v___x_3274_ = v_reuseFailAlloc_3286_;
goto v_reusejp_3273_;
}
v_reusejp_3273_:
{
lean_object* v___x_3275_; 
v___x_3275_ = l_String_Slice_toNat_x3f(v___x_3274_);
lean_dec_ref(v___x_3274_);
if (lean_obj_tag(v___x_3275_) == 0)
{
lean_object* v___x_3276_; 
v___x_3276_ = lean_box(0);
return v___x_3276_;
}
else
{
lean_object* v_val_3277_; lean_object* v___x_3279_; uint8_t v_isShared_3280_; uint8_t v_isSharedCheck_3285_; 
v_val_3277_ = lean_ctor_get(v___x_3275_, 0);
v_isSharedCheck_3285_ = !lean_is_exclusive(v___x_3275_);
if (v_isSharedCheck_3285_ == 0)
{
v___x_3279_ = v___x_3275_;
v_isShared_3280_ = v_isSharedCheck_3285_;
goto v_resetjp_3278_;
}
else
{
lean_inc(v_val_3277_);
lean_dec(v___x_3275_);
v___x_3279_ = lean_box(0);
v_isShared_3280_ = v_isSharedCheck_3285_;
goto v_resetjp_3278_;
}
v_resetjp_3278_:
{
lean_object* v___x_3281_; lean_object* v___x_3283_; 
v___x_3281_ = l_Int_negOfNat(v_val_3277_);
lean_dec(v_val_3277_);
if (v_isShared_3280_ == 0)
{
lean_ctor_set(v___x_3279_, 0, v___x_3281_);
v___x_3283_ = v___x_3279_;
goto v_reusejp_3282_;
}
else
{
lean_object* v_reuseFailAlloc_3284_; 
v_reuseFailAlloc_3284_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3284_, 0, v___x_3281_);
v___x_3283_ = v_reuseFailAlloc_3284_;
goto v_reusejp_3282_;
}
v_reusejp_3282_:
{
return v___x_3283_;
}
}
}
}
}
}
}
else
{
goto v___jp_3246_;
}
v___jp_3246_:
{
lean_object* v___x_3247_; 
v___x_3247_ = l_String_Slice_toNat_x3f(v_s_3245_);
lean_dec_ref(v_s_3245_);
if (lean_obj_tag(v___x_3247_) == 0)
{
lean_object* v___x_3248_; 
v___x_3248_ = lean_box(0);
return v___x_3248_;
}
else
{
lean_object* v_val_3249_; lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3257_; 
v_val_3249_ = lean_ctor_get(v___x_3247_, 0);
v_isSharedCheck_3257_ = !lean_is_exclusive(v___x_3247_);
if (v_isSharedCheck_3257_ == 0)
{
v___x_3251_ = v___x_3247_;
v_isShared_3252_ = v_isSharedCheck_3257_;
goto v_resetjp_3250_;
}
else
{
lean_inc(v_val_3249_);
lean_dec(v___x_3247_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3257_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v___x_3255_; 
v___x_3253_ = lean_nat_to_int(v_val_3249_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 0, v___x_3253_);
v___x_3255_ = v___x_3251_;
goto v_reusejp_3254_;
}
else
{
lean_object* v_reuseFailAlloc_3256_; 
v_reuseFailAlloc_3256_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3256_, 0, v___x_3253_);
v___x_3255_ = v_reuseFailAlloc_3256_;
goto v_reusejp_3254_;
}
v_reusejp_3254_:
{
return v___x_3255_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x21(lean_object* v_s_3292_){
_start:
{
lean_object* v___x_3293_; 
v___x_3293_ = l_String_Slice_toInt_x3f(v_s_3292_);
if (lean_obj_tag(v___x_3293_) == 0)
{
lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3296_; 
v___x_3294_ = l_Int_instInhabited;
v___x_3295_ = ((lean_object*)(l_String_Slice_toInt_x21___closed__0));
v___x_3296_ = l_panic___redArg(v___x_3294_, v___x_3295_);
return v___x_3296_;
}
else
{
lean_object* v_val_3297_; 
v_val_3297_ = lean_ctor_get(v___x_3293_, 0);
lean_inc(v_val_3297_);
lean_dec_ref_known(v___x_3293_, 1);
return v_val_3297_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object* v_s_3298_){
_start:
{
lean_object* v_startInclusive_3299_; lean_object* v_endExclusive_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_startInclusive_3299_ = lean_ctor_get(v_s_3298_, 1);
v_endExclusive_3300_ = lean_ctor_get(v_s_3298_, 2);
v___x_3301_ = lean_nat_sub(v_endExclusive_3300_, v_startInclusive_3299_);
v___x_3302_ = l_String_Slice_Pos_prev_x3f(v_s_3298_, v___x_3301_);
lean_dec(v___x_3301_);
if (lean_obj_tag(v___x_3302_) == 0)
{
lean_object* v___x_3303_; 
v___x_3303_ = lean_box(0);
return v___x_3303_;
}
else
{
lean_object* v_val_3304_; lean_object* v___x_3305_; 
v_val_3304_ = lean_ctor_get(v___x_3302_, 0);
lean_inc(v_val_3304_);
lean_dec_ref_known(v___x_3302_, 1);
v___x_3305_ = l_String_Slice_Pos_get_x3f(v_s_3298_, v_val_3304_);
lean_dec(v_val_3304_);
return v___x_3305_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object* v_s_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l_String_Slice_back_x3f(v_s_3306_);
lean_dec_ref(v_s_3306_);
return v_res_3307_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_back(lean_object* v_s_3308_){
_start:
{
lean_object* v_startInclusive_3309_; lean_object* v_endExclusive_3310_; lean_object* v___x_3311_; lean_object* v___x_3312_; 
v_startInclusive_3309_ = lean_ctor_get(v_s_3308_, 1);
v_endExclusive_3310_ = lean_ctor_get(v_s_3308_, 2);
v___x_3311_ = lean_nat_sub(v_endExclusive_3310_, v_startInclusive_3309_);
v___x_3312_ = l_String_Slice_Pos_prev_x3f(v_s_3308_, v___x_3311_);
lean_dec(v___x_3311_);
if (lean_obj_tag(v___x_3312_) == 0)
{
uint32_t v___x_3313_; 
v___x_3313_ = 65;
return v___x_3313_;
}
else
{
lean_object* v_val_3314_; lean_object* v___x_3315_; 
v_val_3314_ = lean_ctor_get(v___x_3312_, 0);
lean_inc(v_val_3314_);
lean_dec_ref_known(v___x_3312_, 1);
v___x_3315_ = l_String_Slice_Pos_get_x3f(v_s_3308_, v_val_3314_);
lean_dec(v_val_3314_);
if (lean_obj_tag(v___x_3315_) == 0)
{
uint32_t v___x_3316_; 
v___x_3316_ = 65;
return v___x_3316_;
}
else
{
lean_object* v_val_3317_; uint32_t v___x_3318_; 
v_val_3317_ = lean_ctor_get(v___x_3315_, 0);
lean_inc(v_val_3317_);
lean_dec_ref_known(v___x_3315_, 1);
v___x_3318_ = lean_unbox_uint32(v_val_3317_);
lean_dec(v_val_3317_);
return v___x_3318_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object* v_s_3319_){
_start:
{
uint32_t v_res_3320_; lean_object* v_r_3321_; 
v_res_3320_ = l_String_Slice_back(v_s_3319_);
lean_dec_ref(v_s_3319_);
v_r_3321_ = lean_box_uint32(v_res_3320_);
return v_r_3321_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(lean_object* v_acc_3322_, lean_object* v_s_3323_, lean_object* v_a_3324_){
_start:
{
if (lean_obj_tag(v_a_3324_) == 0)
{
return v_acc_3322_;
}
else
{
lean_object* v_head_3325_; lean_object* v_tail_3326_; lean_object* v_str_3327_; lean_object* v_startInclusive_3328_; lean_object* v_endExclusive_3329_; lean_object* v_str_3330_; lean_object* v_startInclusive_3331_; lean_object* v_endExclusive_3332_; lean_object* v___x_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; lean_object* v___x_3336_; 
v_head_3325_ = lean_ctor_get(v_a_3324_, 0);
v_tail_3326_ = lean_ctor_get(v_a_3324_, 1);
v_str_3327_ = lean_ctor_get(v_s_3323_, 0);
v_startInclusive_3328_ = lean_ctor_get(v_s_3323_, 1);
v_endExclusive_3329_ = lean_ctor_get(v_s_3323_, 2);
v_str_3330_ = lean_ctor_get(v_head_3325_, 0);
v_startInclusive_3331_ = lean_ctor_get(v_head_3325_, 1);
v_endExclusive_3332_ = lean_ctor_get(v_head_3325_, 2);
v___x_3333_ = lean_string_utf8_extract(v_str_3327_, v_startInclusive_3328_, v_endExclusive_3329_);
v___x_3334_ = lean_string_append(v_acc_3322_, v___x_3333_);
lean_dec_ref(v___x_3333_);
v___x_3335_ = lean_string_utf8_extract(v_str_3330_, v_startInclusive_3331_, v_endExclusive_3332_);
v___x_3336_ = lean_string_append(v___x_3334_, v___x_3335_);
lean_dec_ref(v___x_3335_);
v_acc_3322_ = v___x_3336_;
v_a_3324_ = v_tail_3326_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go___boxed(lean_object* v_acc_3338_, lean_object* v_s_3339_, lean_object* v_a_3340_){
_start:
{
lean_object* v_res_3341_; 
v_res_3341_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v_acc_3338_, v_s_3339_, v_a_3340_);
lean_dec(v_a_3340_);
lean_dec_ref(v_s_3339_);
return v_res_3341_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object* v_s_3342_, lean_object* v_x_3343_){
_start:
{
if (lean_obj_tag(v_x_3343_) == 0)
{
lean_object* v___x_3344_; 
v___x_3344_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
return v___x_3344_;
}
else
{
lean_object* v_head_3345_; lean_object* v_tail_3346_; lean_object* v_str_3347_; lean_object* v_startInclusive_3348_; lean_object* v_endExclusive_3349_; lean_object* v___x_3350_; lean_object* v___x_3351_; 
v_head_3345_ = lean_ctor_get(v_x_3343_, 0);
v_tail_3346_ = lean_ctor_get(v_x_3343_, 1);
v_str_3347_ = lean_ctor_get(v_head_3345_, 0);
v_startInclusive_3348_ = lean_ctor_get(v_head_3345_, 1);
v_endExclusive_3349_ = lean_ctor_get(v_head_3345_, 2);
v___x_3350_ = lean_string_utf8_extract(v_str_3347_, v_startInclusive_3348_, v_endExclusive_3349_);
v___x_3351_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v___x_3350_, v_s_3342_, v_tail_3346_);
return v___x_3351_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object* v_s_3352_, lean_object* v_x_3353_){
_start:
{
lean_object* v_res_3354_; 
v_res_3354_ = l_String_Slice_intercalate(v_s_3352_, v_x_3353_);
lean_dec(v_x_3353_);
lean_dec_ref(v_s_3352_);
return v_res_3354_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0(lean_object* v_x_3355_, lean_object* v_x_3356_){
_start:
{
if (lean_obj_tag(v_x_3356_) == 0)
{
return v_x_3355_;
}
else
{
lean_object* v_head_3357_; lean_object* v_tail_3358_; lean_object* v_str_3359_; lean_object* v_startInclusive_3360_; lean_object* v_endExclusive_3361_; lean_object* v___x_3362_; lean_object* v___x_3363_; 
v_head_3357_ = lean_ctor_get(v_x_3356_, 0);
v_tail_3358_ = lean_ctor_get(v_x_3356_, 1);
v_str_3359_ = lean_ctor_get(v_head_3357_, 0);
v_startInclusive_3360_ = lean_ctor_get(v_head_3357_, 1);
v_endExclusive_3361_ = lean_ctor_get(v_head_3357_, 2);
v___x_3362_ = lean_string_utf8_extract(v_str_3359_, v_startInclusive_3360_, v_endExclusive_3361_);
v___x_3363_ = lean_string_append(v_x_3355_, v___x_3362_);
lean_dec_ref(v___x_3362_);
v_x_3355_ = v___x_3363_;
v_x_3356_ = v_tail_3358_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0___boxed(lean_object* v_x_3365_, lean_object* v_x_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l_List_foldl___at___00String_Slice_join_spec__0(v_x_3365_, v_x_3366_);
lean_dec(v_x_3366_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join(lean_object* v_l_3368_){
_start:
{
lean_object* v___x_3369_; lean_object* v___x_3370_; 
v___x_3369_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
v___x_3370_ = l_List_foldl___at___00String_Slice_join_spec__0(v___x_3369_, v_l_3368_);
return v___x_3370_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join___boxed(lean_object* v_l_3371_){
_start:
{
lean_object* v_res_3372_; 
v_res_3372_ = l_String_Slice_join(v_l_3371_);
lean_dec(v_l_3371_);
return v_res_3372_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object* v_s_3373_){
_start:
{
lean_object* v___x_3374_; lean_object* v___x_3375_; 
v___x_3374_ = l_String_Slice_toString(v_s_3373_);
v___x_3375_ = l_String_toName(v___x_3374_);
return v___x_3375_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object* v_s_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_String_Slice_toName(v_s_3376_);
lean_dec_ref(v_s_3376_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object* v_s_3378_){
_start:
{
lean_object* v_str_3379_; lean_object* v_startInclusive_3380_; lean_object* v_endExclusive_3381_; lean_object* v___x_3382_; lean_object* v___x_3383_; 
v_str_3379_ = lean_ctor_get(v_s_3378_, 0);
v_startInclusive_3380_ = lean_ctor_get(v_s_3378_, 1);
v_endExclusive_3381_ = lean_ctor_get(v_s_3378_, 2);
v___x_3382_ = lean_string_utf8_extract(v_str_3379_, v_startInclusive_3380_, v_endExclusive_3381_);
v___x_3383_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3383_, 0, v___x_3382_);
return v___x_3383_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object* v_s_3384_){
_start:
{
lean_object* v_res_3385_; 
v_res_3385_ = l_String_Slice_instToFormat___lam__0(v_s_3384_);
lean_dec_ref(v_s_3384_);
return v_res_3385_;
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
