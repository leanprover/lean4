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
lean_object* lean_string_utf8_extract_fast(lean_object*, lean_object*, lean_object*);
lean_object* lean_string_append(lean_object*, lean_object*);
lean_object* lean_nat_sub(lean_object*, lean_object*);
uint8_t lean_nat_dec_eq(lean_object*, lean_object*);
lean_object* lean_nat_add(lean_object*, lean_object*);
lean_object* l_WellFounded_opaqueFix_u2083___redArg(lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* l_String_Slice_subslice_x21(lean_object*, lean_object*, lean_object*);
uint8_t lean_nat_dec_le(lean_object*, lean_object*);
uint32_t lean_string_utf8_get_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_eq(uint32_t, uint32_t);
lean_object* lean_string_utf8_next_fast(lean_object*, lean_object*);
uint8_t lean_uint32_dec_le(uint32_t, uint32_t);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
uint8_t l_String_instDecidableLtRaw(lean_object*, lean_object*);
uint8_t lean_string_get_byte_fast(lean_object*, lean_object*);
uint8_t lean_uint8_sub(uint8_t, uint8_t);
uint8_t lean_uint8_dec_lt(uint8_t, uint8_t);
uint8_t lean_bool_to_uint8(uint8_t);
uint8_t lean_uint8_shift_left(uint8_t, uint8_t);
uint8_t lean_uint8_add(uint8_t, uint8_t);
uint8_t lean_uint8_dec_eq(uint8_t, uint8_t);
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
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___redArg();
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___redArg___boxed(lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___boxed(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___redArg();
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg___boxed(lean_object*);
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
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg();
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg___boxed(lean_object*);
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
v___x_6_ = lean_string_utf8_extract_fast(v_str_3_, v_startInclusive_4_, v_endExclusive_5_);
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
v___x_35_ = lean_string_utf8_extract_fast(v_str_32_, v_startInclusive_33_, v_endExclusive_34_);
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
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg(){
_start:
{
lean_object* v___x_191_; 
v___x_191_ = lean_box(1);
return v___x_191_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg___boxed(lean_object* v___dummy_192_){
_start:
{
lean_object* v_res_193_; 
v_res_193_ = l_String_Slice_instInhabitedSplitIterator_default___redArg();
return v_res_193_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default(lean_object* v_00_u03c3_194_, lean_object* v_00_u03c1_195_, lean_object* v_pat_196_, lean_object* v_s_197_, lean_object* v_inst_198_){
_start:
{
lean_object* v___x_199_; 
v___x_199_ = lean_box(1);
return v___x_199_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___boxed(lean_object* v_00_u03c3_200_, lean_object* v_00_u03c1_201_, lean_object* v_pat_202_, lean_object* v_s_203_, lean_object* v_inst_204_){
_start:
{
lean_object* v_res_205_; 
v_res_205_ = l_String_Slice_instInhabitedSplitIterator_default(v_00_u03c3_200_, v_00_u03c1_201_, v_pat_202_, v_s_203_, v_inst_204_);
lean_dec(v_inst_204_);
lean_dec_ref(v_s_203_);
lean_dec(v_pat_202_);
return v_res_205_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___redArg(){
_start:
{
lean_object* v___x_207_; 
v___x_207_ = lean_box(1);
return v___x_207_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___redArg___boxed(lean_object* v___dummy_208_){
_start:
{
lean_object* v_res_209_; 
v_res_209_ = l_String_Slice_instInhabitedSplitIterator___redArg();
return v_res_209_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator(lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_, lean_object* v_a_214_){
_start:
{
lean_object* v___x_215_; 
v___x_215_ = lean_box(1);
return v___x_215_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___boxed(lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_){
_start:
{
lean_object* v_res_221_; 
v_res_221_ = l_String_Slice_instInhabitedSplitIterator(v_a_216_, v_a_217_, v_a_218_, v_a_219_, v_a_220_);
lean_dec(v_a_220_);
lean_dec_ref(v_a_219_);
lean_dec(v_a_218_);
return v_res_221_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___redArg(){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___redArg___boxed(lean_object* v___dummy_223_){
_start:
{
lean_object* v_res_224_; 
v_res_224_ = l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___redArg();
return v_res_224_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx(uint8_t v_x_225_){
_start:
{
lean_internal_panic_unreachable();
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___boxed(lean_object* v_x_226_){
_start:
{
uint8_t v_x_boxed_227_; lean_object* v_res_228_; 
v_x_boxed_227_ = lean_unbox(v_x_226_);
v_res_228_ = l_String_Slice_SplitIterator_PlausibleStep_ctorIdx(v_x_boxed_227_);
return v_res_228_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0(lean_object* v_inst_229_, lean_object* v_s_230_, lean_object* v_x_231_){
_start:
{
if (lean_obj_tag(v_x_231_) == 0)
{
lean_object* v_currPos_232_; lean_object* v_searcher_233_; lean_object* v___x_235_; uint8_t v_isShared_236_; uint8_t v_isSharedCheck_276_; 
v_currPos_232_ = lean_ctor_get(v_x_231_, 0);
v_searcher_233_ = lean_ctor_get(v_x_231_, 1);
v_isSharedCheck_276_ = !lean_is_exclusive(v_x_231_);
if (v_isSharedCheck_276_ == 0)
{
v___x_235_ = v_x_231_;
v_isShared_236_ = v_isSharedCheck_276_;
goto v_resetjp_234_;
}
else
{
lean_inc(v_searcher_233_);
lean_inc(v_currPos_232_);
lean_dec(v_x_231_);
v___x_235_ = lean_box(0);
v_isShared_236_ = v_isSharedCheck_276_;
goto v_resetjp_234_;
}
v_resetjp_234_:
{
lean_object* v___x_237_; 
lean_inc_ref(v_s_230_);
v___x_237_ = lean_apply_2(v_inst_229_, v_s_230_, v_searcher_233_);
switch(lean_obj_tag(v___x_237_))
{
case 0:
{
lean_object* v_out_238_; 
v_out_238_ = lean_ctor_get(v___x_237_, 1);
lean_inc(v_out_238_);
if (lean_obj_tag(v_out_238_) == 0)
{
lean_object* v_it_239_; lean_object* v___x_241_; 
lean_dec_ref_known(v_out_238_, 2);
lean_dec_ref(v_s_230_);
v_it_239_ = lean_ctor_get(v___x_237_, 0);
lean_inc(v_it_239_);
lean_dec_ref_known(v___x_237_, 2);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_it_239_);
v___x_241_ = v___x_235_;
goto v_reusejp_240_;
}
else
{
lean_object* v_reuseFailAlloc_243_; 
v_reuseFailAlloc_243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_243_, 0, v_currPos_232_);
lean_ctor_set(v_reuseFailAlloc_243_, 1, v_it_239_);
v___x_241_ = v_reuseFailAlloc_243_;
goto v_reusejp_240_;
}
v_reusejp_240_:
{
lean_object* v___x_242_; 
v___x_242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_242_, 0, v___x_241_);
return v___x_242_;
}
}
else
{
lean_object* v_it_244_; lean_object* v___x_246_; uint8_t v_isShared_247_; uint8_t v_isSharedCheck_257_; 
v_it_244_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_257_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_257_ == 0)
{
lean_object* v_unused_258_; 
v_unused_258_ = lean_ctor_get(v___x_237_, 1);
lean_dec(v_unused_258_);
v___x_246_ = v___x_237_;
v_isShared_247_ = v_isSharedCheck_257_;
goto v_resetjp_245_;
}
else
{
lean_inc(v_it_244_);
lean_dec(v___x_237_);
v___x_246_ = lean_box(0);
v_isShared_247_ = v_isSharedCheck_257_;
goto v_resetjp_245_;
}
v_resetjp_245_:
{
lean_object* v_startPos_248_; lean_object* v_endPos_249_; lean_object* v_slice_250_; lean_object* v_nextIt_252_; 
v_startPos_248_ = lean_ctor_get(v_out_238_, 0);
lean_inc(v_startPos_248_);
v_endPos_249_ = lean_ctor_get(v_out_238_, 1);
lean_inc(v_endPos_249_);
lean_dec_ref_known(v_out_238_, 2);
v_slice_250_ = l_String_Slice_subslice_x21(v_s_230_, v_currPos_232_, v_startPos_248_);
lean_dec_ref(v_s_230_);
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_it_244_);
lean_ctor_set(v___x_235_, 0, v_endPos_249_);
v_nextIt_252_ = v___x_235_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_256_; 
v_reuseFailAlloc_256_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_256_, 0, v_endPos_249_);
lean_ctor_set(v_reuseFailAlloc_256_, 1, v_it_244_);
v_nextIt_252_ = v_reuseFailAlloc_256_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
lean_object* v___x_254_; 
if (v_isShared_247_ == 0)
{
lean_ctor_set(v___x_246_, 1, v_slice_250_);
lean_ctor_set(v___x_246_, 0, v_nextIt_252_);
v___x_254_ = v___x_246_;
goto v_reusejp_253_;
}
else
{
lean_object* v_reuseFailAlloc_255_; 
v_reuseFailAlloc_255_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_255_, 0, v_nextIt_252_);
lean_ctor_set(v_reuseFailAlloc_255_, 1, v_slice_250_);
v___x_254_ = v_reuseFailAlloc_255_;
goto v_reusejp_253_;
}
v_reusejp_253_:
{
return v___x_254_;
}
}
}
}
}
case 1:
{
lean_object* v_it_259_; lean_object* v___x_261_; uint8_t v_isShared_262_; uint8_t v_isSharedCheck_269_; 
lean_dec_ref(v_s_230_);
v_it_259_ = lean_ctor_get(v___x_237_, 0);
v_isSharedCheck_269_ = !lean_is_exclusive(v___x_237_);
if (v_isSharedCheck_269_ == 0)
{
v___x_261_ = v___x_237_;
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
else
{
lean_inc(v_it_259_);
lean_dec(v___x_237_);
v___x_261_ = lean_box(0);
v_isShared_262_ = v_isSharedCheck_269_;
goto v_resetjp_260_;
}
v_resetjp_260_:
{
lean_object* v___x_264_; 
if (v_isShared_236_ == 0)
{
lean_ctor_set(v___x_235_, 1, v_it_259_);
v___x_264_ = v___x_235_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_268_; 
v_reuseFailAlloc_268_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_268_, 0, v_currPos_232_);
lean_ctor_set(v_reuseFailAlloc_268_, 1, v_it_259_);
v___x_264_ = v_reuseFailAlloc_268_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
lean_object* v___x_266_; 
if (v_isShared_262_ == 0)
{
lean_ctor_set(v___x_261_, 0, v___x_264_);
v___x_266_ = v___x_261_;
goto v_reusejp_265_;
}
else
{
lean_object* v_reuseFailAlloc_267_; 
v_reuseFailAlloc_267_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_267_, 0, v___x_264_);
v___x_266_ = v_reuseFailAlloc_267_;
goto v_reusejp_265_;
}
v_reusejp_265_:
{
return v___x_266_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_270_; lean_object* v_endExclusive_271_; lean_object* v___x_272_; lean_object* v_slice_273_; lean_object* v___x_274_; lean_object* v___x_275_; 
lean_del_object(v___x_235_);
v_startInclusive_270_ = lean_ctor_get(v_s_230_, 1);
lean_inc(v_startInclusive_270_);
v_endExclusive_271_ = lean_ctor_get(v_s_230_, 2);
lean_inc(v_endExclusive_271_);
lean_dec_ref(v_s_230_);
v___x_272_ = lean_nat_sub(v_endExclusive_271_, v_startInclusive_270_);
lean_dec(v_startInclusive_270_);
lean_dec(v_endExclusive_271_);
v_slice_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_273_, 0, v_currPos_232_);
lean_ctor_set(v_slice_273_, 1, v___x_272_);
v___x_274_ = lean_box(1);
v___x_275_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_275_, 0, v___x_274_);
lean_ctor_set(v___x_275_, 1, v_slice_273_);
return v___x_275_;
}
}
}
}
else
{
lean_object* v___x_277_; 
lean_dec_ref(v_s_230_);
lean_dec(v_inst_229_);
v___x_277_ = lean_box(2);
return v___x_277_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg(lean_object* v_inst_278_, lean_object* v_s_279_){
_start:
{
lean_object* v___f_280_; 
v___f_280_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0), 3, 2);
lean_closure_set(v___f_280_, 0, v_inst_278_);
lean_closure_set(v___f_280_, 1, v_s_279_);
return v___f_280_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice(lean_object* v_00_u03c1_281_, lean_object* v_00_u03c3_282_, lean_object* v_inst_283_, lean_object* v_pat_284_, lean_object* v_inst_285_, lean_object* v_s_286_){
_start:
{
lean_object* v___f_287_; 
v___f_287_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0), 3, 2);
lean_closure_set(v___f_287_, 0, v_inst_283_);
lean_closure_set(v___f_287_, 1, v_s_286_);
return v___f_287_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___boxed(lean_object* v_00_u03c1_288_, lean_object* v_00_u03c3_289_, lean_object* v_inst_290_, lean_object* v_pat_291_, lean_object* v_inst_292_, lean_object* v_s_293_){
_start:
{
lean_object* v_res_294_; 
v_res_294_ = l_String_Slice_SplitIterator_instIteratorIdSubslice(v_00_u03c1_288_, v_00_u03c3_289_, v_inst_290_, v_pat_291_, v_inst_292_, v_s_293_);
lean_dec(v_inst_292_);
lean_dec(v_pat_291_);
return v_res_294_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(lean_object* v_x_295_){
_start:
{
if (lean_obj_tag(v_x_295_) == 0)
{
lean_object* v_searcher_296_; lean_object* v___x_297_; 
v_searcher_296_ = lean_ctor_get(v_x_295_, 1);
lean_inc(v_searcher_296_);
v___x_297_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_297_, 0, v_searcher_296_);
return v___x_297_;
}
else
{
lean_object* v___x_298_; 
v___x_298_ = lean_box(0);
return v___x_298_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg___boxed(lean_object* v_x_299_){
_start:
{
lean_object* v_res_300_; 
v_res_300_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(v_x_299_);
lean_dec(v_x_299_);
return v_res_300_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption(lean_object* v_00_u03c1_301_, lean_object* v_00_u03c3_302_, lean_object* v_pat_303_, lean_object* v_inst_304_, lean_object* v_s_305_, lean_object* v_x_306_){
_start:
{
lean_object* v___x_307_; 
v___x_307_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(v_x_306_);
return v___x_307_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___boxed(lean_object* v_00_u03c1_308_, lean_object* v_00_u03c3_309_, lean_object* v_pat_310_, lean_object* v_inst_311_, lean_object* v_s_312_, lean_object* v_x_313_){
_start:
{
lean_object* v_res_314_; 
v_res_314_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption(v_00_u03c1_308_, v_00_u03c3_309_, v_pat_310_, v_inst_311_, v_s_312_, v_x_313_);
lean_dec(v_x_313_);
lean_dec_ref(v_s_312_);
lean_dec(v_inst_311_);
lean_dec(v_pat_310_);
return v_res_314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___redArg(lean_object* v_x_315_, lean_object* v_h__1_316_, lean_object* v_h__2_317_){
_start:
{
if (lean_obj_tag(v_x_315_) == 0)
{
lean_object* v_currPos_318_; lean_object* v_searcher_319_; lean_object* v___x_320_; 
lean_dec(v_h__2_317_);
v_currPos_318_ = lean_ctor_get(v_x_315_, 0);
lean_inc(v_currPos_318_);
v_searcher_319_ = lean_ctor_get(v_x_315_, 1);
lean_inc(v_searcher_319_);
lean_dec_ref_known(v_x_315_, 2);
v___x_320_ = lean_apply_2(v_h__1_316_, v_currPos_318_, v_searcher_319_);
return v___x_320_;
}
else
{
lean_object* v___x_321_; lean_object* v___x_322_; 
lean_dec(v_h__1_316_);
v___x_321_ = lean_box(0);
v___x_322_ = lean_apply_1(v_h__2_317_, v___x_321_);
return v___x_322_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(lean_object* v_00_u03c1_323_, lean_object* v_00_u03c3_324_, lean_object* v_pat_325_, lean_object* v_inst_326_, lean_object* v_s_327_, lean_object* v_motive_328_, lean_object* v_x_329_, lean_object* v_h__1_330_, lean_object* v_h__2_331_){
_start:
{
if (lean_obj_tag(v_x_329_) == 0)
{
lean_object* v_currPos_332_; lean_object* v_searcher_333_; lean_object* v___x_334_; 
lean_dec(v_h__2_331_);
v_currPos_332_ = lean_ctor_get(v_x_329_, 0);
lean_inc(v_currPos_332_);
v_searcher_333_ = lean_ctor_get(v_x_329_, 1);
lean_inc(v_searcher_333_);
lean_dec_ref_known(v_x_329_, 2);
v___x_334_ = lean_apply_2(v_h__1_330_, v_currPos_332_, v_searcher_333_);
return v___x_334_;
}
else
{
lean_object* v___x_335_; lean_object* v___x_336_; 
lean_dec(v_h__1_330_);
v___x_335_ = lean_box(0);
v___x_336_ = lean_apply_1(v_h__2_331_, v___x_335_);
return v___x_336_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___boxed(lean_object* v_00_u03c1_337_, lean_object* v_00_u03c3_338_, lean_object* v_pat_339_, lean_object* v_inst_340_, lean_object* v_s_341_, lean_object* v_motive_342_, lean_object* v_x_343_, lean_object* v_h__1_344_, lean_object* v_h__2_345_){
_start:
{
lean_object* v_res_346_; 
v_res_346_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(v_00_u03c1_337_, v_00_u03c3_338_, v_pat_339_, v_inst_340_, v_s_341_, v_motive_342_, v_x_343_, v_h__1_344_, v_h__2_345_);
lean_dec_ref(v_s_341_);
lean_dec(v_inst_340_);
lean_dec(v_pat_339_);
return v_res_346_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object* v_x_347_, lean_object* v_h__1_348_, lean_object* v_h__2_349_, lean_object* v_h__3_350_, lean_object* v_h__4_351_){
_start:
{
switch(lean_obj_tag(v_x_347_))
{
case 0:
{
lean_object* v_out_352_; 
lean_dec(v_h__4_351_);
lean_dec(v_h__3_350_);
v_out_352_ = lean_ctor_get(v_x_347_, 1);
lean_inc(v_out_352_);
if (lean_obj_tag(v_out_352_) == 0)
{
lean_object* v_it_353_; lean_object* v_startPos_354_; lean_object* v_endPos_355_; lean_object* v___x_356_; 
lean_dec(v_h__1_348_);
v_it_353_ = lean_ctor_get(v_x_347_, 0);
lean_inc(v_it_353_);
lean_dec_ref_known(v_x_347_, 2);
v_startPos_354_ = lean_ctor_get(v_out_352_, 0);
lean_inc(v_startPos_354_);
v_endPos_355_ = lean_ctor_get(v_out_352_, 1);
lean_inc(v_endPos_355_);
lean_dec_ref_known(v_out_352_, 2);
v___x_356_ = lean_apply_5(v_h__2_349_, v_it_353_, v_startPos_354_, v_endPos_355_, lean_box(0), lean_box(0));
return v___x_356_;
}
else
{
lean_object* v_it_357_; lean_object* v_startPos_358_; lean_object* v_endPos_359_; lean_object* v___x_360_; 
lean_dec(v_h__2_349_);
v_it_357_ = lean_ctor_get(v_x_347_, 0);
lean_inc(v_it_357_);
lean_dec_ref_known(v_x_347_, 2);
v_startPos_358_ = lean_ctor_get(v_out_352_, 0);
lean_inc(v_startPos_358_);
v_endPos_359_ = lean_ctor_get(v_out_352_, 1);
lean_inc(v_endPos_359_);
lean_dec_ref_known(v_out_352_, 2);
v___x_360_ = lean_apply_5(v_h__1_348_, v_it_357_, v_startPos_358_, v_endPos_359_, lean_box(0), lean_box(0));
return v___x_360_;
}
}
case 1:
{
lean_object* v_it_361_; lean_object* v___x_362_; 
lean_dec(v_h__4_351_);
lean_dec(v_h__2_349_);
lean_dec(v_h__1_348_);
v_it_361_ = lean_ctor_get(v_x_347_, 0);
lean_inc(v_it_361_);
lean_dec_ref_known(v_x_347_, 1);
v___x_362_ = lean_apply_3(v_h__3_350_, v_it_361_, lean_box(0), lean_box(0));
return v___x_362_;
}
default: 
{
lean_object* v___x_363_; 
lean_dec(v_h__3_350_);
lean_dec(v_h__2_349_);
lean_dec(v_h__1_348_);
v___x_363_ = lean_apply_2(v_h__4_351_, lean_box(0), lean_box(0));
return v___x_363_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object* v_00_u03c3_364_, lean_object* v_inst_365_, lean_object* v_s_366_, lean_object* v_searcher_367_, lean_object* v_motive_368_, lean_object* v_x_369_, lean_object* v_h__1_370_, lean_object* v_h__2_371_, lean_object* v_h__3_372_, lean_object* v_h__4_373_){
_start:
{
switch(lean_obj_tag(v_x_369_))
{
case 0:
{
lean_object* v_out_374_; 
lean_dec(v_h__4_373_);
lean_dec(v_h__3_372_);
v_out_374_ = lean_ctor_get(v_x_369_, 1);
lean_inc(v_out_374_);
if (lean_obj_tag(v_out_374_) == 0)
{
lean_object* v_it_375_; lean_object* v_startPos_376_; lean_object* v_endPos_377_; lean_object* v___x_378_; 
lean_dec(v_h__1_370_);
v_it_375_ = lean_ctor_get(v_x_369_, 0);
lean_inc(v_it_375_);
lean_dec_ref_known(v_x_369_, 2);
v_startPos_376_ = lean_ctor_get(v_out_374_, 0);
lean_inc(v_startPos_376_);
v_endPos_377_ = lean_ctor_get(v_out_374_, 1);
lean_inc(v_endPos_377_);
lean_dec_ref_known(v_out_374_, 2);
v___x_378_ = lean_apply_5(v_h__2_371_, v_it_375_, v_startPos_376_, v_endPos_377_, lean_box(0), lean_box(0));
return v___x_378_;
}
else
{
lean_object* v_it_379_; lean_object* v_startPos_380_; lean_object* v_endPos_381_; lean_object* v___x_382_; 
lean_dec(v_h__2_371_);
v_it_379_ = lean_ctor_get(v_x_369_, 0);
lean_inc(v_it_379_);
lean_dec_ref_known(v_x_369_, 2);
v_startPos_380_ = lean_ctor_get(v_out_374_, 0);
lean_inc(v_startPos_380_);
v_endPos_381_ = lean_ctor_get(v_out_374_, 1);
lean_inc(v_endPos_381_);
lean_dec_ref_known(v_out_374_, 2);
v___x_382_ = lean_apply_5(v_h__1_370_, v_it_379_, v_startPos_380_, v_endPos_381_, lean_box(0), lean_box(0));
return v___x_382_;
}
}
case 1:
{
lean_object* v_it_383_; lean_object* v___x_384_; 
lean_dec(v_h__4_373_);
lean_dec(v_h__2_371_);
lean_dec(v_h__1_370_);
v_it_383_ = lean_ctor_get(v_x_369_, 0);
lean_inc(v_it_383_);
lean_dec_ref_known(v_x_369_, 1);
v___x_384_ = lean_apply_3(v_h__3_372_, v_it_383_, lean_box(0), lean_box(0));
return v___x_384_;
}
default: 
{
lean_object* v___x_385_; 
lean_dec(v_h__3_372_);
lean_dec(v_h__2_371_);
lean_dec(v_h__1_370_);
v___x_385_ = lean_apply_2(v_h__4_373_, lean_box(0), lean_box(0));
return v___x_385_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object* v_00_u03c3_386_, lean_object* v_inst_387_, lean_object* v_s_388_, lean_object* v_searcher_389_, lean_object* v_motive_390_, lean_object* v_x_391_, lean_object* v_h__1_392_, lean_object* v_h__2_393_, lean_object* v_h__3_394_, lean_object* v_h__4_395_){
_start:
{
lean_object* v_res_396_; 
v_res_396_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(v_00_u03c3_386_, v_inst_387_, v_s_388_, v_searcher_389_, v_motive_390_, v_x_391_, v_h__1_392_, v_h__2_393_, v_h__3_394_, v_h__4_395_);
lean_dec(v_searcher_389_);
lean_dec_ref(v_s_388_);
lean_dec(v_inst_387_);
return v_res_396_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___redArg(lean_object* v_x_397_, lean_object* v_x_398_, lean_object* v_h__1_399_, lean_object* v_h__2_400_, lean_object* v_h__3_401_, lean_object* v_h__4_402_, lean_object* v_h__5_403_, lean_object* v_h__6_404_, lean_object* v_h__7_405_, lean_object* v_h__8_406_){
_start:
{
if (lean_obj_tag(v_x_397_) == 0)
{
lean_dec(v_h__8_406_);
lean_dec(v_h__7_405_);
lean_dec(v_h__6_404_);
switch(lean_obj_tag(v_x_398_))
{
case 0:
{
lean_object* v_it_407_; 
lean_dec(v_h__5_403_);
lean_dec(v_h__4_402_);
lean_dec(v_h__3_401_);
v_it_407_ = lean_ctor_get(v_x_398_, 0);
if (lean_obj_tag(v_it_407_) == 0)
{
lean_object* v_currPos_408_; lean_object* v_searcher_409_; lean_object* v_out_410_; lean_object* v_currPos_411_; lean_object* v_searcher_412_; lean_object* v___x_413_; 
lean_inc_ref(v_it_407_);
lean_dec(v_h__2_400_);
v_currPos_408_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_currPos_408_);
v_searcher_409_ = lean_ctor_get(v_x_397_, 1);
lean_inc(v_searcher_409_);
lean_dec_ref_known(v_x_397_, 2);
v_out_410_ = lean_ctor_get(v_x_398_, 1);
lean_inc(v_out_410_);
lean_dec_ref_known(v_x_398_, 2);
v_currPos_411_ = lean_ctor_get(v_it_407_, 0);
lean_inc(v_currPos_411_);
v_searcher_412_ = lean_ctor_get(v_it_407_, 1);
lean_inc(v_searcher_412_);
lean_dec_ref_known(v_it_407_, 2);
v___x_413_ = lean_apply_5(v_h__1_399_, v_currPos_408_, v_searcher_409_, v_currPos_411_, v_searcher_412_, v_out_410_);
return v___x_413_;
}
else
{
lean_object* v_currPos_414_; lean_object* v_searcher_415_; lean_object* v_out_416_; lean_object* v___x_417_; 
lean_dec(v_h__1_399_);
v_currPos_414_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_currPos_414_);
v_searcher_415_ = lean_ctor_get(v_x_397_, 1);
lean_inc(v_searcher_415_);
lean_dec_ref_known(v_x_397_, 2);
v_out_416_ = lean_ctor_get(v_x_398_, 1);
lean_inc(v_out_416_);
lean_dec_ref_known(v_x_398_, 2);
v___x_417_ = lean_apply_3(v_h__2_400_, v_currPos_414_, v_searcher_415_, v_out_416_);
return v___x_417_;
}
}
case 1:
{
lean_object* v_it_418_; 
lean_dec(v_h__5_403_);
lean_dec(v_h__2_400_);
lean_dec(v_h__1_399_);
v_it_418_ = lean_ctor_get(v_x_398_, 0);
lean_inc(v_it_418_);
lean_dec_ref_known(v_x_398_, 1);
if (lean_obj_tag(v_it_418_) == 0)
{
lean_object* v_currPos_419_; lean_object* v_searcher_420_; lean_object* v_currPos_421_; lean_object* v_searcher_422_; lean_object* v___x_423_; 
lean_dec(v_h__4_402_);
v_currPos_419_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_currPos_419_);
v_searcher_420_ = lean_ctor_get(v_x_397_, 1);
lean_inc(v_searcher_420_);
lean_dec_ref_known(v_x_397_, 2);
v_currPos_421_ = lean_ctor_get(v_it_418_, 0);
lean_inc(v_currPos_421_);
v_searcher_422_ = lean_ctor_get(v_it_418_, 1);
lean_inc(v_searcher_422_);
lean_dec_ref_known(v_it_418_, 2);
v___x_423_ = lean_apply_4(v_h__3_401_, v_currPos_419_, v_searcher_420_, v_currPos_421_, v_searcher_422_);
return v___x_423_;
}
else
{
lean_object* v_currPos_424_; lean_object* v_searcher_425_; lean_object* v___x_426_; 
lean_dec(v_h__3_401_);
v_currPos_424_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_currPos_424_);
v_searcher_425_ = lean_ctor_get(v_x_397_, 1);
lean_inc(v_searcher_425_);
lean_dec_ref_known(v_x_397_, 2);
v___x_426_ = lean_apply_2(v_h__4_402_, v_currPos_424_, v_searcher_425_);
return v___x_426_;
}
}
default: 
{
lean_object* v_currPos_427_; lean_object* v_searcher_428_; lean_object* v___x_429_; 
lean_dec(v_h__4_402_);
lean_dec(v_h__3_401_);
lean_dec(v_h__2_400_);
lean_dec(v_h__1_399_);
v_currPos_427_ = lean_ctor_get(v_x_397_, 0);
lean_inc(v_currPos_427_);
v_searcher_428_ = lean_ctor_get(v_x_397_, 1);
lean_inc(v_searcher_428_);
lean_dec_ref_known(v_x_397_, 2);
v___x_429_ = lean_apply_2(v_h__5_403_, v_currPos_427_, v_searcher_428_);
return v___x_429_;
}
}
}
else
{
lean_dec(v_h__5_403_);
lean_dec(v_h__4_402_);
lean_dec(v_h__3_401_);
lean_dec(v_h__2_400_);
lean_dec(v_h__1_399_);
switch(lean_obj_tag(v_x_398_))
{
case 0:
{
lean_object* v_it_430_; lean_object* v_out_431_; lean_object* v___x_432_; 
lean_dec(v_h__8_406_);
lean_dec(v_h__7_405_);
v_it_430_ = lean_ctor_get(v_x_398_, 0);
lean_inc(v_it_430_);
v_out_431_ = lean_ctor_get(v_x_398_, 1);
lean_inc(v_out_431_);
lean_dec_ref_known(v_x_398_, 2);
v___x_432_ = lean_apply_2(v_h__6_404_, v_it_430_, v_out_431_);
return v___x_432_;
}
case 1:
{
lean_object* v_it_433_; lean_object* v___x_434_; 
lean_dec(v_h__8_406_);
lean_dec(v_h__6_404_);
v_it_433_ = lean_ctor_get(v_x_398_, 0);
lean_inc(v_it_433_);
lean_dec_ref_known(v_x_398_, 1);
v___x_434_ = lean_apply_1(v_h__7_405_, v_it_433_);
return v___x_434_;
}
default: 
{
lean_object* v___x_435_; lean_object* v___x_436_; 
lean_dec(v_h__7_405_);
lean_dec(v_h__6_404_);
v___x_435_ = lean_box(0);
v___x_436_ = lean_apply_1(v_h__8_406_, v___x_435_);
return v___x_436_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(lean_object* v_00_u03c1_437_, lean_object* v_00_u03c3_438_, lean_object* v_pat_439_, lean_object* v_inst_440_, lean_object* v_s_441_, lean_object* v_motive_442_, lean_object* v_x_443_, lean_object* v_x_444_, lean_object* v_h__1_445_, lean_object* v_h__2_446_, lean_object* v_h__3_447_, lean_object* v_h__4_448_, lean_object* v_h__5_449_, lean_object* v_h__6_450_, lean_object* v_h__7_451_, lean_object* v_h__8_452_){
_start:
{
if (lean_obj_tag(v_x_443_) == 0)
{
lean_dec(v_h__8_452_);
lean_dec(v_h__7_451_);
lean_dec(v_h__6_450_);
switch(lean_obj_tag(v_x_444_))
{
case 0:
{
lean_object* v_it_453_; 
lean_dec(v_h__5_449_);
lean_dec(v_h__4_448_);
lean_dec(v_h__3_447_);
v_it_453_ = lean_ctor_get(v_x_444_, 0);
if (lean_obj_tag(v_it_453_) == 0)
{
lean_object* v_currPos_454_; lean_object* v_searcher_455_; lean_object* v_out_456_; lean_object* v_currPos_457_; lean_object* v_searcher_458_; lean_object* v___x_459_; 
lean_inc_ref(v_it_453_);
lean_dec(v_h__2_446_);
v_currPos_454_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_currPos_454_);
v_searcher_455_ = lean_ctor_get(v_x_443_, 1);
lean_inc(v_searcher_455_);
lean_dec_ref_known(v_x_443_, 2);
v_out_456_ = lean_ctor_get(v_x_444_, 1);
lean_inc(v_out_456_);
lean_dec_ref_known(v_x_444_, 2);
v_currPos_457_ = lean_ctor_get(v_it_453_, 0);
lean_inc(v_currPos_457_);
v_searcher_458_ = lean_ctor_get(v_it_453_, 1);
lean_inc(v_searcher_458_);
lean_dec_ref_known(v_it_453_, 2);
v___x_459_ = lean_apply_5(v_h__1_445_, v_currPos_454_, v_searcher_455_, v_currPos_457_, v_searcher_458_, v_out_456_);
return v___x_459_;
}
else
{
lean_object* v_currPos_460_; lean_object* v_searcher_461_; lean_object* v_out_462_; lean_object* v___x_463_; 
lean_dec(v_h__1_445_);
v_currPos_460_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_currPos_460_);
v_searcher_461_ = lean_ctor_get(v_x_443_, 1);
lean_inc(v_searcher_461_);
lean_dec_ref_known(v_x_443_, 2);
v_out_462_ = lean_ctor_get(v_x_444_, 1);
lean_inc(v_out_462_);
lean_dec_ref_known(v_x_444_, 2);
v___x_463_ = lean_apply_3(v_h__2_446_, v_currPos_460_, v_searcher_461_, v_out_462_);
return v___x_463_;
}
}
case 1:
{
lean_object* v_it_464_; 
lean_dec(v_h__5_449_);
lean_dec(v_h__2_446_);
lean_dec(v_h__1_445_);
v_it_464_ = lean_ctor_get(v_x_444_, 0);
lean_inc(v_it_464_);
lean_dec_ref_known(v_x_444_, 1);
if (lean_obj_tag(v_it_464_) == 0)
{
lean_object* v_currPos_465_; lean_object* v_searcher_466_; lean_object* v_currPos_467_; lean_object* v_searcher_468_; lean_object* v___x_469_; 
lean_dec(v_h__4_448_);
v_currPos_465_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_currPos_465_);
v_searcher_466_ = lean_ctor_get(v_x_443_, 1);
lean_inc(v_searcher_466_);
lean_dec_ref_known(v_x_443_, 2);
v_currPos_467_ = lean_ctor_get(v_it_464_, 0);
lean_inc(v_currPos_467_);
v_searcher_468_ = lean_ctor_get(v_it_464_, 1);
lean_inc(v_searcher_468_);
lean_dec_ref_known(v_it_464_, 2);
v___x_469_ = lean_apply_4(v_h__3_447_, v_currPos_465_, v_searcher_466_, v_currPos_467_, v_searcher_468_);
return v___x_469_;
}
else
{
lean_object* v_currPos_470_; lean_object* v_searcher_471_; lean_object* v___x_472_; 
lean_dec(v_h__3_447_);
v_currPos_470_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_currPos_470_);
v_searcher_471_ = lean_ctor_get(v_x_443_, 1);
lean_inc(v_searcher_471_);
lean_dec_ref_known(v_x_443_, 2);
v___x_472_ = lean_apply_2(v_h__4_448_, v_currPos_470_, v_searcher_471_);
return v___x_472_;
}
}
default: 
{
lean_object* v_currPos_473_; lean_object* v_searcher_474_; lean_object* v___x_475_; 
lean_dec(v_h__4_448_);
lean_dec(v_h__3_447_);
lean_dec(v_h__2_446_);
lean_dec(v_h__1_445_);
v_currPos_473_ = lean_ctor_get(v_x_443_, 0);
lean_inc(v_currPos_473_);
v_searcher_474_ = lean_ctor_get(v_x_443_, 1);
lean_inc(v_searcher_474_);
lean_dec_ref_known(v_x_443_, 2);
v___x_475_ = lean_apply_2(v_h__5_449_, v_currPos_473_, v_searcher_474_);
return v___x_475_;
}
}
}
else
{
lean_dec(v_h__5_449_);
lean_dec(v_h__4_448_);
lean_dec(v_h__3_447_);
lean_dec(v_h__2_446_);
lean_dec(v_h__1_445_);
switch(lean_obj_tag(v_x_444_))
{
case 0:
{
lean_object* v_it_476_; lean_object* v_out_477_; lean_object* v___x_478_; 
lean_dec(v_h__8_452_);
lean_dec(v_h__7_451_);
v_it_476_ = lean_ctor_get(v_x_444_, 0);
lean_inc(v_it_476_);
v_out_477_ = lean_ctor_get(v_x_444_, 1);
lean_inc(v_out_477_);
lean_dec_ref_known(v_x_444_, 2);
v___x_478_ = lean_apply_2(v_h__6_450_, v_it_476_, v_out_477_);
return v___x_478_;
}
case 1:
{
lean_object* v_it_479_; lean_object* v___x_480_; 
lean_dec(v_h__8_452_);
lean_dec(v_h__6_450_);
v_it_479_ = lean_ctor_get(v_x_444_, 0);
lean_inc(v_it_479_);
lean_dec_ref_known(v_x_444_, 1);
v___x_480_ = lean_apply_1(v_h__7_451_, v_it_479_);
return v___x_480_;
}
default: 
{
lean_object* v___x_481_; lean_object* v___x_482_; 
lean_dec(v_h__7_451_);
lean_dec(v_h__6_450_);
v___x_481_ = lean_box(0);
v___x_482_ = lean_apply_1(v_h__8_452_, v___x_481_);
return v___x_482_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___boxed(lean_object* v_00_u03c1_483_, lean_object* v_00_u03c3_484_, lean_object* v_pat_485_, lean_object* v_inst_486_, lean_object* v_s_487_, lean_object* v_motive_488_, lean_object* v_x_489_, lean_object* v_x_490_, lean_object* v_h__1_491_, lean_object* v_h__2_492_, lean_object* v_h__3_493_, lean_object* v_h__4_494_, lean_object* v_h__5_495_, lean_object* v_h__6_496_, lean_object* v_h__7_497_, lean_object* v_h__8_498_){
_start:
{
lean_object* v_res_499_; 
v_res_499_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(v_00_u03c1_483_, v_00_u03c3_484_, v_pat_485_, v_inst_486_, v_s_487_, v_motive_488_, v_x_489_, v_x_490_, v_h__1_491_, v_h__2_492_, v_h__3_493_, v_h__4_494_, v_h__5_495_, v_h__6_496_, v_h__7_497_, v_h__8_498_);
lean_dec_ref(v_s_487_);
lean_dec(v_inst_486_);
lean_dec(v_pat_485_);
return v_res_499_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___redArg(lean_object* v_x_500_, lean_object* v_h__1_501_, lean_object* v_h__2_502_){
_start:
{
if (lean_obj_tag(v_x_500_) == 0)
{
lean_object* v_currPos_503_; lean_object* v_searcher_504_; lean_object* v___x_505_; 
lean_dec(v_h__2_502_);
v_currPos_503_ = lean_ctor_get(v_x_500_, 0);
lean_inc(v_currPos_503_);
v_searcher_504_ = lean_ctor_get(v_x_500_, 1);
lean_inc(v_searcher_504_);
lean_dec_ref_known(v_x_500_, 2);
v___x_505_ = lean_apply_2(v_h__1_501_, v_currPos_503_, v_searcher_504_);
return v___x_505_;
}
else
{
lean_object* v___x_506_; lean_object* v___x_507_; 
lean_dec(v_h__1_501_);
v___x_506_ = lean_box(0);
v___x_507_ = lean_apply_1(v_h__2_502_, v___x_506_);
return v___x_507_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_508_, lean_object* v_00_u03c3_509_, lean_object* v_pat_510_, lean_object* v_inst_511_, lean_object* v_s_512_, lean_object* v_motive_513_, lean_object* v_x_514_, lean_object* v_h__1_515_, lean_object* v_h__2_516_){
_start:
{
if (lean_obj_tag(v_x_514_) == 0)
{
lean_object* v_currPos_517_; lean_object* v_searcher_518_; lean_object* v___x_519_; 
lean_dec(v_h__2_516_);
v_currPos_517_ = lean_ctor_get(v_x_514_, 0);
lean_inc(v_currPos_517_);
v_searcher_518_ = lean_ctor_get(v_x_514_, 1);
lean_inc(v_searcher_518_);
lean_dec_ref_known(v_x_514_, 2);
v___x_519_ = lean_apply_2(v_h__1_515_, v_currPos_517_, v_searcher_518_);
return v___x_519_;
}
else
{
lean_object* v___x_520_; lean_object* v___x_521_; 
lean_dec(v_h__1_515_);
v___x_520_ = lean_box(0);
v___x_521_ = lean_apply_1(v_h__2_516_, v___x_520_);
return v___x_521_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_522_, lean_object* v_00_u03c3_523_, lean_object* v_pat_524_, lean_object* v_inst_525_, lean_object* v_s_526_, lean_object* v_motive_527_, lean_object* v_x_528_, lean_object* v_h__1_529_, lean_object* v_h__2_530_){
_start:
{
lean_object* v_res_531_; 
v_res_531_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter(v_00_u03c1_522_, v_00_u03c3_523_, v_pat_524_, v_inst_525_, v_s_526_, v_motive_527_, v_x_528_, v_h__1_529_, v_h__2_530_);
lean_dec_ref(v_s_526_);
lean_dec(v_inst_525_);
lean_dec(v_pat_524_);
return v_res_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_533_; 
v___x_533_ = lean_box(0);
return v___x_533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_534_){
_start:
{
lean_object* v_res_535_; 
v_res_535_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg();
return v_res_535_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(lean_object* v_00_u03c1_536_, lean_object* v_00_u03c3_537_, lean_object* v_inst_538_, lean_object* v_pat_539_, lean_object* v_inst_540_, lean_object* v_s_541_, lean_object* v_inst_542_){
_start:
{
lean_object* v___x_543_; 
v___x_543_ = lean_box(0);
return v___x_543_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_544_, lean_object* v_00_u03c3_545_, lean_object* v_inst_546_, lean_object* v_pat_547_, lean_object* v_inst_548_, lean_object* v_s_549_, lean_object* v_inst_550_){
_start:
{
lean_object* v_res_551_; 
v_res_551_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(v_00_u03c1_544_, v_00_u03c3_545_, v_inst_546_, v_pat_547_, v_inst_548_, v_s_549_, v_inst_550_);
lean_dec_ref(v_s_549_);
lean_dec(v_inst_548_);
lean_dec(v_pat_547_);
lean_dec(v_inst_546_);
return v_res_551_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0(lean_object* v_toPure_552_, lean_object* v_recur_553_, lean_object* v_it_554_, lean_object* v_____do__lift_555_){
_start:
{
if (lean_obj_tag(v_____do__lift_555_) == 0)
{
lean_object* v_a_556_; lean_object* v___x_557_; 
lean_dec(v_it_554_);
lean_dec(v_recur_553_);
v_a_556_ = lean_ctor_get(v_____do__lift_555_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v_____do__lift_555_, 1);
v___x_557_ = lean_apply_2(v_toPure_552_, lean_box(0), v_a_556_);
return v___x_557_;
}
else
{
lean_object* v_a_558_; lean_object* v___x_559_; 
lean_dec(v_toPure_552_);
v_a_558_ = lean_ctor_get(v_____do__lift_555_, 0);
lean_inc(v_a_558_);
lean_dec_ref_known(v_____do__lift_555_, 1);
v___x_559_ = lean_apply_4(v_recur_553_, v_it_554_, v_a_558_, lean_box(0), lean_box(0));
return v___x_559_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1(lean_object* v_toPure_560_, lean_object* v_recur_561_, lean_object* v___y_562_, lean_object* v_acc_563_, lean_object* v_toBind_564_, lean_object* v_s_565_){
_start:
{
switch(lean_obj_tag(v_s_565_))
{
case 0:
{
lean_object* v_it_566_; lean_object* v_out_567_; lean_object* v___f_568_; lean_object* v___x_569_; lean_object* v___x_570_; 
v_it_566_ = lean_ctor_get(v_s_565_, 0);
lean_inc(v_it_566_);
v_out_567_ = lean_ctor_get(v_s_565_, 1);
lean_inc(v_out_567_);
lean_dec_ref_known(v_s_565_, 2);
v___f_568_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_568_, 0, v_toPure_560_);
lean_closure_set(v___f_568_, 1, v_recur_561_);
lean_closure_set(v___f_568_, 2, v_it_566_);
v___x_569_ = lean_apply_3(v___y_562_, v_out_567_, lean_box(0), v_acc_563_);
v___x_570_ = lean_apply_4(v_toBind_564_, lean_box(0), lean_box(0), v___x_569_, v___f_568_);
return v___x_570_;
}
case 1:
{
lean_object* v_it_571_; lean_object* v___x_572_; 
lean_dec(v_toBind_564_);
lean_dec(v___y_562_);
lean_dec(v_toPure_560_);
v_it_571_ = lean_ctor_get(v_s_565_, 0);
lean_inc(v_it_571_);
lean_dec_ref_known(v_s_565_, 1);
v___x_572_ = lean_apply_4(v_recur_561_, v_it_571_, v_acc_563_, lean_box(0), lean_box(0));
return v___x_572_;
}
default: 
{
lean_object* v___x_573_; 
lean_dec(v_toBind_564_);
lean_dec(v___y_562_);
lean_dec(v_recur_561_);
v___x_573_ = lean_apply_2(v_toPure_560_, lean_box(0), v_acc_563_);
return v___x_573_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2(lean_object* v_toPure_574_, lean_object* v___y_575_, lean_object* v_toBind_576_, lean_object* v_inst_577_, lean_object* v_s_578_, lean_object* v_lift_579_, lean_object* v_it_580_, lean_object* v_acc_581_, lean_object* v_hP_582_, lean_object* v_recur_583_){
_start:
{
lean_object* v___f_584_; 
v___f_584_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_584_, 0, v_toPure_574_);
lean_closure_set(v___f_584_, 1, v_recur_583_);
lean_closure_set(v___f_584_, 2, v___y_575_);
lean_closure_set(v___f_584_, 3, v_acc_581_);
lean_closure_set(v___f_584_, 4, v_toBind_576_);
if (lean_obj_tag(v_it_580_) == 0)
{
lean_object* v_currPos_585_; lean_object* v_searcher_586_; lean_object* v___x_588_; uint8_t v_isShared_589_; uint8_t v_isSharedCheck_633_; 
v_currPos_585_ = lean_ctor_get(v_it_580_, 0);
v_searcher_586_ = lean_ctor_get(v_it_580_, 1);
v_isSharedCheck_633_ = !lean_is_exclusive(v_it_580_);
if (v_isSharedCheck_633_ == 0)
{
v___x_588_ = v_it_580_;
v_isShared_589_ = v_isSharedCheck_633_;
goto v_resetjp_587_;
}
else
{
lean_inc(v_searcher_586_);
lean_inc(v_currPos_585_);
lean_dec(v_it_580_);
v___x_588_ = lean_box(0);
v_isShared_589_ = v_isSharedCheck_633_;
goto v_resetjp_587_;
}
v_resetjp_587_:
{
lean_object* v___x_590_; 
lean_inc_ref(v_s_578_);
v___x_590_ = lean_apply_2(v_inst_577_, v_s_578_, v_searcher_586_);
switch(lean_obj_tag(v___x_590_))
{
case 0:
{
lean_object* v_out_591_; 
v_out_591_ = lean_ctor_get(v___x_590_, 1);
lean_inc(v_out_591_);
if (lean_obj_tag(v_out_591_) == 0)
{
lean_object* v_it_592_; lean_object* v___x_594_; 
lean_dec_ref_known(v_out_591_, 2);
lean_dec_ref(v_s_578_);
v_it_592_ = lean_ctor_get(v___x_590_, 0);
lean_inc(v_it_592_);
lean_dec_ref_known(v___x_590_, 2);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v_it_592_);
v___x_594_ = v___x_588_;
goto v_reusejp_593_;
}
else
{
lean_object* v_reuseFailAlloc_597_; 
v_reuseFailAlloc_597_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_597_, 0, v_currPos_585_);
lean_ctor_set(v_reuseFailAlloc_597_, 1, v_it_592_);
v___x_594_ = v_reuseFailAlloc_597_;
goto v_reusejp_593_;
}
v_reusejp_593_:
{
lean_object* v___x_595_; lean_object* v___x_596_; 
v___x_595_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_595_, 0, v___x_594_);
v___x_596_ = lean_apply_4(v_lift_579_, lean_box(0), lean_box(0), v___f_584_, v___x_595_);
return v___x_596_;
}
}
else
{
lean_object* v_it_598_; lean_object* v___x_600_; uint8_t v_isShared_601_; uint8_t v_isSharedCheck_612_; 
v_it_598_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_612_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_612_ == 0)
{
lean_object* v_unused_613_; 
v_unused_613_ = lean_ctor_get(v___x_590_, 1);
lean_dec(v_unused_613_);
v___x_600_ = v___x_590_;
v_isShared_601_ = v_isSharedCheck_612_;
goto v_resetjp_599_;
}
else
{
lean_inc(v_it_598_);
lean_dec(v___x_590_);
v___x_600_ = lean_box(0);
v_isShared_601_ = v_isSharedCheck_612_;
goto v_resetjp_599_;
}
v_resetjp_599_:
{
lean_object* v_startPos_602_; lean_object* v_endPos_603_; lean_object* v_slice_604_; lean_object* v_nextIt_606_; 
v_startPos_602_ = lean_ctor_get(v_out_591_, 0);
lean_inc(v_startPos_602_);
v_endPos_603_ = lean_ctor_get(v_out_591_, 1);
lean_inc(v_endPos_603_);
lean_dec_ref_known(v_out_591_, 2);
v_slice_604_ = l_String_Slice_subslice_x21(v_s_578_, v_currPos_585_, v_startPos_602_);
lean_dec_ref(v_s_578_);
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v_it_598_);
lean_ctor_set(v___x_588_, 0, v_endPos_603_);
v_nextIt_606_ = v___x_588_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_611_; 
v_reuseFailAlloc_611_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_611_, 0, v_endPos_603_);
lean_ctor_set(v_reuseFailAlloc_611_, 1, v_it_598_);
v_nextIt_606_ = v_reuseFailAlloc_611_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_608_; 
if (v_isShared_601_ == 0)
{
lean_ctor_set(v___x_600_, 1, v_slice_604_);
lean_ctor_set(v___x_600_, 0, v_nextIt_606_);
v___x_608_ = v___x_600_;
goto v_reusejp_607_;
}
else
{
lean_object* v_reuseFailAlloc_610_; 
v_reuseFailAlloc_610_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_610_, 0, v_nextIt_606_);
lean_ctor_set(v_reuseFailAlloc_610_, 1, v_slice_604_);
v___x_608_ = v_reuseFailAlloc_610_;
goto v_reusejp_607_;
}
v_reusejp_607_:
{
lean_object* v___x_609_; 
v___x_609_ = lean_apply_4(v_lift_579_, lean_box(0), lean_box(0), v___f_584_, v___x_608_);
return v___x_609_;
}
}
}
}
}
case 1:
{
lean_object* v_it_614_; lean_object* v___x_616_; uint8_t v_isShared_617_; uint8_t v_isSharedCheck_625_; 
lean_dec_ref(v_s_578_);
v_it_614_ = lean_ctor_get(v___x_590_, 0);
v_isSharedCheck_625_ = !lean_is_exclusive(v___x_590_);
if (v_isSharedCheck_625_ == 0)
{
v___x_616_ = v___x_590_;
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
else
{
lean_inc(v_it_614_);
lean_dec(v___x_590_);
v___x_616_ = lean_box(0);
v_isShared_617_ = v_isSharedCheck_625_;
goto v_resetjp_615_;
}
v_resetjp_615_:
{
lean_object* v___x_619_; 
if (v_isShared_589_ == 0)
{
lean_ctor_set(v___x_588_, 1, v_it_614_);
v___x_619_ = v___x_588_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_624_; 
v_reuseFailAlloc_624_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_624_, 0, v_currPos_585_);
lean_ctor_set(v_reuseFailAlloc_624_, 1, v_it_614_);
v___x_619_ = v_reuseFailAlloc_624_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_621_; 
if (v_isShared_617_ == 0)
{
lean_ctor_set(v___x_616_, 0, v___x_619_);
v___x_621_ = v___x_616_;
goto v_reusejp_620_;
}
else
{
lean_object* v_reuseFailAlloc_623_; 
v_reuseFailAlloc_623_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_623_, 0, v___x_619_);
v___x_621_ = v_reuseFailAlloc_623_;
goto v_reusejp_620_;
}
v_reusejp_620_:
{
lean_object* v___x_622_; 
v___x_622_ = lean_apply_4(v_lift_579_, lean_box(0), lean_box(0), v___f_584_, v___x_621_);
return v___x_622_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_626_; lean_object* v_endExclusive_627_; lean_object* v___x_628_; lean_object* v_slice_629_; lean_object* v___x_630_; lean_object* v___x_631_; lean_object* v___x_632_; 
lean_del_object(v___x_588_);
v_startInclusive_626_ = lean_ctor_get(v_s_578_, 1);
lean_inc(v_startInclusive_626_);
v_endExclusive_627_ = lean_ctor_get(v_s_578_, 2);
lean_inc(v_endExclusive_627_);
lean_dec_ref(v_s_578_);
v___x_628_ = lean_nat_sub(v_endExclusive_627_, v_startInclusive_626_);
lean_dec(v_startInclusive_626_);
lean_dec(v_endExclusive_627_);
v_slice_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_629_, 0, v_currPos_585_);
lean_ctor_set(v_slice_629_, 1, v___x_628_);
v___x_630_ = lean_box(1);
v___x_631_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_631_, 0, v___x_630_);
lean_ctor_set(v___x_631_, 1, v_slice_629_);
v___x_632_ = lean_apply_4(v_lift_579_, lean_box(0), lean_box(0), v___f_584_, v___x_631_);
return v___x_632_;
}
}
}
}
else
{
lean_object* v___x_634_; lean_object* v___x_635_; 
lean_dec_ref(v_s_578_);
lean_dec(v_inst_577_);
v___x_634_ = lean_box(2);
v___x_635_ = lean_apply_4(v_lift_579_, lean_box(0), lean_box(0), v___f_584_, v___x_634_);
return v___x_635_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3(lean_object* v_inst_636_, lean_object* v_inst_637_, lean_object* v_s_638_, lean_object* v_lift_639_, lean_object* v_00_u03b3_640_, lean_object* v_Pl_641_, lean_object* v_it_642_, lean_object* v_init_643_, lean_object* v___y_644_){
_start:
{
lean_object* v_toApplicative_645_; lean_object* v_toBind_646_; lean_object* v_toPure_647_; lean_object* v___f_648_; lean_object* v___x_649_; 
v_toApplicative_645_ = lean_ctor_get(v_inst_636_, 0);
lean_inc_ref(v_toApplicative_645_);
v_toBind_646_ = lean_ctor_get(v_inst_636_, 1);
lean_inc(v_toBind_646_);
lean_dec_ref(v_inst_636_);
v_toPure_647_ = lean_ctor_get(v_toApplicative_645_, 1);
lean_inc(v_toPure_647_);
lean_dec_ref(v_toApplicative_645_);
v___f_648_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_648_, 0, v_toPure_647_);
lean_closure_set(v___f_648_, 1, v___y_644_);
lean_closure_set(v___f_648_, 2, v_toBind_646_);
lean_closure_set(v___f_648_, 3, v_inst_637_);
lean_closure_set(v___f_648_, 4, v_s_638_);
lean_closure_set(v___f_648_, 5, v_lift_639_);
v___x_649_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_648_, v_it_642_, v_init_643_, lean_box(0));
return v___x_649_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg(lean_object* v_inst_650_, lean_object* v_s_651_, lean_object* v_inst_652_){
_start:
{
lean_object* v___f_653_; 
v___f_653_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_653_, 0, v_inst_652_);
lean_closure_set(v___f_653_, 1, v_inst_650_);
lean_closure_set(v___f_653_, 2, v_s_651_);
return v___f_653_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(lean_object* v_00_u03c1_654_, lean_object* v_00_u03c3_655_, lean_object* v_inst_656_, lean_object* v_pat_657_, lean_object* v_inst_658_, lean_object* v_n_659_, lean_object* v_s_660_, lean_object* v_inst_661_){
_start:
{
lean_object* v___f_662_; 
v___f_662_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_662_, 0, v_inst_661_);
lean_closure_set(v___f_662_, 1, v_inst_656_);
lean_closure_set(v___f_662_, 2, v_s_660_);
return v___f_662_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___boxed(lean_object* v_00_u03c1_663_, lean_object* v_00_u03c3_664_, lean_object* v_inst_665_, lean_object* v_pat_666_, lean_object* v_inst_667_, lean_object* v_n_668_, lean_object* v_s_669_, lean_object* v_inst_670_){
_start:
{
lean_object* v_res_671_; 
v_res_671_ = l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(v_00_u03c1_663_, v_00_u03c3_664_, v_inst_665_, v_pat_666_, v_inst_667_, v_n_668_, v_s_669_, v_inst_670_);
lean_dec(v_inst_667_);
lean_dec(v_pat_666_);
return v_res_671_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___redArg(lean_object* v_s_672_, lean_object* v_inst_673_){
_start:
{
lean_object* v___x_674_; lean_object* v___x_675_; lean_object* v___x_676_; 
v___x_674_ = lean_unsigned_to_nat(0u);
v___x_675_ = lean_apply_1(v_inst_673_, v_s_672_);
v___x_676_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_676_, 0, v___x_674_);
lean_ctor_set(v___x_676_, 1, v___x_675_);
return v___x_676_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice(lean_object* v_00_u03c1_677_, lean_object* v_00_u03c3_678_, lean_object* v_s_679_, lean_object* v_pat_680_, lean_object* v_inst_681_){
_start:
{
lean_object* v___x_682_; 
v___x_682_ = l_String_Slice_splitToSubslice___redArg(v_s_679_, v_inst_681_);
return v___x_682_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___boxed(lean_object* v_00_u03c1_683_, lean_object* v_00_u03c3_684_, lean_object* v_s_685_, lean_object* v_pat_686_, lean_object* v_inst_687_){
_start:
{
lean_object* v_res_688_; 
v_res_688_ = l_String_Slice_splitToSubslice(v_00_u03c1_683_, v_00_u03c3_684_, v_s_685_, v_pat_686_, v_inst_687_);
lean_dec(v_pat_686_);
return v_res_688_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___redArg(lean_object* v_s_689_, lean_object* v_inst_690_){
_start:
{
lean_object* v___x_691_; 
v___x_691_ = l_String_Slice_splitToSubslice___redArg(v_s_689_, v_inst_690_);
return v___x_691_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split(lean_object* v_00_u03c1_692_, lean_object* v_00_u03c3_693_, lean_object* v_inst_694_, lean_object* v_s_695_, lean_object* v_pat_696_, lean_object* v_inst_697_){
_start:
{
lean_object* v___x_698_; 
v___x_698_ = l_String_Slice_splitToSubslice___redArg(v_s_695_, v_inst_697_);
return v___x_698_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___boxed(lean_object* v_00_u03c1_699_, lean_object* v_00_u03c3_700_, lean_object* v_inst_701_, lean_object* v_s_702_, lean_object* v_pat_703_, lean_object* v_inst_704_){
_start:
{
lean_object* v_res_705_; 
v_res_705_ = l_String_Slice_split(v_00_u03c1_699_, v_00_u03c3_700_, v_inst_701_, v_s_702_, v_pat_703_, v_inst_704_);
lean_dec(v_pat_703_);
lean_dec(v_inst_701_);
return v_res_705_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(lean_object* v_x_706_){
_start:
{
if (lean_obj_tag(v_x_706_) == 0)
{
lean_object* v___x_707_; 
v___x_707_ = lean_unsigned_to_nat(0u);
return v___x_707_;
}
else
{
lean_object* v___x_708_; 
v___x_708_ = lean_unsigned_to_nat(1u);
return v___x_708_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg___boxed(lean_object* v_x_709_){
_start:
{
lean_object* v_res_710_; 
v_res_710_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(v_x_709_);
lean_dec(v_x_709_);
return v_res_710_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx(lean_object* v_00_u03c3_711_, lean_object* v_00_u03c1_712_, lean_object* v_pat_713_, lean_object* v_s_714_, lean_object* v_inst_715_, lean_object* v_x_716_){
_start:
{
lean_object* v___x_717_; 
v___x_717_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___redArg(v_x_716_);
return v___x_717_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___boxed(lean_object* v_00_u03c3_718_, lean_object* v_00_u03c1_719_, lean_object* v_pat_720_, lean_object* v_s_721_, lean_object* v_inst_722_, lean_object* v_x_723_){
_start:
{
lean_object* v_res_724_; 
v_res_724_ = l_String_Slice_SplitInclusiveIterator_ctorIdx(v_00_u03c3_718_, v_00_u03c1_719_, v_pat_720_, v_s_721_, v_inst_722_, v_x_723_);
lean_dec(v_x_723_);
lean_dec(v_inst_722_);
lean_dec_ref(v_s_721_);
lean_dec(v_pat_720_);
return v_res_724_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(lean_object* v_t_725_, lean_object* v_k_726_){
_start:
{
if (lean_obj_tag(v_t_725_) == 0)
{
lean_object* v_currPos_727_; lean_object* v_searcher_728_; lean_object* v___x_729_; 
v_currPos_727_ = lean_ctor_get(v_t_725_, 0);
lean_inc(v_currPos_727_);
v_searcher_728_ = lean_ctor_get(v_t_725_, 1);
lean_inc(v_searcher_728_);
lean_dec_ref_known(v_t_725_, 2);
v___x_729_ = lean_apply_2(v_k_726_, v_currPos_727_, v_searcher_728_);
return v___x_729_;
}
else
{
return v_k_726_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim(lean_object* v_00_u03c3_730_, lean_object* v_00_u03c1_731_, lean_object* v_pat_732_, lean_object* v_s_733_, lean_object* v_inst_734_, lean_object* v_motive_735_, lean_object* v_ctorIdx_736_, lean_object* v_t_737_, lean_object* v_h_738_, lean_object* v_k_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_737_, v_k_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___boxed(lean_object* v_00_u03c3_741_, lean_object* v_00_u03c1_742_, lean_object* v_pat_743_, lean_object* v_s_744_, lean_object* v_inst_745_, lean_object* v_motive_746_, lean_object* v_ctorIdx_747_, lean_object* v_t_748_, lean_object* v_h_749_, lean_object* v_k_750_){
_start:
{
lean_object* v_res_751_; 
v_res_751_ = l_String_Slice_SplitInclusiveIterator_ctorElim(v_00_u03c3_741_, v_00_u03c1_742_, v_pat_743_, v_s_744_, v_inst_745_, v_motive_746_, v_ctorIdx_747_, v_t_748_, v_h_749_, v_k_750_);
lean_dec(v_ctorIdx_747_);
lean_dec(v_inst_745_);
lean_dec_ref(v_s_744_);
lean_dec(v_pat_743_);
return v_res_751_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___redArg(lean_object* v_t_752_, lean_object* v_operating_753_){
_start:
{
lean_object* v___x_754_; 
v___x_754_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_752_, v_operating_753_);
return v___x_754_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim(lean_object* v_00_u03c3_755_, lean_object* v_00_u03c1_756_, lean_object* v_pat_757_, lean_object* v_s_758_, lean_object* v_inst_759_, lean_object* v_motive_760_, lean_object* v_t_761_, lean_object* v_h_762_, lean_object* v_operating_763_){
_start:
{
lean_object* v___x_764_; 
v___x_764_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_761_, v_operating_763_);
return v___x_764_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___boxed(lean_object* v_00_u03c3_765_, lean_object* v_00_u03c1_766_, lean_object* v_pat_767_, lean_object* v_s_768_, lean_object* v_inst_769_, lean_object* v_motive_770_, lean_object* v_t_771_, lean_object* v_h_772_, lean_object* v_operating_773_){
_start:
{
lean_object* v_res_774_; 
v_res_774_ = l_String_Slice_SplitInclusiveIterator_operating_elim(v_00_u03c3_765_, v_00_u03c1_766_, v_pat_767_, v_s_768_, v_inst_769_, v_motive_770_, v_t_771_, v_h_772_, v_operating_773_);
lean_dec(v_inst_769_);
lean_dec_ref(v_s_768_);
lean_dec(v_pat_767_);
return v_res_774_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___redArg(lean_object* v_t_775_, lean_object* v_atEnd_776_){
_start:
{
lean_object* v___x_777_; 
v___x_777_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_775_, v_atEnd_776_);
return v___x_777_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim(lean_object* v_00_u03c3_778_, lean_object* v_00_u03c1_779_, lean_object* v_pat_780_, lean_object* v_s_781_, lean_object* v_inst_782_, lean_object* v_motive_783_, lean_object* v_t_784_, lean_object* v_h_785_, lean_object* v_atEnd_786_){
_start:
{
lean_object* v___x_787_; 
v___x_787_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_784_, v_atEnd_786_);
return v___x_787_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_788_, lean_object* v_00_u03c1_789_, lean_object* v_pat_790_, lean_object* v_s_791_, lean_object* v_inst_792_, lean_object* v_motive_793_, lean_object* v_t_794_, lean_object* v_h_795_, lean_object* v_atEnd_796_){
_start:
{
lean_object* v_res_797_; 
v_res_797_ = l_String_Slice_SplitInclusiveIterator_atEnd_elim(v_00_u03c3_788_, v_00_u03c1_789_, v_pat_790_, v_s_791_, v_inst_792_, v_motive_793_, v_t_794_, v_h_795_, v_atEnd_796_);
lean_dec(v_inst_792_);
lean_dec_ref(v_s_791_);
lean_dec(v_pat_790_);
return v_res_797_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg(){
_start:
{
lean_object* v___x_799_; 
v___x_799_ = lean_box(1);
return v___x_799_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg___boxed(lean_object* v___dummy_800_){
_start:
{
lean_object* v_res_801_; 
v_res_801_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg();
return v_res_801_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default(lean_object* v_00_u03c3_802_, lean_object* v_00_u03c1_803_, lean_object* v_pat_804_, lean_object* v_s_805_, lean_object* v_inst_806_){
_start:
{
lean_object* v___x_807_; 
v___x_807_ = lean_box(1);
return v___x_807_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___boxed(lean_object* v_00_u03c3_808_, lean_object* v_00_u03c1_809_, lean_object* v_pat_810_, lean_object* v_s_811_, lean_object* v_inst_812_){
_start:
{
lean_object* v_res_813_; 
v_res_813_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default(v_00_u03c3_808_, v_00_u03c1_809_, v_pat_810_, v_s_811_, v_inst_812_);
lean_dec(v_inst_812_);
lean_dec_ref(v_s_811_);
lean_dec(v_pat_810_);
return v_res_813_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg(){
_start:
{
lean_object* v___x_815_; 
v___x_815_ = lean_box(1);
return v___x_815_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg___boxed(lean_object* v___dummy_816_){
_start:
{
lean_object* v_res_817_; 
v_res_817_ = l_String_Slice_instInhabitedSplitInclusiveIterator___redArg();
return v_res_817_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator(lean_object* v_a_818_, lean_object* v_a_819_, lean_object* v_a_820_, lean_object* v_a_821_, lean_object* v_a_822_){
_start:
{
lean_object* v___x_823_; 
v___x_823_ = lean_box(1);
return v___x_823_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___boxed(lean_object* v_a_824_, lean_object* v_a_825_, lean_object* v_a_826_, lean_object* v_a_827_, lean_object* v_a_828_){
_start:
{
lean_object* v_res_829_; 
v_res_829_ = l_String_Slice_instInhabitedSplitInclusiveIterator(v_a_824_, v_a_825_, v_a_826_, v_a_827_, v_a_828_);
lean_dec(v_a_828_);
lean_dec_ref(v_a_827_);
lean_dec(v_a_826_);
return v_res_829_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0(lean_object* v_inst_830_, lean_object* v_s_831_, lean_object* v_x_832_){
_start:
{
if (lean_obj_tag(v_x_832_) == 0)
{
lean_object* v_currPos_833_; lean_object* v_searcher_834_; lean_object* v___x_836_; uint8_t v_isShared_837_; uint8_t v_isSharedCheck_886_; 
v_currPos_833_ = lean_ctor_get(v_x_832_, 0);
v_searcher_834_ = lean_ctor_get(v_x_832_, 1);
v_isSharedCheck_886_ = !lean_is_exclusive(v_x_832_);
if (v_isSharedCheck_886_ == 0)
{
v___x_836_ = v_x_832_;
v_isShared_837_ = v_isSharedCheck_886_;
goto v_resetjp_835_;
}
else
{
lean_inc(v_searcher_834_);
lean_inc(v_currPos_833_);
lean_dec(v_x_832_);
v___x_836_ = lean_box(0);
v_isShared_837_ = v_isSharedCheck_886_;
goto v_resetjp_835_;
}
v_resetjp_835_:
{
lean_object* v___x_838_; 
lean_inc_ref(v_s_831_);
v___x_838_ = lean_apply_2(v_inst_830_, v_s_831_, v_searcher_834_);
switch(lean_obj_tag(v___x_838_))
{
case 0:
{
lean_object* v_out_839_; 
v_out_839_ = lean_ctor_get(v___x_838_, 1);
lean_inc(v_out_839_);
if (lean_obj_tag(v_out_839_) == 0)
{
lean_object* v_it_840_; lean_object* v___x_842_; 
lean_dec_ref_known(v_out_839_, 2);
lean_dec_ref(v_s_831_);
v_it_840_ = lean_ctor_get(v___x_838_, 0);
lean_inc(v_it_840_);
lean_dec_ref_known(v___x_838_, 2);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_it_840_);
v___x_842_ = v___x_836_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_844_; 
v_reuseFailAlloc_844_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_844_, 0, v_currPos_833_);
lean_ctor_set(v_reuseFailAlloc_844_, 1, v_it_840_);
v___x_842_ = v_reuseFailAlloc_844_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_843_; 
v___x_843_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_843_, 0, v___x_842_);
return v___x_843_;
}
}
else
{
lean_object* v_it_845_; lean_object* v___x_847_; uint8_t v_isShared_848_; uint8_t v_isSharedCheck_857_; 
v_it_845_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_857_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_857_ == 0)
{
lean_object* v_unused_858_; 
v_unused_858_ = lean_ctor_get(v___x_838_, 1);
lean_dec(v_unused_858_);
v___x_847_ = v___x_838_;
v_isShared_848_ = v_isSharedCheck_857_;
goto v_resetjp_846_;
}
else
{
lean_inc(v_it_845_);
lean_dec(v___x_838_);
v___x_847_ = lean_box(0);
v_isShared_848_ = v_isSharedCheck_857_;
goto v_resetjp_846_;
}
v_resetjp_846_:
{
lean_object* v_endPos_849_; lean_object* v_slice_850_; lean_object* v_nextIt_852_; 
v_endPos_849_ = lean_ctor_get(v_out_839_, 1);
lean_inc(v_endPos_849_);
lean_dec_ref_known(v_out_839_, 2);
v_slice_850_ = l_String_Slice_slice_x21(v_s_831_, v_currPos_833_, v_endPos_849_);
lean_dec(v_currPos_833_);
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_it_845_);
lean_ctor_set(v___x_836_, 0, v_endPos_849_);
v_nextIt_852_ = v___x_836_;
goto v_reusejp_851_;
}
else
{
lean_object* v_reuseFailAlloc_856_; 
v_reuseFailAlloc_856_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_856_, 0, v_endPos_849_);
lean_ctor_set(v_reuseFailAlloc_856_, 1, v_it_845_);
v_nextIt_852_ = v_reuseFailAlloc_856_;
goto v_reusejp_851_;
}
v_reusejp_851_:
{
lean_object* v___x_854_; 
if (v_isShared_848_ == 0)
{
lean_ctor_set(v___x_847_, 1, v_slice_850_);
lean_ctor_set(v___x_847_, 0, v_nextIt_852_);
v___x_854_ = v___x_847_;
goto v_reusejp_853_;
}
else
{
lean_object* v_reuseFailAlloc_855_; 
v_reuseFailAlloc_855_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_855_, 0, v_nextIt_852_);
lean_ctor_set(v_reuseFailAlloc_855_, 1, v_slice_850_);
v___x_854_ = v_reuseFailAlloc_855_;
goto v_reusejp_853_;
}
v_reusejp_853_:
{
return v___x_854_;
}
}
}
}
}
case 1:
{
lean_object* v_it_859_; lean_object* v___x_861_; uint8_t v_isShared_862_; uint8_t v_isSharedCheck_869_; 
lean_dec_ref(v_s_831_);
v_it_859_ = lean_ctor_get(v___x_838_, 0);
v_isSharedCheck_869_ = !lean_is_exclusive(v___x_838_);
if (v_isSharedCheck_869_ == 0)
{
v___x_861_ = v___x_838_;
v_isShared_862_ = v_isSharedCheck_869_;
goto v_resetjp_860_;
}
else
{
lean_inc(v_it_859_);
lean_dec(v___x_838_);
v___x_861_ = lean_box(0);
v_isShared_862_ = v_isSharedCheck_869_;
goto v_resetjp_860_;
}
v_resetjp_860_:
{
lean_object* v___x_864_; 
if (v_isShared_837_ == 0)
{
lean_ctor_set(v___x_836_, 1, v_it_859_);
v___x_864_ = v___x_836_;
goto v_reusejp_863_;
}
else
{
lean_object* v_reuseFailAlloc_868_; 
v_reuseFailAlloc_868_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_868_, 0, v_currPos_833_);
lean_ctor_set(v_reuseFailAlloc_868_, 1, v_it_859_);
v___x_864_ = v_reuseFailAlloc_868_;
goto v_reusejp_863_;
}
v_reusejp_863_:
{
lean_object* v___x_866_; 
if (v_isShared_862_ == 0)
{
lean_ctor_set(v___x_861_, 0, v___x_864_);
v___x_866_ = v___x_861_;
goto v_reusejp_865_;
}
else
{
lean_object* v_reuseFailAlloc_867_; 
v_reuseFailAlloc_867_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_867_, 0, v___x_864_);
v___x_866_ = v_reuseFailAlloc_867_;
goto v_reusejp_865_;
}
v_reusejp_865_:
{
return v___x_866_;
}
}
}
}
default: 
{
lean_object* v_str_870_; lean_object* v_startInclusive_871_; lean_object* v_endExclusive_872_; lean_object* v___x_874_; uint8_t v_isShared_875_; uint8_t v_isSharedCheck_885_; 
lean_del_object(v___x_836_);
v_str_870_ = lean_ctor_get(v_s_831_, 0);
v_startInclusive_871_ = lean_ctor_get(v_s_831_, 1);
v_endExclusive_872_ = lean_ctor_get(v_s_831_, 2);
v_isSharedCheck_885_ = !lean_is_exclusive(v_s_831_);
if (v_isSharedCheck_885_ == 0)
{
v___x_874_ = v_s_831_;
v_isShared_875_ = v_isSharedCheck_885_;
goto v_resetjp_873_;
}
else
{
lean_inc(v_endExclusive_872_);
lean_inc(v_startInclusive_871_);
lean_inc(v_str_870_);
lean_dec(v_s_831_);
v___x_874_ = lean_box(0);
v_isShared_875_ = v_isSharedCheck_885_;
goto v_resetjp_873_;
}
v_resetjp_873_:
{
lean_object* v___x_876_; uint8_t v_decide_877_; 
v___x_876_ = lean_nat_sub(v_endExclusive_872_, v_startInclusive_871_);
v_decide_877_ = lean_nat_dec_eq(v_currPos_833_, v___x_876_);
lean_dec(v___x_876_);
if (v_decide_877_ == 0)
{
lean_object* v___x_878_; lean_object* v_slice_880_; 
v___x_878_ = lean_nat_add(v_startInclusive_871_, v_currPos_833_);
lean_dec(v_currPos_833_);
lean_dec(v_startInclusive_871_);
if (v_isShared_875_ == 0)
{
lean_ctor_set(v___x_874_, 1, v___x_878_);
v_slice_880_ = v___x_874_;
goto v_reusejp_879_;
}
else
{
lean_object* v_reuseFailAlloc_883_; 
v_reuseFailAlloc_883_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_883_, 0, v_str_870_);
lean_ctor_set(v_reuseFailAlloc_883_, 1, v___x_878_);
lean_ctor_set(v_reuseFailAlloc_883_, 2, v_endExclusive_872_);
v_slice_880_ = v_reuseFailAlloc_883_;
goto v_reusejp_879_;
}
v_reusejp_879_:
{
lean_object* v___x_881_; lean_object* v___x_882_; 
v___x_881_ = lean_box(1);
v___x_882_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_882_, 0, v___x_881_);
lean_ctor_set(v___x_882_, 1, v_slice_880_);
return v___x_882_;
}
}
else
{
lean_object* v___x_884_; 
lean_del_object(v___x_874_);
lean_dec(v_endExclusive_872_);
lean_dec(v_startInclusive_871_);
lean_dec_ref(v_str_870_);
lean_dec(v_currPos_833_);
v___x_884_ = lean_box(2);
return v___x_884_;
}
}
}
}
}
}
else
{
lean_object* v___x_887_; 
lean_dec_ref(v_s_831_);
lean_dec(v_inst_830_);
v___x_887_ = lean_box(2);
return v___x_887_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg(lean_object* v_inst_888_, lean_object* v_s_889_){
_start:
{
lean_object* v___f_890_; 
v___f_890_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_890_, 0, v_inst_888_);
lean_closure_set(v___f_890_, 1, v_s_889_);
return v___f_890_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId(lean_object* v_00_u03c1_891_, lean_object* v_00_u03c3_892_, lean_object* v_inst_893_, lean_object* v_pat_894_, lean_object* v_inst_895_, lean_object* v_s_896_){
_start:
{
lean_object* v___f_897_; 
v___f_897_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_897_, 0, v_inst_893_);
lean_closure_set(v___f_897_, 1, v_s_896_);
return v___f_897_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___boxed(lean_object* v_00_u03c1_898_, lean_object* v_00_u03c3_899_, lean_object* v_inst_900_, lean_object* v_pat_901_, lean_object* v_inst_902_, lean_object* v_s_903_){
_start:
{
lean_object* v_res_904_; 
v_res_904_ = l_String_Slice_SplitInclusiveIterator_instIteratorId(v_00_u03c1_898_, v_00_u03c3_899_, v_inst_900_, v_pat_901_, v_inst_902_, v_s_903_);
lean_dec(v_inst_902_);
lean_dec(v_pat_901_);
return v_res_904_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(lean_object* v_x_905_){
_start:
{
if (lean_obj_tag(v_x_905_) == 0)
{
lean_object* v_searcher_906_; lean_object* v___x_907_; 
v_searcher_906_ = lean_ctor_get(v_x_905_, 1);
lean_inc(v_searcher_906_);
v___x_907_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_907_, 0, v_searcher_906_);
return v___x_907_;
}
else
{
lean_object* v___x_908_; 
v___x_908_ = lean_box(0);
return v___x_908_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg___boxed(lean_object* v_x_909_){
_start:
{
lean_object* v_res_910_; 
v_res_910_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_909_);
lean_dec(v_x_909_);
return v_res_910_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(lean_object* v_00_u03c1_911_, lean_object* v_00_u03c3_912_, lean_object* v_pat_913_, lean_object* v_inst_914_, lean_object* v_s_915_, lean_object* v_x_916_){
_start:
{
lean_object* v___x_917_; 
v___x_917_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_916_);
return v___x_917_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___boxed(lean_object* v_00_u03c1_918_, lean_object* v_00_u03c3_919_, lean_object* v_pat_920_, lean_object* v_inst_921_, lean_object* v_s_922_, lean_object* v_x_923_){
_start:
{
lean_object* v_res_924_; 
v_res_924_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(v_00_u03c1_918_, v_00_u03c3_919_, v_pat_920_, v_inst_921_, v_s_922_, v_x_923_);
lean_dec(v_x_923_);
lean_dec_ref(v_s_922_);
lean_dec(v_inst_921_);
lean_dec(v_pat_920_);
return v_res_924_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___redArg(lean_object* v_x_925_, lean_object* v_h__1_926_, lean_object* v_h__2_927_){
_start:
{
if (lean_obj_tag(v_x_925_) == 0)
{
lean_object* v_currPos_928_; lean_object* v_searcher_929_; lean_object* v___x_930_; 
lean_dec(v_h__2_927_);
v_currPos_928_ = lean_ctor_get(v_x_925_, 0);
lean_inc(v_currPos_928_);
v_searcher_929_ = lean_ctor_get(v_x_925_, 1);
lean_inc(v_searcher_929_);
lean_dec_ref_known(v_x_925_, 2);
v___x_930_ = lean_apply_2(v_h__1_926_, v_currPos_928_, v_searcher_929_);
return v___x_930_;
}
else
{
lean_object* v___x_931_; lean_object* v___x_932_; 
lean_dec(v_h__1_926_);
v___x_931_ = lean_box(0);
v___x_932_ = lean_apply_1(v_h__2_927_, v___x_931_);
return v___x_932_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(lean_object* v_00_u03c1_933_, lean_object* v_00_u03c3_934_, lean_object* v_pat_935_, lean_object* v_inst_936_, lean_object* v_s_937_, lean_object* v_motive_938_, lean_object* v_x_939_, lean_object* v_h__1_940_, lean_object* v_h__2_941_){
_start:
{
if (lean_obj_tag(v_x_939_) == 0)
{
lean_object* v_currPos_942_; lean_object* v_searcher_943_; lean_object* v___x_944_; 
lean_dec(v_h__2_941_);
v_currPos_942_ = lean_ctor_get(v_x_939_, 0);
lean_inc(v_currPos_942_);
v_searcher_943_ = lean_ctor_get(v_x_939_, 1);
lean_inc(v_searcher_943_);
lean_dec_ref_known(v_x_939_, 2);
v___x_944_ = lean_apply_2(v_h__1_940_, v_currPos_942_, v_searcher_943_);
return v___x_944_;
}
else
{
lean_object* v___x_945_; lean_object* v___x_946_; 
lean_dec(v_h__1_940_);
v___x_945_ = lean_box(0);
v___x_946_ = lean_apply_1(v_h__2_941_, v___x_945_);
return v___x_946_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___boxed(lean_object* v_00_u03c1_947_, lean_object* v_00_u03c3_948_, lean_object* v_pat_949_, lean_object* v_inst_950_, lean_object* v_s_951_, lean_object* v_motive_952_, lean_object* v_x_953_, lean_object* v_h__1_954_, lean_object* v_h__2_955_){
_start:
{
lean_object* v_res_956_; 
v_res_956_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(v_00_u03c1_947_, v_00_u03c3_948_, v_pat_949_, v_inst_950_, v_s_951_, v_motive_952_, v_x_953_, v_h__1_954_, v_h__2_955_);
lean_dec_ref(v_s_951_);
lean_dec(v_inst_950_);
lean_dec(v_pat_949_);
return v_res_956_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___redArg(lean_object* v_x_957_, lean_object* v_x_958_, lean_object* v_h__1_959_, lean_object* v_h__2_960_, lean_object* v_h__3_961_, lean_object* v_h__4_962_, lean_object* v_h__5_963_, lean_object* v_h__6_964_, lean_object* v_h__7_965_, lean_object* v_h__8_966_){
_start:
{
if (lean_obj_tag(v_x_957_) == 0)
{
lean_dec(v_h__8_966_);
lean_dec(v_h__7_965_);
lean_dec(v_h__6_964_);
switch(lean_obj_tag(v_x_958_))
{
case 0:
{
lean_object* v_it_967_; 
lean_dec(v_h__5_963_);
lean_dec(v_h__4_962_);
lean_dec(v_h__3_961_);
v_it_967_ = lean_ctor_get(v_x_958_, 0);
if (lean_obj_tag(v_it_967_) == 0)
{
lean_object* v_currPos_968_; lean_object* v_searcher_969_; lean_object* v_out_970_; lean_object* v_currPos_971_; lean_object* v_searcher_972_; lean_object* v___x_973_; 
lean_inc_ref(v_it_967_);
lean_dec(v_h__2_960_);
v_currPos_968_ = lean_ctor_get(v_x_957_, 0);
lean_inc(v_currPos_968_);
v_searcher_969_ = lean_ctor_get(v_x_957_, 1);
lean_inc(v_searcher_969_);
lean_dec_ref_known(v_x_957_, 2);
v_out_970_ = lean_ctor_get(v_x_958_, 1);
lean_inc(v_out_970_);
lean_dec_ref_known(v_x_958_, 2);
v_currPos_971_ = lean_ctor_get(v_it_967_, 0);
lean_inc(v_currPos_971_);
v_searcher_972_ = lean_ctor_get(v_it_967_, 1);
lean_inc(v_searcher_972_);
lean_dec_ref_known(v_it_967_, 2);
v___x_973_ = lean_apply_5(v_h__1_959_, v_currPos_968_, v_searcher_969_, v_currPos_971_, v_searcher_972_, v_out_970_);
return v___x_973_;
}
else
{
lean_object* v_currPos_974_; lean_object* v_searcher_975_; lean_object* v_out_976_; lean_object* v___x_977_; 
lean_dec(v_h__1_959_);
v_currPos_974_ = lean_ctor_get(v_x_957_, 0);
lean_inc(v_currPos_974_);
v_searcher_975_ = lean_ctor_get(v_x_957_, 1);
lean_inc(v_searcher_975_);
lean_dec_ref_known(v_x_957_, 2);
v_out_976_ = lean_ctor_get(v_x_958_, 1);
lean_inc(v_out_976_);
lean_dec_ref_known(v_x_958_, 2);
v___x_977_ = lean_apply_3(v_h__2_960_, v_currPos_974_, v_searcher_975_, v_out_976_);
return v___x_977_;
}
}
case 1:
{
lean_object* v_it_978_; 
lean_dec(v_h__5_963_);
lean_dec(v_h__2_960_);
lean_dec(v_h__1_959_);
v_it_978_ = lean_ctor_get(v_x_958_, 0);
lean_inc(v_it_978_);
lean_dec_ref_known(v_x_958_, 1);
if (lean_obj_tag(v_it_978_) == 0)
{
lean_object* v_currPos_979_; lean_object* v_searcher_980_; lean_object* v_currPos_981_; lean_object* v_searcher_982_; lean_object* v___x_983_; 
lean_dec(v_h__4_962_);
v_currPos_979_ = lean_ctor_get(v_x_957_, 0);
lean_inc(v_currPos_979_);
v_searcher_980_ = lean_ctor_get(v_x_957_, 1);
lean_inc(v_searcher_980_);
lean_dec_ref_known(v_x_957_, 2);
v_currPos_981_ = lean_ctor_get(v_it_978_, 0);
lean_inc(v_currPos_981_);
v_searcher_982_ = lean_ctor_get(v_it_978_, 1);
lean_inc(v_searcher_982_);
lean_dec_ref_known(v_it_978_, 2);
v___x_983_ = lean_apply_4(v_h__3_961_, v_currPos_979_, v_searcher_980_, v_currPos_981_, v_searcher_982_);
return v___x_983_;
}
else
{
lean_object* v_currPos_984_; lean_object* v_searcher_985_; lean_object* v___x_986_; 
lean_dec(v_h__3_961_);
v_currPos_984_ = lean_ctor_get(v_x_957_, 0);
lean_inc(v_currPos_984_);
v_searcher_985_ = lean_ctor_get(v_x_957_, 1);
lean_inc(v_searcher_985_);
lean_dec_ref_known(v_x_957_, 2);
v___x_986_ = lean_apply_2(v_h__4_962_, v_currPos_984_, v_searcher_985_);
return v___x_986_;
}
}
default: 
{
lean_object* v_currPos_987_; lean_object* v_searcher_988_; lean_object* v___x_989_; 
lean_dec(v_h__4_962_);
lean_dec(v_h__3_961_);
lean_dec(v_h__2_960_);
lean_dec(v_h__1_959_);
v_currPos_987_ = lean_ctor_get(v_x_957_, 0);
lean_inc(v_currPos_987_);
v_searcher_988_ = lean_ctor_get(v_x_957_, 1);
lean_inc(v_searcher_988_);
lean_dec_ref_known(v_x_957_, 2);
v___x_989_ = lean_apply_2(v_h__5_963_, v_currPos_987_, v_searcher_988_);
return v___x_989_;
}
}
}
else
{
lean_dec(v_h__5_963_);
lean_dec(v_h__4_962_);
lean_dec(v_h__3_961_);
lean_dec(v_h__2_960_);
lean_dec(v_h__1_959_);
switch(lean_obj_tag(v_x_958_))
{
case 0:
{
lean_object* v_it_990_; lean_object* v_out_991_; lean_object* v___x_992_; 
lean_dec(v_h__8_966_);
lean_dec(v_h__7_965_);
v_it_990_ = lean_ctor_get(v_x_958_, 0);
lean_inc(v_it_990_);
v_out_991_ = lean_ctor_get(v_x_958_, 1);
lean_inc(v_out_991_);
lean_dec_ref_known(v_x_958_, 2);
v___x_992_ = lean_apply_2(v_h__6_964_, v_it_990_, v_out_991_);
return v___x_992_;
}
case 1:
{
lean_object* v_it_993_; lean_object* v___x_994_; 
lean_dec(v_h__8_966_);
lean_dec(v_h__6_964_);
v_it_993_ = lean_ctor_get(v_x_958_, 0);
lean_inc(v_it_993_);
lean_dec_ref_known(v_x_958_, 1);
v___x_994_ = lean_apply_1(v_h__7_965_, v_it_993_);
return v___x_994_;
}
default: 
{
lean_object* v___x_995_; lean_object* v___x_996_; 
lean_dec(v_h__7_965_);
lean_dec(v_h__6_964_);
v___x_995_ = lean_box(0);
v___x_996_ = lean_apply_1(v_h__8_966_, v___x_995_);
return v___x_996_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(lean_object* v_00_u03c1_997_, lean_object* v_00_u03c3_998_, lean_object* v_pat_999_, lean_object* v_inst_1000_, lean_object* v_s_1001_, lean_object* v_motive_1002_, lean_object* v_x_1003_, lean_object* v_x_1004_, lean_object* v_h__1_1005_, lean_object* v_h__2_1006_, lean_object* v_h__3_1007_, lean_object* v_h__4_1008_, lean_object* v_h__5_1009_, lean_object* v_h__6_1010_, lean_object* v_h__7_1011_, lean_object* v_h__8_1012_){
_start:
{
if (lean_obj_tag(v_x_1003_) == 0)
{
lean_dec(v_h__8_1012_);
lean_dec(v_h__7_1011_);
lean_dec(v_h__6_1010_);
switch(lean_obj_tag(v_x_1004_))
{
case 0:
{
lean_object* v_it_1013_; 
lean_dec(v_h__5_1009_);
lean_dec(v_h__4_1008_);
lean_dec(v_h__3_1007_);
v_it_1013_ = lean_ctor_get(v_x_1004_, 0);
if (lean_obj_tag(v_it_1013_) == 0)
{
lean_object* v_currPos_1014_; lean_object* v_searcher_1015_; lean_object* v_out_1016_; lean_object* v_currPos_1017_; lean_object* v_searcher_1018_; lean_object* v___x_1019_; 
lean_inc_ref(v_it_1013_);
lean_dec(v_h__2_1006_);
v_currPos_1014_ = lean_ctor_get(v_x_1003_, 0);
lean_inc(v_currPos_1014_);
v_searcher_1015_ = lean_ctor_get(v_x_1003_, 1);
lean_inc(v_searcher_1015_);
lean_dec_ref_known(v_x_1003_, 2);
v_out_1016_ = lean_ctor_get(v_x_1004_, 1);
lean_inc(v_out_1016_);
lean_dec_ref_known(v_x_1004_, 2);
v_currPos_1017_ = lean_ctor_get(v_it_1013_, 0);
lean_inc(v_currPos_1017_);
v_searcher_1018_ = lean_ctor_get(v_it_1013_, 1);
lean_inc(v_searcher_1018_);
lean_dec_ref_known(v_it_1013_, 2);
v___x_1019_ = lean_apply_5(v_h__1_1005_, v_currPos_1014_, v_searcher_1015_, v_currPos_1017_, v_searcher_1018_, v_out_1016_);
return v___x_1019_;
}
else
{
lean_object* v_currPos_1020_; lean_object* v_searcher_1021_; lean_object* v_out_1022_; lean_object* v___x_1023_; 
lean_dec(v_h__1_1005_);
v_currPos_1020_ = lean_ctor_get(v_x_1003_, 0);
lean_inc(v_currPos_1020_);
v_searcher_1021_ = lean_ctor_get(v_x_1003_, 1);
lean_inc(v_searcher_1021_);
lean_dec_ref_known(v_x_1003_, 2);
v_out_1022_ = lean_ctor_get(v_x_1004_, 1);
lean_inc(v_out_1022_);
lean_dec_ref_known(v_x_1004_, 2);
v___x_1023_ = lean_apply_3(v_h__2_1006_, v_currPos_1020_, v_searcher_1021_, v_out_1022_);
return v___x_1023_;
}
}
case 1:
{
lean_object* v_it_1024_; 
lean_dec(v_h__5_1009_);
lean_dec(v_h__2_1006_);
lean_dec(v_h__1_1005_);
v_it_1024_ = lean_ctor_get(v_x_1004_, 0);
lean_inc(v_it_1024_);
lean_dec_ref_known(v_x_1004_, 1);
if (lean_obj_tag(v_it_1024_) == 0)
{
lean_object* v_currPos_1025_; lean_object* v_searcher_1026_; lean_object* v_currPos_1027_; lean_object* v_searcher_1028_; lean_object* v___x_1029_; 
lean_dec(v_h__4_1008_);
v_currPos_1025_ = lean_ctor_get(v_x_1003_, 0);
lean_inc(v_currPos_1025_);
v_searcher_1026_ = lean_ctor_get(v_x_1003_, 1);
lean_inc(v_searcher_1026_);
lean_dec_ref_known(v_x_1003_, 2);
v_currPos_1027_ = lean_ctor_get(v_it_1024_, 0);
lean_inc(v_currPos_1027_);
v_searcher_1028_ = lean_ctor_get(v_it_1024_, 1);
lean_inc(v_searcher_1028_);
lean_dec_ref_known(v_it_1024_, 2);
v___x_1029_ = lean_apply_4(v_h__3_1007_, v_currPos_1025_, v_searcher_1026_, v_currPos_1027_, v_searcher_1028_);
return v___x_1029_;
}
else
{
lean_object* v_currPos_1030_; lean_object* v_searcher_1031_; lean_object* v___x_1032_; 
lean_dec(v_h__3_1007_);
v_currPos_1030_ = lean_ctor_get(v_x_1003_, 0);
lean_inc(v_currPos_1030_);
v_searcher_1031_ = lean_ctor_get(v_x_1003_, 1);
lean_inc(v_searcher_1031_);
lean_dec_ref_known(v_x_1003_, 2);
v___x_1032_ = lean_apply_2(v_h__4_1008_, v_currPos_1030_, v_searcher_1031_);
return v___x_1032_;
}
}
default: 
{
lean_object* v_currPos_1033_; lean_object* v_searcher_1034_; lean_object* v___x_1035_; 
lean_dec(v_h__4_1008_);
lean_dec(v_h__3_1007_);
lean_dec(v_h__2_1006_);
lean_dec(v_h__1_1005_);
v_currPos_1033_ = lean_ctor_get(v_x_1003_, 0);
lean_inc(v_currPos_1033_);
v_searcher_1034_ = lean_ctor_get(v_x_1003_, 1);
lean_inc(v_searcher_1034_);
lean_dec_ref_known(v_x_1003_, 2);
v___x_1035_ = lean_apply_2(v_h__5_1009_, v_currPos_1033_, v_searcher_1034_);
return v___x_1035_;
}
}
}
else
{
lean_dec(v_h__5_1009_);
lean_dec(v_h__4_1008_);
lean_dec(v_h__3_1007_);
lean_dec(v_h__2_1006_);
lean_dec(v_h__1_1005_);
switch(lean_obj_tag(v_x_1004_))
{
case 0:
{
lean_object* v_it_1036_; lean_object* v_out_1037_; lean_object* v___x_1038_; 
lean_dec(v_h__8_1012_);
lean_dec(v_h__7_1011_);
v_it_1036_ = lean_ctor_get(v_x_1004_, 0);
lean_inc(v_it_1036_);
v_out_1037_ = lean_ctor_get(v_x_1004_, 1);
lean_inc(v_out_1037_);
lean_dec_ref_known(v_x_1004_, 2);
v___x_1038_ = lean_apply_2(v_h__6_1010_, v_it_1036_, v_out_1037_);
return v___x_1038_;
}
case 1:
{
lean_object* v_it_1039_; lean_object* v___x_1040_; 
lean_dec(v_h__8_1012_);
lean_dec(v_h__6_1010_);
v_it_1039_ = lean_ctor_get(v_x_1004_, 0);
lean_inc(v_it_1039_);
lean_dec_ref_known(v_x_1004_, 1);
v___x_1040_ = lean_apply_1(v_h__7_1011_, v_it_1039_);
return v___x_1040_;
}
default: 
{
lean_object* v___x_1041_; lean_object* v___x_1042_; 
lean_dec(v_h__7_1011_);
lean_dec(v_h__6_1010_);
v___x_1041_ = lean_box(0);
v___x_1042_ = lean_apply_1(v_h__8_1012_, v___x_1041_);
return v___x_1042_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___boxed(lean_object* v_00_u03c1_1043_, lean_object* v_00_u03c3_1044_, lean_object* v_pat_1045_, lean_object* v_inst_1046_, lean_object* v_s_1047_, lean_object* v_motive_1048_, lean_object* v_x_1049_, lean_object* v_x_1050_, lean_object* v_h__1_1051_, lean_object* v_h__2_1052_, lean_object* v_h__3_1053_, lean_object* v_h__4_1054_, lean_object* v_h__5_1055_, lean_object* v_h__6_1056_, lean_object* v_h__7_1057_, lean_object* v_h__8_1058_){
_start:
{
lean_object* v_res_1059_; 
v_res_1059_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(v_00_u03c1_1043_, v_00_u03c3_1044_, v_pat_1045_, v_inst_1046_, v_s_1047_, v_motive_1048_, v_x_1049_, v_x_1050_, v_h__1_1051_, v_h__2_1052_, v_h__3_1053_, v_h__4_1054_, v_h__5_1055_, v_h__6_1056_, v_h__7_1057_, v_h__8_1058_);
lean_dec_ref(v_s_1047_);
lean_dec(v_inst_1046_);
lean_dec(v_pat_1045_);
return v_res_1059_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___redArg(lean_object* v_x_1060_, lean_object* v_h__1_1061_, lean_object* v_h__2_1062_){
_start:
{
if (lean_obj_tag(v_x_1060_) == 0)
{
lean_object* v_currPos_1063_; lean_object* v_searcher_1064_; lean_object* v___x_1065_; 
lean_dec(v_h__2_1062_);
v_currPos_1063_ = lean_ctor_get(v_x_1060_, 0);
lean_inc(v_currPos_1063_);
v_searcher_1064_ = lean_ctor_get(v_x_1060_, 1);
lean_inc(v_searcher_1064_);
lean_dec_ref_known(v_x_1060_, 2);
v___x_1065_ = lean_apply_2(v_h__1_1061_, v_currPos_1063_, v_searcher_1064_);
return v___x_1065_;
}
else
{
lean_object* v___x_1066_; lean_object* v___x_1067_; 
lean_dec(v_h__1_1061_);
v___x_1066_ = lean_box(0);
v___x_1067_ = lean_apply_1(v_h__2_1062_, v___x_1066_);
return v___x_1067_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_1068_, lean_object* v_00_u03c3_1069_, lean_object* v_pat_1070_, lean_object* v_inst_1071_, lean_object* v_s_1072_, lean_object* v_motive_1073_, lean_object* v_x_1074_, lean_object* v_h__1_1075_, lean_object* v_h__2_1076_){
_start:
{
if (lean_obj_tag(v_x_1074_) == 0)
{
lean_object* v_currPos_1077_; lean_object* v_searcher_1078_; lean_object* v___x_1079_; 
lean_dec(v_h__2_1076_);
v_currPos_1077_ = lean_ctor_get(v_x_1074_, 0);
lean_inc(v_currPos_1077_);
v_searcher_1078_ = lean_ctor_get(v_x_1074_, 1);
lean_inc(v_searcher_1078_);
lean_dec_ref_known(v_x_1074_, 2);
v___x_1079_ = lean_apply_2(v_h__1_1075_, v_currPos_1077_, v_searcher_1078_);
return v___x_1079_;
}
else
{
lean_object* v___x_1080_; lean_object* v___x_1081_; 
lean_dec(v_h__1_1075_);
v___x_1080_ = lean_box(0);
v___x_1081_ = lean_apply_1(v_h__2_1076_, v___x_1080_);
return v___x_1081_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_1082_, lean_object* v_00_u03c3_1083_, lean_object* v_pat_1084_, lean_object* v_inst_1085_, lean_object* v_s_1086_, lean_object* v_motive_1087_, lean_object* v_x_1088_, lean_object* v_h__1_1089_, lean_object* v_h__2_1090_){
_start:
{
lean_object* v_res_1091_; 
v_res_1091_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(v_00_u03c1_1082_, v_00_u03c3_1083_, v_pat_1084_, v_inst_1085_, v_s_1086_, v_motive_1087_, v_x_1088_, v_h__1_1089_, v_h__2_1090_);
lean_dec_ref(v_s_1086_);
lean_dec(v_inst_1085_);
lean_dec(v_pat_1084_);
return v_res_1091_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_1093_; 
v___x_1093_ = lean_box(0);
return v___x_1093_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_1094_){
_start:
{
lean_object* v_res_1095_; 
v_res_1095_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg();
return v_res_1095_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(lean_object* v_00_u03c1_1096_, lean_object* v_00_u03c3_1097_, lean_object* v_inst_1098_, lean_object* v_pat_1099_, lean_object* v_inst_1100_, lean_object* v_s_1101_, lean_object* v_inst_1102_){
_start:
{
lean_object* v___x_1103_; 
v___x_1103_ = lean_box(0);
return v___x_1103_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_1104_, lean_object* v_00_u03c3_1105_, lean_object* v_inst_1106_, lean_object* v_pat_1107_, lean_object* v_inst_1108_, lean_object* v_s_1109_, lean_object* v_inst_1110_){
_start:
{
lean_object* v_res_1111_; 
v_res_1111_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(v_00_u03c1_1104_, v_00_u03c3_1105_, v_inst_1106_, v_pat_1107_, v_inst_1108_, v_s_1109_, v_inst_1110_);
lean_dec_ref(v_s_1109_);
lean_dec(v_inst_1108_);
lean_dec(v_pat_1107_);
lean_dec(v_inst_1106_);
return v_res_1111_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0(lean_object* v_toPure_1112_, lean_object* v_recur_1113_, lean_object* v_it_1114_, lean_object* v_____do__lift_1115_){
_start:
{
if (lean_obj_tag(v_____do__lift_1115_) == 0)
{
lean_object* v_a_1116_; lean_object* v___x_1117_; 
lean_dec(v_it_1114_);
lean_dec(v_recur_1113_);
v_a_1116_ = lean_ctor_get(v_____do__lift_1115_, 0);
lean_inc(v_a_1116_);
lean_dec_ref_known(v_____do__lift_1115_, 1);
v___x_1117_ = lean_apply_2(v_toPure_1112_, lean_box(0), v_a_1116_);
return v___x_1117_;
}
else
{
lean_object* v_a_1118_; lean_object* v___x_1119_; 
lean_dec(v_toPure_1112_);
v_a_1118_ = lean_ctor_get(v_____do__lift_1115_, 0);
lean_inc(v_a_1118_);
lean_dec_ref_known(v_____do__lift_1115_, 1);
v___x_1119_ = lean_apply_4(v_recur_1113_, v_it_1114_, v_a_1118_, lean_box(0), lean_box(0));
return v___x_1119_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1(lean_object* v_toPure_1120_, lean_object* v_recur_1121_, lean_object* v___y_1122_, lean_object* v_acc_1123_, lean_object* v_toBind_1124_, lean_object* v_s_1125_){
_start:
{
switch(lean_obj_tag(v_s_1125_))
{
case 0:
{
lean_object* v_it_1126_; lean_object* v_out_1127_; lean_object* v___f_1128_; lean_object* v___x_1129_; lean_object* v___x_1130_; 
v_it_1126_ = lean_ctor_get(v_s_1125_, 0);
lean_inc(v_it_1126_);
v_out_1127_ = lean_ctor_get(v_s_1125_, 1);
lean_inc(v_out_1127_);
lean_dec_ref_known(v_s_1125_, 2);
v___f_1128_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1128_, 0, v_toPure_1120_);
lean_closure_set(v___f_1128_, 1, v_recur_1121_);
lean_closure_set(v___f_1128_, 2, v_it_1126_);
v___x_1129_ = lean_apply_3(v___y_1122_, v_out_1127_, lean_box(0), v_acc_1123_);
v___x_1130_ = lean_apply_4(v_toBind_1124_, lean_box(0), lean_box(0), v___x_1129_, v___f_1128_);
return v___x_1130_;
}
case 1:
{
lean_object* v_it_1131_; lean_object* v___x_1132_; 
lean_dec(v_toBind_1124_);
lean_dec(v___y_1122_);
lean_dec(v_toPure_1120_);
v_it_1131_ = lean_ctor_get(v_s_1125_, 0);
lean_inc(v_it_1131_);
lean_dec_ref_known(v_s_1125_, 1);
v___x_1132_ = lean_apply_4(v_recur_1121_, v_it_1131_, v_acc_1123_, lean_box(0), lean_box(0));
return v___x_1132_;
}
default: 
{
lean_object* v___x_1133_; 
lean_dec(v_toBind_1124_);
lean_dec(v___y_1122_);
lean_dec(v_recur_1121_);
v___x_1133_ = lean_apply_2(v_toPure_1120_, lean_box(0), v_acc_1123_);
return v___x_1133_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2(lean_object* v_toPure_1134_, lean_object* v___y_1135_, lean_object* v_toBind_1136_, lean_object* v_inst_1137_, lean_object* v_s_1138_, lean_object* v_lift_1139_, lean_object* v_it_1140_, lean_object* v_acc_1141_, lean_object* v_hP_1142_, lean_object* v_recur_1143_){
_start:
{
lean_object* v___f_1144_; 
v___f_1144_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_1144_, 0, v_toPure_1134_);
lean_closure_set(v___f_1144_, 1, v_recur_1143_);
lean_closure_set(v___f_1144_, 2, v___y_1135_);
lean_closure_set(v___f_1144_, 3, v_acc_1141_);
lean_closure_set(v___f_1144_, 4, v_toBind_1136_);
if (lean_obj_tag(v_it_1140_) == 0)
{
lean_object* v_currPos_1145_; lean_object* v_searcher_1146_; lean_object* v___x_1148_; uint8_t v_isShared_1149_; uint8_t v_isSharedCheck_1203_; 
v_currPos_1145_ = lean_ctor_get(v_it_1140_, 0);
v_searcher_1146_ = lean_ctor_get(v_it_1140_, 1);
v_isSharedCheck_1203_ = !lean_is_exclusive(v_it_1140_);
if (v_isSharedCheck_1203_ == 0)
{
v___x_1148_ = v_it_1140_;
v_isShared_1149_ = v_isSharedCheck_1203_;
goto v_resetjp_1147_;
}
else
{
lean_inc(v_searcher_1146_);
lean_inc(v_currPos_1145_);
lean_dec(v_it_1140_);
v___x_1148_ = lean_box(0);
v_isShared_1149_ = v_isSharedCheck_1203_;
goto v_resetjp_1147_;
}
v_resetjp_1147_:
{
lean_object* v___x_1150_; 
lean_inc_ref(v_s_1138_);
v___x_1150_ = lean_apply_2(v_inst_1137_, v_s_1138_, v_searcher_1146_);
switch(lean_obj_tag(v___x_1150_))
{
case 0:
{
lean_object* v_out_1151_; 
v_out_1151_ = lean_ctor_get(v___x_1150_, 1);
lean_inc(v_out_1151_);
if (lean_obj_tag(v_out_1151_) == 0)
{
lean_object* v_it_1152_; lean_object* v___x_1154_; 
lean_dec_ref_known(v_out_1151_, 2);
lean_dec_ref(v_s_1138_);
v_it_1152_ = lean_ctor_get(v___x_1150_, 0);
lean_inc(v_it_1152_);
lean_dec_ref_known(v___x_1150_, 2);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_it_1152_);
v___x_1154_ = v___x_1148_;
goto v_reusejp_1153_;
}
else
{
lean_object* v_reuseFailAlloc_1157_; 
v_reuseFailAlloc_1157_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1157_, 0, v_currPos_1145_);
lean_ctor_set(v_reuseFailAlloc_1157_, 1, v_it_1152_);
v___x_1154_ = v_reuseFailAlloc_1157_;
goto v_reusejp_1153_;
}
v_reusejp_1153_:
{
lean_object* v___x_1155_; lean_object* v___x_1156_; 
v___x_1155_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1155_, 0, v___x_1154_);
v___x_1156_ = lean_apply_4(v_lift_1139_, lean_box(0), lean_box(0), v___f_1144_, v___x_1155_);
return v___x_1156_;
}
}
else
{
lean_object* v_it_1158_; lean_object* v___x_1160_; uint8_t v_isShared_1161_; uint8_t v_isSharedCheck_1171_; 
v_it_1158_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1171_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1171_ == 0)
{
lean_object* v_unused_1172_; 
v_unused_1172_ = lean_ctor_get(v___x_1150_, 1);
lean_dec(v_unused_1172_);
v___x_1160_ = v___x_1150_;
v_isShared_1161_ = v_isSharedCheck_1171_;
goto v_resetjp_1159_;
}
else
{
lean_inc(v_it_1158_);
lean_dec(v___x_1150_);
v___x_1160_ = lean_box(0);
v_isShared_1161_ = v_isSharedCheck_1171_;
goto v_resetjp_1159_;
}
v_resetjp_1159_:
{
lean_object* v_endPos_1162_; lean_object* v_slice_1163_; lean_object* v_nextIt_1165_; 
v_endPos_1162_ = lean_ctor_get(v_out_1151_, 1);
lean_inc(v_endPos_1162_);
lean_dec_ref_known(v_out_1151_, 2);
v_slice_1163_ = l_String_Slice_slice_x21(v_s_1138_, v_currPos_1145_, v_endPos_1162_);
lean_dec(v_currPos_1145_);
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_it_1158_);
lean_ctor_set(v___x_1148_, 0, v_endPos_1162_);
v_nextIt_1165_ = v___x_1148_;
goto v_reusejp_1164_;
}
else
{
lean_object* v_reuseFailAlloc_1170_; 
v_reuseFailAlloc_1170_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1170_, 0, v_endPos_1162_);
lean_ctor_set(v_reuseFailAlloc_1170_, 1, v_it_1158_);
v_nextIt_1165_ = v_reuseFailAlloc_1170_;
goto v_reusejp_1164_;
}
v_reusejp_1164_:
{
lean_object* v___x_1167_; 
if (v_isShared_1161_ == 0)
{
lean_ctor_set(v___x_1160_, 1, v_slice_1163_);
lean_ctor_set(v___x_1160_, 0, v_nextIt_1165_);
v___x_1167_ = v___x_1160_;
goto v_reusejp_1166_;
}
else
{
lean_object* v_reuseFailAlloc_1169_; 
v_reuseFailAlloc_1169_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1169_, 0, v_nextIt_1165_);
lean_ctor_set(v_reuseFailAlloc_1169_, 1, v_slice_1163_);
v___x_1167_ = v_reuseFailAlloc_1169_;
goto v_reusejp_1166_;
}
v_reusejp_1166_:
{
lean_object* v___x_1168_; 
v___x_1168_ = lean_apply_4(v_lift_1139_, lean_box(0), lean_box(0), v___f_1144_, v___x_1167_);
return v___x_1168_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1173_; lean_object* v___x_1175_; uint8_t v_isShared_1176_; uint8_t v_isSharedCheck_1184_; 
lean_dec_ref(v_s_1138_);
v_it_1173_ = lean_ctor_get(v___x_1150_, 0);
v_isSharedCheck_1184_ = !lean_is_exclusive(v___x_1150_);
if (v_isSharedCheck_1184_ == 0)
{
v___x_1175_ = v___x_1150_;
v_isShared_1176_ = v_isSharedCheck_1184_;
goto v_resetjp_1174_;
}
else
{
lean_inc(v_it_1173_);
lean_dec(v___x_1150_);
v___x_1175_ = lean_box(0);
v_isShared_1176_ = v_isSharedCheck_1184_;
goto v_resetjp_1174_;
}
v_resetjp_1174_:
{
lean_object* v___x_1178_; 
if (v_isShared_1149_ == 0)
{
lean_ctor_set(v___x_1148_, 1, v_it_1173_);
v___x_1178_ = v___x_1148_;
goto v_reusejp_1177_;
}
else
{
lean_object* v_reuseFailAlloc_1183_; 
v_reuseFailAlloc_1183_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1183_, 0, v_currPos_1145_);
lean_ctor_set(v_reuseFailAlloc_1183_, 1, v_it_1173_);
v___x_1178_ = v_reuseFailAlloc_1183_;
goto v_reusejp_1177_;
}
v_reusejp_1177_:
{
lean_object* v___x_1180_; 
if (v_isShared_1176_ == 0)
{
lean_ctor_set(v___x_1175_, 0, v___x_1178_);
v___x_1180_ = v___x_1175_;
goto v_reusejp_1179_;
}
else
{
lean_object* v_reuseFailAlloc_1182_; 
v_reuseFailAlloc_1182_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1182_, 0, v___x_1178_);
v___x_1180_ = v_reuseFailAlloc_1182_;
goto v_reusejp_1179_;
}
v_reusejp_1179_:
{
lean_object* v___x_1181_; 
v___x_1181_ = lean_apply_4(v_lift_1139_, lean_box(0), lean_box(0), v___f_1144_, v___x_1180_);
return v___x_1181_;
}
}
}
}
default: 
{
lean_object* v_str_1185_; lean_object* v_startInclusive_1186_; lean_object* v_endExclusive_1187_; lean_object* v___x_1189_; uint8_t v_isShared_1190_; uint8_t v_isSharedCheck_1202_; 
lean_del_object(v___x_1148_);
v_str_1185_ = lean_ctor_get(v_s_1138_, 0);
v_startInclusive_1186_ = lean_ctor_get(v_s_1138_, 1);
v_endExclusive_1187_ = lean_ctor_get(v_s_1138_, 2);
v_isSharedCheck_1202_ = !lean_is_exclusive(v_s_1138_);
if (v_isSharedCheck_1202_ == 0)
{
v___x_1189_ = v_s_1138_;
v_isShared_1190_ = v_isSharedCheck_1202_;
goto v_resetjp_1188_;
}
else
{
lean_inc(v_endExclusive_1187_);
lean_inc(v_startInclusive_1186_);
lean_inc(v_str_1185_);
lean_dec(v_s_1138_);
v___x_1189_ = lean_box(0);
v_isShared_1190_ = v_isSharedCheck_1202_;
goto v_resetjp_1188_;
}
v_resetjp_1188_:
{
lean_object* v___x_1191_; uint8_t v_decide_1192_; 
v___x_1191_ = lean_nat_sub(v_endExclusive_1187_, v_startInclusive_1186_);
v_decide_1192_ = lean_nat_dec_eq(v_currPos_1145_, v___x_1191_);
lean_dec(v___x_1191_);
if (v_decide_1192_ == 0)
{
lean_object* v___x_1193_; lean_object* v_slice_1195_; 
v___x_1193_ = lean_nat_add(v_startInclusive_1186_, v_currPos_1145_);
lean_dec(v_currPos_1145_);
lean_dec(v_startInclusive_1186_);
if (v_isShared_1190_ == 0)
{
lean_ctor_set(v___x_1189_, 1, v___x_1193_);
v_slice_1195_ = v___x_1189_;
goto v_reusejp_1194_;
}
else
{
lean_object* v_reuseFailAlloc_1199_; 
v_reuseFailAlloc_1199_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1199_, 0, v_str_1185_);
lean_ctor_set(v_reuseFailAlloc_1199_, 1, v___x_1193_);
lean_ctor_set(v_reuseFailAlloc_1199_, 2, v_endExclusive_1187_);
v_slice_1195_ = v_reuseFailAlloc_1199_;
goto v_reusejp_1194_;
}
v_reusejp_1194_:
{
lean_object* v___x_1196_; lean_object* v___x_1197_; lean_object* v___x_1198_; 
v___x_1196_ = lean_box(1);
v___x_1197_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1197_, 0, v___x_1196_);
lean_ctor_set(v___x_1197_, 1, v_slice_1195_);
v___x_1198_ = lean_apply_4(v_lift_1139_, lean_box(0), lean_box(0), v___f_1144_, v___x_1197_);
return v___x_1198_;
}
}
else
{
lean_object* v___x_1200_; lean_object* v___x_1201_; 
lean_del_object(v___x_1189_);
lean_dec(v_endExclusive_1187_);
lean_dec(v_startInclusive_1186_);
lean_dec_ref(v_str_1185_);
lean_dec(v_currPos_1145_);
v___x_1200_ = lean_box(2);
v___x_1201_ = lean_apply_4(v_lift_1139_, lean_box(0), lean_box(0), v___f_1144_, v___x_1200_);
return v___x_1201_;
}
}
}
}
}
}
else
{
lean_object* v___x_1204_; lean_object* v___x_1205_; 
lean_dec_ref(v_s_1138_);
lean_dec(v_inst_1137_);
v___x_1204_ = lean_box(2);
v___x_1205_ = lean_apply_4(v_lift_1139_, lean_box(0), lean_box(0), v___f_1144_, v___x_1204_);
return v___x_1205_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3(lean_object* v_inst_1206_, lean_object* v_inst_1207_, lean_object* v_s_1208_, lean_object* v_lift_1209_, lean_object* v_00_u03b3_1210_, lean_object* v_Pl_1211_, lean_object* v_it_1212_, lean_object* v_init_1213_, lean_object* v___y_1214_){
_start:
{
lean_object* v_toApplicative_1215_; lean_object* v_toBind_1216_; lean_object* v_toPure_1217_; lean_object* v___f_1218_; lean_object* v___x_1219_; 
v_toApplicative_1215_ = lean_ctor_get(v_inst_1206_, 0);
lean_inc_ref(v_toApplicative_1215_);
v_toBind_1216_ = lean_ctor_get(v_inst_1206_, 1);
lean_inc(v_toBind_1216_);
lean_dec_ref(v_inst_1206_);
v_toPure_1217_ = lean_ctor_get(v_toApplicative_1215_, 1);
lean_inc(v_toPure_1217_);
lean_dec_ref(v_toApplicative_1215_);
v___f_1218_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_1218_, 0, v_toPure_1217_);
lean_closure_set(v___f_1218_, 1, v___y_1214_);
lean_closure_set(v___f_1218_, 2, v_toBind_1216_);
lean_closure_set(v___f_1218_, 3, v_inst_1207_);
lean_closure_set(v___f_1218_, 4, v_s_1208_);
lean_closure_set(v___f_1218_, 5, v_lift_1209_);
v___x_1219_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1218_, v_it_1212_, v_init_1213_, lean_box(0));
return v___x_1219_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg(lean_object* v_inst_1220_, lean_object* v_inst_1221_, lean_object* v_s_1222_){
_start:
{
lean_object* v___f_1223_; 
v___f_1223_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1223_, 0, v_inst_1221_);
lean_closure_set(v___f_1223_, 1, v_inst_1220_);
lean_closure_set(v___f_1223_, 2, v_s_1222_);
return v___f_1223_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(lean_object* v_00_u03c1_1224_, lean_object* v_00_u03c3_1225_, lean_object* v_inst_1226_, lean_object* v_pat_1227_, lean_object* v_inst_1228_, lean_object* v_n_1229_, lean_object* v_inst_1230_, lean_object* v_s_1231_){
_start:
{
lean_object* v___f_1232_; 
v___f_1232_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1232_, 0, v_inst_1230_);
lean_closure_set(v___f_1232_, 1, v_inst_1226_);
lean_closure_set(v___f_1232_, 2, v_s_1231_);
return v___f_1232_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___boxed(lean_object* v_00_u03c1_1233_, lean_object* v_00_u03c3_1234_, lean_object* v_inst_1235_, lean_object* v_pat_1236_, lean_object* v_inst_1237_, lean_object* v_n_1238_, lean_object* v_inst_1239_, lean_object* v_s_1240_){
_start:
{
lean_object* v_res_1241_; 
v_res_1241_ = l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(v_00_u03c1_1233_, v_00_u03c3_1234_, v_inst_1235_, v_pat_1236_, v_inst_1237_, v_n_1238_, v_inst_1239_, v_s_1240_);
lean_dec(v_inst_1237_);
lean_dec(v_pat_1236_);
return v_res_1241_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___redArg(lean_object* v_s_1242_, lean_object* v_inst_1243_){
_start:
{
lean_object* v___x_1244_; lean_object* v___x_1245_; lean_object* v___x_1246_; 
v___x_1244_ = lean_unsigned_to_nat(0u);
v___x_1245_ = lean_apply_1(v_inst_1243_, v_s_1242_);
v___x_1246_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1246_, 0, v___x_1244_);
lean_ctor_set(v___x_1246_, 1, v___x_1245_);
return v___x_1246_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive(lean_object* v_00_u03c1_1247_, lean_object* v_00_u03c3_1248_, lean_object* v_s_1249_, lean_object* v_pat_1250_, lean_object* v_inst_1251_){
_start:
{
lean_object* v___x_1252_; 
v___x_1252_ = l_String_Slice_splitInclusive___redArg(v_s_1249_, v_inst_1251_);
return v___x_1252_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___boxed(lean_object* v_00_u03c1_1253_, lean_object* v_00_u03c3_1254_, lean_object* v_s_1255_, lean_object* v_pat_1256_, lean_object* v_inst_1257_){
_start:
{
lean_object* v_res_1258_; 
v_res_1258_ = l_String_Slice_splitInclusive(v_00_u03c1_1253_, v_00_u03c3_1254_, v_s_1255_, v_pat_1256_, v_inst_1257_);
lean_dec(v_pat_1256_);
return v_res_1258_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___redArg(lean_object* v_s_1259_, lean_object* v_inst_1260_){
_start:
{
lean_object* v_skipPrefix_x3f_1261_; lean_object* v___x_1262_; 
v_skipPrefix_x3f_1261_ = lean_ctor_get(v_inst_1260_, 0);
lean_inc_ref(v_skipPrefix_x3f_1261_);
lean_dec_ref(v_inst_1260_);
v___x_1262_ = lean_apply_1(v_skipPrefix_x3f_1261_, v_s_1259_);
return v___x_1262_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f(lean_object* v_00_u03c1_1263_, lean_object* v_s_1264_, lean_object* v_pat_1265_, lean_object* v_inst_1266_){
_start:
{
lean_object* v_skipPrefix_x3f_1267_; lean_object* v___x_1268_; 
v_skipPrefix_x3f_1267_ = lean_ctor_get(v_inst_1266_, 0);
lean_inc_ref(v_skipPrefix_x3f_1267_);
lean_dec_ref(v_inst_1266_);
v___x_1268_ = lean_apply_1(v_skipPrefix_x3f_1267_, v_s_1264_);
return v___x_1268_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___boxed(lean_object* v_00_u03c1_1269_, lean_object* v_s_1270_, lean_object* v_pat_1271_, lean_object* v_inst_1272_){
_start:
{
lean_object* v_res_1273_; 
v_res_1273_ = l_String_Slice_skipPrefix_x3f(v_00_u03c1_1269_, v_s_1270_, v_pat_1271_, v_inst_1272_);
lean_dec(v_pat_1271_);
return v_res_1273_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg(lean_object* v_s_1274_, lean_object* v_pos_1275_, lean_object* v_inst_1276_){
_start:
{
lean_object* v_str_1277_; lean_object* v_startInclusive_1278_; lean_object* v_endExclusive_1279_; lean_object* v___x_1281_; uint8_t v_isShared_1282_; uint8_t v_isSharedCheck_1298_; 
v_str_1277_ = lean_ctor_get(v_s_1274_, 0);
v_startInclusive_1278_ = lean_ctor_get(v_s_1274_, 1);
v_endExclusive_1279_ = lean_ctor_get(v_s_1274_, 2);
v_isSharedCheck_1298_ = !lean_is_exclusive(v_s_1274_);
if (v_isSharedCheck_1298_ == 0)
{
v___x_1281_ = v_s_1274_;
v_isShared_1282_ = v_isSharedCheck_1298_;
goto v_resetjp_1280_;
}
else
{
lean_inc(v_endExclusive_1279_);
lean_inc(v_startInclusive_1278_);
lean_inc(v_str_1277_);
lean_dec(v_s_1274_);
v___x_1281_ = lean_box(0);
v_isShared_1282_ = v_isSharedCheck_1298_;
goto v_resetjp_1280_;
}
v_resetjp_1280_:
{
lean_object* v_skipPrefix_x3f_1283_; lean_object* v___x_1284_; lean_object* v___x_1286_; 
v_skipPrefix_x3f_1283_ = lean_ctor_get(v_inst_1276_, 0);
lean_inc_ref(v_skipPrefix_x3f_1283_);
lean_dec_ref(v_inst_1276_);
v___x_1284_ = lean_nat_add(v_startInclusive_1278_, v_pos_1275_);
lean_dec(v_startInclusive_1278_);
if (v_isShared_1282_ == 0)
{
lean_ctor_set(v___x_1281_, 1, v___x_1284_);
v___x_1286_ = v___x_1281_;
goto v_reusejp_1285_;
}
else
{
lean_object* v_reuseFailAlloc_1297_; 
v_reuseFailAlloc_1297_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1297_, 0, v_str_1277_);
lean_ctor_set(v_reuseFailAlloc_1297_, 1, v___x_1284_);
lean_ctor_set(v_reuseFailAlloc_1297_, 2, v_endExclusive_1279_);
v___x_1286_ = v_reuseFailAlloc_1297_;
goto v_reusejp_1285_;
}
v_reusejp_1285_:
{
lean_object* v___x_1287_; 
v___x_1287_ = lean_apply_1(v_skipPrefix_x3f_1283_, v___x_1286_);
if (lean_obj_tag(v___x_1287_) == 0)
{
return v___x_1287_;
}
else
{
lean_object* v_val_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1296_; 
v_val_1288_ = lean_ctor_get(v___x_1287_, 0);
v_isSharedCheck_1296_ = !lean_is_exclusive(v___x_1287_);
if (v_isSharedCheck_1296_ == 0)
{
v___x_1290_ = v___x_1287_;
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_val_1288_);
lean_dec(v___x_1287_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1296_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v___x_1292_; lean_object* v___x_1294_; 
v___x_1292_ = lean_nat_add(v_pos_1275_, v_val_1288_);
lean_dec(v_val_1288_);
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1292_);
v___x_1294_ = v___x_1290_;
goto v_reusejp_1293_;
}
else
{
lean_object* v_reuseFailAlloc_1295_; 
v_reuseFailAlloc_1295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1295_, 0, v___x_1292_);
v___x_1294_ = v_reuseFailAlloc_1295_;
goto v_reusejp_1293_;
}
v_reusejp_1293_:
{
return v___x_1294_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg___boxed(lean_object* v_s_1299_, lean_object* v_pos_1300_, lean_object* v_inst_1301_){
_start:
{
lean_object* v_res_1302_; 
v_res_1302_ = l_String_Slice_Pos_skip_x3f___redArg(v_s_1299_, v_pos_1300_, v_inst_1301_);
lean_dec(v_pos_1300_);
return v_res_1302_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f(lean_object* v_00_u03c1_1303_, lean_object* v_s_1304_, lean_object* v_pos_1305_, lean_object* v_pat_1306_, lean_object* v_inst_1307_){
_start:
{
lean_object* v_str_1308_; lean_object* v_startInclusive_1309_; lean_object* v_endExclusive_1310_; lean_object* v___x_1312_; uint8_t v_isShared_1313_; uint8_t v_isSharedCheck_1329_; 
v_str_1308_ = lean_ctor_get(v_s_1304_, 0);
v_startInclusive_1309_ = lean_ctor_get(v_s_1304_, 1);
v_endExclusive_1310_ = lean_ctor_get(v_s_1304_, 2);
v_isSharedCheck_1329_ = !lean_is_exclusive(v_s_1304_);
if (v_isSharedCheck_1329_ == 0)
{
v___x_1312_ = v_s_1304_;
v_isShared_1313_ = v_isSharedCheck_1329_;
goto v_resetjp_1311_;
}
else
{
lean_inc(v_endExclusive_1310_);
lean_inc(v_startInclusive_1309_);
lean_inc(v_str_1308_);
lean_dec(v_s_1304_);
v___x_1312_ = lean_box(0);
v_isShared_1313_ = v_isSharedCheck_1329_;
goto v_resetjp_1311_;
}
v_resetjp_1311_:
{
lean_object* v_skipPrefix_x3f_1314_; lean_object* v___x_1315_; lean_object* v___x_1317_; 
v_skipPrefix_x3f_1314_ = lean_ctor_get(v_inst_1307_, 0);
lean_inc_ref(v_skipPrefix_x3f_1314_);
lean_dec_ref(v_inst_1307_);
v___x_1315_ = lean_nat_add(v_startInclusive_1309_, v_pos_1305_);
lean_dec(v_startInclusive_1309_);
if (v_isShared_1313_ == 0)
{
lean_ctor_set(v___x_1312_, 1, v___x_1315_);
v___x_1317_ = v___x_1312_;
goto v_reusejp_1316_;
}
else
{
lean_object* v_reuseFailAlloc_1328_; 
v_reuseFailAlloc_1328_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1328_, 0, v_str_1308_);
lean_ctor_set(v_reuseFailAlloc_1328_, 1, v___x_1315_);
lean_ctor_set(v_reuseFailAlloc_1328_, 2, v_endExclusive_1310_);
v___x_1317_ = v_reuseFailAlloc_1328_;
goto v_reusejp_1316_;
}
v_reusejp_1316_:
{
lean_object* v___x_1318_; 
v___x_1318_ = lean_apply_1(v_skipPrefix_x3f_1314_, v___x_1317_);
if (lean_obj_tag(v___x_1318_) == 0)
{
return v___x_1318_;
}
else
{
lean_object* v_val_1319_; lean_object* v___x_1321_; uint8_t v_isShared_1322_; uint8_t v_isSharedCheck_1327_; 
v_val_1319_ = lean_ctor_get(v___x_1318_, 0);
v_isSharedCheck_1327_ = !lean_is_exclusive(v___x_1318_);
if (v_isSharedCheck_1327_ == 0)
{
v___x_1321_ = v___x_1318_;
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
else
{
lean_inc(v_val_1319_);
lean_dec(v___x_1318_);
v___x_1321_ = lean_box(0);
v_isShared_1322_ = v_isSharedCheck_1327_;
goto v_resetjp_1320_;
}
v_resetjp_1320_:
{
lean_object* v___x_1323_; lean_object* v___x_1325_; 
v___x_1323_ = lean_nat_add(v_pos_1305_, v_val_1319_);
lean_dec(v_val_1319_);
if (v_isShared_1322_ == 0)
{
lean_ctor_set(v___x_1321_, 0, v___x_1323_);
v___x_1325_ = v___x_1321_;
goto v_reusejp_1324_;
}
else
{
lean_object* v_reuseFailAlloc_1326_; 
v_reuseFailAlloc_1326_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1326_, 0, v___x_1323_);
v___x_1325_ = v_reuseFailAlloc_1326_;
goto v_reusejp_1324_;
}
v_reusejp_1324_:
{
return v___x_1325_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_1330_, lean_object* v_s_1331_, lean_object* v_pos_1332_, lean_object* v_pat_1333_, lean_object* v_inst_1334_){
_start:
{
lean_object* v_res_1335_; 
v_res_1335_ = l_String_Slice_Pos_skip_x3f(v_00_u03c1_1330_, v_s_1331_, v_pos_1332_, v_pat_1333_, v_inst_1334_);
lean_dec(v_pat_1333_);
lean_dec(v_pos_1332_);
return v_res_1335_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___redArg(lean_object* v_s_1336_, lean_object* v_inst_1337_){
_start:
{
lean_object* v_skipPrefix_x3f_1338_; lean_object* v___x_1339_; 
v_skipPrefix_x3f_1338_ = lean_ctor_get(v_inst_1337_, 0);
lean_inc_ref(v_skipPrefix_x3f_1338_);
lean_dec_ref(v_inst_1337_);
lean_inc_ref(v_s_1336_);
v___x_1339_ = lean_apply_1(v_skipPrefix_x3f_1338_, v_s_1336_);
if (lean_obj_tag(v___x_1339_) == 0)
{
lean_object* v___x_1340_; 
lean_dec_ref(v_s_1336_);
v___x_1340_ = lean_box(0);
return v___x_1340_;
}
else
{
lean_object* v_val_1341_; lean_object* v___x_1343_; uint8_t v_isShared_1344_; uint8_t v_isSharedCheck_1359_; 
v_val_1341_ = lean_ctor_get(v___x_1339_, 0);
v_isSharedCheck_1359_ = !lean_is_exclusive(v___x_1339_);
if (v_isSharedCheck_1359_ == 0)
{
v___x_1343_ = v___x_1339_;
v_isShared_1344_ = v_isSharedCheck_1359_;
goto v_resetjp_1342_;
}
else
{
lean_inc(v_val_1341_);
lean_dec(v___x_1339_);
v___x_1343_ = lean_box(0);
v_isShared_1344_ = v_isSharedCheck_1359_;
goto v_resetjp_1342_;
}
v_resetjp_1342_:
{
lean_object* v_str_1345_; lean_object* v_startInclusive_1346_; lean_object* v_endExclusive_1347_; lean_object* v___x_1349_; uint8_t v_isShared_1350_; uint8_t v_isSharedCheck_1358_; 
v_str_1345_ = lean_ctor_get(v_s_1336_, 0);
v_startInclusive_1346_ = lean_ctor_get(v_s_1336_, 1);
v_endExclusive_1347_ = lean_ctor_get(v_s_1336_, 2);
v_isSharedCheck_1358_ = !lean_is_exclusive(v_s_1336_);
if (v_isSharedCheck_1358_ == 0)
{
v___x_1349_ = v_s_1336_;
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
else
{
lean_inc(v_endExclusive_1347_);
lean_inc(v_startInclusive_1346_);
lean_inc(v_str_1345_);
lean_dec(v_s_1336_);
v___x_1349_ = lean_box(0);
v_isShared_1350_ = v_isSharedCheck_1358_;
goto v_resetjp_1348_;
}
v_resetjp_1348_:
{
lean_object* v___x_1351_; lean_object* v___x_1353_; 
v___x_1351_ = lean_nat_add(v_startInclusive_1346_, v_val_1341_);
lean_dec(v_val_1341_);
lean_dec(v_startInclusive_1346_);
if (v_isShared_1350_ == 0)
{
lean_ctor_set(v___x_1349_, 1, v___x_1351_);
v___x_1353_ = v___x_1349_;
goto v_reusejp_1352_;
}
else
{
lean_object* v_reuseFailAlloc_1357_; 
v_reuseFailAlloc_1357_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1357_, 0, v_str_1345_);
lean_ctor_set(v_reuseFailAlloc_1357_, 1, v___x_1351_);
lean_ctor_set(v_reuseFailAlloc_1357_, 2, v_endExclusive_1347_);
v___x_1353_ = v_reuseFailAlloc_1357_;
goto v_reusejp_1352_;
}
v_reusejp_1352_:
{
lean_object* v___x_1355_; 
if (v_isShared_1344_ == 0)
{
lean_ctor_set(v___x_1343_, 0, v___x_1353_);
v___x_1355_ = v___x_1343_;
goto v_reusejp_1354_;
}
else
{
lean_object* v_reuseFailAlloc_1356_; 
v_reuseFailAlloc_1356_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1356_, 0, v___x_1353_);
v___x_1355_ = v_reuseFailAlloc_1356_;
goto v_reusejp_1354_;
}
v_reusejp_1354_:
{
return v___x_1355_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f(lean_object* v_00_u03c1_1360_, lean_object* v_s_1361_, lean_object* v_pat_1362_, lean_object* v_inst_1363_){
_start:
{
lean_object* v_skipPrefix_x3f_1364_; lean_object* v___x_1365_; 
v_skipPrefix_x3f_1364_ = lean_ctor_get(v_inst_1363_, 0);
lean_inc_ref(v_skipPrefix_x3f_1364_);
lean_dec_ref(v_inst_1363_);
lean_inc_ref(v_s_1361_);
v___x_1365_ = lean_apply_1(v_skipPrefix_x3f_1364_, v_s_1361_);
if (lean_obj_tag(v___x_1365_) == 0)
{
lean_object* v___x_1366_; 
lean_dec_ref(v_s_1361_);
v___x_1366_ = lean_box(0);
return v___x_1366_;
}
else
{
lean_object* v_val_1367_; lean_object* v___x_1369_; uint8_t v_isShared_1370_; uint8_t v_isSharedCheck_1385_; 
v_val_1367_ = lean_ctor_get(v___x_1365_, 0);
v_isSharedCheck_1385_ = !lean_is_exclusive(v___x_1365_);
if (v_isSharedCheck_1385_ == 0)
{
v___x_1369_ = v___x_1365_;
v_isShared_1370_ = v_isSharedCheck_1385_;
goto v_resetjp_1368_;
}
else
{
lean_inc(v_val_1367_);
lean_dec(v___x_1365_);
v___x_1369_ = lean_box(0);
v_isShared_1370_ = v_isSharedCheck_1385_;
goto v_resetjp_1368_;
}
v_resetjp_1368_:
{
lean_object* v_str_1371_; lean_object* v_startInclusive_1372_; lean_object* v_endExclusive_1373_; lean_object* v___x_1375_; uint8_t v_isShared_1376_; uint8_t v_isSharedCheck_1384_; 
v_str_1371_ = lean_ctor_get(v_s_1361_, 0);
v_startInclusive_1372_ = lean_ctor_get(v_s_1361_, 1);
v_endExclusive_1373_ = lean_ctor_get(v_s_1361_, 2);
v_isSharedCheck_1384_ = !lean_is_exclusive(v_s_1361_);
if (v_isSharedCheck_1384_ == 0)
{
v___x_1375_ = v_s_1361_;
v_isShared_1376_ = v_isSharedCheck_1384_;
goto v_resetjp_1374_;
}
else
{
lean_inc(v_endExclusive_1373_);
lean_inc(v_startInclusive_1372_);
lean_inc(v_str_1371_);
lean_dec(v_s_1361_);
v___x_1375_ = lean_box(0);
v_isShared_1376_ = v_isSharedCheck_1384_;
goto v_resetjp_1374_;
}
v_resetjp_1374_:
{
lean_object* v___x_1377_; lean_object* v___x_1379_; 
v___x_1377_ = lean_nat_add(v_startInclusive_1372_, v_val_1367_);
lean_dec(v_val_1367_);
lean_dec(v_startInclusive_1372_);
if (v_isShared_1376_ == 0)
{
lean_ctor_set(v___x_1375_, 1, v___x_1377_);
v___x_1379_ = v___x_1375_;
goto v_reusejp_1378_;
}
else
{
lean_object* v_reuseFailAlloc_1383_; 
v_reuseFailAlloc_1383_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1383_, 0, v_str_1371_);
lean_ctor_set(v_reuseFailAlloc_1383_, 1, v___x_1377_);
lean_ctor_set(v_reuseFailAlloc_1383_, 2, v_endExclusive_1373_);
v___x_1379_ = v_reuseFailAlloc_1383_;
goto v_reusejp_1378_;
}
v_reusejp_1378_:
{
lean_object* v___x_1381_; 
if (v_isShared_1370_ == 0)
{
lean_ctor_set(v___x_1369_, 0, v___x_1379_);
v___x_1381_ = v___x_1369_;
goto v_reusejp_1380_;
}
else
{
lean_object* v_reuseFailAlloc_1382_; 
v_reuseFailAlloc_1382_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1382_, 0, v___x_1379_);
v___x_1381_ = v_reuseFailAlloc_1382_;
goto v_reusejp_1380_;
}
v_reusejp_1380_:
{
return v___x_1381_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_1386_, lean_object* v_s_1387_, lean_object* v_pat_1388_, lean_object* v_inst_1389_){
_start:
{
lean_object* v_res_1390_; 
v_res_1390_ = l_String_Slice_dropPrefix_x3f(v_00_u03c1_1386_, v_s_1387_, v_pat_1388_, v_inst_1389_);
lean_dec(v_pat_1388_);
return v_res_1390_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___redArg(lean_object* v_s_1391_, lean_object* v_inst_1392_){
_start:
{
lean_object* v_skipPrefix_x3f_1393_; lean_object* v___x_1394_; 
v_skipPrefix_x3f_1393_ = lean_ctor_get(v_inst_1392_, 0);
lean_inc_ref(v_skipPrefix_x3f_1393_);
lean_dec_ref(v_inst_1392_);
lean_inc_ref(v_s_1391_);
v___x_1394_ = lean_apply_1(v_skipPrefix_x3f_1393_, v_s_1391_);
if (lean_obj_tag(v___x_1394_) == 0)
{
return v_s_1391_;
}
else
{
lean_object* v_val_1395_; lean_object* v_str_1396_; lean_object* v_startInclusive_1397_; lean_object* v_endExclusive_1398_; lean_object* v___x_1400_; uint8_t v_isShared_1401_; uint8_t v_isSharedCheck_1406_; 
v_val_1395_ = lean_ctor_get(v___x_1394_, 0);
lean_inc(v_val_1395_);
lean_dec_ref_known(v___x_1394_, 1);
v_str_1396_ = lean_ctor_get(v_s_1391_, 0);
v_startInclusive_1397_ = lean_ctor_get(v_s_1391_, 1);
v_endExclusive_1398_ = lean_ctor_get(v_s_1391_, 2);
v_isSharedCheck_1406_ = !lean_is_exclusive(v_s_1391_);
if (v_isSharedCheck_1406_ == 0)
{
v___x_1400_ = v_s_1391_;
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
else
{
lean_inc(v_endExclusive_1398_);
lean_inc(v_startInclusive_1397_);
lean_inc(v_str_1396_);
lean_dec(v_s_1391_);
v___x_1400_ = lean_box(0);
v_isShared_1401_ = v_isSharedCheck_1406_;
goto v_resetjp_1399_;
}
v_resetjp_1399_:
{
lean_object* v___x_1402_; lean_object* v___x_1404_; 
v___x_1402_ = lean_nat_add(v_startInclusive_1397_, v_val_1395_);
lean_dec(v_val_1395_);
lean_dec(v_startInclusive_1397_);
if (v_isShared_1401_ == 0)
{
lean_ctor_set(v___x_1400_, 1, v___x_1402_);
v___x_1404_ = v___x_1400_;
goto v_reusejp_1403_;
}
else
{
lean_object* v_reuseFailAlloc_1405_; 
v_reuseFailAlloc_1405_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1405_, 0, v_str_1396_);
lean_ctor_set(v_reuseFailAlloc_1405_, 1, v___x_1402_);
lean_ctor_set(v_reuseFailAlloc_1405_, 2, v_endExclusive_1398_);
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
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix(lean_object* v_00_u03c1_1407_, lean_object* v_s_1408_, lean_object* v_pat_1409_, lean_object* v_inst_1410_){
_start:
{
lean_object* v___x_1411_; 
v___x_1411_ = l_String_Slice_dropPrefix___redArg(v_s_1408_, v_inst_1410_);
return v___x_1411_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___boxed(lean_object* v_00_u03c1_1412_, lean_object* v_s_1413_, lean_object* v_pat_1414_, lean_object* v_inst_1415_){
_start:
{
lean_object* v_res_1416_; 
v_res_1416_ = l_String_Slice_dropPrefix(v_00_u03c1_1412_, v_s_1413_, v_pat_1414_, v_inst_1415_);
lean_dec(v_pat_1414_);
return v_res_1416_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__0(lean_object* v_x_1417_, lean_object* v_x_1418_, lean_object* v_f_1419_, lean_object* v_c_1420_){
_start:
{
lean_object* v___x_1421_; 
v___x_1421_ = lean_apply_1(v_f_1419_, v_c_1420_);
return v___x_1421_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1(lean_object* v_s_1422_, lean_object* v_inst_1423_, lean_object* v_replacement_1424_, lean_object* v_x1_1425_, lean_object* v_x2_1426_, lean_object* v_x3_1427_){
_start:
{
if (lean_obj_tag(v_x1_1425_) == 0)
{
lean_object* v_startPos_1428_; lean_object* v_endPos_1429_; lean_object* v___x_1430_; lean_object* v_str_1431_; lean_object* v_startInclusive_1432_; lean_object* v_endExclusive_1433_; lean_object* v___x_1434_; lean_object* v___x_1435_; lean_object* v___x_1436_; 
lean_dec(v_replacement_1424_);
lean_dec_ref(v_inst_1423_);
v_startPos_1428_ = lean_ctor_get(v_x1_1425_, 0);
v_endPos_1429_ = lean_ctor_get(v_x1_1425_, 1);
v___x_1430_ = l_String_Slice_slice_x21(v_s_1422_, v_startPos_1428_, v_endPos_1429_);
v_str_1431_ = lean_ctor_get(v___x_1430_, 0);
lean_inc_ref(v_str_1431_);
v_startInclusive_1432_ = lean_ctor_get(v___x_1430_, 1);
lean_inc(v_startInclusive_1432_);
v_endExclusive_1433_ = lean_ctor_get(v___x_1430_, 2);
lean_inc(v_endExclusive_1433_);
lean_dec_ref(v___x_1430_);
v___x_1434_ = lean_string_utf8_extract_fast(v_str_1431_, v_startInclusive_1432_, v_endExclusive_1433_);
lean_dec(v_endExclusive_1433_);
lean_dec(v_startInclusive_1432_);
lean_dec_ref(v_str_1431_);
v___x_1435_ = lean_string_append(v_x3_1427_, v___x_1434_);
lean_dec_ref(v___x_1434_);
v___x_1436_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1436_, 0, v___x_1435_);
return v___x_1436_;
}
else
{
lean_object* v___x_1437_; lean_object* v_str_1438_; lean_object* v_startInclusive_1439_; lean_object* v_endExclusive_1440_; lean_object* v___x_1441_; lean_object* v___x_1442_; lean_object* v___x_1443_; 
lean_dec_ref(v_s_1422_);
v___x_1437_ = lean_apply_1(v_inst_1423_, v_replacement_1424_);
v_str_1438_ = lean_ctor_get(v___x_1437_, 0);
lean_inc_ref(v_str_1438_);
v_startInclusive_1439_ = lean_ctor_get(v___x_1437_, 1);
lean_inc(v_startInclusive_1439_);
v_endExclusive_1440_ = lean_ctor_get(v___x_1437_, 2);
lean_inc(v_endExclusive_1440_);
lean_dec_ref(v___x_1437_);
v___x_1441_ = lean_string_utf8_extract_fast(v_str_1438_, v_startInclusive_1439_, v_endExclusive_1440_);
lean_dec(v_endExclusive_1440_);
lean_dec(v_startInclusive_1439_);
lean_dec_ref(v_str_1438_);
v___x_1442_ = lean_string_append(v_x3_1427_, v___x_1441_);
lean_dec_ref(v___x_1441_);
v___x_1443_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1443_, 0, v___x_1442_);
return v___x_1443_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1___boxed(lean_object* v_s_1444_, lean_object* v_inst_1445_, lean_object* v_replacement_1446_, lean_object* v_x1_1447_, lean_object* v_x2_1448_, lean_object* v_x3_1449_){
_start:
{
lean_object* v_res_1450_; 
v_res_1450_ = l_String_Slice_replace___redArg___lam__1(v_s_1444_, v_inst_1445_, v_replacement_1446_, v_x1_1447_, v_x2_1448_, v_x3_1449_);
lean_dec_ref(v_x1_1447_);
return v_res_1450_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg(lean_object* v_inst_1453_, lean_object* v_inst_1454_, lean_object* v_s_1455_, lean_object* v_inst_1456_, lean_object* v_replacement_1457_){
_start:
{
lean_object* v___f_1458_; lean_object* v___f_1459_; lean_object* v___x_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; 
v___f_1458_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1455_, 2);
v___f_1459_ = lean_alloc_closure((void*)(l_String_Slice_replace___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1459_, 0, v_s_1455_);
lean_closure_set(v___f_1459_, 1, v_inst_1454_);
lean_closure_set(v___f_1459_, 2, v_replacement_1457_);
v___x_1460_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
v___x_1461_ = lean_apply_1(v_inst_1456_, v_s_1455_);
v___x_1462_ = lean_apply_7(v_inst_1453_, v_s_1455_, v___f_1458_, lean_box(0), lean_box(0), v___x_1461_, v___x_1460_, v___f_1459_);
return v___x_1462_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace(lean_object* v_00_u03c1_1463_, lean_object* v_00_u03c3_1464_, lean_object* v_inst_1465_, lean_object* v_inst_1466_, lean_object* v_00_u03b1_1467_, lean_object* v_inst_1468_, lean_object* v_s_1469_, lean_object* v_pattern_1470_, lean_object* v_inst_1471_, lean_object* v_replacement_1472_){
_start:
{
lean_object* v___x_1473_; 
v___x_1473_ = l_String_Slice_replace___redArg(v_inst_1466_, v_inst_1468_, v_s_1469_, v_inst_1471_, v_replacement_1472_);
return v___x_1473_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___boxed(lean_object* v_00_u03c1_1474_, lean_object* v_00_u03c3_1475_, lean_object* v_inst_1476_, lean_object* v_inst_1477_, lean_object* v_00_u03b1_1478_, lean_object* v_inst_1479_, lean_object* v_s_1480_, lean_object* v_pattern_1481_, lean_object* v_inst_1482_, lean_object* v_replacement_1483_){
_start:
{
lean_object* v_res_1484_; 
v_res_1484_ = l_String_Slice_replace(v_00_u03c1_1474_, v_00_u03c3_1475_, v_inst_1476_, v_inst_1477_, v_00_u03b1_1478_, v_inst_1479_, v_s_1480_, v_pattern_1481_, v_inst_1482_, v_replacement_1483_);
lean_dec(v_pattern_1481_);
lean_dec(v_inst_1476_);
return v_res_1484_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object* v_s_1485_, lean_object* v_n_1486_){
_start:
{
lean_object* v_str_1487_; lean_object* v_startInclusive_1488_; lean_object* v_endExclusive_1489_; lean_object* v___x_1490_; lean_object* v___x_1491_; lean_object* v___x_1493_; uint8_t v_isShared_1494_; uint8_t v_isSharedCheck_1499_; 
v_str_1487_ = lean_ctor_get(v_s_1485_, 0);
lean_inc_ref(v_str_1487_);
v_startInclusive_1488_ = lean_ctor_get(v_s_1485_, 1);
lean_inc(v_startInclusive_1488_);
v_endExclusive_1489_ = lean_ctor_get(v_s_1485_, 2);
lean_inc(v_endExclusive_1489_);
v___x_1490_ = lean_unsigned_to_nat(0u);
v___x_1491_ = l_String_Slice_Pos_nextn(v_s_1485_, v___x_1490_, v_n_1486_);
v_isSharedCheck_1499_ = !lean_is_exclusive(v_s_1485_);
if (v_isSharedCheck_1499_ == 0)
{
lean_object* v_unused_1500_; lean_object* v_unused_1501_; lean_object* v_unused_1502_; 
v_unused_1500_ = lean_ctor_get(v_s_1485_, 2);
lean_dec(v_unused_1500_);
v_unused_1501_ = lean_ctor_get(v_s_1485_, 1);
lean_dec(v_unused_1501_);
v_unused_1502_ = lean_ctor_get(v_s_1485_, 0);
lean_dec(v_unused_1502_);
v___x_1493_ = v_s_1485_;
v_isShared_1494_ = v_isSharedCheck_1499_;
goto v_resetjp_1492_;
}
else
{
lean_dec(v_s_1485_);
v___x_1493_ = lean_box(0);
v_isShared_1494_ = v_isSharedCheck_1499_;
goto v_resetjp_1492_;
}
v_resetjp_1492_:
{
lean_object* v___x_1495_; lean_object* v___x_1497_; 
v___x_1495_ = lean_nat_add(v_startInclusive_1488_, v___x_1491_);
lean_dec(v___x_1491_);
lean_dec(v_startInclusive_1488_);
if (v_isShared_1494_ == 0)
{
lean_ctor_set(v___x_1493_, 1, v___x_1495_);
v___x_1497_ = v___x_1493_;
goto v_reusejp_1496_;
}
else
{
lean_object* v_reuseFailAlloc_1498_; 
v_reuseFailAlloc_1498_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1498_, 0, v_str_1487_);
lean_ctor_set(v_reuseFailAlloc_1498_, 1, v___x_1495_);
lean_ctor_set(v_reuseFailAlloc_1498_, 2, v_endExclusive_1489_);
v___x_1497_ = v_reuseFailAlloc_1498_;
goto v_reusejp_1496_;
}
v_reusejp_1496_:
{
return v___x_1497_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object* v_s_1503_, lean_object* v_pos_1504_, lean_object* v_inst_1505_){
_start:
{
lean_object* v_str_1506_; lean_object* v_startInclusive_1507_; lean_object* v_endExclusive_1508_; lean_object* v_skipPrefix_x3f_1509_; lean_object* v___x_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; 
v_str_1506_ = lean_ctor_get(v_s_1503_, 0);
v_startInclusive_1507_ = lean_ctor_get(v_s_1503_, 1);
v_endExclusive_1508_ = lean_ctor_get(v_s_1503_, 2);
v_skipPrefix_x3f_1509_ = lean_ctor_get(v_inst_1505_, 0);
v___x_1510_ = lean_nat_add(v_startInclusive_1507_, v_pos_1504_);
lean_inc(v_endExclusive_1508_);
lean_inc_ref(v_str_1506_);
v___x_1511_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1511_, 0, v_str_1506_);
lean_ctor_set(v___x_1511_, 1, v___x_1510_);
lean_ctor_set(v___x_1511_, 2, v_endExclusive_1508_);
lean_inc_ref(v_skipPrefix_x3f_1509_);
v___x_1512_ = lean_apply_1(v_skipPrefix_x3f_1509_, v___x_1511_);
if (lean_obj_tag(v___x_1512_) == 0)
{
lean_dec_ref(v_inst_1505_);
return v_pos_1504_;
}
else
{
lean_object* v_val_1513_; lean_object* v___x_1514_; lean_object* v___x_1515_; lean_object* v___x_1516_; uint8_t v___x_1517_; 
v_val_1513_ = lean_ctor_get(v___x_1512_, 0);
lean_inc(v_val_1513_);
lean_dec_ref_known(v___x_1512_, 1);
v___x_1514_ = lean_nat_add(v_pos_1504_, v_val_1513_);
lean_dec(v_val_1513_);
v___x_1515_ = lean_unsigned_to_nat(1u);
v___x_1516_ = lean_nat_add(v_pos_1504_, v___x_1515_);
v___x_1517_ = lean_nat_dec_le(v___x_1516_, v___x_1514_);
lean_dec(v___x_1516_);
if (v___x_1517_ == 0)
{
lean_dec(v___x_1514_);
lean_dec_ref(v_inst_1505_);
return v_pos_1504_;
}
else
{
lean_dec(v_pos_1504_);
v_pos_1504_ = v___x_1514_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg___boxed(lean_object* v_s_1519_, lean_object* v_pos_1520_, lean_object* v_inst_1521_){
_start:
{
lean_object* v_res_1522_; 
v_res_1522_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1519_, v_pos_1520_, v_inst_1521_);
lean_dec_ref(v_s_1519_);
return v_res_1522_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile(lean_object* v_00_u03c1_1523_, lean_object* v_s_1524_, lean_object* v_pos_1525_, lean_object* v_pat_1526_, lean_object* v_inst_1527_){
_start:
{
lean_object* v___x_1528_; 
v___x_1528_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1524_, v_pos_1525_, v_inst_1527_);
return v___x_1528_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___boxed(lean_object* v_00_u03c1_1529_, lean_object* v_s_1530_, lean_object* v_pos_1531_, lean_object* v_pat_1532_, lean_object* v_inst_1533_){
_start:
{
lean_object* v_res_1534_; 
v_res_1534_ = l_String_Slice_Pos_skipWhile(v_00_u03c1_1529_, v_s_1530_, v_pos_1531_, v_pat_1532_, v_inst_1533_);
lean_dec(v_pat_1532_);
lean_dec_ref(v_s_1530_);
return v_res_1534_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object* v_x_1535_, lean_object* v_h__1_1536_, lean_object* v_h__2_1537_){
_start:
{
if (lean_obj_tag(v_x_1535_) == 0)
{
lean_object* v___x_1538_; lean_object* v___x_1539_; 
lean_dec(v_h__1_1536_);
v___x_1538_ = lean_box(0);
v___x_1539_ = lean_apply_1(v_h__2_1537_, v___x_1538_);
return v___x_1539_;
}
else
{
lean_object* v_val_1540_; lean_object* v___x_1541_; 
lean_dec(v_h__2_1537_);
v_val_1540_ = lean_ctor_get(v_x_1535_, 0);
lean_inc(v_val_1540_);
lean_dec_ref_known(v_x_1535_, 1);
v___x_1541_ = lean_apply_1(v_h__1_1536_, v_val_1540_);
return v___x_1541_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object* v_s_1542_, lean_object* v_motive_1543_, lean_object* v_x_1544_, lean_object* v_h__1_1545_, lean_object* v_h__2_1546_){
_start:
{
if (lean_obj_tag(v_x_1544_) == 0)
{
lean_object* v___x_1547_; lean_object* v___x_1548_; 
lean_dec(v_h__1_1545_);
v___x_1547_ = lean_box(0);
v___x_1548_ = lean_apply_1(v_h__2_1546_, v___x_1547_);
return v___x_1548_;
}
else
{
lean_object* v_val_1549_; lean_object* v___x_1550_; 
lean_dec(v_h__2_1546_);
v_val_1549_ = lean_ctor_get(v_x_1544_, 0);
lean_inc(v_val_1549_);
lean_dec_ref_known(v_x_1544_, 1);
v___x_1550_ = lean_apply_1(v_h__1_1545_, v_val_1549_);
return v___x_1550_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object* v_s_1551_, lean_object* v_motive_1552_, lean_object* v_x_1553_, lean_object* v_h__1_1554_, lean_object* v_h__2_1555_){
_start:
{
lean_object* v_res_1556_; 
v_res_1556_ = l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_1551_, v_motive_1552_, v_x_1553_, v_h__1_1554_, v_h__2_1555_);
lean_dec_ref(v_s_1551_);
return v_res_1556_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg(lean_object* v_s_1557_, lean_object* v_inst_1558_){
_start:
{
lean_object* v___x_1559_; lean_object* v___x_1560_; 
v___x_1559_ = lean_unsigned_to_nat(0u);
v___x_1560_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1557_, v___x_1559_, v_inst_1558_);
return v___x_1560_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg___boxed(lean_object* v_s_1561_, lean_object* v_inst_1562_){
_start:
{
lean_object* v_res_1563_; 
v_res_1563_ = l_String_Slice_skipPrefixWhile___redArg(v_s_1561_, v_inst_1562_);
lean_dec_ref(v_s_1561_);
return v_res_1563_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile(lean_object* v_00_u03c1_1564_, lean_object* v_s_1565_, lean_object* v_pat_1566_, lean_object* v_inst_1567_){
_start:
{
lean_object* v___x_1568_; lean_object* v___x_1569_; 
v___x_1568_ = lean_unsigned_to_nat(0u);
v___x_1569_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1565_, v___x_1568_, v_inst_1567_);
return v___x_1569_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___boxed(lean_object* v_00_u03c1_1570_, lean_object* v_s_1571_, lean_object* v_pat_1572_, lean_object* v_inst_1573_){
_start:
{
lean_object* v_res_1574_; 
v_res_1574_ = l_String_Slice_skipPrefixWhile(v_00_u03c1_1570_, v_s_1571_, v_pat_1572_, v_inst_1573_);
lean_dec(v_pat_1572_);
lean_dec_ref(v_s_1571_);
return v_res_1574_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg(lean_object* v_s_1575_, lean_object* v_inst_1576_){
_start:
{
lean_object* v_str_1577_; lean_object* v_startInclusive_1578_; lean_object* v_endExclusive_1579_; lean_object* v___x_1580_; lean_object* v___x_1581_; lean_object* v___x_1583_; uint8_t v_isShared_1584_; uint8_t v_isSharedCheck_1589_; 
v_str_1577_ = lean_ctor_get(v_s_1575_, 0);
lean_inc_ref(v_str_1577_);
v_startInclusive_1578_ = lean_ctor_get(v_s_1575_, 1);
lean_inc(v_startInclusive_1578_);
v_endExclusive_1579_ = lean_ctor_get(v_s_1575_, 2);
lean_inc(v_endExclusive_1579_);
v___x_1580_ = lean_unsigned_to_nat(0u);
v___x_1581_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1575_, v___x_1580_, v_inst_1576_);
v_isSharedCheck_1589_ = !lean_is_exclusive(v_s_1575_);
if (v_isSharedCheck_1589_ == 0)
{
lean_object* v_unused_1590_; lean_object* v_unused_1591_; lean_object* v_unused_1592_; 
v_unused_1590_ = lean_ctor_get(v_s_1575_, 2);
lean_dec(v_unused_1590_);
v_unused_1591_ = lean_ctor_get(v_s_1575_, 1);
lean_dec(v_unused_1591_);
v_unused_1592_ = lean_ctor_get(v_s_1575_, 0);
lean_dec(v_unused_1592_);
v___x_1583_ = v_s_1575_;
v_isShared_1584_ = v_isSharedCheck_1589_;
goto v_resetjp_1582_;
}
else
{
lean_dec(v_s_1575_);
v___x_1583_ = lean_box(0);
v_isShared_1584_ = v_isSharedCheck_1589_;
goto v_resetjp_1582_;
}
v_resetjp_1582_:
{
lean_object* v___x_1585_; lean_object* v___x_1587_; 
v___x_1585_ = lean_nat_add(v_startInclusive_1578_, v___x_1581_);
lean_dec(v___x_1581_);
lean_dec(v_startInclusive_1578_);
if (v_isShared_1584_ == 0)
{
lean_ctor_set(v___x_1583_, 1, v___x_1585_);
v___x_1587_ = v___x_1583_;
goto v_reusejp_1586_;
}
else
{
lean_object* v_reuseFailAlloc_1588_; 
v_reuseFailAlloc_1588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1588_, 0, v_str_1577_);
lean_ctor_set(v_reuseFailAlloc_1588_, 1, v___x_1585_);
lean_ctor_set(v_reuseFailAlloc_1588_, 2, v_endExclusive_1579_);
v___x_1587_ = v_reuseFailAlloc_1588_;
goto v_reusejp_1586_;
}
v_reusejp_1586_:
{
return v___x_1587_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile(lean_object* v_00_u03c1_1593_, lean_object* v_s_1594_, lean_object* v_pat_1595_, lean_object* v_inst_1596_){
_start:
{
lean_object* v_str_1597_; lean_object* v_startInclusive_1598_; lean_object* v_endExclusive_1599_; lean_object* v___x_1600_; lean_object* v___x_1601_; lean_object* v___x_1603_; uint8_t v_isShared_1604_; uint8_t v_isSharedCheck_1609_; 
v_str_1597_ = lean_ctor_get(v_s_1594_, 0);
lean_inc_ref(v_str_1597_);
v_startInclusive_1598_ = lean_ctor_get(v_s_1594_, 1);
lean_inc(v_startInclusive_1598_);
v_endExclusive_1599_ = lean_ctor_get(v_s_1594_, 2);
lean_inc(v_endExclusive_1599_);
v___x_1600_ = lean_unsigned_to_nat(0u);
v___x_1601_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1594_, v___x_1600_, v_inst_1596_);
v_isSharedCheck_1609_ = !lean_is_exclusive(v_s_1594_);
if (v_isSharedCheck_1609_ == 0)
{
lean_object* v_unused_1610_; lean_object* v_unused_1611_; lean_object* v_unused_1612_; 
v_unused_1610_ = lean_ctor_get(v_s_1594_, 2);
lean_dec(v_unused_1610_);
v_unused_1611_ = lean_ctor_get(v_s_1594_, 1);
lean_dec(v_unused_1611_);
v_unused_1612_ = lean_ctor_get(v_s_1594_, 0);
lean_dec(v_unused_1612_);
v___x_1603_ = v_s_1594_;
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
else
{
lean_dec(v_s_1594_);
v___x_1603_ = lean_box(0);
v_isShared_1604_ = v_isSharedCheck_1609_;
goto v_resetjp_1602_;
}
v_resetjp_1602_:
{
lean_object* v___x_1605_; lean_object* v___x_1607_; 
v___x_1605_ = lean_nat_add(v_startInclusive_1598_, v___x_1601_);
lean_dec(v___x_1601_);
lean_dec(v_startInclusive_1598_);
if (v_isShared_1604_ == 0)
{
lean_ctor_set(v___x_1603_, 1, v___x_1605_);
v___x_1607_ = v___x_1603_;
goto v_reusejp_1606_;
}
else
{
lean_object* v_reuseFailAlloc_1608_; 
v_reuseFailAlloc_1608_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1608_, 0, v_str_1597_);
lean_ctor_set(v_reuseFailAlloc_1608_, 1, v___x_1605_);
lean_ctor_set(v_reuseFailAlloc_1608_, 2, v_endExclusive_1599_);
v___x_1607_ = v_reuseFailAlloc_1608_;
goto v_reusejp_1606_;
}
v_reusejp_1606_:
{
return v___x_1607_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___boxed(lean_object* v_00_u03c1_1613_, lean_object* v_s_1614_, lean_object* v_pat_1615_, lean_object* v_inst_1616_){
_start:
{
lean_object* v_res_1617_; 
v_res_1617_ = l_String_Slice_dropWhile(v_00_u03c1_1613_, v_s_1614_, v_pat_1615_, v_inst_1616_);
lean_dec(v_pat_1615_);
return v_res_1617_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiStart___closed__1(void){
_start:
{
lean_object* v___x_1619_; lean_object* v___x_1620_; 
v___x_1619_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_1620_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1619_);
return v___x_1620_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart(lean_object* v_s_1621_){
_start:
{
lean_object* v___x_1622_; lean_object* v_str_1623_; lean_object* v_startInclusive_1624_; lean_object* v_endExclusive_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1635_; 
v___x_1622_ = lean_obj_once(&l_String_Slice_trimAsciiStart___closed__1, &l_String_Slice_trimAsciiStart___closed__1_once, _init_l_String_Slice_trimAsciiStart___closed__1);
v_str_1623_ = lean_ctor_get(v_s_1621_, 0);
lean_inc_ref(v_str_1623_);
v_startInclusive_1624_ = lean_ctor_get(v_s_1621_, 1);
lean_inc(v_startInclusive_1624_);
v_endExclusive_1625_ = lean_ctor_get(v_s_1621_, 2);
lean_inc(v_endExclusive_1625_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1621_, v___x_1626_, v___x_1622_);
v_isSharedCheck_1635_ = !lean_is_exclusive(v_s_1621_);
if (v_isSharedCheck_1635_ == 0)
{
lean_object* v_unused_1636_; lean_object* v_unused_1637_; lean_object* v_unused_1638_; 
v_unused_1636_ = lean_ctor_get(v_s_1621_, 2);
lean_dec(v_unused_1636_);
v_unused_1637_ = lean_ctor_get(v_s_1621_, 1);
lean_dec(v_unused_1637_);
v_unused_1638_ = lean_ctor_get(v_s_1621_, 0);
lean_dec(v_unused_1638_);
v___x_1629_ = v_s_1621_;
v_isShared_1630_ = v_isSharedCheck_1635_;
goto v_resetjp_1628_;
}
else
{
lean_dec(v_s_1621_);
v___x_1629_ = lean_box(0);
v_isShared_1630_ = v_isSharedCheck_1635_;
goto v_resetjp_1628_;
}
v_resetjp_1628_:
{
lean_object* v___x_1631_; lean_object* v___x_1633_; 
v___x_1631_ = lean_nat_add(v_startInclusive_1624_, v___x_1627_);
lean_dec(v___x_1627_);
lean_dec(v_startInclusive_1624_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 1, v___x_1631_);
v___x_1633_ = v___x_1629_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_str_1623_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v___x_1631_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v_endExclusive_1625_);
v___x_1633_ = v_reuseFailAlloc_1634_;
goto v_reusejp_1632_;
}
v_reusejp_1632_:
{
return v___x_1633_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object* v_s_1639_, lean_object* v_n_1640_){
_start:
{
lean_object* v_str_1641_; lean_object* v_startInclusive_1642_; lean_object* v___x_1643_; lean_object* v___x_1644_; lean_object* v___x_1646_; uint8_t v_isShared_1647_; uint8_t v_isSharedCheck_1652_; 
v_str_1641_ = lean_ctor_get(v_s_1639_, 0);
lean_inc_ref(v_str_1641_);
v_startInclusive_1642_ = lean_ctor_get(v_s_1639_, 1);
lean_inc(v_startInclusive_1642_);
v___x_1643_ = lean_unsigned_to_nat(0u);
v___x_1644_ = l_String_Slice_Pos_nextn(v_s_1639_, v___x_1643_, v_n_1640_);
v_isSharedCheck_1652_ = !lean_is_exclusive(v_s_1639_);
if (v_isSharedCheck_1652_ == 0)
{
lean_object* v_unused_1653_; lean_object* v_unused_1654_; lean_object* v_unused_1655_; 
v_unused_1653_ = lean_ctor_get(v_s_1639_, 2);
lean_dec(v_unused_1653_);
v_unused_1654_ = lean_ctor_get(v_s_1639_, 1);
lean_dec(v_unused_1654_);
v_unused_1655_ = lean_ctor_get(v_s_1639_, 0);
lean_dec(v_unused_1655_);
v___x_1646_ = v_s_1639_;
v_isShared_1647_ = v_isSharedCheck_1652_;
goto v_resetjp_1645_;
}
else
{
lean_dec(v_s_1639_);
v___x_1646_ = lean_box(0);
v_isShared_1647_ = v_isSharedCheck_1652_;
goto v_resetjp_1645_;
}
v_resetjp_1645_:
{
lean_object* v___x_1648_; lean_object* v___x_1650_; 
v___x_1648_ = lean_nat_add(v_startInclusive_1642_, v___x_1644_);
lean_dec(v___x_1644_);
if (v_isShared_1647_ == 0)
{
lean_ctor_set(v___x_1646_, 2, v___x_1648_);
v___x_1650_ = v___x_1646_;
goto v_reusejp_1649_;
}
else
{
lean_object* v_reuseFailAlloc_1651_; 
v_reuseFailAlloc_1651_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1651_, 0, v_str_1641_);
lean_ctor_set(v_reuseFailAlloc_1651_, 1, v_startInclusive_1642_);
lean_ctor_set(v_reuseFailAlloc_1651_, 2, v___x_1648_);
v___x_1650_ = v_reuseFailAlloc_1651_;
goto v_reusejp_1649_;
}
v_reusejp_1649_:
{
return v___x_1650_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___redArg(lean_object* v_s_1656_, lean_object* v_inst_1657_){
_start:
{
lean_object* v_str_1658_; lean_object* v_startInclusive_1659_; lean_object* v___x_1660_; lean_object* v___x_1661_; lean_object* v___x_1663_; uint8_t v_isShared_1664_; uint8_t v_isSharedCheck_1669_; 
v_str_1658_ = lean_ctor_get(v_s_1656_, 0);
lean_inc_ref(v_str_1658_);
v_startInclusive_1659_ = lean_ctor_get(v_s_1656_, 1);
lean_inc(v_startInclusive_1659_);
v___x_1660_ = lean_unsigned_to_nat(0u);
v___x_1661_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1656_, v___x_1660_, v_inst_1657_);
v_isSharedCheck_1669_ = !lean_is_exclusive(v_s_1656_);
if (v_isSharedCheck_1669_ == 0)
{
lean_object* v_unused_1670_; lean_object* v_unused_1671_; lean_object* v_unused_1672_; 
v_unused_1670_ = lean_ctor_get(v_s_1656_, 2);
lean_dec(v_unused_1670_);
v_unused_1671_ = lean_ctor_get(v_s_1656_, 1);
lean_dec(v_unused_1671_);
v_unused_1672_ = lean_ctor_get(v_s_1656_, 0);
lean_dec(v_unused_1672_);
v___x_1663_ = v_s_1656_;
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
else
{
lean_dec(v_s_1656_);
v___x_1663_ = lean_box(0);
v_isShared_1664_ = v_isSharedCheck_1669_;
goto v_resetjp_1662_;
}
v_resetjp_1662_:
{
lean_object* v___x_1665_; lean_object* v___x_1667_; 
v___x_1665_ = lean_nat_add(v_startInclusive_1659_, v___x_1661_);
lean_dec(v___x_1661_);
if (v_isShared_1664_ == 0)
{
lean_ctor_set(v___x_1663_, 2, v___x_1665_);
v___x_1667_ = v___x_1663_;
goto v_reusejp_1666_;
}
else
{
lean_object* v_reuseFailAlloc_1668_; 
v_reuseFailAlloc_1668_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1668_, 0, v_str_1658_);
lean_ctor_set(v_reuseFailAlloc_1668_, 1, v_startInclusive_1659_);
lean_ctor_set(v_reuseFailAlloc_1668_, 2, v___x_1665_);
v___x_1667_ = v_reuseFailAlloc_1668_;
goto v_reusejp_1666_;
}
v_reusejp_1666_:
{
return v___x_1667_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile(lean_object* v_00_u03c1_1673_, lean_object* v_s_1674_, lean_object* v_pat_1675_, lean_object* v_inst_1676_){
_start:
{
lean_object* v_str_1677_; lean_object* v_startInclusive_1678_; lean_object* v___x_1679_; lean_object* v___x_1680_; lean_object* v___x_1682_; uint8_t v_isShared_1683_; uint8_t v_isSharedCheck_1688_; 
v_str_1677_ = lean_ctor_get(v_s_1674_, 0);
lean_inc_ref(v_str_1677_);
v_startInclusive_1678_ = lean_ctor_get(v_s_1674_, 1);
lean_inc(v_startInclusive_1678_);
v___x_1679_ = lean_unsigned_to_nat(0u);
v___x_1680_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1674_, v___x_1679_, v_inst_1676_);
v_isSharedCheck_1688_ = !lean_is_exclusive(v_s_1674_);
if (v_isSharedCheck_1688_ == 0)
{
lean_object* v_unused_1689_; lean_object* v_unused_1690_; lean_object* v_unused_1691_; 
v_unused_1689_ = lean_ctor_get(v_s_1674_, 2);
lean_dec(v_unused_1689_);
v_unused_1690_ = lean_ctor_get(v_s_1674_, 1);
lean_dec(v_unused_1690_);
v_unused_1691_ = lean_ctor_get(v_s_1674_, 0);
lean_dec(v_unused_1691_);
v___x_1682_ = v_s_1674_;
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
else
{
lean_dec(v_s_1674_);
v___x_1682_ = lean_box(0);
v_isShared_1683_ = v_isSharedCheck_1688_;
goto v_resetjp_1681_;
}
v_resetjp_1681_:
{
lean_object* v___x_1684_; lean_object* v___x_1686_; 
v___x_1684_ = lean_nat_add(v_startInclusive_1678_, v___x_1680_);
lean_dec(v___x_1680_);
if (v_isShared_1683_ == 0)
{
lean_ctor_set(v___x_1682_, 2, v___x_1684_);
v___x_1686_ = v___x_1682_;
goto v_reusejp_1685_;
}
else
{
lean_object* v_reuseFailAlloc_1687_; 
v_reuseFailAlloc_1687_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1687_, 0, v_str_1677_);
lean_ctor_set(v_reuseFailAlloc_1687_, 1, v_startInclusive_1678_);
lean_ctor_set(v_reuseFailAlloc_1687_, 2, v___x_1684_);
v___x_1686_ = v_reuseFailAlloc_1687_;
goto v_reusejp_1685_;
}
v_reusejp_1685_:
{
return v___x_1686_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___boxed(lean_object* v_00_u03c1_1692_, lean_object* v_s_1693_, lean_object* v_pat_1694_, lean_object* v_inst_1695_){
_start:
{
lean_object* v_res_1696_; 
v_res_1696_ = l_String_Slice_takeWhile(v_00_u03c1_1692_, v_s_1693_, v_pat_1694_, v_inst_1695_);
lean_dec(v_pat_1694_);
return v_res_1696_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1(lean_object* v___x_1697_, lean_object* v_x1_1698_, lean_object* v_x2_1699_, lean_object* v_x3_1700_){
_start:
{
if (lean_obj_tag(v_x1_1698_) == 0)
{
lean_object* v___x_1701_; 
v___x_1701_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1697_);
return v___x_1701_;
}
else
{
lean_object* v_startPos_1702_; lean_object* v___x_1703_; lean_object* v___x_1704_; 
lean_dec(v___x_1697_);
v_startPos_1702_ = lean_ctor_get(v_x1_1698_, 0);
lean_inc(v_startPos_1702_);
v___x_1703_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1703_, 0, v_startPos_1702_);
v___x_1704_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1704_, 0, v___x_1703_);
return v___x_1704_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1___boxed(lean_object* v___x_1705_, lean_object* v_x1_1706_, lean_object* v_x2_1707_, lean_object* v_x3_1708_){
_start:
{
lean_object* v_res_1709_; 
v_res_1709_ = l_String_Slice_find_x3f___redArg___lam__1(v___x_1705_, v_x1_1706_, v_x2_1707_, v_x3_1708_);
lean_dec(v_x3_1708_);
lean_dec_ref(v_x1_1706_);
return v_res_1709_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg(lean_object* v_inst_1712_, lean_object* v_s_1713_, lean_object* v_inst_1714_){
_start:
{
lean_object* v___f_1715_; lean_object* v_searcher_1716_; lean_object* v___x_1717_; lean_object* v___f_1718_; lean_object* v___x_1719_; 
v___f_1715_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1713_);
v_searcher_1716_ = lean_apply_1(v_inst_1714_, v_s_1713_);
v___x_1717_ = lean_box(0);
v___f_1718_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1719_ = lean_apply_7(v_inst_1712_, v_s_1713_, v___f_1715_, lean_box(0), lean_box(0), v_searcher_1716_, v___x_1717_, v___f_1718_);
return v___x_1719_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f(lean_object* v_00_u03c1_1720_, lean_object* v_00_u03c3_1721_, lean_object* v_inst_1722_, lean_object* v_inst_1723_, lean_object* v_s_1724_, lean_object* v_pat_1725_, lean_object* v_inst_1726_){
_start:
{
lean_object* v___f_1727_; lean_object* v_searcher_1728_; lean_object* v___x_1729_; lean_object* v___f_1730_; lean_object* v___x_1731_; 
v___f_1727_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1724_);
v_searcher_1728_ = lean_apply_1(v_inst_1726_, v_s_1724_);
v___x_1729_ = lean_box(0);
v___f_1730_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1731_ = lean_apply_7(v_inst_1723_, v_s_1724_, v___f_1727_, lean_box(0), lean_box(0), v_searcher_1728_, v___x_1729_, v___f_1730_);
return v___x_1731_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___boxed(lean_object* v_00_u03c1_1732_, lean_object* v_00_u03c3_1733_, lean_object* v_inst_1734_, lean_object* v_inst_1735_, lean_object* v_s_1736_, lean_object* v_pat_1737_, lean_object* v_inst_1738_){
_start:
{
lean_object* v_res_1739_; 
v_res_1739_ = l_String_Slice_find_x3f(v_00_u03c1_1732_, v_00_u03c3_1733_, v_inst_1734_, v_inst_1735_, v_s_1736_, v_pat_1737_, v_inst_1738_);
lean_dec(v_pat_1737_);
lean_dec(v_inst_1734_);
return v_res_1739_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___redArg(lean_object* v_inst_1740_, lean_object* v_s_1741_, lean_object* v_inst_1742_){
_start:
{
lean_object* v___f_1743_; lean_object* v_searcher_1744_; lean_object* v___x_1745_; lean_object* v___f_1746_; lean_object* v___x_1747_; 
v___f_1743_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1741_, 2);
v_searcher_1744_ = lean_apply_1(v_inst_1742_, v_s_1741_);
v___x_1745_ = lean_box(0);
v___f_1746_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1747_ = lean_apply_7(v_inst_1740_, v_s_1741_, v___f_1743_, lean_box(0), lean_box(0), v_searcher_1744_, v___x_1745_, v___f_1746_);
if (lean_obj_tag(v___x_1747_) == 0)
{
lean_object* v_startInclusive_1748_; lean_object* v_endExclusive_1749_; lean_object* v___x_1750_; 
v_startInclusive_1748_ = lean_ctor_get(v_s_1741_, 1);
lean_inc(v_startInclusive_1748_);
v_endExclusive_1749_ = lean_ctor_get(v_s_1741_, 2);
lean_inc(v_endExclusive_1749_);
lean_dec_ref(v_s_1741_);
v___x_1750_ = lean_nat_sub(v_endExclusive_1749_, v_startInclusive_1748_);
lean_dec(v_startInclusive_1748_);
lean_dec(v_endExclusive_1749_);
return v___x_1750_;
}
else
{
lean_object* v_val_1751_; 
lean_dec_ref(v_s_1741_);
v_val_1751_ = lean_ctor_get(v___x_1747_, 0);
lean_inc(v_val_1751_);
lean_dec_ref_known(v___x_1747_, 1);
return v_val_1751_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find(lean_object* v_00_u03c1_1752_, lean_object* v_00_u03c3_1753_, lean_object* v_inst_1754_, lean_object* v_inst_1755_, lean_object* v_s_1756_, lean_object* v_pat_1757_, lean_object* v_inst_1758_){
_start:
{
lean_object* v___f_1759_; lean_object* v_searcher_1760_; lean_object* v___x_1761_; lean_object* v___f_1762_; lean_object* v___x_1763_; 
v___f_1759_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1756_, 2);
v_searcher_1760_ = lean_apply_1(v_inst_1758_, v_s_1756_);
v___x_1761_ = lean_box(0);
v___f_1762_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1763_ = lean_apply_7(v_inst_1755_, v_s_1756_, v___f_1759_, lean_box(0), lean_box(0), v_searcher_1760_, v___x_1761_, v___f_1762_);
if (lean_obj_tag(v___x_1763_) == 0)
{
lean_object* v_startInclusive_1764_; lean_object* v_endExclusive_1765_; lean_object* v___x_1766_; 
v_startInclusive_1764_ = lean_ctor_get(v_s_1756_, 1);
lean_inc(v_startInclusive_1764_);
v_endExclusive_1765_ = lean_ctor_get(v_s_1756_, 2);
lean_inc(v_endExclusive_1765_);
lean_dec_ref(v_s_1756_);
v___x_1766_ = lean_nat_sub(v_endExclusive_1765_, v_startInclusive_1764_);
lean_dec(v_startInclusive_1764_);
lean_dec(v_endExclusive_1765_);
return v___x_1766_;
}
else
{
lean_object* v_val_1767_; 
lean_dec_ref(v_s_1756_);
v_val_1767_ = lean_ctor_get(v___x_1763_, 0);
lean_inc(v_val_1767_);
lean_dec_ref_known(v___x_1763_, 1);
return v_val_1767_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___boxed(lean_object* v_00_u03c1_1768_, lean_object* v_00_u03c3_1769_, lean_object* v_inst_1770_, lean_object* v_inst_1771_, lean_object* v_s_1772_, lean_object* v_pat_1773_, lean_object* v_inst_1774_){
_start:
{
lean_object* v_res_1775_; 
v_res_1775_ = l_String_Slice_find(v_00_u03c1_1768_, v_00_u03c3_1769_, v_inst_1770_, v_inst_1771_, v_s_1772_, v_pat_1773_, v_inst_1774_);
lean_dec(v_pat_1773_);
lean_dec(v_inst_1770_);
return v_res_1775_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1(uint8_t v___x_1779_, lean_object* v_x1_1780_, lean_object* v_x2_1781_, uint8_t v_x3_1782_){
_start:
{
if (lean_obj_tag(v_x1_1780_) == 1)
{
lean_object* v___x_1783_; 
v___x_1783_ = ((lean_object*)(l_String_Slice_contains___redArg___lam__1___closed__0));
return v___x_1783_;
}
else
{
lean_object* v___x_1784_; lean_object* v___x_1785_; 
v___x_1784_ = lean_box(v___x_1779_);
v___x_1785_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1785_, 0, v___x_1784_);
return v___x_1785_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1___boxed(lean_object* v___x_1786_, lean_object* v_x1_1787_, lean_object* v_x2_1788_, lean_object* v_x3_1789_){
_start:
{
uint8_t v___x_82__boxed_1790_; uint8_t v_x3_85__boxed_1791_; lean_object* v_res_1792_; 
v___x_82__boxed_1790_ = lean_unbox(v___x_1786_);
v_x3_85__boxed_1791_ = lean_unbox(v_x3_1789_);
v_res_1792_ = l_String_Slice_contains___redArg___lam__1(v___x_82__boxed_1790_, v_x1_1787_, v_x2_1788_, v_x3_85__boxed_1791_);
lean_dec_ref(v_x1_1787_);
return v_res_1792_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___redArg(lean_object* v_inst_1796_, lean_object* v_s_1797_, lean_object* v_inst_1798_){
_start:
{
lean_object* v___f_1799_; lean_object* v_searcher_1800_; uint8_t v___x_1801_; lean_object* v___f_1802_; lean_object* v___x_1803_; lean_object* v___x_1804_; uint8_t v___x_1805_; 
v___f_1799_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1797_);
v_searcher_1800_ = lean_apply_1(v_inst_1798_, v_s_1797_);
v___x_1801_ = 0;
v___f_1802_ = ((lean_object*)(l_String_Slice_contains___redArg___closed__0));
v___x_1803_ = lean_box(v___x_1801_);
v___x_1804_ = lean_apply_7(v_inst_1796_, v_s_1797_, v___f_1799_, lean_box(0), lean_box(0), v_searcher_1800_, v___x_1803_, v___f_1802_);
v___x_1805_ = lean_unbox(v___x_1804_);
return v___x_1805_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___boxed(lean_object* v_inst_1806_, lean_object* v_s_1807_, lean_object* v_inst_1808_){
_start:
{
uint8_t v_res_1809_; lean_object* v_r_1810_; 
v_res_1809_ = l_String_Slice_contains___redArg(v_inst_1806_, v_s_1807_, v_inst_1808_);
v_r_1810_ = lean_box(v_res_1809_);
return v_r_1810_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains(lean_object* v_00_u03c1_1811_, lean_object* v_00_u03c3_1812_, lean_object* v_inst_1813_, lean_object* v_inst_1814_, lean_object* v_s_1815_, lean_object* v_pat_1816_, lean_object* v_inst_1817_){
_start:
{
uint8_t v___x_1818_; 
v___x_1818_ = l_String_Slice_contains___redArg(v_inst_1814_, v_s_1815_, v_inst_1817_);
return v___x_1818_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___boxed(lean_object* v_00_u03c1_1819_, lean_object* v_00_u03c3_1820_, lean_object* v_inst_1821_, lean_object* v_inst_1822_, lean_object* v_s_1823_, lean_object* v_pat_1824_, lean_object* v_inst_1825_){
_start:
{
uint8_t v_res_1826_; lean_object* v_r_1827_; 
v_res_1826_ = l_String_Slice_contains(v_00_u03c1_1819_, v_00_u03c3_1820_, v_inst_1821_, v_inst_1822_, v_s_1823_, v_pat_1824_, v_inst_1825_);
lean_dec(v_pat_1824_);
lean_dec(v_inst_1821_);
v_r_1827_ = lean_box(v_res_1826_);
return v_r_1827_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any___redArg(lean_object* v_inst_1828_, lean_object* v_s_1829_, lean_object* v_inst_1830_){
_start:
{
uint8_t v___x_1831_; 
v___x_1831_ = l_String_Slice_contains___redArg(v_inst_1828_, v_s_1829_, v_inst_1830_);
return v___x_1831_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___redArg___boxed(lean_object* v_inst_1832_, lean_object* v_s_1833_, lean_object* v_inst_1834_){
_start:
{
uint8_t v_res_1835_; lean_object* v_r_1836_; 
v_res_1835_ = l_String_Slice_any___redArg(v_inst_1832_, v_s_1833_, v_inst_1834_);
v_r_1836_ = lean_box(v_res_1835_);
return v_r_1836_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any(lean_object* v_00_u03c1_1837_, lean_object* v_00_u03c3_1838_, lean_object* v_inst_1839_, lean_object* v_inst_1840_, lean_object* v_s_1841_, lean_object* v_pat_1842_, lean_object* v_inst_1843_){
_start:
{
uint8_t v___x_1844_; 
v___x_1844_ = l_String_Slice_contains___redArg(v_inst_1840_, v_s_1841_, v_inst_1843_);
return v___x_1844_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___boxed(lean_object* v_00_u03c1_1845_, lean_object* v_00_u03c3_1846_, lean_object* v_inst_1847_, lean_object* v_inst_1848_, lean_object* v_s_1849_, lean_object* v_pat_1850_, lean_object* v_inst_1851_){
_start:
{
uint8_t v_res_1852_; lean_object* v_r_1853_; 
v_res_1852_ = l_String_Slice_any(v_00_u03c1_1845_, v_00_u03c3_1846_, v_inst_1847_, v_inst_1848_, v_s_1849_, v_pat_1850_, v_inst_1851_);
lean_dec(v_pat_1850_);
lean_dec(v_inst_1847_);
v_r_1853_ = lean_box(v_res_1852_);
return v_r_1853_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all___redArg(lean_object* v_s_1854_, lean_object* v_inst_1855_){
_start:
{
lean_object* v_startInclusive_1856_; lean_object* v_endExclusive_1857_; lean_object* v___x_1858_; lean_object* v___x_1859_; lean_object* v___x_1860_; uint8_t v_decide_1861_; 
v_startInclusive_1856_ = lean_ctor_get(v_s_1854_, 1);
v_endExclusive_1857_ = lean_ctor_get(v_s_1854_, 2);
v___x_1858_ = lean_unsigned_to_nat(0u);
v___x_1859_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1854_, v___x_1858_, v_inst_1855_);
v___x_1860_ = lean_nat_sub(v_endExclusive_1857_, v_startInclusive_1856_);
v_decide_1861_ = lean_nat_dec_eq(v___x_1859_, v___x_1860_);
lean_dec(v___x_1860_);
lean_dec(v___x_1859_);
return v_decide_1861_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___redArg___boxed(lean_object* v_s_1862_, lean_object* v_inst_1863_){
_start:
{
uint8_t v_res_1864_; lean_object* v_r_1865_; 
v_res_1864_ = l_String_Slice_all___redArg(v_s_1862_, v_inst_1863_);
lean_dec_ref(v_s_1862_);
v_r_1865_ = lean_box(v_res_1864_);
return v_r_1865_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all(lean_object* v_00_u03c1_1866_, lean_object* v_s_1867_, lean_object* v_pat_1868_, lean_object* v_inst_1869_){
_start:
{
lean_object* v_startInclusive_1870_; lean_object* v_endExclusive_1871_; lean_object* v___x_1872_; lean_object* v___x_1873_; lean_object* v___x_1874_; uint8_t v_decide_1875_; 
v_startInclusive_1870_ = lean_ctor_get(v_s_1867_, 1);
v_endExclusive_1871_ = lean_ctor_get(v_s_1867_, 2);
v___x_1872_ = lean_unsigned_to_nat(0u);
v___x_1873_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1867_, v___x_1872_, v_inst_1869_);
v___x_1874_ = lean_nat_sub(v_endExclusive_1871_, v_startInclusive_1870_);
v_decide_1875_ = lean_nat_dec_eq(v___x_1873_, v___x_1874_);
lean_dec(v___x_1874_);
lean_dec(v___x_1873_);
return v_decide_1875_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___boxed(lean_object* v_00_u03c1_1876_, lean_object* v_s_1877_, lean_object* v_pat_1878_, lean_object* v_inst_1879_){
_start:
{
uint8_t v_res_1880_; lean_object* v_r_1881_; 
v_res_1880_ = l_String_Slice_all(v_00_u03c1_1876_, v_s_1877_, v_pat_1878_, v_inst_1879_);
lean_dec(v_pat_1878_);
lean_dec_ref(v_s_1877_);
v_r_1881_ = lean_box(v_res_1880_);
return v_r_1881_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith___redArg(lean_object* v_s_1882_, lean_object* v_inst_1883_){
_start:
{
lean_object* v_endsWith_1884_; lean_object* v___x_1885_; uint8_t v___x_1886_; 
v_endsWith_1884_ = lean_ctor_get(v_inst_1883_, 2);
lean_inc_ref(v_endsWith_1884_);
lean_dec_ref(v_inst_1883_);
v___x_1885_ = lean_apply_1(v_endsWith_1884_, v_s_1882_);
v___x_1886_ = lean_unbox(v___x_1885_);
return v___x_1886_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___redArg___boxed(lean_object* v_s_1887_, lean_object* v_inst_1888_){
_start:
{
uint8_t v_res_1889_; lean_object* v_r_1890_; 
v_res_1889_ = l_String_Slice_endsWith___redArg(v_s_1887_, v_inst_1888_);
v_r_1890_ = lean_box(v_res_1889_);
return v_r_1890_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith(lean_object* v_00_u03c1_1891_, lean_object* v_s_1892_, lean_object* v_pat_1893_, lean_object* v_inst_1894_){
_start:
{
lean_object* v_endsWith_1895_; lean_object* v___x_1896_; uint8_t v___x_1897_; 
v_endsWith_1895_ = lean_ctor_get(v_inst_1894_, 2);
lean_inc_ref(v_endsWith_1895_);
lean_dec_ref(v_inst_1894_);
v___x_1896_ = lean_apply_1(v_endsWith_1895_, v_s_1892_);
v___x_1897_ = lean_unbox(v___x_1896_);
return v___x_1897_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___boxed(lean_object* v_00_u03c1_1898_, lean_object* v_s_1899_, lean_object* v_pat_1900_, lean_object* v_inst_1901_){
_start:
{
uint8_t v_res_1902_; lean_object* v_r_1903_; 
v_res_1902_ = l_String_Slice_endsWith(v_00_u03c1_1898_, v_s_1899_, v_pat_1900_, v_inst_1901_);
lean_dec(v_pat_1900_);
v_r_1903_ = lean_box(v_res_1902_);
return v_r_1903_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___redArg(lean_object* v_x_1904_){
_start:
{
if (lean_obj_tag(v_x_1904_) == 0)
{
lean_object* v___x_1905_; 
v___x_1905_ = lean_unsigned_to_nat(0u);
return v___x_1905_;
}
else
{
lean_object* v___x_1906_; 
v___x_1906_ = lean_unsigned_to_nat(1u);
return v___x_1906_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___redArg___boxed(lean_object* v_x_1907_){
_start:
{
lean_object* v_res_1908_; 
v_res_1908_ = l_String_Slice_RevSplitIterator_ctorIdx___redArg(v_x_1907_);
lean_dec(v_x_1907_);
return v_res_1908_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx(lean_object* v_00_u03c3_1909_, lean_object* v_00_u03c1_1910_, lean_object* v_pat_1911_, lean_object* v_s_1912_, lean_object* v_inst_1913_, lean_object* v_x_1914_){
_start:
{
lean_object* v___x_1915_; 
v___x_1915_ = l_String_Slice_RevSplitIterator_ctorIdx___redArg(v_x_1914_);
return v___x_1915_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___boxed(lean_object* v_00_u03c3_1916_, lean_object* v_00_u03c1_1917_, lean_object* v_pat_1918_, lean_object* v_s_1919_, lean_object* v_inst_1920_, lean_object* v_x_1921_){
_start:
{
lean_object* v_res_1922_; 
v_res_1922_ = l_String_Slice_RevSplitIterator_ctorIdx(v_00_u03c3_1916_, v_00_u03c1_1917_, v_pat_1918_, v_s_1919_, v_inst_1920_, v_x_1921_);
lean_dec(v_x_1921_);
lean_dec(v_inst_1920_);
lean_dec_ref(v_s_1919_);
lean_dec(v_pat_1918_);
return v_res_1922_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___redArg(lean_object* v_t_1923_, lean_object* v_k_1924_){
_start:
{
if (lean_obj_tag(v_t_1923_) == 0)
{
lean_object* v_currPos_1925_; lean_object* v_searcher_1926_; lean_object* v___x_1927_; 
v_currPos_1925_ = lean_ctor_get(v_t_1923_, 0);
lean_inc(v_currPos_1925_);
v_searcher_1926_ = lean_ctor_get(v_t_1923_, 1);
lean_inc(v_searcher_1926_);
lean_dec_ref_known(v_t_1923_, 2);
v___x_1927_ = lean_apply_2(v_k_1924_, v_currPos_1925_, v_searcher_1926_);
return v___x_1927_;
}
else
{
return v_k_1924_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim(lean_object* v_00_u03c3_1928_, lean_object* v_00_u03c1_1929_, lean_object* v_pat_1930_, lean_object* v_s_1931_, lean_object* v_inst_1932_, lean_object* v_motive_1933_, lean_object* v_ctorIdx_1934_, lean_object* v_t_1935_, lean_object* v_h_1936_, lean_object* v_k_1937_){
_start:
{
lean_object* v___x_1938_; 
v___x_1938_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1935_, v_k_1937_);
return v___x_1938_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_1939_, lean_object* v_00_u03c1_1940_, lean_object* v_pat_1941_, lean_object* v_s_1942_, lean_object* v_inst_1943_, lean_object* v_motive_1944_, lean_object* v_ctorIdx_1945_, lean_object* v_t_1946_, lean_object* v_h_1947_, lean_object* v_k_1948_){
_start:
{
lean_object* v_res_1949_; 
v_res_1949_ = l_String_Slice_RevSplitIterator_ctorElim(v_00_u03c3_1939_, v_00_u03c1_1940_, v_pat_1941_, v_s_1942_, v_inst_1943_, v_motive_1944_, v_ctorIdx_1945_, v_t_1946_, v_h_1947_, v_k_1948_);
lean_dec(v_ctorIdx_1945_);
lean_dec(v_inst_1943_);
lean_dec_ref(v_s_1942_);
lean_dec(v_pat_1941_);
return v_res_1949_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___redArg(lean_object* v_t_1950_, lean_object* v_operating_1951_){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1950_, v_operating_1951_);
return v___x_1952_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim(lean_object* v_00_u03c3_1953_, lean_object* v_00_u03c1_1954_, lean_object* v_pat_1955_, lean_object* v_s_1956_, lean_object* v_inst_1957_, lean_object* v_motive_1958_, lean_object* v_t_1959_, lean_object* v_h_1960_, lean_object* v_operating_1961_){
_start:
{
lean_object* v___x_1962_; 
v___x_1962_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1959_, v_operating_1961_);
return v___x_1962_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_1963_, lean_object* v_00_u03c1_1964_, lean_object* v_pat_1965_, lean_object* v_s_1966_, lean_object* v_inst_1967_, lean_object* v_motive_1968_, lean_object* v_t_1969_, lean_object* v_h_1970_, lean_object* v_operating_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_String_Slice_RevSplitIterator_operating_elim(v_00_u03c3_1963_, v_00_u03c1_1964_, v_pat_1965_, v_s_1966_, v_inst_1967_, v_motive_1968_, v_t_1969_, v_h_1970_, v_operating_1971_);
lean_dec(v_inst_1967_);
lean_dec_ref(v_s_1966_);
lean_dec(v_pat_1965_);
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___redArg(lean_object* v_t_1973_, lean_object* v_atEnd_1974_){
_start:
{
lean_object* v___x_1975_; 
v___x_1975_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1973_, v_atEnd_1974_);
return v___x_1975_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim(lean_object* v_00_u03c3_1976_, lean_object* v_00_u03c1_1977_, lean_object* v_pat_1978_, lean_object* v_s_1979_, lean_object* v_inst_1980_, lean_object* v_motive_1981_, lean_object* v_t_1982_, lean_object* v_h_1983_, lean_object* v_atEnd_1984_){
_start:
{
lean_object* v___x_1985_; 
v___x_1985_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1982_, v_atEnd_1984_);
return v___x_1985_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_1986_, lean_object* v_00_u03c1_1987_, lean_object* v_pat_1988_, lean_object* v_s_1989_, lean_object* v_inst_1990_, lean_object* v_motive_1991_, lean_object* v_t_1992_, lean_object* v_h_1993_, lean_object* v_atEnd_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_String_Slice_RevSplitIterator_atEnd_elim(v_00_u03c3_1986_, v_00_u03c1_1987_, v_pat_1988_, v_s_1989_, v_inst_1990_, v_motive_1991_, v_t_1992_, v_h_1993_, v_atEnd_1994_);
lean_dec(v_inst_1990_);
lean_dec_ref(v_s_1989_);
lean_dec(v_pat_1988_);
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg(){
_start:
{
lean_object* v___x_1997_; 
v___x_1997_ = lean_box(1);
return v___x_1997_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg___boxed(lean_object* v___dummy_1998_){
_start:
{
lean_object* v_res_1999_; 
v_res_1999_ = l_String_Slice_instInhabitedRevSplitIterator_default___redArg();
return v_res_1999_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default(lean_object* v_00_u03c3_2000_, lean_object* v_00_u03c1_2001_, lean_object* v_pat_2002_, lean_object* v_s_2003_, lean_object* v_inst_2004_){
_start:
{
lean_object* v___x_2005_; 
v___x_2005_ = lean_box(1);
return v___x_2005_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___boxed(lean_object* v_00_u03c3_2006_, lean_object* v_00_u03c1_2007_, lean_object* v_pat_2008_, lean_object* v_s_2009_, lean_object* v_inst_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_String_Slice_instInhabitedRevSplitIterator_default(v_00_u03c3_2006_, v_00_u03c1_2007_, v_pat_2008_, v_s_2009_, v_inst_2010_);
lean_dec(v_inst_2010_);
lean_dec_ref(v_s_2009_);
lean_dec(v_pat_2008_);
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg(){
_start:
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_box(1);
return v___x_2013_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg___boxed(lean_object* v___dummy_2014_){
_start:
{
lean_object* v_res_2015_; 
v_res_2015_ = l_String_Slice_instInhabitedRevSplitIterator___redArg();
return v_res_2015_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator(lean_object* v_a_2016_, lean_object* v_a_2017_, lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_){
_start:
{
lean_object* v___x_2021_; 
v___x_2021_ = lean_box(1);
return v___x_2021_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___boxed(lean_object* v_a_2022_, lean_object* v_a_2023_, lean_object* v_a_2024_, lean_object* v_a_2025_, lean_object* v_a_2026_){
_start:
{
lean_object* v_res_2027_; 
v_res_2027_ = l_String_Slice_instInhabitedRevSplitIterator(v_a_2022_, v_a_2023_, v_a_2024_, v_a_2025_, v_a_2026_);
lean_dec(v_a_2026_);
lean_dec_ref(v_a_2025_);
lean_dec(v_a_2024_);
return v_res_2027_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0(lean_object* v_inst_2028_, lean_object* v_s_2029_, lean_object* v_inst_2030_, lean_object* v_x_2031_){
_start:
{
if (lean_obj_tag(v_x_2031_) == 0)
{
lean_object* v_currPos_2032_; lean_object* v_searcher_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2091_; 
v_currPos_2032_ = lean_ctor_get(v_x_2031_, 0);
v_searcher_2033_ = lean_ctor_get(v_x_2031_, 1);
v_isSharedCheck_2091_ = !lean_is_exclusive(v_x_2031_);
if (v_isSharedCheck_2091_ == 0)
{
v___x_2035_ = v_x_2031_;
v_isShared_2036_ = v_isSharedCheck_2091_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_searcher_2033_);
lean_inc(v_currPos_2032_);
lean_dec(v_x_2031_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2091_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; 
lean_inc_ref(v_s_2029_);
v___x_2037_ = lean_apply_2(v_inst_2028_, v_s_2029_, v_searcher_2033_);
switch(lean_obj_tag(v___x_2037_))
{
case 0:
{
lean_object* v_out_2038_; 
v_out_2038_ = lean_ctor_get(v___x_2037_, 1);
lean_inc(v_out_2038_);
if (lean_obj_tag(v_out_2038_) == 0)
{
lean_object* v_it_2039_; lean_object* v___x_2041_; 
lean_dec_ref_known(v_out_2038_, 2);
lean_dec_ref(v_s_2029_);
v_it_2039_ = lean_ctor_get(v___x_2037_, 0);
lean_inc(v_it_2039_);
lean_dec_ref_known(v___x_2037_, 2);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v_it_2039_);
v___x_2041_ = v___x_2035_;
goto v_reusejp_2040_;
}
else
{
lean_object* v_reuseFailAlloc_2044_; 
v_reuseFailAlloc_2044_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2044_, 0, v_currPos_2032_);
lean_ctor_set(v_reuseFailAlloc_2044_, 1, v_it_2039_);
v___x_2041_ = v_reuseFailAlloc_2044_;
goto v_reusejp_2040_;
}
v_reusejp_2040_:
{
lean_object* v___x_2042_; lean_object* v___x_2043_; 
v___x_2042_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2042_, 0, v___x_2041_);
v___x_2043_ = lean_apply_2(v_inst_2030_, lean_box(0), v___x_2042_);
return v___x_2043_;
}
}
else
{
lean_object* v_it_2045_; lean_object* v___x_2047_; uint8_t v_isShared_2048_; uint8_t v_isSharedCheck_2059_; 
v_it_2045_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2059_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2059_ == 0)
{
lean_object* v_unused_2060_; 
v_unused_2060_ = lean_ctor_get(v___x_2037_, 1);
lean_dec(v_unused_2060_);
v___x_2047_ = v___x_2037_;
v_isShared_2048_ = v_isSharedCheck_2059_;
goto v_resetjp_2046_;
}
else
{
lean_inc(v_it_2045_);
lean_dec(v___x_2037_);
v___x_2047_ = lean_box(0);
v_isShared_2048_ = v_isSharedCheck_2059_;
goto v_resetjp_2046_;
}
v_resetjp_2046_:
{
lean_object* v_startPos_2049_; lean_object* v_endPos_2050_; lean_object* v_slice_2051_; lean_object* v_nextIt_2053_; 
v_startPos_2049_ = lean_ctor_get(v_out_2038_, 0);
lean_inc(v_startPos_2049_);
v_endPos_2050_ = lean_ctor_get(v_out_2038_, 1);
lean_inc(v_endPos_2050_);
lean_dec_ref_known(v_out_2038_, 2);
v_slice_2051_ = l_String_Slice_slice_x21(v_s_2029_, v_endPos_2050_, v_currPos_2032_);
lean_dec(v_currPos_2032_);
lean_dec(v_endPos_2050_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v_it_2045_);
lean_ctor_set(v___x_2035_, 0, v_startPos_2049_);
v_nextIt_2053_ = v___x_2035_;
goto v_reusejp_2052_;
}
else
{
lean_object* v_reuseFailAlloc_2058_; 
v_reuseFailAlloc_2058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2058_, 0, v_startPos_2049_);
lean_ctor_set(v_reuseFailAlloc_2058_, 1, v_it_2045_);
v_nextIt_2053_ = v_reuseFailAlloc_2058_;
goto v_reusejp_2052_;
}
v_reusejp_2052_:
{
lean_object* v___x_2055_; 
if (v_isShared_2048_ == 0)
{
lean_ctor_set(v___x_2047_, 1, v_slice_2051_);
lean_ctor_set(v___x_2047_, 0, v_nextIt_2053_);
v___x_2055_ = v___x_2047_;
goto v_reusejp_2054_;
}
else
{
lean_object* v_reuseFailAlloc_2057_; 
v_reuseFailAlloc_2057_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2057_, 0, v_nextIt_2053_);
lean_ctor_set(v_reuseFailAlloc_2057_, 1, v_slice_2051_);
v___x_2055_ = v_reuseFailAlloc_2057_;
goto v_reusejp_2054_;
}
v_reusejp_2054_:
{
lean_object* v___x_2056_; 
v___x_2056_ = lean_apply_2(v_inst_2030_, lean_box(0), v___x_2055_);
return v___x_2056_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2061_; lean_object* v___x_2063_; uint8_t v_isShared_2064_; uint8_t v_isSharedCheck_2072_; 
lean_dec_ref(v_s_2029_);
v_it_2061_ = lean_ctor_get(v___x_2037_, 0);
v_isSharedCheck_2072_ = !lean_is_exclusive(v___x_2037_);
if (v_isSharedCheck_2072_ == 0)
{
v___x_2063_ = v___x_2037_;
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
else
{
lean_inc(v_it_2061_);
lean_dec(v___x_2037_);
v___x_2063_ = lean_box(0);
v_isShared_2064_ = v_isSharedCheck_2072_;
goto v_resetjp_2062_;
}
v_resetjp_2062_:
{
lean_object* v___x_2066_; 
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 1, v_it_2061_);
v___x_2066_ = v___x_2035_;
goto v_reusejp_2065_;
}
else
{
lean_object* v_reuseFailAlloc_2071_; 
v_reuseFailAlloc_2071_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2071_, 0, v_currPos_2032_);
lean_ctor_set(v_reuseFailAlloc_2071_, 1, v_it_2061_);
v___x_2066_ = v_reuseFailAlloc_2071_;
goto v_reusejp_2065_;
}
v_reusejp_2065_:
{
lean_object* v___x_2068_; 
if (v_isShared_2064_ == 0)
{
lean_ctor_set(v___x_2063_, 0, v___x_2066_);
v___x_2068_ = v___x_2063_;
goto v_reusejp_2067_;
}
else
{
lean_object* v_reuseFailAlloc_2070_; 
v_reuseFailAlloc_2070_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2070_, 0, v___x_2066_);
v___x_2068_ = v_reuseFailAlloc_2070_;
goto v_reusejp_2067_;
}
v_reusejp_2067_:
{
lean_object* v___x_2069_; 
v___x_2069_ = lean_apply_2(v_inst_2030_, lean_box(0), v___x_2068_);
return v___x_2069_;
}
}
}
}
default: 
{
lean_object* v___x_2073_; uint8_t v_decide_2074_; 
lean_del_object(v___x_2035_);
v___x_2073_ = lean_unsigned_to_nat(0u);
v_decide_2074_ = lean_nat_dec_eq(v_currPos_2032_, v___x_2073_);
if (v_decide_2074_ == 0)
{
lean_object* v_str_2075_; lean_object* v_startInclusive_2076_; lean_object* v___x_2078_; uint8_t v_isShared_2079_; uint8_t v_isSharedCheck_2087_; 
v_str_2075_ = lean_ctor_get(v_s_2029_, 0);
v_startInclusive_2076_ = lean_ctor_get(v_s_2029_, 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_s_2029_);
if (v_isSharedCheck_2087_ == 0)
{
lean_object* v_unused_2088_; 
v_unused_2088_ = lean_ctor_get(v_s_2029_, 2);
lean_dec(v_unused_2088_);
v___x_2078_ = v_s_2029_;
v_isShared_2079_ = v_isSharedCheck_2087_;
goto v_resetjp_2077_;
}
else
{
lean_inc(v_startInclusive_2076_);
lean_inc(v_str_2075_);
lean_dec(v_s_2029_);
v___x_2078_ = lean_box(0);
v_isShared_2079_ = v_isSharedCheck_2087_;
goto v_resetjp_2077_;
}
v_resetjp_2077_:
{
lean_object* v___x_2080_; lean_object* v_slice_2082_; 
v___x_2080_ = lean_nat_add(v_startInclusive_2076_, v_currPos_2032_);
lean_dec(v_currPos_2032_);
if (v_isShared_2079_ == 0)
{
lean_ctor_set(v___x_2078_, 2, v___x_2080_);
v_slice_2082_ = v___x_2078_;
goto v_reusejp_2081_;
}
else
{
lean_object* v_reuseFailAlloc_2086_; 
v_reuseFailAlloc_2086_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2086_, 0, v_str_2075_);
lean_ctor_set(v_reuseFailAlloc_2086_, 1, v_startInclusive_2076_);
lean_ctor_set(v_reuseFailAlloc_2086_, 2, v___x_2080_);
v_slice_2082_ = v_reuseFailAlloc_2086_;
goto v_reusejp_2081_;
}
v_reusejp_2081_:
{
lean_object* v___x_2083_; lean_object* v___x_2084_; lean_object* v___x_2085_; 
v___x_2083_ = lean_box(1);
v___x_2084_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2084_, 0, v___x_2083_);
lean_ctor_set(v___x_2084_, 1, v_slice_2082_);
v___x_2085_ = lean_apply_2(v_inst_2030_, lean_box(0), v___x_2084_);
return v___x_2085_;
}
}
}
else
{
lean_object* v___x_2089_; lean_object* v___x_2090_; 
lean_dec(v_currPos_2032_);
lean_dec_ref(v_s_2029_);
v___x_2089_ = lean_box(2);
v___x_2090_ = lean_apply_2(v_inst_2030_, lean_box(0), v___x_2089_);
return v___x_2090_;
}
}
}
}
}
else
{
lean_object* v___x_2092_; lean_object* v___x_2093_; 
lean_dec_ref(v_s_2029_);
lean_dec(v_inst_2028_);
v___x_2092_ = lean_box(2);
v___x_2093_ = lean_apply_2(v_inst_2030_, lean_box(0), v___x_2092_);
return v___x_2093_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg(lean_object* v_inst_2094_, lean_object* v_s_2095_, lean_object* v_inst_2096_){
_start:
{
lean_object* v___f_2097_; 
v___f_2097_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2097_, 0, v_inst_2094_);
lean_closure_set(v___f_2097_, 1, v_s_2095_);
lean_closure_set(v___f_2097_, 2, v_inst_2096_);
return v___f_2097_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure(lean_object* v_00_u03c1_2098_, lean_object* v_00_u03c1_2099_, lean_object* v_00_u03c3_2100_, lean_object* v_inst_2101_, lean_object* v_inst_2102_, lean_object* v_m_2103_, lean_object* v_s_2104_, lean_object* v_inst_2105_){
_start:
{
lean_object* v___f_2106_; 
v___f_2106_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2106_, 0, v_inst_2101_);
lean_closure_set(v___f_2106_, 1, v_s_2104_);
lean_closure_set(v___f_2106_, 2, v_inst_2105_);
return v___f_2106_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___boxed(lean_object* v_00_u03c1_2107_, lean_object* v_00_u03c1_2108_, lean_object* v_00_u03c3_2109_, lean_object* v_inst_2110_, lean_object* v_inst_2111_, lean_object* v_m_2112_, lean_object* v_s_2113_, lean_object* v_inst_2114_){
_start:
{
lean_object* v_res_2115_; 
v_res_2115_ = l_String_Slice_RevSplitIterator_instIteratorOfPure(v_00_u03c1_2107_, v_00_u03c1_2108_, v_00_u03c3_2109_, v_inst_2110_, v_inst_2111_, v_m_2112_, v_s_2113_, v_inst_2114_);
lean_dec(v_inst_2111_);
lean_dec(v_00_u03c1_2108_);
return v_res_2115_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(lean_object* v_x_2116_){
_start:
{
if (lean_obj_tag(v_x_2116_) == 0)
{
lean_object* v_searcher_2117_; lean_object* v___x_2118_; 
v_searcher_2117_ = lean_ctor_get(v_x_2116_, 1);
lean_inc(v_searcher_2117_);
v___x_2118_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2118_, 0, v_searcher_2117_);
return v___x_2118_;
}
else
{
lean_object* v___x_2119_; 
v___x_2119_ = lean_box(0);
return v___x_2119_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg___boxed(lean_object* v_x_2120_){
_start:
{
lean_object* v_res_2121_; 
v_res_2121_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2120_);
lean_dec(v_x_2120_);
return v_res_2121_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(lean_object* v_00_u03c1_2122_, lean_object* v_00_u03c1_2123_, lean_object* v_00_u03c3_2124_, lean_object* v_inst_2125_, lean_object* v_s_2126_, lean_object* v_x_2127_){
_start:
{
lean_object* v___x_2128_; 
v___x_2128_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2127_);
return v___x_2128_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___boxed(lean_object* v_00_u03c1_2129_, lean_object* v_00_u03c1_2130_, lean_object* v_00_u03c3_2131_, lean_object* v_inst_2132_, lean_object* v_s_2133_, lean_object* v_x_2134_){
_start:
{
lean_object* v_res_2135_; 
v_res_2135_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(v_00_u03c1_2129_, v_00_u03c1_2130_, v_00_u03c3_2131_, v_inst_2132_, v_s_2133_, v_x_2134_);
lean_dec(v_x_2134_);
lean_dec_ref(v_s_2133_);
lean_dec(v_inst_2132_);
lean_dec(v_00_u03c1_2130_);
return v_res_2135_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(lean_object* v_x_2136_, lean_object* v_h__1_2137_, lean_object* v_h__2_2138_){
_start:
{
if (lean_obj_tag(v_x_2136_) == 0)
{
lean_object* v_currPos_2139_; lean_object* v_searcher_2140_; lean_object* v___x_2141_; 
lean_dec(v_h__2_2138_);
v_currPos_2139_ = lean_ctor_get(v_x_2136_, 0);
lean_inc(v_currPos_2139_);
v_searcher_2140_ = lean_ctor_get(v_x_2136_, 1);
lean_inc(v_searcher_2140_);
lean_dec_ref_known(v_x_2136_, 2);
v___x_2141_ = lean_apply_2(v_h__1_2137_, v_currPos_2139_, v_searcher_2140_);
return v___x_2141_;
}
else
{
lean_object* v___x_2142_; lean_object* v___x_2143_; 
lean_dec(v_h__1_2137_);
v___x_2142_ = lean_box(0);
v___x_2143_ = lean_apply_1(v_h__2_2138_, v___x_2142_);
return v___x_2143_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(lean_object* v_00_u03c1_2144_, lean_object* v_00_u03c1_2145_, lean_object* v_00_u03c3_2146_, lean_object* v_inst_2147_, lean_object* v_m_2148_, lean_object* v_s_2149_, lean_object* v_motive_2150_, lean_object* v_x_2151_, lean_object* v_h__1_2152_, lean_object* v_h__2_2153_){
_start:
{
if (lean_obj_tag(v_x_2151_) == 0)
{
lean_object* v_currPos_2154_; lean_object* v_searcher_2155_; lean_object* v___x_2156_; 
lean_dec(v_h__2_2153_);
v_currPos_2154_ = lean_ctor_get(v_x_2151_, 0);
lean_inc(v_currPos_2154_);
v_searcher_2155_ = lean_ctor_get(v_x_2151_, 1);
lean_inc(v_searcher_2155_);
lean_dec_ref_known(v_x_2151_, 2);
v___x_2156_ = lean_apply_2(v_h__1_2152_, v_currPos_2154_, v_searcher_2155_);
return v___x_2156_;
}
else
{
lean_object* v___x_2157_; lean_object* v___x_2158_; 
lean_dec(v_h__1_2152_);
v___x_2157_ = lean_box(0);
v___x_2158_ = lean_apply_1(v_h__2_2153_, v___x_2157_);
return v___x_2158_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___boxed(lean_object* v_00_u03c1_2159_, lean_object* v_00_u03c1_2160_, lean_object* v_00_u03c3_2161_, lean_object* v_inst_2162_, lean_object* v_m_2163_, lean_object* v_s_2164_, lean_object* v_motive_2165_, lean_object* v_x_2166_, lean_object* v_h__1_2167_, lean_object* v_h__2_2168_){
_start:
{
lean_object* v_res_2169_; 
v_res_2169_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(v_00_u03c1_2159_, v_00_u03c1_2160_, v_00_u03c3_2161_, v_inst_2162_, v_m_2163_, v_s_2164_, v_motive_2165_, v_x_2166_, v_h__1_2167_, v_h__2_2168_);
lean_dec_ref(v_s_2164_);
lean_dec(v_inst_2162_);
lean_dec(v_00_u03c1_2160_);
return v_res_2169_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(lean_object* v_x_2170_, lean_object* v_x_2171_, lean_object* v_h__1_2172_, lean_object* v_h__2_2173_, lean_object* v_h__3_2174_, lean_object* v_h__4_2175_, lean_object* v_h__5_2176_, lean_object* v_h__6_2177_, lean_object* v_h__7_2178_, lean_object* v_h__8_2179_){
_start:
{
if (lean_obj_tag(v_x_2170_) == 0)
{
lean_dec(v_h__8_2179_);
lean_dec(v_h__7_2178_);
lean_dec(v_h__6_2177_);
switch(lean_obj_tag(v_x_2171_))
{
case 0:
{
lean_object* v_it_2180_; 
lean_dec(v_h__5_2176_);
lean_dec(v_h__4_2175_);
lean_dec(v_h__3_2174_);
v_it_2180_ = lean_ctor_get(v_x_2171_, 0);
if (lean_obj_tag(v_it_2180_) == 0)
{
lean_object* v_currPos_2181_; lean_object* v_searcher_2182_; lean_object* v_out_2183_; lean_object* v_currPos_2184_; lean_object* v_searcher_2185_; lean_object* v___x_2186_; 
lean_inc_ref(v_it_2180_);
lean_dec(v_h__2_2173_);
v_currPos_2181_ = lean_ctor_get(v_x_2170_, 0);
lean_inc(v_currPos_2181_);
v_searcher_2182_ = lean_ctor_get(v_x_2170_, 1);
lean_inc(v_searcher_2182_);
lean_dec_ref_known(v_x_2170_, 2);
v_out_2183_ = lean_ctor_get(v_x_2171_, 1);
lean_inc(v_out_2183_);
lean_dec_ref_known(v_x_2171_, 2);
v_currPos_2184_ = lean_ctor_get(v_it_2180_, 0);
lean_inc(v_currPos_2184_);
v_searcher_2185_ = lean_ctor_get(v_it_2180_, 1);
lean_inc(v_searcher_2185_);
lean_dec_ref_known(v_it_2180_, 2);
v___x_2186_ = lean_apply_5(v_h__1_2172_, v_currPos_2181_, v_searcher_2182_, v_currPos_2184_, v_searcher_2185_, v_out_2183_);
return v___x_2186_;
}
else
{
lean_object* v_currPos_2187_; lean_object* v_searcher_2188_; lean_object* v_out_2189_; lean_object* v___x_2190_; 
lean_dec(v_h__1_2172_);
v_currPos_2187_ = lean_ctor_get(v_x_2170_, 0);
lean_inc(v_currPos_2187_);
v_searcher_2188_ = lean_ctor_get(v_x_2170_, 1);
lean_inc(v_searcher_2188_);
lean_dec_ref_known(v_x_2170_, 2);
v_out_2189_ = lean_ctor_get(v_x_2171_, 1);
lean_inc(v_out_2189_);
lean_dec_ref_known(v_x_2171_, 2);
v___x_2190_ = lean_apply_3(v_h__2_2173_, v_currPos_2187_, v_searcher_2188_, v_out_2189_);
return v___x_2190_;
}
}
case 1:
{
lean_object* v_it_2191_; 
lean_dec(v_h__5_2176_);
lean_dec(v_h__2_2173_);
lean_dec(v_h__1_2172_);
v_it_2191_ = lean_ctor_get(v_x_2171_, 0);
lean_inc(v_it_2191_);
lean_dec_ref_known(v_x_2171_, 1);
if (lean_obj_tag(v_it_2191_) == 0)
{
lean_object* v_currPos_2192_; lean_object* v_searcher_2193_; lean_object* v_currPos_2194_; lean_object* v_searcher_2195_; lean_object* v___x_2196_; 
lean_dec(v_h__4_2175_);
v_currPos_2192_ = lean_ctor_get(v_x_2170_, 0);
lean_inc(v_currPos_2192_);
v_searcher_2193_ = lean_ctor_get(v_x_2170_, 1);
lean_inc(v_searcher_2193_);
lean_dec_ref_known(v_x_2170_, 2);
v_currPos_2194_ = lean_ctor_get(v_it_2191_, 0);
lean_inc(v_currPos_2194_);
v_searcher_2195_ = lean_ctor_get(v_it_2191_, 1);
lean_inc(v_searcher_2195_);
lean_dec_ref_known(v_it_2191_, 2);
v___x_2196_ = lean_apply_4(v_h__3_2174_, v_currPos_2192_, v_searcher_2193_, v_currPos_2194_, v_searcher_2195_);
return v___x_2196_;
}
else
{
lean_object* v_currPos_2197_; lean_object* v_searcher_2198_; lean_object* v___x_2199_; 
lean_dec(v_h__3_2174_);
v_currPos_2197_ = lean_ctor_get(v_x_2170_, 0);
lean_inc(v_currPos_2197_);
v_searcher_2198_ = lean_ctor_get(v_x_2170_, 1);
lean_inc(v_searcher_2198_);
lean_dec_ref_known(v_x_2170_, 2);
v___x_2199_ = lean_apply_2(v_h__4_2175_, v_currPos_2197_, v_searcher_2198_);
return v___x_2199_;
}
}
default: 
{
lean_object* v_currPos_2200_; lean_object* v_searcher_2201_; lean_object* v___x_2202_; 
lean_dec(v_h__4_2175_);
lean_dec(v_h__3_2174_);
lean_dec(v_h__2_2173_);
lean_dec(v_h__1_2172_);
v_currPos_2200_ = lean_ctor_get(v_x_2170_, 0);
lean_inc(v_currPos_2200_);
v_searcher_2201_ = lean_ctor_get(v_x_2170_, 1);
lean_inc(v_searcher_2201_);
lean_dec_ref_known(v_x_2170_, 2);
v___x_2202_ = lean_apply_2(v_h__5_2176_, v_currPos_2200_, v_searcher_2201_);
return v___x_2202_;
}
}
}
else
{
lean_dec(v_h__5_2176_);
lean_dec(v_h__4_2175_);
lean_dec(v_h__3_2174_);
lean_dec(v_h__2_2173_);
lean_dec(v_h__1_2172_);
switch(lean_obj_tag(v_x_2171_))
{
case 0:
{
lean_object* v_it_2203_; lean_object* v_out_2204_; lean_object* v___x_2205_; 
lean_dec(v_h__8_2179_);
lean_dec(v_h__7_2178_);
v_it_2203_ = lean_ctor_get(v_x_2171_, 0);
lean_inc(v_it_2203_);
v_out_2204_ = lean_ctor_get(v_x_2171_, 1);
lean_inc(v_out_2204_);
lean_dec_ref_known(v_x_2171_, 2);
v___x_2205_ = lean_apply_2(v_h__6_2177_, v_it_2203_, v_out_2204_);
return v___x_2205_;
}
case 1:
{
lean_object* v_it_2206_; lean_object* v___x_2207_; 
lean_dec(v_h__8_2179_);
lean_dec(v_h__6_2177_);
v_it_2206_ = lean_ctor_get(v_x_2171_, 0);
lean_inc(v_it_2206_);
lean_dec_ref_known(v_x_2171_, 1);
v___x_2207_ = lean_apply_1(v_h__7_2178_, v_it_2206_);
return v___x_2207_;
}
default: 
{
lean_object* v___x_2208_; lean_object* v___x_2209_; 
lean_dec(v_h__7_2178_);
lean_dec(v_h__6_2177_);
v___x_2208_ = lean_box(0);
v___x_2209_ = lean_apply_1(v_h__8_2179_, v___x_2208_);
return v___x_2209_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(lean_object* v_00_u03c1_2210_, lean_object* v_00_u03c1_2211_, lean_object* v_00_u03c3_2212_, lean_object* v_inst_2213_, lean_object* v_m_2214_, lean_object* v_s_2215_, lean_object* v_motive_2216_, lean_object* v_x_2217_, lean_object* v_x_2218_, lean_object* v_h__1_2219_, lean_object* v_h__2_2220_, lean_object* v_h__3_2221_, lean_object* v_h__4_2222_, lean_object* v_h__5_2223_, lean_object* v_h__6_2224_, lean_object* v_h__7_2225_, lean_object* v_h__8_2226_){
_start:
{
if (lean_obj_tag(v_x_2217_) == 0)
{
lean_dec(v_h__8_2226_);
lean_dec(v_h__7_2225_);
lean_dec(v_h__6_2224_);
switch(lean_obj_tag(v_x_2218_))
{
case 0:
{
lean_object* v_it_2227_; 
lean_dec(v_h__5_2223_);
lean_dec(v_h__4_2222_);
lean_dec(v_h__3_2221_);
v_it_2227_ = lean_ctor_get(v_x_2218_, 0);
if (lean_obj_tag(v_it_2227_) == 0)
{
lean_object* v_currPos_2228_; lean_object* v_searcher_2229_; lean_object* v_out_2230_; lean_object* v_currPos_2231_; lean_object* v_searcher_2232_; lean_object* v___x_2233_; 
lean_inc_ref(v_it_2227_);
lean_dec(v_h__2_2220_);
v_currPos_2228_ = lean_ctor_get(v_x_2217_, 0);
lean_inc(v_currPos_2228_);
v_searcher_2229_ = lean_ctor_get(v_x_2217_, 1);
lean_inc(v_searcher_2229_);
lean_dec_ref_known(v_x_2217_, 2);
v_out_2230_ = lean_ctor_get(v_x_2218_, 1);
lean_inc(v_out_2230_);
lean_dec_ref_known(v_x_2218_, 2);
v_currPos_2231_ = lean_ctor_get(v_it_2227_, 0);
lean_inc(v_currPos_2231_);
v_searcher_2232_ = lean_ctor_get(v_it_2227_, 1);
lean_inc(v_searcher_2232_);
lean_dec_ref_known(v_it_2227_, 2);
v___x_2233_ = lean_apply_5(v_h__1_2219_, v_currPos_2228_, v_searcher_2229_, v_currPos_2231_, v_searcher_2232_, v_out_2230_);
return v___x_2233_;
}
else
{
lean_object* v_currPos_2234_; lean_object* v_searcher_2235_; lean_object* v_out_2236_; lean_object* v___x_2237_; 
lean_dec(v_h__1_2219_);
v_currPos_2234_ = lean_ctor_get(v_x_2217_, 0);
lean_inc(v_currPos_2234_);
v_searcher_2235_ = lean_ctor_get(v_x_2217_, 1);
lean_inc(v_searcher_2235_);
lean_dec_ref_known(v_x_2217_, 2);
v_out_2236_ = lean_ctor_get(v_x_2218_, 1);
lean_inc(v_out_2236_);
lean_dec_ref_known(v_x_2218_, 2);
v___x_2237_ = lean_apply_3(v_h__2_2220_, v_currPos_2234_, v_searcher_2235_, v_out_2236_);
return v___x_2237_;
}
}
case 1:
{
lean_object* v_it_2238_; 
lean_dec(v_h__5_2223_);
lean_dec(v_h__2_2220_);
lean_dec(v_h__1_2219_);
v_it_2238_ = lean_ctor_get(v_x_2218_, 0);
lean_inc(v_it_2238_);
lean_dec_ref_known(v_x_2218_, 1);
if (lean_obj_tag(v_it_2238_) == 0)
{
lean_object* v_currPos_2239_; lean_object* v_searcher_2240_; lean_object* v_currPos_2241_; lean_object* v_searcher_2242_; lean_object* v___x_2243_; 
lean_dec(v_h__4_2222_);
v_currPos_2239_ = lean_ctor_get(v_x_2217_, 0);
lean_inc(v_currPos_2239_);
v_searcher_2240_ = lean_ctor_get(v_x_2217_, 1);
lean_inc(v_searcher_2240_);
lean_dec_ref_known(v_x_2217_, 2);
v_currPos_2241_ = lean_ctor_get(v_it_2238_, 0);
lean_inc(v_currPos_2241_);
v_searcher_2242_ = lean_ctor_get(v_it_2238_, 1);
lean_inc(v_searcher_2242_);
lean_dec_ref_known(v_it_2238_, 2);
v___x_2243_ = lean_apply_4(v_h__3_2221_, v_currPos_2239_, v_searcher_2240_, v_currPos_2241_, v_searcher_2242_);
return v___x_2243_;
}
else
{
lean_object* v_currPos_2244_; lean_object* v_searcher_2245_; lean_object* v___x_2246_; 
lean_dec(v_h__3_2221_);
v_currPos_2244_ = lean_ctor_get(v_x_2217_, 0);
lean_inc(v_currPos_2244_);
v_searcher_2245_ = lean_ctor_get(v_x_2217_, 1);
lean_inc(v_searcher_2245_);
lean_dec_ref_known(v_x_2217_, 2);
v___x_2246_ = lean_apply_2(v_h__4_2222_, v_currPos_2244_, v_searcher_2245_);
return v___x_2246_;
}
}
default: 
{
lean_object* v_currPos_2247_; lean_object* v_searcher_2248_; lean_object* v___x_2249_; 
lean_dec(v_h__4_2222_);
lean_dec(v_h__3_2221_);
lean_dec(v_h__2_2220_);
lean_dec(v_h__1_2219_);
v_currPos_2247_ = lean_ctor_get(v_x_2217_, 0);
lean_inc(v_currPos_2247_);
v_searcher_2248_ = lean_ctor_get(v_x_2217_, 1);
lean_inc(v_searcher_2248_);
lean_dec_ref_known(v_x_2217_, 2);
v___x_2249_ = lean_apply_2(v_h__5_2223_, v_currPos_2247_, v_searcher_2248_);
return v___x_2249_;
}
}
}
else
{
lean_dec(v_h__5_2223_);
lean_dec(v_h__4_2222_);
lean_dec(v_h__3_2221_);
lean_dec(v_h__2_2220_);
lean_dec(v_h__1_2219_);
switch(lean_obj_tag(v_x_2218_))
{
case 0:
{
lean_object* v_it_2250_; lean_object* v_out_2251_; lean_object* v___x_2252_; 
lean_dec(v_h__8_2226_);
lean_dec(v_h__7_2225_);
v_it_2250_ = lean_ctor_get(v_x_2218_, 0);
lean_inc(v_it_2250_);
v_out_2251_ = lean_ctor_get(v_x_2218_, 1);
lean_inc(v_out_2251_);
lean_dec_ref_known(v_x_2218_, 2);
v___x_2252_ = lean_apply_2(v_h__6_2224_, v_it_2250_, v_out_2251_);
return v___x_2252_;
}
case 1:
{
lean_object* v_it_2253_; lean_object* v___x_2254_; 
lean_dec(v_h__8_2226_);
lean_dec(v_h__6_2224_);
v_it_2253_ = lean_ctor_get(v_x_2218_, 0);
lean_inc(v_it_2253_);
lean_dec_ref_known(v_x_2218_, 1);
v___x_2254_ = lean_apply_1(v_h__7_2225_, v_it_2253_);
return v___x_2254_;
}
default: 
{
lean_object* v___x_2255_; lean_object* v___x_2256_; 
lean_dec(v_h__7_2225_);
lean_dec(v_h__6_2224_);
v___x_2255_ = lean_box(0);
v___x_2256_ = lean_apply_1(v_h__8_2226_, v___x_2255_);
return v___x_2256_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___boxed(lean_object** _args){
lean_object* v_00_u03c1_2257_ = _args[0];
lean_object* v_00_u03c1_2258_ = _args[1];
lean_object* v_00_u03c3_2259_ = _args[2];
lean_object* v_inst_2260_ = _args[3];
lean_object* v_m_2261_ = _args[4];
lean_object* v_s_2262_ = _args[5];
lean_object* v_motive_2263_ = _args[6];
lean_object* v_x_2264_ = _args[7];
lean_object* v_x_2265_ = _args[8];
lean_object* v_h__1_2266_ = _args[9];
lean_object* v_h__2_2267_ = _args[10];
lean_object* v_h__3_2268_ = _args[11];
lean_object* v_h__4_2269_ = _args[12];
lean_object* v_h__5_2270_ = _args[13];
lean_object* v_h__6_2271_ = _args[14];
lean_object* v_h__7_2272_ = _args[15];
lean_object* v_h__8_2273_ = _args[16];
_start:
{
lean_object* v_res_2274_; 
v_res_2274_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(v_00_u03c1_2257_, v_00_u03c1_2258_, v_00_u03c3_2259_, v_inst_2260_, v_m_2261_, v_s_2262_, v_motive_2263_, v_x_2264_, v_x_2265_, v_h__1_2266_, v_h__2_2267_, v_h__3_2268_, v_h__4_2269_, v_h__5_2270_, v_h__6_2271_, v_h__7_2272_, v_h__8_2273_);
lean_dec_ref(v_s_2262_);
lean_dec(v_inst_2260_);
lean_dec(v_00_u03c1_2258_);
return v_res_2274_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___redArg(lean_object* v_x_2275_, lean_object* v_h__1_2276_, lean_object* v_h__2_2277_){
_start:
{
if (lean_obj_tag(v_x_2275_) == 0)
{
lean_object* v_currPos_2278_; lean_object* v_searcher_2279_; lean_object* v___x_2280_; 
lean_dec(v_h__2_2277_);
v_currPos_2278_ = lean_ctor_get(v_x_2275_, 0);
lean_inc(v_currPos_2278_);
v_searcher_2279_ = lean_ctor_get(v_x_2275_, 1);
lean_inc(v_searcher_2279_);
lean_dec_ref_known(v_x_2275_, 2);
v___x_2280_ = lean_apply_2(v_h__1_2276_, v_currPos_2278_, v_searcher_2279_);
return v___x_2280_;
}
else
{
lean_object* v___x_2281_; lean_object* v___x_2282_; 
lean_dec(v_h__1_2276_);
v___x_2281_ = lean_box(0);
v___x_2282_ = lean_apply_1(v_h__2_2277_, v___x_2281_);
return v___x_2282_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_2283_, lean_object* v_00_u03c1_2284_, lean_object* v_00_u03c3_2285_, lean_object* v_inst_2286_, lean_object* v_s_2287_, lean_object* v_motive_2288_, lean_object* v_x_2289_, lean_object* v_h__1_2290_, lean_object* v_h__2_2291_){
_start:
{
if (lean_obj_tag(v_x_2289_) == 0)
{
lean_object* v_currPos_2292_; lean_object* v_searcher_2293_; lean_object* v___x_2294_; 
lean_dec(v_h__2_2291_);
v_currPos_2292_ = lean_ctor_get(v_x_2289_, 0);
lean_inc(v_currPos_2292_);
v_searcher_2293_ = lean_ctor_get(v_x_2289_, 1);
lean_inc(v_searcher_2293_);
lean_dec_ref_known(v_x_2289_, 2);
v___x_2294_ = lean_apply_2(v_h__1_2290_, v_currPos_2292_, v_searcher_2293_);
return v___x_2294_;
}
else
{
lean_object* v___x_2295_; lean_object* v___x_2296_; 
lean_dec(v_h__1_2290_);
v___x_2295_ = lean_box(0);
v___x_2296_ = lean_apply_1(v_h__2_2291_, v___x_2295_);
return v___x_2296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_2297_, lean_object* v_00_u03c1_2298_, lean_object* v_00_u03c3_2299_, lean_object* v_inst_2300_, lean_object* v_s_2301_, lean_object* v_motive_2302_, lean_object* v_x_2303_, lean_object* v_h__1_2304_, lean_object* v_h__2_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(v_00_u03c1_2297_, v_00_u03c1_2298_, v_00_u03c3_2299_, v_inst_2300_, v_s_2301_, v_motive_2302_, v_x_2303_, v_h__1_2304_, v_h__2_2305_);
lean_dec_ref(v_s_2301_);
lean_dec(v_inst_2300_);
lean_dec(v_00_u03c1_2298_);
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_2308_; 
v___x_2308_ = lean_box(0);
return v___x_2308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_2309_){
_start:
{
lean_object* v_res_2310_; 
v_res_2310_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg();
return v_res_2310_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(lean_object* v_00_u03c1_2311_, lean_object* v_00_u03c1_2312_, lean_object* v_00_u03c3_2313_, lean_object* v_inst_2314_, lean_object* v_inst_2315_, lean_object* v_s_2316_, lean_object* v_inst_2317_){
_start:
{
lean_object* v___x_2318_; 
v___x_2318_ = lean_box(0);
return v___x_2318_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_2319_, lean_object* v_00_u03c1_2320_, lean_object* v_00_u03c3_2321_, lean_object* v_inst_2322_, lean_object* v_inst_2323_, lean_object* v_s_2324_, lean_object* v_inst_2325_){
_start:
{
lean_object* v_res_2326_; 
v_res_2326_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(v_00_u03c1_2319_, v_00_u03c1_2320_, v_00_u03c3_2321_, v_inst_2322_, v_inst_2323_, v_s_2324_, v_inst_2325_);
lean_dec_ref(v_s_2324_);
lean_dec(v_inst_2323_);
lean_dec(v_inst_2322_);
lean_dec(v_00_u03c1_2320_);
return v_res_2326_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object* v_toPure_2327_, lean_object* v_recur_2328_, lean_object* v_it_2329_, lean_object* v_____do__lift_2330_){
_start:
{
if (lean_obj_tag(v_____do__lift_2330_) == 0)
{
lean_object* v_a_2331_; lean_object* v___x_2332_; 
lean_dec(v_it_2329_);
lean_dec(v_recur_2328_);
v_a_2331_ = lean_ctor_get(v_____do__lift_2330_, 0);
lean_inc(v_a_2331_);
lean_dec_ref_known(v_____do__lift_2330_, 1);
v___x_2332_ = lean_apply_2(v_toPure_2327_, lean_box(0), v_a_2331_);
return v___x_2332_;
}
else
{
lean_object* v_a_2333_; lean_object* v___x_2334_; 
lean_dec(v_toPure_2327_);
v_a_2333_ = lean_ctor_get(v_____do__lift_2330_, 0);
lean_inc(v_a_2333_);
lean_dec_ref_known(v_____do__lift_2330_, 1);
v___x_2334_ = lean_apply_4(v_recur_2328_, v_it_2329_, v_a_2333_, lean_box(0), lean_box(0));
return v___x_2334_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object* v_toPure_2335_, lean_object* v_recur_2336_, lean_object* v___y_2337_, lean_object* v_acc_2338_, lean_object* v_toBind_2339_, lean_object* v_s_2340_){
_start:
{
switch(lean_obj_tag(v_s_2340_))
{
case 0:
{
lean_object* v_it_2341_; lean_object* v_out_2342_; lean_object* v___f_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v_it_2341_ = lean_ctor_get(v_s_2340_, 0);
lean_inc(v_it_2341_);
v_out_2342_ = lean_ctor_get(v_s_2340_, 1);
lean_inc(v_out_2342_);
lean_dec_ref_known(v_s_2340_, 2);
v___f_2343_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2343_, 0, v_toPure_2335_);
lean_closure_set(v___f_2343_, 1, v_recur_2336_);
lean_closure_set(v___f_2343_, 2, v_it_2341_);
v___x_2344_ = lean_apply_3(v___y_2337_, v_out_2342_, lean_box(0), v_acc_2338_);
v___x_2345_ = lean_apply_4(v_toBind_2339_, lean_box(0), lean_box(0), v___x_2344_, v___f_2343_);
return v___x_2345_;
}
case 1:
{
lean_object* v_it_2346_; lean_object* v___x_2347_; 
lean_dec(v_toBind_2339_);
lean_dec(v___y_2337_);
lean_dec(v_toPure_2335_);
v_it_2346_ = lean_ctor_get(v_s_2340_, 0);
lean_inc(v_it_2346_);
lean_dec_ref_known(v_s_2340_, 1);
v___x_2347_ = lean_apply_4(v_recur_2336_, v_it_2346_, v_acc_2338_, lean_box(0), lean_box(0));
return v___x_2347_;
}
default: 
{
lean_object* v___x_2348_; 
lean_dec(v_toBind_2339_);
lean_dec(v___y_2337_);
lean_dec(v_recur_2336_);
v___x_2348_ = lean_apply_2(v_toPure_2335_, lean_box(0), v_acc_2338_);
return v___x_2348_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object* v_toPure_2349_, lean_object* v___y_2350_, lean_object* v_toBind_2351_, lean_object* v_inst_2352_, lean_object* v_s_2353_, lean_object* v_toPure_2354_, lean_object* v_lift_2355_, lean_object* v_it_2356_, lean_object* v_acc_2357_, lean_object* v_hP_2358_, lean_object* v_recur_2359_){
_start:
{
lean_object* v___f_2360_; 
v___f_2360_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2360_, 0, v_toPure_2349_);
lean_closure_set(v___f_2360_, 1, v_recur_2359_);
lean_closure_set(v___f_2360_, 2, v___y_2350_);
lean_closure_set(v___f_2360_, 3, v_acc_2357_);
lean_closure_set(v___f_2360_, 4, v_toBind_2351_);
if (lean_obj_tag(v_it_2356_) == 0)
{
lean_object* v_currPos_2361_; lean_object* v_searcher_2362_; lean_object* v___x_2364_; uint8_t v_isShared_2365_; uint8_t v_isSharedCheck_2425_; 
v_currPos_2361_ = lean_ctor_get(v_it_2356_, 0);
v_searcher_2362_ = lean_ctor_get(v_it_2356_, 1);
v_isSharedCheck_2425_ = !lean_is_exclusive(v_it_2356_);
if (v_isSharedCheck_2425_ == 0)
{
v___x_2364_ = v_it_2356_;
v_isShared_2365_ = v_isSharedCheck_2425_;
goto v_resetjp_2363_;
}
else
{
lean_inc(v_searcher_2362_);
lean_inc(v_currPos_2361_);
lean_dec(v_it_2356_);
v___x_2364_ = lean_box(0);
v_isShared_2365_ = v_isSharedCheck_2425_;
goto v_resetjp_2363_;
}
v_resetjp_2363_:
{
lean_object* v___x_2366_; 
lean_inc_ref(v_s_2353_);
v___x_2366_ = lean_apply_2(v_inst_2352_, v_s_2353_, v_searcher_2362_);
switch(lean_obj_tag(v___x_2366_))
{
case 0:
{
lean_object* v_out_2367_; 
v_out_2367_ = lean_ctor_get(v___x_2366_, 1);
lean_inc(v_out_2367_);
if (lean_obj_tag(v_out_2367_) == 0)
{
lean_object* v_it_2368_; lean_object* v___x_2370_; 
lean_dec_ref_known(v_out_2367_, 2);
lean_dec_ref(v_s_2353_);
v_it_2368_ = lean_ctor_get(v___x_2366_, 0);
lean_inc(v_it_2368_);
lean_dec_ref_known(v___x_2366_, 2);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v_it_2368_);
v___x_2370_ = v___x_2364_;
goto v_reusejp_2369_;
}
else
{
lean_object* v_reuseFailAlloc_2374_; 
v_reuseFailAlloc_2374_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2374_, 0, v_currPos_2361_);
lean_ctor_set(v_reuseFailAlloc_2374_, 1, v_it_2368_);
v___x_2370_ = v_reuseFailAlloc_2374_;
goto v_reusejp_2369_;
}
v_reusejp_2369_:
{
lean_object* v___x_2371_; lean_object* v___x_2372_; lean_object* v___x_2373_; 
v___x_2371_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2371_, 0, v___x_2370_);
v___x_2372_ = lean_apply_2(v_toPure_2354_, lean_box(0), v___x_2371_);
v___x_2373_ = lean_apply_4(v_lift_2355_, lean_box(0), lean_box(0), v___f_2360_, v___x_2372_);
return v___x_2373_;
}
}
else
{
lean_object* v_it_2375_; lean_object* v___x_2377_; uint8_t v_isShared_2378_; uint8_t v_isSharedCheck_2390_; 
v_it_2375_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2390_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2390_ == 0)
{
lean_object* v_unused_2391_; 
v_unused_2391_ = lean_ctor_get(v___x_2366_, 1);
lean_dec(v_unused_2391_);
v___x_2377_ = v___x_2366_;
v_isShared_2378_ = v_isSharedCheck_2390_;
goto v_resetjp_2376_;
}
else
{
lean_inc(v_it_2375_);
lean_dec(v___x_2366_);
v___x_2377_ = lean_box(0);
v_isShared_2378_ = v_isSharedCheck_2390_;
goto v_resetjp_2376_;
}
v_resetjp_2376_:
{
lean_object* v_startPos_2379_; lean_object* v_endPos_2380_; lean_object* v_slice_2381_; lean_object* v_nextIt_2383_; 
v_startPos_2379_ = lean_ctor_get(v_out_2367_, 0);
lean_inc(v_startPos_2379_);
v_endPos_2380_ = lean_ctor_get(v_out_2367_, 1);
lean_inc(v_endPos_2380_);
lean_dec_ref_known(v_out_2367_, 2);
v_slice_2381_ = l_String_Slice_slice_x21(v_s_2353_, v_endPos_2380_, v_currPos_2361_);
lean_dec(v_currPos_2361_);
lean_dec(v_endPos_2380_);
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v_it_2375_);
lean_ctor_set(v___x_2364_, 0, v_startPos_2379_);
v_nextIt_2383_ = v___x_2364_;
goto v_reusejp_2382_;
}
else
{
lean_object* v_reuseFailAlloc_2389_; 
v_reuseFailAlloc_2389_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2389_, 0, v_startPos_2379_);
lean_ctor_set(v_reuseFailAlloc_2389_, 1, v_it_2375_);
v_nextIt_2383_ = v_reuseFailAlloc_2389_;
goto v_reusejp_2382_;
}
v_reusejp_2382_:
{
lean_object* v___x_2385_; 
if (v_isShared_2378_ == 0)
{
lean_ctor_set(v___x_2377_, 1, v_slice_2381_);
lean_ctor_set(v___x_2377_, 0, v_nextIt_2383_);
v___x_2385_ = v___x_2377_;
goto v_reusejp_2384_;
}
else
{
lean_object* v_reuseFailAlloc_2388_; 
v_reuseFailAlloc_2388_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2388_, 0, v_nextIt_2383_);
lean_ctor_set(v_reuseFailAlloc_2388_, 1, v_slice_2381_);
v___x_2385_ = v_reuseFailAlloc_2388_;
goto v_reusejp_2384_;
}
v_reusejp_2384_:
{
lean_object* v___x_2386_; lean_object* v___x_2387_; 
v___x_2386_ = lean_apply_2(v_toPure_2354_, lean_box(0), v___x_2385_);
v___x_2387_ = lean_apply_4(v_lift_2355_, lean_box(0), lean_box(0), v___f_2360_, v___x_2386_);
return v___x_2387_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2392_; lean_object* v___x_2394_; uint8_t v_isShared_2395_; uint8_t v_isSharedCheck_2404_; 
lean_dec_ref(v_s_2353_);
v_it_2392_ = lean_ctor_get(v___x_2366_, 0);
v_isSharedCheck_2404_ = !lean_is_exclusive(v___x_2366_);
if (v_isSharedCheck_2404_ == 0)
{
v___x_2394_ = v___x_2366_;
v_isShared_2395_ = v_isSharedCheck_2404_;
goto v_resetjp_2393_;
}
else
{
lean_inc(v_it_2392_);
lean_dec(v___x_2366_);
v___x_2394_ = lean_box(0);
v_isShared_2395_ = v_isSharedCheck_2404_;
goto v_resetjp_2393_;
}
v_resetjp_2393_:
{
lean_object* v___x_2397_; 
if (v_isShared_2365_ == 0)
{
lean_ctor_set(v___x_2364_, 1, v_it_2392_);
v___x_2397_ = v___x_2364_;
goto v_reusejp_2396_;
}
else
{
lean_object* v_reuseFailAlloc_2403_; 
v_reuseFailAlloc_2403_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2403_, 0, v_currPos_2361_);
lean_ctor_set(v_reuseFailAlloc_2403_, 1, v_it_2392_);
v___x_2397_ = v_reuseFailAlloc_2403_;
goto v_reusejp_2396_;
}
v_reusejp_2396_:
{
lean_object* v___x_2399_; 
if (v_isShared_2395_ == 0)
{
lean_ctor_set(v___x_2394_, 0, v___x_2397_);
v___x_2399_ = v___x_2394_;
goto v_reusejp_2398_;
}
else
{
lean_object* v_reuseFailAlloc_2402_; 
v_reuseFailAlloc_2402_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2402_, 0, v___x_2397_);
v___x_2399_ = v_reuseFailAlloc_2402_;
goto v_reusejp_2398_;
}
v_reusejp_2398_:
{
lean_object* v___x_2400_; lean_object* v___x_2401_; 
v___x_2400_ = lean_apply_2(v_toPure_2354_, lean_box(0), v___x_2399_);
v___x_2401_ = lean_apply_4(v_lift_2355_, lean_box(0), lean_box(0), v___f_2360_, v___x_2400_);
return v___x_2401_;
}
}
}
}
default: 
{
lean_object* v___x_2405_; uint8_t v_decide_2406_; 
lean_del_object(v___x_2364_);
v___x_2405_ = lean_unsigned_to_nat(0u);
v_decide_2406_ = lean_nat_dec_eq(v_currPos_2361_, v___x_2405_);
if (v_decide_2406_ == 0)
{
lean_object* v_str_2407_; lean_object* v_startInclusive_2408_; lean_object* v___x_2410_; uint8_t v_isShared_2411_; uint8_t v_isSharedCheck_2420_; 
v_str_2407_ = lean_ctor_get(v_s_2353_, 0);
v_startInclusive_2408_ = lean_ctor_get(v_s_2353_, 1);
v_isSharedCheck_2420_ = !lean_is_exclusive(v_s_2353_);
if (v_isSharedCheck_2420_ == 0)
{
lean_object* v_unused_2421_; 
v_unused_2421_ = lean_ctor_get(v_s_2353_, 2);
lean_dec(v_unused_2421_);
v___x_2410_ = v_s_2353_;
v_isShared_2411_ = v_isSharedCheck_2420_;
goto v_resetjp_2409_;
}
else
{
lean_inc(v_startInclusive_2408_);
lean_inc(v_str_2407_);
lean_dec(v_s_2353_);
v___x_2410_ = lean_box(0);
v_isShared_2411_ = v_isSharedCheck_2420_;
goto v_resetjp_2409_;
}
v_resetjp_2409_:
{
lean_object* v___x_2412_; lean_object* v_slice_2414_; 
v___x_2412_ = lean_nat_add(v_startInclusive_2408_, v_currPos_2361_);
lean_dec(v_currPos_2361_);
if (v_isShared_2411_ == 0)
{
lean_ctor_set(v___x_2410_, 2, v___x_2412_);
v_slice_2414_ = v___x_2410_;
goto v_reusejp_2413_;
}
else
{
lean_object* v_reuseFailAlloc_2419_; 
v_reuseFailAlloc_2419_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2419_, 0, v_str_2407_);
lean_ctor_set(v_reuseFailAlloc_2419_, 1, v_startInclusive_2408_);
lean_ctor_set(v_reuseFailAlloc_2419_, 2, v___x_2412_);
v_slice_2414_ = v_reuseFailAlloc_2419_;
goto v_reusejp_2413_;
}
v_reusejp_2413_:
{
lean_object* v___x_2415_; lean_object* v___x_2416_; lean_object* v___x_2417_; lean_object* v___x_2418_; 
v___x_2415_ = lean_box(1);
v___x_2416_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2416_, 0, v___x_2415_);
lean_ctor_set(v___x_2416_, 1, v_slice_2414_);
v___x_2417_ = lean_apply_2(v_toPure_2354_, lean_box(0), v___x_2416_);
v___x_2418_ = lean_apply_4(v_lift_2355_, lean_box(0), lean_box(0), v___f_2360_, v___x_2417_);
return v___x_2418_;
}
}
}
else
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_dec(v_currPos_2361_);
lean_dec_ref(v_s_2353_);
v___x_2422_ = lean_box(2);
v___x_2423_ = lean_apply_2(v_toPure_2354_, lean_box(0), v___x_2422_);
v___x_2424_ = lean_apply_4(v_lift_2355_, lean_box(0), lean_box(0), v___f_2360_, v___x_2423_);
return v___x_2424_;
}
}
}
}
}
else
{
lean_object* v___x_2426_; lean_object* v___x_2427_; lean_object* v___x_2428_; 
lean_dec_ref(v_s_2353_);
lean_dec(v_inst_2352_);
v___x_2426_ = lean_box(2);
v___x_2427_ = lean_apply_2(v_toPure_2354_, lean_box(0), v___x_2426_);
v___x_2428_ = lean_apply_4(v_lift_2355_, lean_box(0), lean_box(0), v___f_2360_, v___x_2427_);
return v___x_2428_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object* v_inst_2429_, lean_object* v_inst_2430_, lean_object* v_s_2431_, lean_object* v_toPure_2432_, lean_object* v_lift_2433_, lean_object* v_00_u03b3_2434_, lean_object* v_Pl_2435_, lean_object* v_it_2436_, lean_object* v_init_2437_, lean_object* v___y_2438_){
_start:
{
lean_object* v_toApplicative_2439_; lean_object* v_toBind_2440_; lean_object* v_toPure_2441_; lean_object* v___f_2442_; lean_object* v___x_2443_; 
v_toApplicative_2439_ = lean_ctor_get(v_inst_2429_, 0);
lean_inc_ref(v_toApplicative_2439_);
v_toBind_2440_ = lean_ctor_get(v_inst_2429_, 1);
lean_inc(v_toBind_2440_);
lean_dec_ref(v_inst_2429_);
v_toPure_2441_ = lean_ctor_get(v_toApplicative_2439_, 1);
lean_inc(v_toPure_2441_);
lean_dec_ref(v_toApplicative_2439_);
v___f_2442_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2), 11, 7);
lean_closure_set(v___f_2442_, 0, v_toPure_2441_);
lean_closure_set(v___f_2442_, 1, v___y_2438_);
lean_closure_set(v___f_2442_, 2, v_toBind_2440_);
lean_closure_set(v___f_2442_, 3, v_inst_2430_);
lean_closure_set(v___f_2442_, 4, v_s_2431_);
lean_closure_set(v___f_2442_, 5, v_toPure_2432_);
lean_closure_set(v___f_2442_, 6, v_lift_2433_);
v___x_2443_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2442_, v_it_2436_, v_init_2437_, lean_box(0));
return v___x_2443_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(lean_object* v_inst_2444_, lean_object* v_s_2445_, lean_object* v_inst_2446_, lean_object* v_inst_2447_){
_start:
{
lean_object* v_toApplicative_2448_; lean_object* v_toPure_2449_; lean_object* v___f_2450_; 
v_toApplicative_2448_ = lean_ctor_get(v_inst_2446_, 0);
lean_inc_ref(v_toApplicative_2448_);
lean_dec_ref(v_inst_2446_);
v_toPure_2449_ = lean_ctor_get(v_toApplicative_2448_, 1);
lean_inc(v_toPure_2449_);
lean_dec_ref(v_toApplicative_2448_);
v___f_2450_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3), 10, 4);
lean_closure_set(v___f_2450_, 0, v_inst_2447_);
lean_closure_set(v___f_2450_, 1, v_inst_2444_);
lean_closure_set(v___f_2450_, 2, v_s_2445_);
lean_closure_set(v___f_2450_, 3, v_toPure_2449_);
return v___f_2450_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(lean_object* v_00_u03c1_2451_, lean_object* v_00_u03c1_2452_, lean_object* v_00_u03c3_2453_, lean_object* v_inst_2454_, lean_object* v_inst_2455_, lean_object* v_m_2456_, lean_object* v_n_2457_, lean_object* v_s_2458_, lean_object* v_inst_2459_, lean_object* v_inst_2460_){
_start:
{
lean_object* v___x_2461_; 
v___x_2461_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(v_inst_2454_, v_s_2458_, v_inst_2459_, v_inst_2460_);
return v___x_2461_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___boxed(lean_object* v_00_u03c1_2462_, lean_object* v_00_u03c1_2463_, lean_object* v_00_u03c3_2464_, lean_object* v_inst_2465_, lean_object* v_inst_2466_, lean_object* v_m_2467_, lean_object* v_n_2468_, lean_object* v_s_2469_, lean_object* v_inst_2470_, lean_object* v_inst_2471_){
_start:
{
lean_object* v_res_2472_; 
v_res_2472_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(v_00_u03c1_2462_, v_00_u03c1_2463_, v_00_u03c3_2464_, v_inst_2465_, v_inst_2466_, v_m_2467_, v_n_2468_, v_s_2469_, v_inst_2470_, v_inst_2471_);
lean_dec(v_inst_2466_);
lean_dec(v_00_u03c1_2463_);
return v_res_2472_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___redArg(lean_object* v_s_2473_, lean_object* v_inst_2474_){
_start:
{
lean_object* v_startInclusive_2475_; lean_object* v_endExclusive_2476_; lean_object* v___x_2477_; lean_object* v___x_2478_; lean_object* v___x_2479_; 
v_startInclusive_2475_ = lean_ctor_get(v_s_2473_, 1);
v_endExclusive_2476_ = lean_ctor_get(v_s_2473_, 2);
v___x_2477_ = lean_nat_sub(v_endExclusive_2476_, v_startInclusive_2475_);
v___x_2478_ = lean_apply_1(v_inst_2474_, v_s_2473_);
v___x_2479_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2479_, 0, v___x_2477_);
lean_ctor_set(v___x_2479_, 1, v___x_2478_);
return v___x_2479_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit(lean_object* v_00_u03c3_2480_, lean_object* v_00_u03c1_2481_, lean_object* v_s_2482_, lean_object* v_pat_2483_, lean_object* v_inst_2484_){
_start:
{
lean_object* v___x_2485_; 
v___x_2485_ = l_String_Slice_revSplit___redArg(v_s_2482_, v_inst_2484_);
return v___x_2485_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___boxed(lean_object* v_00_u03c3_2486_, lean_object* v_00_u03c1_2487_, lean_object* v_s_2488_, lean_object* v_pat_2489_, lean_object* v_inst_2490_){
_start:
{
lean_object* v_res_2491_; 
v_res_2491_ = l_String_Slice_revSplit(v_00_u03c3_2486_, v_00_u03c1_2487_, v_s_2488_, v_pat_2489_, v_inst_2490_);
lean_dec(v_pat_2489_);
return v_res_2491_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___redArg(lean_object* v_s_2492_, lean_object* v_inst_2493_){
_start:
{
lean_object* v_skipSuffix_x3f_2494_; lean_object* v___x_2495_; 
v_skipSuffix_x3f_2494_ = lean_ctor_get(v_inst_2493_, 0);
lean_inc_ref(v_skipSuffix_x3f_2494_);
lean_dec_ref(v_inst_2493_);
v___x_2495_ = lean_apply_1(v_skipSuffix_x3f_2494_, v_s_2492_);
return v___x_2495_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f(lean_object* v_00_u03c1_2496_, lean_object* v_s_2497_, lean_object* v_pat_2498_, lean_object* v_inst_2499_){
_start:
{
lean_object* v_skipSuffix_x3f_2500_; lean_object* v___x_2501_; 
v_skipSuffix_x3f_2500_ = lean_ctor_get(v_inst_2499_, 0);
lean_inc_ref(v_skipSuffix_x3f_2500_);
lean_dec_ref(v_inst_2499_);
v___x_2501_ = lean_apply_1(v_skipSuffix_x3f_2500_, v_s_2497_);
return v___x_2501_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___boxed(lean_object* v_00_u03c1_2502_, lean_object* v_s_2503_, lean_object* v_pat_2504_, lean_object* v_inst_2505_){
_start:
{
lean_object* v_res_2506_; 
v_res_2506_ = l_String_Slice_skipSuffix_x3f(v_00_u03c1_2502_, v_s_2503_, v_pat_2504_, v_inst_2505_);
lean_dec(v_pat_2504_);
return v_res_2506_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg(lean_object* v_s_2507_, lean_object* v_pos_2508_, lean_object* v_inst_2509_){
_start:
{
lean_object* v_str_2510_; lean_object* v_startInclusive_2511_; lean_object* v___x_2513_; uint8_t v_isShared_2514_; uint8_t v_isSharedCheck_2529_; 
v_str_2510_ = lean_ctor_get(v_s_2507_, 0);
v_startInclusive_2511_ = lean_ctor_get(v_s_2507_, 1);
v_isSharedCheck_2529_ = !lean_is_exclusive(v_s_2507_);
if (v_isSharedCheck_2529_ == 0)
{
lean_object* v_unused_2530_; 
v_unused_2530_ = lean_ctor_get(v_s_2507_, 2);
lean_dec(v_unused_2530_);
v___x_2513_ = v_s_2507_;
v_isShared_2514_ = v_isSharedCheck_2529_;
goto v_resetjp_2512_;
}
else
{
lean_inc(v_startInclusive_2511_);
lean_inc(v_str_2510_);
lean_dec(v_s_2507_);
v___x_2513_ = lean_box(0);
v_isShared_2514_ = v_isSharedCheck_2529_;
goto v_resetjp_2512_;
}
v_resetjp_2512_:
{
lean_object* v_skipSuffix_x3f_2515_; lean_object* v___x_2516_; lean_object* v___x_2518_; 
v_skipSuffix_x3f_2515_ = lean_ctor_get(v_inst_2509_, 0);
lean_inc_ref(v_skipSuffix_x3f_2515_);
lean_dec_ref(v_inst_2509_);
v___x_2516_ = lean_nat_add(v_startInclusive_2511_, v_pos_2508_);
if (v_isShared_2514_ == 0)
{
lean_ctor_set(v___x_2513_, 2, v___x_2516_);
v___x_2518_ = v___x_2513_;
goto v_reusejp_2517_;
}
else
{
lean_object* v_reuseFailAlloc_2528_; 
v_reuseFailAlloc_2528_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2528_, 0, v_str_2510_);
lean_ctor_set(v_reuseFailAlloc_2528_, 1, v_startInclusive_2511_);
lean_ctor_set(v_reuseFailAlloc_2528_, 2, v___x_2516_);
v___x_2518_ = v_reuseFailAlloc_2528_;
goto v_reusejp_2517_;
}
v_reusejp_2517_:
{
lean_object* v___x_2519_; 
v___x_2519_ = lean_apply_1(v_skipSuffix_x3f_2515_, v___x_2518_);
if (lean_obj_tag(v___x_2519_) == 0)
{
return v___x_2519_;
}
else
{
lean_object* v_val_2520_; lean_object* v___x_2522_; uint8_t v_isShared_2523_; uint8_t v_isSharedCheck_2527_; 
v_val_2520_ = lean_ctor_get(v___x_2519_, 0);
v_isSharedCheck_2527_ = !lean_is_exclusive(v___x_2519_);
if (v_isSharedCheck_2527_ == 0)
{
v___x_2522_ = v___x_2519_;
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
else
{
lean_inc(v_val_2520_);
lean_dec(v___x_2519_);
v___x_2522_ = lean_box(0);
v_isShared_2523_ = v_isSharedCheck_2527_;
goto v_resetjp_2521_;
}
v_resetjp_2521_:
{
lean_object* v___x_2525_; 
if (v_isShared_2523_ == 0)
{
v___x_2525_ = v___x_2522_;
goto v_reusejp_2524_;
}
else
{
lean_object* v_reuseFailAlloc_2526_; 
v_reuseFailAlloc_2526_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2526_, 0, v_val_2520_);
v___x_2525_ = v_reuseFailAlloc_2526_;
goto v_reusejp_2524_;
}
v_reusejp_2524_:
{
return v___x_2525_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg___boxed(lean_object* v_s_2531_, lean_object* v_pos_2532_, lean_object* v_inst_2533_){
_start:
{
lean_object* v_res_2534_; 
v_res_2534_ = l_String_Slice_Pos_revSkip_x3f___redArg(v_s_2531_, v_pos_2532_, v_inst_2533_);
lean_dec(v_pos_2532_);
return v_res_2534_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f(lean_object* v_00_u03c1_2535_, lean_object* v_s_2536_, lean_object* v_pos_2537_, lean_object* v_pat_2538_, lean_object* v_inst_2539_){
_start:
{
lean_object* v_str_2540_; lean_object* v_startInclusive_2541_; lean_object* v___x_2543_; uint8_t v_isShared_2544_; uint8_t v_isSharedCheck_2559_; 
v_str_2540_ = lean_ctor_get(v_s_2536_, 0);
v_startInclusive_2541_ = lean_ctor_get(v_s_2536_, 1);
v_isSharedCheck_2559_ = !lean_is_exclusive(v_s_2536_);
if (v_isSharedCheck_2559_ == 0)
{
lean_object* v_unused_2560_; 
v_unused_2560_ = lean_ctor_get(v_s_2536_, 2);
lean_dec(v_unused_2560_);
v___x_2543_ = v_s_2536_;
v_isShared_2544_ = v_isSharedCheck_2559_;
goto v_resetjp_2542_;
}
else
{
lean_inc(v_startInclusive_2541_);
lean_inc(v_str_2540_);
lean_dec(v_s_2536_);
v___x_2543_ = lean_box(0);
v_isShared_2544_ = v_isSharedCheck_2559_;
goto v_resetjp_2542_;
}
v_resetjp_2542_:
{
lean_object* v_skipSuffix_x3f_2545_; lean_object* v___x_2546_; lean_object* v___x_2548_; 
v_skipSuffix_x3f_2545_ = lean_ctor_get(v_inst_2539_, 0);
lean_inc_ref(v_skipSuffix_x3f_2545_);
lean_dec_ref(v_inst_2539_);
v___x_2546_ = lean_nat_add(v_startInclusive_2541_, v_pos_2537_);
if (v_isShared_2544_ == 0)
{
lean_ctor_set(v___x_2543_, 2, v___x_2546_);
v___x_2548_ = v___x_2543_;
goto v_reusejp_2547_;
}
else
{
lean_object* v_reuseFailAlloc_2558_; 
v_reuseFailAlloc_2558_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2558_, 0, v_str_2540_);
lean_ctor_set(v_reuseFailAlloc_2558_, 1, v_startInclusive_2541_);
lean_ctor_set(v_reuseFailAlloc_2558_, 2, v___x_2546_);
v___x_2548_ = v_reuseFailAlloc_2558_;
goto v_reusejp_2547_;
}
v_reusejp_2547_:
{
lean_object* v___x_2549_; 
v___x_2549_ = lean_apply_1(v_skipSuffix_x3f_2545_, v___x_2548_);
if (lean_obj_tag(v___x_2549_) == 0)
{
return v___x_2549_;
}
else
{
lean_object* v_val_2550_; lean_object* v___x_2552_; uint8_t v_isShared_2553_; uint8_t v_isSharedCheck_2557_; 
v_val_2550_ = lean_ctor_get(v___x_2549_, 0);
v_isSharedCheck_2557_ = !lean_is_exclusive(v___x_2549_);
if (v_isSharedCheck_2557_ == 0)
{
v___x_2552_ = v___x_2549_;
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
else
{
lean_inc(v_val_2550_);
lean_dec(v___x_2549_);
v___x_2552_ = lean_box(0);
v_isShared_2553_ = v_isSharedCheck_2557_;
goto v_resetjp_2551_;
}
v_resetjp_2551_:
{
lean_object* v___x_2555_; 
if (v_isShared_2553_ == 0)
{
v___x_2555_ = v___x_2552_;
goto v_reusejp_2554_;
}
else
{
lean_object* v_reuseFailAlloc_2556_; 
v_reuseFailAlloc_2556_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2556_, 0, v_val_2550_);
v___x_2555_ = v_reuseFailAlloc_2556_;
goto v_reusejp_2554_;
}
v_reusejp_2554_:
{
return v___x_2555_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_2561_, lean_object* v_s_2562_, lean_object* v_pos_2563_, lean_object* v_pat_2564_, lean_object* v_inst_2565_){
_start:
{
lean_object* v_res_2566_; 
v_res_2566_ = l_String_Slice_Pos_revSkip_x3f(v_00_u03c1_2561_, v_s_2562_, v_pos_2563_, v_pat_2564_, v_inst_2565_);
lean_dec(v_pat_2564_);
lean_dec(v_pos_2563_);
return v_res_2566_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___redArg(lean_object* v_s_2567_, lean_object* v_inst_2568_){
_start:
{
lean_object* v_skipSuffix_x3f_2569_; lean_object* v___x_2570_; 
v_skipSuffix_x3f_2569_ = lean_ctor_get(v_inst_2568_, 0);
lean_inc_ref(v_skipSuffix_x3f_2569_);
lean_dec_ref(v_inst_2568_);
lean_inc_ref(v_s_2567_);
v___x_2570_ = lean_apply_1(v_skipSuffix_x3f_2569_, v_s_2567_);
if (lean_obj_tag(v___x_2570_) == 0)
{
lean_object* v___x_2571_; 
lean_dec_ref(v_s_2567_);
v___x_2571_ = lean_box(0);
return v___x_2571_;
}
else
{
lean_object* v_val_2572_; lean_object* v___x_2574_; uint8_t v_isShared_2575_; uint8_t v_isSharedCheck_2590_; 
v_val_2572_ = lean_ctor_get(v___x_2570_, 0);
v_isSharedCheck_2590_ = !lean_is_exclusive(v___x_2570_);
if (v_isSharedCheck_2590_ == 0)
{
v___x_2574_ = v___x_2570_;
v_isShared_2575_ = v_isSharedCheck_2590_;
goto v_resetjp_2573_;
}
else
{
lean_inc(v_val_2572_);
lean_dec(v___x_2570_);
v___x_2574_ = lean_box(0);
v_isShared_2575_ = v_isSharedCheck_2590_;
goto v_resetjp_2573_;
}
v_resetjp_2573_:
{
lean_object* v_str_2576_; lean_object* v_startInclusive_2577_; lean_object* v___x_2579_; uint8_t v_isShared_2580_; uint8_t v_isSharedCheck_2588_; 
v_str_2576_ = lean_ctor_get(v_s_2567_, 0);
v_startInclusive_2577_ = lean_ctor_get(v_s_2567_, 1);
v_isSharedCheck_2588_ = !lean_is_exclusive(v_s_2567_);
if (v_isSharedCheck_2588_ == 0)
{
lean_object* v_unused_2589_; 
v_unused_2589_ = lean_ctor_get(v_s_2567_, 2);
lean_dec(v_unused_2589_);
v___x_2579_ = v_s_2567_;
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
else
{
lean_inc(v_startInclusive_2577_);
lean_inc(v_str_2576_);
lean_dec(v_s_2567_);
v___x_2579_ = lean_box(0);
v_isShared_2580_ = v_isSharedCheck_2588_;
goto v_resetjp_2578_;
}
v_resetjp_2578_:
{
lean_object* v___x_2581_; lean_object* v___x_2583_; 
v___x_2581_ = lean_nat_add(v_startInclusive_2577_, v_val_2572_);
lean_dec(v_val_2572_);
if (v_isShared_2580_ == 0)
{
lean_ctor_set(v___x_2579_, 2, v___x_2581_);
v___x_2583_ = v___x_2579_;
goto v_reusejp_2582_;
}
else
{
lean_object* v_reuseFailAlloc_2587_; 
v_reuseFailAlloc_2587_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2587_, 0, v_str_2576_);
lean_ctor_set(v_reuseFailAlloc_2587_, 1, v_startInclusive_2577_);
lean_ctor_set(v_reuseFailAlloc_2587_, 2, v___x_2581_);
v___x_2583_ = v_reuseFailAlloc_2587_;
goto v_reusejp_2582_;
}
v_reusejp_2582_:
{
lean_object* v___x_2585_; 
if (v_isShared_2575_ == 0)
{
lean_ctor_set(v___x_2574_, 0, v___x_2583_);
v___x_2585_ = v___x_2574_;
goto v_reusejp_2584_;
}
else
{
lean_object* v_reuseFailAlloc_2586_; 
v_reuseFailAlloc_2586_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2586_, 0, v___x_2583_);
v___x_2585_ = v_reuseFailAlloc_2586_;
goto v_reusejp_2584_;
}
v_reusejp_2584_:
{
return v___x_2585_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f(lean_object* v_00_u03c1_2591_, lean_object* v_s_2592_, lean_object* v_pat_2593_, lean_object* v_inst_2594_){
_start:
{
lean_object* v_skipSuffix_x3f_2595_; lean_object* v___x_2596_; 
v_skipSuffix_x3f_2595_ = lean_ctor_get(v_inst_2594_, 0);
lean_inc_ref(v_skipSuffix_x3f_2595_);
lean_dec_ref(v_inst_2594_);
lean_inc_ref(v_s_2592_);
v___x_2596_ = lean_apply_1(v_skipSuffix_x3f_2595_, v_s_2592_);
if (lean_obj_tag(v___x_2596_) == 0)
{
lean_object* v___x_2597_; 
lean_dec_ref(v_s_2592_);
v___x_2597_ = lean_box(0);
return v___x_2597_;
}
else
{
lean_object* v_val_2598_; lean_object* v___x_2600_; uint8_t v_isShared_2601_; uint8_t v_isSharedCheck_2616_; 
v_val_2598_ = lean_ctor_get(v___x_2596_, 0);
v_isSharedCheck_2616_ = !lean_is_exclusive(v___x_2596_);
if (v_isSharedCheck_2616_ == 0)
{
v___x_2600_ = v___x_2596_;
v_isShared_2601_ = v_isSharedCheck_2616_;
goto v_resetjp_2599_;
}
else
{
lean_inc(v_val_2598_);
lean_dec(v___x_2596_);
v___x_2600_ = lean_box(0);
v_isShared_2601_ = v_isSharedCheck_2616_;
goto v_resetjp_2599_;
}
v_resetjp_2599_:
{
lean_object* v_str_2602_; lean_object* v_startInclusive_2603_; lean_object* v___x_2605_; uint8_t v_isShared_2606_; uint8_t v_isSharedCheck_2614_; 
v_str_2602_ = lean_ctor_get(v_s_2592_, 0);
v_startInclusive_2603_ = lean_ctor_get(v_s_2592_, 1);
v_isSharedCheck_2614_ = !lean_is_exclusive(v_s_2592_);
if (v_isSharedCheck_2614_ == 0)
{
lean_object* v_unused_2615_; 
v_unused_2615_ = lean_ctor_get(v_s_2592_, 2);
lean_dec(v_unused_2615_);
v___x_2605_ = v_s_2592_;
v_isShared_2606_ = v_isSharedCheck_2614_;
goto v_resetjp_2604_;
}
else
{
lean_inc(v_startInclusive_2603_);
lean_inc(v_str_2602_);
lean_dec(v_s_2592_);
v___x_2605_ = lean_box(0);
v_isShared_2606_ = v_isSharedCheck_2614_;
goto v_resetjp_2604_;
}
v_resetjp_2604_:
{
lean_object* v___x_2607_; lean_object* v___x_2609_; 
v___x_2607_ = lean_nat_add(v_startInclusive_2603_, v_val_2598_);
lean_dec(v_val_2598_);
if (v_isShared_2606_ == 0)
{
lean_ctor_set(v___x_2605_, 2, v___x_2607_);
v___x_2609_ = v___x_2605_;
goto v_reusejp_2608_;
}
else
{
lean_object* v_reuseFailAlloc_2613_; 
v_reuseFailAlloc_2613_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2613_, 0, v_str_2602_);
lean_ctor_set(v_reuseFailAlloc_2613_, 1, v_startInclusive_2603_);
lean_ctor_set(v_reuseFailAlloc_2613_, 2, v___x_2607_);
v___x_2609_ = v_reuseFailAlloc_2613_;
goto v_reusejp_2608_;
}
v_reusejp_2608_:
{
lean_object* v___x_2611_; 
if (v_isShared_2601_ == 0)
{
lean_ctor_set(v___x_2600_, 0, v___x_2609_);
v___x_2611_ = v___x_2600_;
goto v_reusejp_2610_;
}
else
{
lean_object* v_reuseFailAlloc_2612_; 
v_reuseFailAlloc_2612_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2612_, 0, v___x_2609_);
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
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_2617_, lean_object* v_s_2618_, lean_object* v_pat_2619_, lean_object* v_inst_2620_){
_start:
{
lean_object* v_res_2621_; 
v_res_2621_ = l_String_Slice_dropSuffix_x3f(v_00_u03c1_2617_, v_s_2618_, v_pat_2619_, v_inst_2620_);
lean_dec(v_pat_2619_);
return v_res_2621_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___redArg(lean_object* v_s_2622_, lean_object* v_inst_2623_){
_start:
{
lean_object* v_skipSuffix_x3f_2624_; lean_object* v___x_2625_; 
v_skipSuffix_x3f_2624_ = lean_ctor_get(v_inst_2623_, 0);
lean_inc_ref(v_skipSuffix_x3f_2624_);
lean_dec_ref(v_inst_2623_);
lean_inc_ref(v_s_2622_);
v___x_2625_ = lean_apply_1(v_skipSuffix_x3f_2624_, v_s_2622_);
if (lean_obj_tag(v___x_2625_) == 0)
{
return v_s_2622_;
}
else
{
lean_object* v_val_2626_; lean_object* v_str_2627_; lean_object* v_startInclusive_2628_; lean_object* v___x_2630_; uint8_t v_isShared_2631_; uint8_t v_isSharedCheck_2636_; 
v_val_2626_ = lean_ctor_get(v___x_2625_, 0);
lean_inc(v_val_2626_);
lean_dec_ref_known(v___x_2625_, 1);
v_str_2627_ = lean_ctor_get(v_s_2622_, 0);
v_startInclusive_2628_ = lean_ctor_get(v_s_2622_, 1);
v_isSharedCheck_2636_ = !lean_is_exclusive(v_s_2622_);
if (v_isSharedCheck_2636_ == 0)
{
lean_object* v_unused_2637_; 
v_unused_2637_ = lean_ctor_get(v_s_2622_, 2);
lean_dec(v_unused_2637_);
v___x_2630_ = v_s_2622_;
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
else
{
lean_inc(v_startInclusive_2628_);
lean_inc(v_str_2627_);
lean_dec(v_s_2622_);
v___x_2630_ = lean_box(0);
v_isShared_2631_ = v_isSharedCheck_2636_;
goto v_resetjp_2629_;
}
v_resetjp_2629_:
{
lean_object* v___x_2632_; lean_object* v___x_2634_; 
v___x_2632_ = lean_nat_add(v_startInclusive_2628_, v_val_2626_);
lean_dec(v_val_2626_);
if (v_isShared_2631_ == 0)
{
lean_ctor_set(v___x_2630_, 2, v___x_2632_);
v___x_2634_ = v___x_2630_;
goto v_reusejp_2633_;
}
else
{
lean_object* v_reuseFailAlloc_2635_; 
v_reuseFailAlloc_2635_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2635_, 0, v_str_2627_);
lean_ctor_set(v_reuseFailAlloc_2635_, 1, v_startInclusive_2628_);
lean_ctor_set(v_reuseFailAlloc_2635_, 2, v___x_2632_);
v___x_2634_ = v_reuseFailAlloc_2635_;
goto v_reusejp_2633_;
}
v_reusejp_2633_:
{
return v___x_2634_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix(lean_object* v_00_u03c1_2638_, lean_object* v_s_2639_, lean_object* v_pat_2640_, lean_object* v_inst_2641_){
_start:
{
lean_object* v___x_2642_; 
v___x_2642_ = l_String_Slice_dropSuffix___redArg(v_s_2639_, v_inst_2641_);
return v___x_2642_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___boxed(lean_object* v_00_u03c1_2643_, lean_object* v_s_2644_, lean_object* v_pat_2645_, lean_object* v_inst_2646_){
_start:
{
lean_object* v_res_2647_; 
v_res_2647_ = l_String_Slice_dropSuffix(v_00_u03c1_2643_, v_s_2644_, v_pat_2645_, v_inst_2646_);
lean_dec(v_pat_2645_);
return v_res_2647_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object* v_s_2648_, lean_object* v_n_2649_){
_start:
{
lean_object* v_str_2650_; lean_object* v_startInclusive_2651_; lean_object* v_endExclusive_2652_; lean_object* v___x_2653_; lean_object* v___x_2654_; lean_object* v___x_2656_; uint8_t v_isShared_2657_; uint8_t v_isSharedCheck_2662_; 
v_str_2650_ = lean_ctor_get(v_s_2648_, 0);
lean_inc_ref(v_str_2650_);
v_startInclusive_2651_ = lean_ctor_get(v_s_2648_, 1);
lean_inc(v_startInclusive_2651_);
v_endExclusive_2652_ = lean_ctor_get(v_s_2648_, 2);
v___x_2653_ = lean_nat_sub(v_endExclusive_2652_, v_startInclusive_2651_);
v___x_2654_ = l_String_Slice_Pos_prevn(v_s_2648_, v___x_2653_, v_n_2649_);
v_isSharedCheck_2662_ = !lean_is_exclusive(v_s_2648_);
if (v_isSharedCheck_2662_ == 0)
{
lean_object* v_unused_2663_; lean_object* v_unused_2664_; lean_object* v_unused_2665_; 
v_unused_2663_ = lean_ctor_get(v_s_2648_, 2);
lean_dec(v_unused_2663_);
v_unused_2664_ = lean_ctor_get(v_s_2648_, 1);
lean_dec(v_unused_2664_);
v_unused_2665_ = lean_ctor_get(v_s_2648_, 0);
lean_dec(v_unused_2665_);
v___x_2656_ = v_s_2648_;
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
else
{
lean_dec(v_s_2648_);
v___x_2656_ = lean_box(0);
v_isShared_2657_ = v_isSharedCheck_2662_;
goto v_resetjp_2655_;
}
v_resetjp_2655_:
{
lean_object* v___x_2658_; lean_object* v___x_2660_; 
v___x_2658_ = lean_nat_add(v_startInclusive_2651_, v___x_2654_);
lean_dec(v___x_2654_);
if (v_isShared_2657_ == 0)
{
lean_ctor_set(v___x_2656_, 2, v___x_2658_);
v___x_2660_ = v___x_2656_;
goto v_reusejp_2659_;
}
else
{
lean_object* v_reuseFailAlloc_2661_; 
v_reuseFailAlloc_2661_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2661_, 0, v_str_2650_);
lean_ctor_set(v_reuseFailAlloc_2661_, 1, v_startInclusive_2651_);
lean_ctor_set(v_reuseFailAlloc_2661_, 2, v___x_2658_);
v___x_2660_ = v_reuseFailAlloc_2661_;
goto v_reusejp_2659_;
}
v_reusejp_2659_:
{
return v___x_2660_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object* v_s_2666_, lean_object* v_pos_2667_, lean_object* v_inst_2668_){
_start:
{
lean_object* v_str_2669_; lean_object* v_startInclusive_2670_; lean_object* v_skipSuffix_x3f_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; lean_object* v___x_2674_; 
v_str_2669_ = lean_ctor_get(v_s_2666_, 0);
v_startInclusive_2670_ = lean_ctor_get(v_s_2666_, 1);
v_skipSuffix_x3f_2671_ = lean_ctor_get(v_inst_2668_, 0);
v___x_2672_ = lean_nat_add(v_startInclusive_2670_, v_pos_2667_);
lean_inc(v_startInclusive_2670_);
lean_inc_ref(v_str_2669_);
v___x_2673_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2673_, 0, v_str_2669_);
lean_ctor_set(v___x_2673_, 1, v_startInclusive_2670_);
lean_ctor_set(v___x_2673_, 2, v___x_2672_);
lean_inc_ref(v_skipSuffix_x3f_2671_);
v___x_2674_ = lean_apply_1(v_skipSuffix_x3f_2671_, v___x_2673_);
if (lean_obj_tag(v___x_2674_) == 0)
{
lean_dec_ref(v_inst_2668_);
return v_pos_2667_;
}
else
{
lean_object* v_val_2675_; lean_object* v___x_2676_; lean_object* v___x_2677_; uint8_t v___x_2678_; 
v_val_2675_ = lean_ctor_get(v___x_2674_, 0);
lean_inc(v_val_2675_);
lean_dec_ref_known(v___x_2674_, 1);
v___x_2676_ = lean_unsigned_to_nat(1u);
v___x_2677_ = lean_nat_add(v_val_2675_, v___x_2676_);
v___x_2678_ = lean_nat_dec_le(v___x_2677_, v_pos_2667_);
lean_dec(v___x_2677_);
if (v___x_2678_ == 0)
{
lean_dec(v_val_2675_);
lean_dec_ref(v_inst_2668_);
return v_pos_2667_;
}
else
{
lean_dec(v_pos_2667_);
v_pos_2667_ = v_val_2675_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg___boxed(lean_object* v_s_2680_, lean_object* v_pos_2681_, lean_object* v_inst_2682_){
_start:
{
lean_object* v_res_2683_; 
v_res_2683_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2680_, v_pos_2681_, v_inst_2682_);
lean_dec_ref(v_s_2680_);
return v_res_2683_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile(lean_object* v_00_u03c1_2684_, lean_object* v_s_2685_, lean_object* v_pos_2686_, lean_object* v_pat_2687_, lean_object* v_inst_2688_){
_start:
{
lean_object* v___x_2689_; 
v___x_2689_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2685_, v_pos_2686_, v_inst_2688_);
return v___x_2689_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_2690_, lean_object* v_s_2691_, lean_object* v_pos_2692_, lean_object* v_pat_2693_, lean_object* v_inst_2694_){
_start:
{
lean_object* v_res_2695_; 
v_res_2695_ = l_String_Slice_Pos_revSkipWhile(v_00_u03c1_2690_, v_s_2691_, v_pos_2692_, v_pat_2693_, v_inst_2694_);
lean_dec(v_pat_2693_);
lean_dec_ref(v_s_2691_);
return v_res_2695_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg(lean_object* v_s_2696_, lean_object* v_inst_2697_){
_start:
{
lean_object* v_startInclusive_2698_; lean_object* v_endExclusive_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; 
v_startInclusive_2698_ = lean_ctor_get(v_s_2696_, 1);
v_endExclusive_2699_ = lean_ctor_get(v_s_2696_, 2);
v___x_2700_ = lean_nat_sub(v_endExclusive_2699_, v_startInclusive_2698_);
v___x_2701_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2696_, v___x_2700_, v_inst_2697_);
return v___x_2701_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg___boxed(lean_object* v_s_2702_, lean_object* v_inst_2703_){
_start:
{
lean_object* v_res_2704_; 
v_res_2704_ = l_String_Slice_skipSuffixWhile___redArg(v_s_2702_, v_inst_2703_);
lean_dec_ref(v_s_2702_);
return v_res_2704_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile(lean_object* v_00_u03c1_2705_, lean_object* v_s_2706_, lean_object* v_pat_2707_, lean_object* v_inst_2708_){
_start:
{
lean_object* v_startInclusive_2709_; lean_object* v_endExclusive_2710_; lean_object* v___x_2711_; lean_object* v___x_2712_; 
v_startInclusive_2709_ = lean_ctor_get(v_s_2706_, 1);
v_endExclusive_2710_ = lean_ctor_get(v_s_2706_, 2);
v___x_2711_ = lean_nat_sub(v_endExclusive_2710_, v_startInclusive_2709_);
v___x_2712_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2706_, v___x_2711_, v_inst_2708_);
return v___x_2712_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___boxed(lean_object* v_00_u03c1_2713_, lean_object* v_s_2714_, lean_object* v_pat_2715_, lean_object* v_inst_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_String_Slice_skipSuffixWhile(v_00_u03c1_2713_, v_s_2714_, v_pat_2715_, v_inst_2716_);
lean_dec(v_pat_2715_);
lean_dec_ref(v_s_2714_);
return v_res_2717_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_revAll___redArg(lean_object* v_s_2718_, lean_object* v_inst_2719_){
_start:
{
lean_object* v_startInclusive_2720_; lean_object* v_endExclusive_2721_; lean_object* v___x_2722_; lean_object* v___x_2723_; lean_object* v___x_2724_; uint8_t v_decide_2725_; 
v_startInclusive_2720_ = lean_ctor_get(v_s_2718_, 1);
v_endExclusive_2721_ = lean_ctor_get(v_s_2718_, 2);
v___x_2722_ = lean_nat_sub(v_endExclusive_2721_, v_startInclusive_2720_);
v___x_2723_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2718_, v___x_2722_, v_inst_2719_);
v___x_2724_ = lean_unsigned_to_nat(0u);
v_decide_2725_ = lean_nat_dec_eq(v___x_2723_, v___x_2724_);
lean_dec(v___x_2723_);
return v_decide_2725_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___redArg___boxed(lean_object* v_s_2726_, lean_object* v_inst_2727_){
_start:
{
uint8_t v_res_2728_; lean_object* v_r_2729_; 
v_res_2728_ = l_String_Slice_revAll___redArg(v_s_2726_, v_inst_2727_);
lean_dec_ref(v_s_2726_);
v_r_2729_ = lean_box(v_res_2728_);
return v_r_2729_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_revAll(lean_object* v_00_u03c1_2730_, lean_object* v_s_2731_, lean_object* v_pat_2732_, lean_object* v_inst_2733_){
_start:
{
lean_object* v_startInclusive_2734_; lean_object* v_endExclusive_2735_; lean_object* v___x_2736_; lean_object* v___x_2737_; lean_object* v___x_2738_; uint8_t v_decide_2739_; 
v_startInclusive_2734_ = lean_ctor_get(v_s_2731_, 1);
v_endExclusive_2735_ = lean_ctor_get(v_s_2731_, 2);
v___x_2736_ = lean_nat_sub(v_endExclusive_2735_, v_startInclusive_2734_);
v___x_2737_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2731_, v___x_2736_, v_inst_2733_);
v___x_2738_ = lean_unsigned_to_nat(0u);
v_decide_2739_ = lean_nat_dec_eq(v___x_2737_, v___x_2738_);
lean_dec(v___x_2737_);
return v_decide_2739_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___boxed(lean_object* v_00_u03c1_2740_, lean_object* v_s_2741_, lean_object* v_pat_2742_, lean_object* v_inst_2743_){
_start:
{
uint8_t v_res_2744_; lean_object* v_r_2745_; 
v_res_2744_ = l_String_Slice_revAll(v_00_u03c1_2740_, v_s_2741_, v_pat_2742_, v_inst_2743_);
lean_dec(v_pat_2742_);
lean_dec_ref(v_s_2741_);
v_r_2745_ = lean_box(v_res_2744_);
return v_r_2745_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object* v_s_2746_, lean_object* v_inst_2747_){
_start:
{
lean_object* v_str_2748_; lean_object* v_startInclusive_2749_; lean_object* v_endExclusive_2750_; lean_object* v___x_2751_; lean_object* v___x_2752_; lean_object* v___x_2754_; uint8_t v_isShared_2755_; uint8_t v_isSharedCheck_2760_; 
v_str_2748_ = lean_ctor_get(v_s_2746_, 0);
lean_inc_ref(v_str_2748_);
v_startInclusive_2749_ = lean_ctor_get(v_s_2746_, 1);
lean_inc(v_startInclusive_2749_);
v_endExclusive_2750_ = lean_ctor_get(v_s_2746_, 2);
v___x_2751_ = lean_nat_sub(v_endExclusive_2750_, v_startInclusive_2749_);
v___x_2752_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2746_, v___x_2751_, v_inst_2747_);
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
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object* v_00_u03c1_2764_, lean_object* v_s_2765_, lean_object* v_pat_2766_, lean_object* v_inst_2767_){
_start:
{
lean_object* v_str_2768_; lean_object* v_startInclusive_2769_; lean_object* v_endExclusive_2770_; lean_object* v___x_2771_; lean_object* v___x_2772_; lean_object* v___x_2774_; uint8_t v_isShared_2775_; uint8_t v_isSharedCheck_2780_; 
v_str_2768_ = lean_ctor_get(v_s_2765_, 0);
lean_inc_ref(v_str_2768_);
v_startInclusive_2769_ = lean_ctor_get(v_s_2765_, 1);
lean_inc(v_startInclusive_2769_);
v_endExclusive_2770_ = lean_ctor_get(v_s_2765_, 2);
v___x_2771_ = lean_nat_sub(v_endExclusive_2770_, v_startInclusive_2769_);
v___x_2772_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2765_, v___x_2771_, v_inst_2767_);
v_isSharedCheck_2780_ = !lean_is_exclusive(v_s_2765_);
if (v_isSharedCheck_2780_ == 0)
{
lean_object* v_unused_2781_; lean_object* v_unused_2782_; lean_object* v_unused_2783_; 
v_unused_2781_ = lean_ctor_get(v_s_2765_, 2);
lean_dec(v_unused_2781_);
v_unused_2782_ = lean_ctor_get(v_s_2765_, 1);
lean_dec(v_unused_2782_);
v_unused_2783_ = lean_ctor_get(v_s_2765_, 0);
lean_dec(v_unused_2783_);
v___x_2774_ = v_s_2765_;
v_isShared_2775_ = v_isSharedCheck_2780_;
goto v_resetjp_2773_;
}
else
{
lean_dec(v_s_2765_);
v___x_2774_ = lean_box(0);
v_isShared_2775_ = v_isSharedCheck_2780_;
goto v_resetjp_2773_;
}
v_resetjp_2773_:
{
lean_object* v___x_2776_; lean_object* v___x_2778_; 
v___x_2776_ = lean_nat_add(v_startInclusive_2769_, v___x_2772_);
lean_dec(v___x_2772_);
if (v_isShared_2775_ == 0)
{
lean_ctor_set(v___x_2774_, 2, v___x_2776_);
v___x_2778_ = v___x_2774_;
goto v_reusejp_2777_;
}
else
{
lean_object* v_reuseFailAlloc_2779_; 
v_reuseFailAlloc_2779_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2779_, 0, v_str_2768_);
lean_ctor_set(v_reuseFailAlloc_2779_, 1, v_startInclusive_2769_);
lean_ctor_set(v_reuseFailAlloc_2779_, 2, v___x_2776_);
v___x_2778_ = v_reuseFailAlloc_2779_;
goto v_reusejp_2777_;
}
v_reusejp_2777_:
{
return v___x_2778_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object* v_00_u03c1_2784_, lean_object* v_s_2785_, lean_object* v_pat_2786_, lean_object* v_inst_2787_){
_start:
{
lean_object* v_res_2788_; 
v_res_2788_ = l_String_Slice_dropEndWhile(v_00_u03c1_2784_, v_s_2785_, v_pat_2786_, v_inst_2787_);
lean_dec(v_pat_2786_);
return v_res_2788_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiEnd___closed__0(void){
_start:
{
lean_object* v___x_2789_; lean_object* v___x_2790_; 
v___x_2789_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_2790_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_2789_);
return v___x_2790_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object* v_s_2791_){
_start:
{
lean_object* v___x_2792_; lean_object* v_str_2793_; lean_object* v_startInclusive_2794_; lean_object* v_endExclusive_2795_; lean_object* v___x_2796_; lean_object* v___x_2797_; lean_object* v___x_2799_; uint8_t v_isShared_2800_; uint8_t v_isSharedCheck_2805_; 
v___x_2792_ = lean_obj_once(&l_String_Slice_trimAsciiEnd___closed__0, &l_String_Slice_trimAsciiEnd___closed__0_once, _init_l_String_Slice_trimAsciiEnd___closed__0);
v_str_2793_ = lean_ctor_get(v_s_2791_, 0);
lean_inc_ref(v_str_2793_);
v_startInclusive_2794_ = lean_ctor_get(v_s_2791_, 1);
lean_inc(v_startInclusive_2794_);
v_endExclusive_2795_ = lean_ctor_get(v_s_2791_, 2);
v___x_2796_ = lean_nat_sub(v_endExclusive_2795_, v_startInclusive_2794_);
v___x_2797_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2791_, v___x_2796_, v___x_2792_);
v_isSharedCheck_2805_ = !lean_is_exclusive(v_s_2791_);
if (v_isSharedCheck_2805_ == 0)
{
lean_object* v_unused_2806_; lean_object* v_unused_2807_; lean_object* v_unused_2808_; 
v_unused_2806_ = lean_ctor_get(v_s_2791_, 2);
lean_dec(v_unused_2806_);
v_unused_2807_ = lean_ctor_get(v_s_2791_, 1);
lean_dec(v_unused_2807_);
v_unused_2808_ = lean_ctor_get(v_s_2791_, 0);
lean_dec(v_unused_2808_);
v___x_2799_ = v_s_2791_;
v_isShared_2800_ = v_isSharedCheck_2805_;
goto v_resetjp_2798_;
}
else
{
lean_dec(v_s_2791_);
v___x_2799_ = lean_box(0);
v_isShared_2800_ = v_isSharedCheck_2805_;
goto v_resetjp_2798_;
}
v_resetjp_2798_:
{
lean_object* v___x_2801_; lean_object* v___x_2803_; 
v___x_2801_ = lean_nat_add(v_startInclusive_2794_, v___x_2797_);
lean_dec(v___x_2797_);
if (v_isShared_2800_ == 0)
{
lean_ctor_set(v___x_2799_, 2, v___x_2801_);
v___x_2803_ = v___x_2799_;
goto v_reusejp_2802_;
}
else
{
lean_object* v_reuseFailAlloc_2804_; 
v_reuseFailAlloc_2804_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2804_, 0, v_str_2793_);
lean_ctor_set(v_reuseFailAlloc_2804_, 1, v_startInclusive_2794_);
lean_ctor_set(v_reuseFailAlloc_2804_, 2, v___x_2801_);
v___x_2803_ = v_reuseFailAlloc_2804_;
goto v_reusejp_2802_;
}
v_reusejp_2802_:
{
return v___x_2803_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object* v_s_2809_, lean_object* v_n_2810_){
_start:
{
lean_object* v_str_2811_; lean_object* v_startInclusive_2812_; lean_object* v_endExclusive_2813_; lean_object* v___x_2814_; lean_object* v___x_2815_; lean_object* v___x_2817_; uint8_t v_isShared_2818_; uint8_t v_isSharedCheck_2823_; 
v_str_2811_ = lean_ctor_get(v_s_2809_, 0);
lean_inc_ref(v_str_2811_);
v_startInclusive_2812_ = lean_ctor_get(v_s_2809_, 1);
lean_inc(v_startInclusive_2812_);
v_endExclusive_2813_ = lean_ctor_get(v_s_2809_, 2);
lean_inc(v_endExclusive_2813_);
v___x_2814_ = lean_nat_sub(v_endExclusive_2813_, v_startInclusive_2812_);
v___x_2815_ = l_String_Slice_Pos_prevn(v_s_2809_, v___x_2814_, v_n_2810_);
v_isSharedCheck_2823_ = !lean_is_exclusive(v_s_2809_);
if (v_isSharedCheck_2823_ == 0)
{
lean_object* v_unused_2824_; lean_object* v_unused_2825_; lean_object* v_unused_2826_; 
v_unused_2824_ = lean_ctor_get(v_s_2809_, 2);
lean_dec(v_unused_2824_);
v_unused_2825_ = lean_ctor_get(v_s_2809_, 1);
lean_dec(v_unused_2825_);
v_unused_2826_ = lean_ctor_get(v_s_2809_, 0);
lean_dec(v_unused_2826_);
v___x_2817_ = v_s_2809_;
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
else
{
lean_dec(v_s_2809_);
v___x_2817_ = lean_box(0);
v_isShared_2818_ = v_isSharedCheck_2823_;
goto v_resetjp_2816_;
}
v_resetjp_2816_:
{
lean_object* v___x_2819_; lean_object* v___x_2821_; 
v___x_2819_ = lean_nat_add(v_startInclusive_2812_, v___x_2815_);
lean_dec(v___x_2815_);
lean_dec(v_startInclusive_2812_);
if (v_isShared_2818_ == 0)
{
lean_ctor_set(v___x_2817_, 1, v___x_2819_);
v___x_2821_ = v___x_2817_;
goto v_reusejp_2820_;
}
else
{
lean_object* v_reuseFailAlloc_2822_; 
v_reuseFailAlloc_2822_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2822_, 0, v_str_2811_);
lean_ctor_set(v_reuseFailAlloc_2822_, 1, v___x_2819_);
lean_ctor_set(v_reuseFailAlloc_2822_, 2, v_endExclusive_2813_);
v___x_2821_ = v_reuseFailAlloc_2822_;
goto v_reusejp_2820_;
}
v_reusejp_2820_:
{
return v___x_2821_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___redArg(lean_object* v_s_2827_, lean_object* v_inst_2828_){
_start:
{
lean_object* v_str_2829_; lean_object* v_startInclusive_2830_; lean_object* v_endExclusive_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2835_; uint8_t v_isShared_2836_; uint8_t v_isSharedCheck_2841_; 
v_str_2829_ = lean_ctor_get(v_s_2827_, 0);
lean_inc_ref(v_str_2829_);
v_startInclusive_2830_ = lean_ctor_get(v_s_2827_, 1);
lean_inc(v_startInclusive_2830_);
v_endExclusive_2831_ = lean_ctor_get(v_s_2827_, 2);
lean_inc(v_endExclusive_2831_);
v___x_2832_ = lean_nat_sub(v_endExclusive_2831_, v_startInclusive_2830_);
v___x_2833_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2827_, v___x_2832_, v_inst_2828_);
v_isSharedCheck_2841_ = !lean_is_exclusive(v_s_2827_);
if (v_isSharedCheck_2841_ == 0)
{
lean_object* v_unused_2842_; lean_object* v_unused_2843_; lean_object* v_unused_2844_; 
v_unused_2842_ = lean_ctor_get(v_s_2827_, 2);
lean_dec(v_unused_2842_);
v_unused_2843_ = lean_ctor_get(v_s_2827_, 1);
lean_dec(v_unused_2843_);
v_unused_2844_ = lean_ctor_get(v_s_2827_, 0);
lean_dec(v_unused_2844_);
v___x_2835_ = v_s_2827_;
v_isShared_2836_ = v_isSharedCheck_2841_;
goto v_resetjp_2834_;
}
else
{
lean_dec(v_s_2827_);
v___x_2835_ = lean_box(0);
v_isShared_2836_ = v_isSharedCheck_2841_;
goto v_resetjp_2834_;
}
v_resetjp_2834_:
{
lean_object* v___x_2837_; lean_object* v___x_2839_; 
v___x_2837_ = lean_nat_add(v_startInclusive_2830_, v___x_2833_);
lean_dec(v___x_2833_);
lean_dec(v_startInclusive_2830_);
if (v_isShared_2836_ == 0)
{
lean_ctor_set(v___x_2835_, 1, v___x_2837_);
v___x_2839_ = v___x_2835_;
goto v_reusejp_2838_;
}
else
{
lean_object* v_reuseFailAlloc_2840_; 
v_reuseFailAlloc_2840_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2840_, 0, v_str_2829_);
lean_ctor_set(v_reuseFailAlloc_2840_, 1, v___x_2837_);
lean_ctor_set(v_reuseFailAlloc_2840_, 2, v_endExclusive_2831_);
v___x_2839_ = v_reuseFailAlloc_2840_;
goto v_reusejp_2838_;
}
v_reusejp_2838_:
{
return v___x_2839_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile(lean_object* v_00_u03c1_2845_, lean_object* v_s_2846_, lean_object* v_pat_2847_, lean_object* v_inst_2848_){
_start:
{
lean_object* v_str_2849_; lean_object* v_startInclusive_2850_; lean_object* v_endExclusive_2851_; lean_object* v___x_2852_; lean_object* v___x_2853_; lean_object* v___x_2855_; uint8_t v_isShared_2856_; uint8_t v_isSharedCheck_2861_; 
v_str_2849_ = lean_ctor_get(v_s_2846_, 0);
lean_inc_ref(v_str_2849_);
v_startInclusive_2850_ = lean_ctor_get(v_s_2846_, 1);
lean_inc(v_startInclusive_2850_);
v_endExclusive_2851_ = lean_ctor_get(v_s_2846_, 2);
lean_inc(v_endExclusive_2851_);
v___x_2852_ = lean_nat_sub(v_endExclusive_2851_, v_startInclusive_2850_);
v___x_2853_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2846_, v___x_2852_, v_inst_2848_);
v_isSharedCheck_2861_ = !lean_is_exclusive(v_s_2846_);
if (v_isSharedCheck_2861_ == 0)
{
lean_object* v_unused_2862_; lean_object* v_unused_2863_; lean_object* v_unused_2864_; 
v_unused_2862_ = lean_ctor_get(v_s_2846_, 2);
lean_dec(v_unused_2862_);
v_unused_2863_ = lean_ctor_get(v_s_2846_, 1);
lean_dec(v_unused_2863_);
v_unused_2864_ = lean_ctor_get(v_s_2846_, 0);
lean_dec(v_unused_2864_);
v___x_2855_ = v_s_2846_;
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
else
{
lean_dec(v_s_2846_);
v___x_2855_ = lean_box(0);
v_isShared_2856_ = v_isSharedCheck_2861_;
goto v_resetjp_2854_;
}
v_resetjp_2854_:
{
lean_object* v___x_2857_; lean_object* v___x_2859_; 
v___x_2857_ = lean_nat_add(v_startInclusive_2850_, v___x_2853_);
lean_dec(v___x_2853_);
lean_dec(v_startInclusive_2850_);
if (v_isShared_2856_ == 0)
{
lean_ctor_set(v___x_2855_, 1, v___x_2857_);
v___x_2859_ = v___x_2855_;
goto v_reusejp_2858_;
}
else
{
lean_object* v_reuseFailAlloc_2860_; 
v_reuseFailAlloc_2860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2860_, 0, v_str_2849_);
lean_ctor_set(v_reuseFailAlloc_2860_, 1, v___x_2857_);
lean_ctor_set(v_reuseFailAlloc_2860_, 2, v_endExclusive_2851_);
v___x_2859_ = v_reuseFailAlloc_2860_;
goto v_reusejp_2858_;
}
v_reusejp_2858_:
{
return v___x_2859_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___boxed(lean_object* v_00_u03c1_2865_, lean_object* v_s_2866_, lean_object* v_pat_2867_, lean_object* v_inst_2868_){
_start:
{
lean_object* v_res_2869_; 
v_res_2869_ = l_String_Slice_takeEndWhile(v_00_u03c1_2865_, v_s_2866_, v_pat_2867_, v_inst_2868_);
lean_dec(v_pat_2867_);
return v_res_2869_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___redArg(lean_object* v_inst_2870_, lean_object* v_s_2871_, lean_object* v_inst_2872_){
_start:
{
lean_object* v___f_2873_; lean_object* v_searcher_2874_; lean_object* v___x_2875_; lean_object* v___f_2876_; lean_object* v___x_2877_; 
v___f_2873_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_2871_);
v_searcher_2874_ = lean_apply_1(v_inst_2872_, v_s_2871_);
v___x_2875_ = lean_box(0);
v___f_2876_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_2877_ = lean_apply_7(v_inst_2870_, v_s_2871_, v___f_2873_, lean_box(0), lean_box(0), v_searcher_2874_, v___x_2875_, v___f_2876_);
return v___x_2877_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f(lean_object* v_00_u03c3_2878_, lean_object* v_inst_2879_, lean_object* v_inst_2880_, lean_object* v_00_u03c1_2881_, lean_object* v_s_2882_, lean_object* v_pat_2883_, lean_object* v_inst_2884_){
_start:
{
lean_object* v___x_2885_; 
v___x_2885_ = l_String_Slice_revFind_x3f___redArg(v_inst_2880_, v_s_2882_, v_inst_2884_);
return v___x_2885_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___boxed(lean_object* v_00_u03c3_2886_, lean_object* v_inst_2887_, lean_object* v_inst_2888_, lean_object* v_00_u03c1_2889_, lean_object* v_s_2890_, lean_object* v_pat_2891_, lean_object* v_inst_2892_){
_start:
{
lean_object* v_res_2893_; 
v_res_2893_ = l_String_Slice_revFind_x3f(v_00_u03c3_2886_, v_inst_2887_, v_inst_2888_, v_00_u03c1_2889_, v_s_2890_, v_pat_2891_, v_inst_2892_);
lean_dec(v_pat_2891_);
lean_dec(v_inst_2887_);
return v_res_2893_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(lean_object* v_s_2894_, lean_object* v_pos_2895_){
_start:
{
lean_object* v_str_2896_; lean_object* v_startInclusive_2897_; lean_object* v_endExclusive_2898_; lean_object* v___x_2899_; lean_object* v___x_2908_; lean_object* v___x_2909_; uint8_t v_decide_2910_; 
v_str_2896_ = lean_ctor_get(v_s_2894_, 0);
v_startInclusive_2897_ = lean_ctor_get(v_s_2894_, 1);
v_endExclusive_2898_ = lean_ctor_get(v_s_2894_, 2);
v___x_2899_ = lean_nat_add(v_startInclusive_2897_, v_pos_2895_);
v___x_2908_ = lean_unsigned_to_nat(0u);
v___x_2909_ = lean_nat_sub(v_endExclusive_2898_, v___x_2899_);
v_decide_2910_ = lean_nat_dec_eq(v___x_2908_, v___x_2909_);
lean_dec(v___x_2909_);
if (v_decide_2910_ == 0)
{
uint32_t v___x_2911_; uint32_t v___x_2912_; uint8_t v___x_2913_; 
v___x_2911_ = lean_string_utf8_get_fast(v_str_2896_, v___x_2899_);
v___x_2912_ = 32;
v___x_2913_ = lean_uint32_dec_eq(v___x_2911_, v___x_2912_);
if (v___x_2913_ == 0)
{
uint32_t v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = 9;
v___x_2915_ = lean_uint32_dec_eq(v___x_2911_, v___x_2914_);
if (v___x_2915_ == 0)
{
uint32_t v___x_2916_; uint8_t v___x_2917_; 
v___x_2916_ = 13;
v___x_2917_ = lean_uint32_dec_eq(v___x_2911_, v___x_2916_);
if (v___x_2917_ == 0)
{
uint32_t v___x_2918_; uint8_t v___x_2919_; 
v___x_2918_ = 10;
v___x_2919_ = lean_uint32_dec_eq(v___x_2911_, v___x_2918_);
if (v___x_2919_ == 0)
{
lean_dec(v___x_2899_);
return v_pos_2895_;
}
else
{
goto v___jp_2900_;
}
}
else
{
goto v___jp_2900_;
}
}
else
{
goto v___jp_2900_;
}
}
else
{
goto v___jp_2900_;
}
}
else
{
lean_dec(v___x_2899_);
return v_pos_2895_;
}
v___jp_2900_:
{
lean_object* v___x_2901_; lean_object* v___x_2902_; lean_object* v___x_2903_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v___x_2906_; 
v___x_2901_ = lean_string_utf8_next_fast(v_str_2896_, v___x_2899_);
v___x_2902_ = lean_nat_sub(v___x_2901_, v___x_2899_);
lean_dec(v___x_2899_);
v___x_2903_ = lean_nat_add(v_pos_2895_, v___x_2902_);
lean_dec(v___x_2902_);
v___x_2904_ = lean_unsigned_to_nat(1u);
v___x_2905_ = lean_nat_add(v_pos_2895_, v___x_2904_);
v___x_2906_ = lean_nat_dec_le(v___x_2905_, v___x_2903_);
lean_dec(v___x_2905_);
if (v___x_2906_ == 0)
{
lean_dec(v___x_2903_);
return v_pos_2895_;
}
else
{
lean_dec(v_pos_2895_);
v_pos_2895_ = v___x_2903_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0___boxed(lean_object* v_s_2920_, lean_object* v_pos_2921_){
_start:
{
lean_object* v_res_2922_; 
v_res_2922_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2920_, v_pos_2921_);
lean_dec_ref(v_s_2920_);
return v_res_2922_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(lean_object* v_s_2923_, lean_object* v_pos_2924_){
_start:
{
lean_object* v_str_2925_; lean_object* v_startInclusive_2926_; lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; uint8_t v_decide_2930_; 
v_str_2925_ = lean_ctor_get(v_s_2923_, 0);
v_startInclusive_2926_ = lean_ctor_get(v_s_2923_, 1);
v___x_2927_ = lean_nat_add(v_startInclusive_2926_, v_pos_2924_);
v___x_2928_ = lean_nat_sub(v___x_2927_, v_startInclusive_2926_);
v___x_2929_ = lean_unsigned_to_nat(0u);
v_decide_2930_ = lean_nat_dec_eq(v___x_2928_, v___x_2929_);
if (v_decide_2930_ == 0)
{
lean_object* v___x_2931_; lean_object* v___x_2932_; lean_object* v___x_2933_; lean_object* v___x_2934_; lean_object* v___x_2939_; uint32_t v___x_2940_; uint32_t v___x_2941_; uint8_t v___x_2942_; 
lean_inc(v_startInclusive_2926_);
lean_inc_ref(v_str_2925_);
v___x_2931_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2931_, 0, v_str_2925_);
lean_ctor_set(v___x_2931_, 1, v_startInclusive_2926_);
lean_ctor_set(v___x_2931_, 2, v___x_2927_);
v___x_2932_ = lean_unsigned_to_nat(1u);
v___x_2933_ = lean_nat_sub(v___x_2928_, v___x_2932_);
lean_dec(v___x_2928_);
v___x_2934_ = l_String_Slice_posLE(v___x_2931_, v___x_2933_);
lean_dec_ref_known(v___x_2931_, 3);
v___x_2939_ = lean_nat_add(v_startInclusive_2926_, v___x_2934_);
v___x_2940_ = lean_string_utf8_get_fast(v_str_2925_, v___x_2939_);
lean_dec(v___x_2939_);
v___x_2941_ = 32;
v___x_2942_ = lean_uint32_dec_eq(v___x_2940_, v___x_2941_);
if (v___x_2942_ == 0)
{
uint32_t v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = 9;
v___x_2944_ = lean_uint32_dec_eq(v___x_2940_, v___x_2943_);
if (v___x_2944_ == 0)
{
uint32_t v___x_2945_; uint8_t v___x_2946_; 
v___x_2945_ = 13;
v___x_2946_ = lean_uint32_dec_eq(v___x_2940_, v___x_2945_);
if (v___x_2946_ == 0)
{
uint32_t v___x_2947_; uint8_t v___x_2948_; 
v___x_2947_ = 10;
v___x_2948_ = lean_uint32_dec_eq(v___x_2940_, v___x_2947_);
if (v___x_2948_ == 0)
{
lean_dec(v___x_2934_);
return v_pos_2924_;
}
else
{
goto v___jp_2935_;
}
}
else
{
goto v___jp_2935_;
}
}
else
{
goto v___jp_2935_;
}
}
else
{
goto v___jp_2935_;
}
v___jp_2935_:
{
lean_object* v___x_2936_; uint8_t v___x_2937_; 
v___x_2936_ = lean_nat_add(v___x_2934_, v___x_2932_);
v___x_2937_ = lean_nat_dec_le(v___x_2936_, v_pos_2924_);
lean_dec(v___x_2936_);
if (v___x_2937_ == 0)
{
lean_dec(v___x_2934_);
return v_pos_2924_;
}
else
{
lean_dec(v_pos_2924_);
v_pos_2924_ = v___x_2934_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2928_);
lean_dec(v___x_2927_);
return v_pos_2924_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1___boxed(lean_object* v_s_2949_, lean_object* v_pos_2950_){
_start:
{
lean_object* v_res_2951_; 
v_res_2951_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v_s_2949_, v_pos_2950_);
lean_dec_ref(v_s_2949_);
return v_res_2951_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAscii(lean_object* v_s_2952_){
_start:
{
lean_object* v_str_2953_; lean_object* v_startInclusive_2954_; lean_object* v_endExclusive_2955_; lean_object* v___x_2956_; lean_object* v___x_2957_; lean_object* v___x_2959_; uint8_t v_isShared_2960_; uint8_t v_isSharedCheck_2969_; 
v_str_2953_ = lean_ctor_get(v_s_2952_, 0);
lean_inc_ref(v_str_2953_);
v_startInclusive_2954_ = lean_ctor_get(v_s_2952_, 1);
lean_inc(v_startInclusive_2954_);
v_endExclusive_2955_ = lean_ctor_get(v_s_2952_, 2);
lean_inc(v_endExclusive_2955_);
v___x_2956_ = lean_unsigned_to_nat(0u);
v___x_2957_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2952_, v___x_2956_);
v_isSharedCheck_2969_ = !lean_is_exclusive(v_s_2952_);
if (v_isSharedCheck_2969_ == 0)
{
lean_object* v_unused_2970_; lean_object* v_unused_2971_; lean_object* v_unused_2972_; 
v_unused_2970_ = lean_ctor_get(v_s_2952_, 2);
lean_dec(v_unused_2970_);
v_unused_2971_ = lean_ctor_get(v_s_2952_, 1);
lean_dec(v_unused_2971_);
v_unused_2972_ = lean_ctor_get(v_s_2952_, 0);
lean_dec(v_unused_2972_);
v___x_2959_ = v_s_2952_;
v_isShared_2960_ = v_isSharedCheck_2969_;
goto v_resetjp_2958_;
}
else
{
lean_dec(v_s_2952_);
v___x_2959_ = lean_box(0);
v_isShared_2960_ = v_isSharedCheck_2969_;
goto v_resetjp_2958_;
}
v_resetjp_2958_:
{
lean_object* v___x_2961_; lean_object* v___x_2963_; 
v___x_2961_ = lean_nat_add(v_startInclusive_2954_, v___x_2957_);
lean_dec(v___x_2957_);
lean_dec(v_startInclusive_2954_);
lean_inc(v_endExclusive_2955_);
lean_inc(v___x_2961_);
lean_inc_ref(v_str_2953_);
if (v_isShared_2960_ == 0)
{
lean_ctor_set(v___x_2959_, 1, v___x_2961_);
v___x_2963_ = v___x_2959_;
goto v_reusejp_2962_;
}
else
{
lean_object* v_reuseFailAlloc_2968_; 
v_reuseFailAlloc_2968_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2968_, 0, v_str_2953_);
lean_ctor_set(v_reuseFailAlloc_2968_, 1, v___x_2961_);
lean_ctor_set(v_reuseFailAlloc_2968_, 2, v_endExclusive_2955_);
v___x_2963_ = v_reuseFailAlloc_2968_;
goto v_reusejp_2962_;
}
v_reusejp_2962_:
{
lean_object* v___x_2964_; lean_object* v___x_2965_; lean_object* v___x_2966_; lean_object* v___x_2967_; 
v___x_2964_ = lean_nat_sub(v_endExclusive_2955_, v___x_2961_);
lean_dec(v_endExclusive_2955_);
v___x_2965_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v___x_2963_, v___x_2964_);
lean_dec_ref(v___x_2963_);
v___x_2966_ = lean_nat_add(v___x_2961_, v___x_2965_);
lean_dec(v___x_2965_);
v___x_2967_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2967_, 0, v_str_2953_);
lean_ctor_set(v___x_2967_, 1, v___x_2961_);
lean_ctor_set(v___x_2967_, 2, v___x_2966_);
return v___x_2967_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(lean_object* v_s1_2973_, lean_object* v_s1Curr_2974_, lean_object* v_s2_2975_, lean_object* v_s2Curr_2976_){
_start:
{
lean_object* v_str_2977_; lean_object* v_startInclusive_2978_; lean_object* v_endExclusive_2979_; lean_object* v_str_2980_; lean_object* v_startInclusive_2981_; lean_object* v_endExclusive_2982_; lean_object* v___x_2983_; uint8_t v___x_2984_; lean_object* v___x_2985_; uint8_t v___y_2987_; 
v_str_2977_ = lean_ctor_get(v_s1_2973_, 0);
v_startInclusive_2978_ = lean_ctor_get(v_s1_2973_, 1);
v_endExclusive_2979_ = lean_ctor_get(v_s1_2973_, 2);
v_str_2980_ = lean_ctor_get(v_s2_2975_, 0);
v_startInclusive_2981_ = lean_ctor_get(v_s2_2975_, 1);
v_endExclusive_2982_ = lean_ctor_get(v_s2_2975_, 2);
v___x_2983_ = lean_nat_sub(v_endExclusive_2979_, v_startInclusive_2978_);
v___x_2984_ = l_String_instDecidableLtRaw(v_s1Curr_2974_, v___x_2983_);
v___x_2985_ = lean_nat_sub(v_endExclusive_2982_, v_startInclusive_2981_);
if (v___x_2984_ == 0)
{
v___y_2987_ = v___x_2984_;
goto v___jp_2986_;
}
else
{
uint8_t v___x_3012_; 
v___x_3012_ = l_String_instDecidableLtRaw(v_s2Curr_2976_, v___x_2985_);
v___y_2987_ = v___x_3012_;
goto v___jp_2986_;
}
v___jp_2986_:
{
if (v___y_2987_ == 0)
{
uint8_t v_decide_2988_; 
v_decide_2988_ = lean_nat_dec_eq(v_s1Curr_2974_, v___x_2983_);
lean_dec(v___x_2983_);
lean_dec(v_s1Curr_2974_);
if (v_decide_2988_ == 0)
{
lean_dec(v___x_2985_);
lean_dec(v_s2Curr_2976_);
return v___y_2987_;
}
else
{
uint8_t v_decide_2989_; 
v_decide_2989_ = lean_nat_dec_eq(v_s2Curr_2976_, v___x_2985_);
lean_dec(v___x_2985_);
lean_dec(v_s2Curr_2976_);
return v_decide_2989_;
}
}
else
{
lean_object* v___x_2990_; uint8_t v___x_2991_; uint8_t v___x_2992_; uint8_t v___x_2993_; uint8_t v___x_2994_; uint8_t v___x_2995_; uint8_t v___x_2996_; uint8_t v___x_2997_; uint8_t v___x_2998_; uint8_t v_c1_2999_; lean_object* v___x_3000_; uint8_t v___x_3001_; uint8_t v___x_3002_; uint8_t v___x_3003_; uint8_t v___x_3004_; uint8_t v___x_3005_; uint8_t v_c2_3006_; uint8_t v___x_3007_; 
lean_dec(v___x_2985_);
lean_dec(v___x_2983_);
v___x_2990_ = lean_nat_add(v_startInclusive_2978_, v_s1Curr_2974_);
v___x_2991_ = lean_string_get_byte_fast(v_str_2977_, v___x_2990_);
v___x_2992_ = 65;
v___x_2993_ = lean_uint8_sub(v___x_2991_, v___x_2992_);
v___x_2994_ = 26;
v___x_2995_ = lean_uint8_dec_lt(v___x_2993_, v___x_2994_);
v___x_2996_ = lean_bool_to_uint8(v___x_2995_);
v___x_2997_ = 5;
v___x_2998_ = lean_uint8_shift_left(v___x_2996_, v___x_2997_);
v_c1_2999_ = lean_uint8_add(v___x_2991_, v___x_2998_);
v___x_3000_ = lean_nat_add(v_startInclusive_2981_, v_s2Curr_2976_);
v___x_3001_ = lean_string_get_byte_fast(v_str_2980_, v___x_3000_);
v___x_3002_ = lean_uint8_sub(v___x_3001_, v___x_2992_);
v___x_3003_ = lean_uint8_dec_lt(v___x_3002_, v___x_2994_);
v___x_3004_ = lean_bool_to_uint8(v___x_3003_);
v___x_3005_ = lean_uint8_shift_left(v___x_3004_, v___x_2997_);
v_c2_3006_ = lean_uint8_add(v___x_3001_, v___x_3005_);
v___x_3007_ = lean_uint8_dec_eq(v_c1_2999_, v_c2_3006_);
if (v___x_3007_ == 0)
{
lean_dec(v_s2Curr_2976_);
lean_dec(v_s1Curr_2974_);
return v___x_3007_;
}
else
{
lean_object* v___x_3008_; lean_object* v___x_3009_; lean_object* v___x_3010_; 
v___x_3008_ = lean_unsigned_to_nat(1u);
v___x_3009_ = lean_nat_add(v_s1Curr_2974_, v___x_3008_);
lean_dec(v_s1Curr_2974_);
v___x_3010_ = lean_nat_add(v_s2Curr_2976_, v___x_3008_);
lean_dec(v_s2Curr_2976_);
v_s1Curr_2974_ = v___x_3009_;
v_s2Curr_2976_ = v___x_3010_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object* v_s1_3013_, lean_object* v_s1Curr_3014_, lean_object* v_s2_3015_, lean_object* v_s2Curr_3016_){
_start:
{
uint8_t v_res_3017_; lean_object* v_r_3018_; 
v_res_3017_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_3013_, v_s1Curr_3014_, v_s2_3015_, v_s2Curr_3016_);
lean_dec_ref(v_s2_3015_);
lean_dec_ref(v_s1_3013_);
v_r_3018_ = lean_box(v_res_3017_);
return v_r_3018_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object* v_s1_3019_, lean_object* v_s2_3020_){
_start:
{
lean_object* v_startInclusive_3021_; lean_object* v_endExclusive_3022_; lean_object* v_startInclusive_3023_; lean_object* v_endExclusive_3024_; lean_object* v___x_3025_; lean_object* v___x_3026_; uint8_t v___x_3027_; 
v_startInclusive_3021_ = lean_ctor_get(v_s1_3019_, 1);
v_endExclusive_3022_ = lean_ctor_get(v_s1_3019_, 2);
v_startInclusive_3023_ = lean_ctor_get(v_s2_3020_, 1);
v_endExclusive_3024_ = lean_ctor_get(v_s2_3020_, 2);
v___x_3025_ = lean_nat_sub(v_endExclusive_3022_, v_startInclusive_3021_);
v___x_3026_ = lean_nat_sub(v_endExclusive_3024_, v_startInclusive_3023_);
v___x_3027_ = lean_nat_dec_eq(v___x_3025_, v___x_3026_);
lean_dec(v___x_3026_);
lean_dec(v___x_3025_);
if (v___x_3027_ == 0)
{
return v___x_3027_;
}
else
{
lean_object* v___x_3028_; uint8_t v___x_3029_; 
v___x_3028_ = lean_unsigned_to_nat(0u);
v___x_3029_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_3019_, v___x_3028_, v_s2_3020_, v___x_3028_);
return v___x_3029_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object* v_s1_3030_, lean_object* v_s2_3031_){
_start:
{
uint8_t v_res_3032_; lean_object* v_r_3033_; 
v_res_3032_ = l_String_Slice_eqIgnoreAsciiCase(v_s1_3030_, v_s2_3031_);
lean_dec_ref(v_s2_3031_);
lean_dec_ref(v_s1_3030_);
v_r_3033_ = lean_box(v_res_3032_);
return v_r_3033_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines_lineMap(lean_object* v_s_3034_){
_start:
{
lean_object* v_str_3035_; lean_object* v_startInclusive_3036_; lean_object* v_endExclusive_3037_; lean_object* v___x_3038_; lean_object* v___x_3039_; uint8_t v_decide_3040_; 
v_str_3035_ = lean_ctor_get(v_s_3034_, 0);
v_startInclusive_3036_ = lean_ctor_get(v_s_3034_, 1);
v_endExclusive_3037_ = lean_ctor_get(v_s_3034_, 2);
v___x_3038_ = lean_nat_sub(v_endExclusive_3037_, v_startInclusive_3036_);
v___x_3039_ = lean_unsigned_to_nat(0u);
v_decide_3040_ = lean_nat_dec_eq(v___x_3038_, v___x_3039_);
if (v_decide_3040_ == 0)
{
uint32_t v___x_3041_; lean_object* v___x_3042_; lean_object* v___x_3043_; lean_object* v___x_3044_; lean_object* v___x_3045_; uint32_t v___x_3046_; uint8_t v___x_3047_; 
v___x_3041_ = 10;
v___x_3042_ = lean_unsigned_to_nat(1u);
v___x_3043_ = lean_nat_sub(v___x_3038_, v___x_3042_);
lean_dec(v___x_3038_);
v___x_3044_ = l_String_Slice_posLE(v_s_3034_, v___x_3043_);
v___x_3045_ = lean_nat_add(v_startInclusive_3036_, v___x_3044_);
lean_dec(v___x_3044_);
v___x_3046_ = lean_string_utf8_get_fast(v_str_3035_, v___x_3045_);
v___x_3047_ = lean_uint32_dec_eq(v___x_3046_, v___x_3041_);
if (v___x_3047_ == 0)
{
lean_dec(v___x_3045_);
return v_s_3034_;
}
else
{
lean_object* v___x_3049_; uint8_t v_isShared_3050_; uint8_t v_isSharedCheck_3063_; 
lean_inc(v_startInclusive_3036_);
lean_inc_ref(v_str_3035_);
v_isSharedCheck_3063_ = !lean_is_exclusive(v_s_3034_);
if (v_isSharedCheck_3063_ == 0)
{
lean_object* v_unused_3064_; lean_object* v_unused_3065_; lean_object* v_unused_3066_; 
v_unused_3064_ = lean_ctor_get(v_s_3034_, 2);
lean_dec(v_unused_3064_);
v_unused_3065_ = lean_ctor_get(v_s_3034_, 1);
lean_dec(v_unused_3065_);
v_unused_3066_ = lean_ctor_get(v_s_3034_, 0);
lean_dec(v_unused_3066_);
v___x_3049_ = v_s_3034_;
v_isShared_3050_ = v_isSharedCheck_3063_;
goto v_resetjp_3048_;
}
else
{
lean_dec(v_s_3034_);
v___x_3049_ = lean_box(0);
v_isShared_3050_ = v_isSharedCheck_3063_;
goto v_resetjp_3048_;
}
v_resetjp_3048_:
{
lean_object* v___x_3052_; 
lean_inc(v___x_3045_);
lean_inc(v_startInclusive_3036_);
lean_inc_ref(v_str_3035_);
if (v_isShared_3050_ == 0)
{
lean_ctor_set(v___x_3049_, 2, v___x_3045_);
v___x_3052_ = v___x_3049_;
goto v_reusejp_3051_;
}
else
{
lean_object* v_reuseFailAlloc_3062_; 
v_reuseFailAlloc_3062_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3062_, 0, v_str_3035_);
lean_ctor_set(v_reuseFailAlloc_3062_, 1, v_startInclusive_3036_);
lean_ctor_set(v_reuseFailAlloc_3062_, 2, v___x_3045_);
v___x_3052_ = v_reuseFailAlloc_3062_;
goto v_reusejp_3051_;
}
v_reusejp_3051_:
{
lean_object* v___x_3053_; uint8_t v_decide_3054_; 
v___x_3053_ = lean_nat_sub(v___x_3045_, v_startInclusive_3036_);
lean_dec(v___x_3045_);
v_decide_3054_ = lean_nat_dec_eq(v___x_3053_, v___x_3039_);
if (v_decide_3054_ == 0)
{
uint32_t v___x_3055_; lean_object* v___x_3056_; lean_object* v___x_3057_; lean_object* v___x_3058_; uint32_t v___x_3059_; uint8_t v___x_3060_; 
v___x_3055_ = 13;
v___x_3056_ = lean_nat_sub(v___x_3053_, v___x_3042_);
lean_dec(v___x_3053_);
v___x_3057_ = l_String_Slice_posLE(v___x_3052_, v___x_3056_);
v___x_3058_ = lean_nat_add(v_startInclusive_3036_, v___x_3057_);
lean_dec(v___x_3057_);
v___x_3059_ = lean_string_utf8_get_fast(v_str_3035_, v___x_3058_);
v___x_3060_ = lean_uint32_dec_eq(v___x_3059_, v___x_3055_);
if (v___x_3060_ == 0)
{
lean_dec(v___x_3058_);
lean_dec(v_startInclusive_3036_);
lean_dec_ref(v_str_3035_);
return v___x_3052_;
}
else
{
lean_object* v___x_3061_; 
lean_dec_ref(v___x_3052_);
v___x_3061_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3061_, 0, v_str_3035_);
lean_ctor_set(v___x_3061_, 1, v_startInclusive_3036_);
lean_ctor_set(v___x_3061_, 2, v___x_3058_);
return v___x_3061_;
}
}
else
{
lean_dec(v___x_3053_);
lean_dec(v_startInclusive_3036_);
lean_dec_ref(v_str_3035_);
return v___x_3052_;
}
}
}
}
}
else
{
lean_dec(v___x_3038_);
return v_s_3034_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg(){
_start:
{
lean_object* v___x_3070_; 
v___x_3070_ = ((lean_object*)(l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___closed__0));
return v___x_3070_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___boxed(lean_object* v___dummy_3071_){
_start:
{
lean_object* v_res_3072_; 
v_res_3072_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
return v_res_3072_;
}
}
static lean_object* _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(lean_object* v_s_3074_){
_start:
{
lean_object* v___x_3075_; 
v___x_3075_ = lean_obj_once(&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0, &l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_once, _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0);
return v___x_3075_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(lean_object* v_s_3076_){
_start:
{
lean_object* v_res_3077_; 
v_res_3077_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_3076_);
lean_dec_ref(v_s_3076_);
return v_res_3077_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines(lean_object* v_s_3078_){
_start:
{
lean_object* v___x_3079_; 
v___x_3079_ = lean_obj_once(&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0, &l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_once, _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0);
return v___x_3079_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines___boxed(lean_object* v_s_3080_){
_start:
{
lean_object* v_res_3081_; 
v_res_3081_ = l_String_Slice_lines(v_s_3080_);
lean_dec_ref(v_s_3080_);
return v_res_3081_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(lean_object* v_s_3082_, lean_object* v_a_3083_, lean_object* v_b_3084_){
_start:
{
lean_object* v_str_3085_; lean_object* v_startInclusive_3086_; lean_object* v_endExclusive_3087_; lean_object* v___x_3088_; uint8_t v_decide_3089_; 
v_str_3085_ = lean_ctor_get(v_s_3082_, 0);
v_startInclusive_3086_ = lean_ctor_get(v_s_3082_, 1);
v_endExclusive_3087_ = lean_ctor_get(v_s_3082_, 2);
v___x_3088_ = lean_nat_sub(v_endExclusive_3087_, v_startInclusive_3086_);
v_decide_3089_ = lean_nat_dec_eq(v_a_3083_, v___x_3088_);
lean_dec(v___x_3088_);
if (v_decide_3089_ == 0)
{
lean_object* v_snd_3090_; lean_object* v___x_3092_; uint8_t v_isShared_3093_; uint8_t v_isSharedCheck_3121_; 
v_snd_3090_ = lean_ctor_get(v_b_3084_, 1);
v_isSharedCheck_3121_ = !lean_is_exclusive(v_b_3084_);
if (v_isSharedCheck_3121_ == 0)
{
lean_object* v_unused_3122_; 
v_unused_3122_ = lean_ctor_get(v_b_3084_, 0);
lean_dec(v_unused_3122_);
v___x_3092_ = v_b_3084_;
v_isShared_3093_ = v_isSharedCheck_3121_;
goto v_resetjp_3091_;
}
else
{
lean_inc(v_snd_3090_);
lean_dec(v_b_3084_);
v___x_3092_ = lean_box(0);
v_isShared_3093_ = v_isSharedCheck_3121_;
goto v_resetjp_3091_;
}
v_resetjp_3091_:
{
lean_object* v___x_3100_; lean_object* v___x_3101_; lean_object* v___x_3102_; lean_object* v___x_3103_; uint32_t v___x_3104_; uint32_t v___x_3105_; uint8_t v___x_3106_; 
v___x_3100_ = lean_box(0);
v___x_3101_ = lean_nat_add(v_startInclusive_3086_, v_a_3083_);
lean_dec(v_a_3083_);
v___x_3102_ = lean_string_utf8_next_fast(v_str_3085_, v___x_3101_);
v___x_3103_ = lean_nat_sub(v___x_3102_, v_startInclusive_3086_);
v___x_3104_ = lean_string_utf8_get_fast(v_str_3085_, v___x_3101_);
lean_dec(v___x_3101_);
v___x_3105_ = 95;
v___x_3106_ = lean_uint32_dec_eq(v___x_3104_, v___x_3105_);
if (v___x_3106_ == 0)
{
uint32_t v___x_3107_; uint8_t v___x_3108_; 
v___x_3107_ = 48;
v___x_3108_ = lean_uint32_dec_le(v___x_3107_, v___x_3104_);
if (v___x_3108_ == 0)
{
lean_dec(v___x_3103_);
goto v___jp_3094_;
}
else
{
uint32_t v___x_3109_; uint8_t v___x_3110_; 
v___x_3109_ = 57;
v___x_3110_ = lean_uint32_dec_le(v___x_3104_, v___x_3109_);
if (v___x_3110_ == 0)
{
lean_dec(v___x_3103_);
goto v___jp_3094_;
}
else
{
lean_object* v___x_3111_; lean_object* v___x_3112_; 
lean_del_object(v___x_3092_);
lean_dec(v_snd_3090_);
v___x_3111_ = lean_box(v___x_3108_);
v___x_3112_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3112_, 0, v___x_3100_);
lean_ctor_set(v___x_3112_, 1, v___x_3111_);
v_a_3083_ = v___x_3103_;
v_b_3084_ = v___x_3112_;
goto _start;
}
}
}
else
{
uint8_t v___x_3114_; 
lean_del_object(v___x_3092_);
v___x_3114_ = lean_unbox(v_snd_3090_);
if (v___x_3114_ == 0)
{
lean_object* v___x_3115_; lean_object* v___x_3116_; lean_object* v___x_3117_; 
lean_dec(v___x_3103_);
v___x_3115_ = lean_box(v_decide_3089_);
v___x_3116_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3116_, 0, v___x_3115_);
v___x_3117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3117_, 0, v___x_3116_);
lean_ctor_set(v___x_3117_, 1, v_snd_3090_);
return v___x_3117_;
}
else
{
lean_object* v___x_3118_; lean_object* v___x_3119_; 
lean_dec(v_snd_3090_);
v___x_3118_ = lean_box(v_decide_3089_);
v___x_3119_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3100_);
lean_ctor_set(v___x_3119_, 1, v___x_3118_);
v_a_3083_ = v___x_3103_;
v_b_3084_ = v___x_3119_;
goto _start;
}
}
v___jp_3094_:
{
lean_object* v___x_3095_; lean_object* v___x_3096_; lean_object* v___x_3098_; 
v___x_3095_ = lean_box(v_decide_3089_);
v___x_3096_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3096_, 0, v___x_3095_);
if (v_isShared_3093_ == 0)
{
lean_ctor_set(v___x_3092_, 0, v___x_3096_);
v___x_3098_ = v___x_3092_;
goto v_reusejp_3097_;
}
else
{
lean_object* v_reuseFailAlloc_3099_; 
v_reuseFailAlloc_3099_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3099_, 0, v___x_3096_);
lean_ctor_set(v_reuseFailAlloc_3099_, 1, v_snd_3090_);
v___x_3098_ = v_reuseFailAlloc_3099_;
goto v_reusejp_3097_;
}
v_reusejp_3097_:
{
return v___x_3098_;
}
}
}
}
else
{
lean_dec(v_a_3083_);
return v_b_3084_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg___boxed(lean_object* v_s_3123_, lean_object* v_a_3124_, lean_object* v_b_3125_){
_start:
{
lean_object* v_res_3126_; 
v_res_3126_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3123_, v_a_3124_, v_b_3125_);
lean_dec_ref(v_s_3123_);
return v_res_3126_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isNat(lean_object* v_s_3131_){
_start:
{
lean_object* v___x_3132_; lean_object* v___x_3133_; lean_object* v___x_3134_; lean_object* v_fst_3135_; 
v___x_3132_ = ((lean_object*)(l_String_Slice_isNat___closed__0));
v___x_3133_ = lean_unsigned_to_nat(0u);
v___x_3134_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3131_, v___x_3133_, v___x_3132_);
v_fst_3135_ = lean_ctor_get(v___x_3134_, 0);
lean_inc(v_fst_3135_);
if (lean_obj_tag(v_fst_3135_) == 0)
{
lean_object* v_snd_3136_; uint8_t v___x_3137_; 
v_snd_3136_ = lean_ctor_get(v___x_3134_, 1);
lean_inc(v_snd_3136_);
lean_dec_ref(v___x_3134_);
v___x_3137_ = lean_unbox(v_snd_3136_);
lean_dec(v_snd_3136_);
return v___x_3137_;
}
else
{
lean_object* v_val_3138_; uint8_t v___x_3139_; 
lean_dec_ref(v___x_3134_);
v_val_3138_ = lean_ctor_get(v_fst_3135_, 0);
lean_inc(v_val_3138_);
lean_dec_ref_known(v_fst_3135_, 1);
v___x_3139_ = lean_unbox(v_val_3138_);
lean_dec(v_val_3138_);
return v___x_3139_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object* v_s_3140_){
_start:
{
uint8_t v_res_3141_; lean_object* v_r_3142_; 
v_res_3141_ = l_String_Slice_isNat(v_s_3140_);
lean_dec_ref(v_s_3140_);
v_r_3142_ = lean_box(v_res_3141_);
return v_r_3142_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(lean_object* v_s_3143_, lean_object* v_inst_3144_, lean_object* v_R_3145_, lean_object* v_a_3146_, lean_object* v_b_3147_, lean_object* v_c_3148_){
_start:
{
lean_object* v___x_3149_; 
v___x_3149_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3143_, v_a_3146_, v_b_3147_);
return v___x_3149_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___boxed(lean_object* v_s_3150_, lean_object* v_inst_3151_, lean_object* v_R_3152_, lean_object* v_a_3153_, lean_object* v_b_3154_, lean_object* v_c_3155_){
_start:
{
lean_object* v_res_3156_; 
v_res_3156_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(v_s_3150_, v_inst_3151_, v_R_3152_, v_a_3153_, v_b_3154_, v_c_3155_);
lean_dec_ref(v_s_3150_);
return v_res_3156_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object* v_s_3157_, lean_object* v_a_3158_, lean_object* v_b_3159_){
_start:
{
lean_object* v_str_3160_; lean_object* v_startInclusive_3161_; lean_object* v_endExclusive_3162_; lean_object* v___x_3163_; uint8_t v_decide_3164_; 
v_str_3160_ = lean_ctor_get(v_s_3157_, 0);
v_startInclusive_3161_ = lean_ctor_get(v_s_3157_, 1);
v_endExclusive_3162_ = lean_ctor_get(v_s_3157_, 2);
v___x_3163_ = lean_nat_sub(v_endExclusive_3162_, v_startInclusive_3161_);
v_decide_3164_ = lean_nat_dec_eq(v_a_3158_, v___x_3163_);
lean_dec(v___x_3163_);
if (v_decide_3164_ == 0)
{
lean_object* v___x_3165_; lean_object* v___x_3166_; lean_object* v___x_3167_; uint32_t v___x_3168_; uint32_t v___x_3169_; uint8_t v___x_3170_; 
v___x_3165_ = lean_nat_add(v_startInclusive_3161_, v_a_3158_);
lean_dec(v_a_3158_);
v___x_3166_ = lean_string_utf8_next_fast(v_str_3160_, v___x_3165_);
v___x_3167_ = lean_nat_sub(v___x_3166_, v_startInclusive_3161_);
v___x_3168_ = lean_string_utf8_get_fast(v_str_3160_, v___x_3165_);
lean_dec(v___x_3165_);
v___x_3169_ = 95;
v___x_3170_ = lean_uint32_dec_eq(v___x_3168_, v___x_3169_);
if (v___x_3170_ == 0)
{
lean_object* v___x_3171_; lean_object* v___x_3172_; lean_object* v___x_3173_; lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; 
v___x_3171_ = lean_unsigned_to_nat(10u);
v___x_3172_ = lean_nat_mul(v_b_3159_, v___x_3171_);
lean_dec(v_b_3159_);
v___x_3173_ = lean_uint32_to_nat(v___x_3168_);
v___x_3174_ = lean_unsigned_to_nat(48u);
v___x_3175_ = lean_nat_sub(v___x_3173_, v___x_3174_);
lean_dec(v___x_3173_);
v___x_3176_ = lean_nat_add(v___x_3172_, v___x_3175_);
lean_dec(v___x_3175_);
lean_dec(v___x_3172_);
v_a_3158_ = v___x_3167_;
v_b_3159_ = v___x_3176_;
goto _start;
}
else
{
v_a_3158_ = v___x_3167_;
goto _start;
}
}
else
{
lean_dec(v_a_3158_);
return v_b_3159_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object* v_s_3179_, lean_object* v_a_3180_, lean_object* v_b_3181_){
_start:
{
lean_object* v_res_3182_; 
v_res_3182_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3179_, v_a_3180_, v_b_3181_);
lean_dec_ref(v_s_3179_);
return v_res_3182_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object* v_s_3183_){
_start:
{
uint8_t v___x_3184_; 
v___x_3184_ = l_String_Slice_isNat(v_s_3183_);
if (v___x_3184_ == 0)
{
lean_object* v___x_3185_; 
v___x_3185_ = lean_box(0);
return v___x_3185_;
}
else
{
lean_object* v___x_3186_; lean_object* v___x_3187_; lean_object* v___x_3188_; 
v___x_3186_ = lean_unsigned_to_nat(0u);
v___x_3187_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3183_, v___x_3186_, v___x_3186_);
v___x_3188_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3188_, 0, v___x_3187_);
return v___x_3188_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object* v_s_3189_){
_start:
{
lean_object* v_res_3190_; 
v_res_3190_ = l_String_Slice_toNat_x3f(v_s_3189_);
lean_dec_ref(v_s_3189_);
return v_res_3190_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object* v_s_3191_, lean_object* v_inst_3192_, lean_object* v_R_3193_, lean_object* v_a_3194_, lean_object* v_b_3195_, lean_object* v_c_3196_){
_start:
{
lean_object* v___x_3197_; 
v___x_3197_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3191_, v_a_3194_, v_b_3195_);
return v___x_3197_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object* v_s_3198_, lean_object* v_inst_3199_, lean_object* v_R_3200_, lean_object* v_a_3201_, lean_object* v_b_3202_, lean_object* v_c_3203_){
_start:
{
lean_object* v_res_3204_; 
v_res_3204_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(v_s_3198_, v_inst_3199_, v_R_3200_, v_a_3201_, v_b_3202_, v_c_3203_);
lean_dec_ref(v_s_3198_);
return v_res_3204_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_toNat_x21_spec__0(lean_object* v_msg_3205_){
_start:
{
lean_object* v___x_3206_; lean_object* v___x_3207_; 
v___x_3206_ = lean_unsigned_to_nat(0u);
v___x_3207_ = lean_panic_fn_borrowed(v___x_3206_, v_msg_3205_);
return v___x_3207_;
}
}
static lean_object* _init_l_String_Slice_toNat_x21___closed__3(void){
_start:
{
lean_object* v___x_3211_; lean_object* v___x_3212_; lean_object* v___x_3213_; lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; 
v___x_3211_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__2));
v___x_3212_ = lean_unsigned_to_nat(4u);
v___x_3213_ = lean_unsigned_to_nat(1040u);
v___x_3214_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__1));
v___x_3215_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__0));
v___x_3216_ = l_mkPanicMessageWithDecl(v___x_3215_, v___x_3214_, v___x_3213_, v___x_3212_, v___x_3211_);
return v___x_3216_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21(lean_object* v_s_3217_){
_start:
{
uint8_t v___x_3218_; 
v___x_3218_ = l_String_Slice_isNat(v_s_3217_);
if (v___x_3218_ == 0)
{
lean_object* v___x_3219_; lean_object* v___x_3220_; 
v___x_3219_ = lean_obj_once(&l_String_Slice_toNat_x21___closed__3, &l_String_Slice_toNat_x21___closed__3_once, _init_l_String_Slice_toNat_x21___closed__3);
v___x_3220_ = l_panic___at___00String_Slice_toNat_x21_spec__0(v___x_3219_);
return v___x_3220_;
}
else
{
lean_object* v___x_3221_; lean_object* v___x_3222_; 
v___x_3221_ = lean_unsigned_to_nat(0u);
v___x_3222_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3217_, v___x_3221_, v___x_3221_);
return v___x_3222_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21___boxed(lean_object* v_s_3223_){
_start:
{
lean_object* v_res_3224_; 
v_res_3224_ = l_String_Slice_toNat_x21(v_s_3223_);
lean_dec_ref(v_s_3223_);
return v_res_3224_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object* v_s_3225_){
_start:
{
lean_object* v___x_3226_; lean_object* v___x_3227_; 
v___x_3226_ = lean_unsigned_to_nat(0u);
v___x_3227_ = l_String_Slice_Pos_get_x3f(v_s_3225_, v___x_3226_);
return v___x_3227_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object* v_s_3228_){
_start:
{
lean_object* v_res_3229_; 
v_res_3229_ = l_String_Slice_front_x3f(v_s_3228_);
lean_dec_ref(v_s_3228_);
return v_res_3229_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_front(lean_object* v_s_3230_){
_start:
{
lean_object* v___x_3231_; lean_object* v___x_3232_; 
v___x_3231_ = lean_unsigned_to_nat(0u);
v___x_3232_ = l_String_Slice_Pos_get_x3f(v_s_3230_, v___x_3231_);
if (lean_obj_tag(v___x_3232_) == 0)
{
uint32_t v___x_3233_; 
v___x_3233_ = 65;
return v___x_3233_;
}
else
{
lean_object* v_val_3234_; uint32_t v___x_3235_; 
v_val_3234_ = lean_ctor_get(v___x_3232_, 0);
lean_inc(v_val_3234_);
lean_dec_ref_known(v___x_3232_, 1);
v___x_3235_ = lean_unbox_uint32(v_val_3234_);
lean_dec(v_val_3234_);
return v___x_3235_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object* v_s_3236_){
_start:
{
uint32_t v_res_3237_; lean_object* v_r_3238_; 
v_res_3237_ = l_String_Slice_front(v_s_3236_);
lean_dec_ref(v_s_3236_);
v_r_3238_ = lean_box_uint32(v_res_3237_);
return v_r_3238_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isInt(lean_object* v_s_3239_){
_start:
{
lean_object* v_str_3240_; lean_object* v_startInclusive_3241_; lean_object* v_endExclusive_3242_; lean_object* v___x_3243_; lean_object* v___x_3244_; uint8_t v_decide_3245_; 
v_str_3240_ = lean_ctor_get(v_s_3239_, 0);
v_startInclusive_3241_ = lean_ctor_get(v_s_3239_, 1);
v_endExclusive_3242_ = lean_ctor_get(v_s_3239_, 2);
v___x_3243_ = lean_unsigned_to_nat(0u);
v___x_3244_ = lean_nat_sub(v_endExclusive_3242_, v_startInclusive_3241_);
v_decide_3245_ = lean_nat_dec_eq(v___x_3243_, v___x_3244_);
lean_dec(v___x_3244_);
if (v_decide_3245_ == 0)
{
uint32_t v___x_3246_; uint32_t v___x_3247_; uint8_t v___x_3248_; 
v___x_3246_ = 45;
v___x_3247_ = lean_string_utf8_get_fast(v_str_3240_, v_startInclusive_3241_);
v___x_3248_ = lean_uint32_dec_eq(v___x_3247_, v___x_3246_);
if (v___x_3248_ == 0)
{
uint8_t v___x_3249_; 
v___x_3249_ = l_String_Slice_isNat(v_s_3239_);
lean_dec_ref(v_s_3239_);
return v___x_3249_;
}
else
{
lean_object* v___x_3251_; uint8_t v_isShared_3252_; uint8_t v_isSharedCheck_3260_; 
lean_inc(v_endExclusive_3242_);
lean_inc(v_startInclusive_3241_);
lean_inc_ref(v_str_3240_);
v_isSharedCheck_3260_ = !lean_is_exclusive(v_s_3239_);
if (v_isSharedCheck_3260_ == 0)
{
lean_object* v_unused_3261_; lean_object* v_unused_3262_; lean_object* v_unused_3263_; 
v_unused_3261_ = lean_ctor_get(v_s_3239_, 2);
lean_dec(v_unused_3261_);
v_unused_3262_ = lean_ctor_get(v_s_3239_, 1);
lean_dec(v_unused_3262_);
v_unused_3263_ = lean_ctor_get(v_s_3239_, 0);
lean_dec(v_unused_3263_);
v___x_3251_ = v_s_3239_;
v_isShared_3252_ = v_isSharedCheck_3260_;
goto v_resetjp_3250_;
}
else
{
lean_dec(v_s_3239_);
v___x_3251_ = lean_box(0);
v_isShared_3252_ = v_isSharedCheck_3260_;
goto v_resetjp_3250_;
}
v_resetjp_3250_:
{
lean_object* v___x_3253_; lean_object* v___x_3254_; lean_object* v___x_3255_; lean_object* v___x_3257_; 
v___x_3253_ = lean_string_utf8_next_fast(v_str_3240_, v_startInclusive_3241_);
v___x_3254_ = lean_nat_sub(v___x_3253_, v_startInclusive_3241_);
v___x_3255_ = lean_nat_add(v_startInclusive_3241_, v___x_3254_);
lean_dec(v___x_3254_);
lean_dec(v_startInclusive_3241_);
if (v_isShared_3252_ == 0)
{
lean_ctor_set(v___x_3251_, 1, v___x_3255_);
v___x_3257_ = v___x_3251_;
goto v_reusejp_3256_;
}
else
{
lean_object* v_reuseFailAlloc_3259_; 
v_reuseFailAlloc_3259_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3259_, 0, v_str_3240_);
lean_ctor_set(v_reuseFailAlloc_3259_, 1, v___x_3255_);
lean_ctor_set(v_reuseFailAlloc_3259_, 2, v_endExclusive_3242_);
v___x_3257_ = v_reuseFailAlloc_3259_;
goto v_reusejp_3256_;
}
v_reusejp_3256_:
{
uint8_t v___x_3258_; 
v___x_3258_ = l_String_Slice_isNat(v___x_3257_);
lean_dec_ref(v___x_3257_);
return v___x_3258_;
}
}
}
}
else
{
uint8_t v___x_3264_; 
v___x_3264_ = l_String_Slice_isNat(v_s_3239_);
lean_dec_ref(v_s_3239_);
return v___x_3264_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object* v_s_3265_){
_start:
{
uint8_t v_res_3266_; lean_object* v_r_3267_; 
v_res_3266_ = l_String_Slice_isInt(v_s_3265_);
v_r_3267_ = lean_box(v_res_3266_);
return v_r_3267_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x3f(lean_object* v_s_3268_){
_start:
{
lean_object* v_str_3281_; lean_object* v_startInclusive_3282_; lean_object* v_endExclusive_3283_; lean_object* v___x_3284_; lean_object* v___x_3285_; uint8_t v_decide_3286_; 
v_str_3281_ = lean_ctor_get(v_s_3268_, 0);
v_startInclusive_3282_ = lean_ctor_get(v_s_3268_, 1);
v_endExclusive_3283_ = lean_ctor_get(v_s_3268_, 2);
v___x_3284_ = lean_unsigned_to_nat(0u);
v___x_3285_ = lean_nat_sub(v_endExclusive_3283_, v_startInclusive_3282_);
v_decide_3286_ = lean_nat_dec_eq(v___x_3284_, v___x_3285_);
lean_dec(v___x_3285_);
if (v_decide_3286_ == 0)
{
uint32_t v___x_3287_; uint32_t v___x_3288_; uint8_t v___x_3289_; 
v___x_3287_ = 45;
v___x_3288_ = lean_string_utf8_get_fast(v_str_3281_, v_startInclusive_3282_);
v___x_3289_ = lean_uint32_dec_eq(v___x_3288_, v___x_3287_);
if (v___x_3289_ == 0)
{
goto v___jp_3269_;
}
else
{
lean_object* v___x_3291_; uint8_t v_isShared_3292_; uint8_t v_isSharedCheck_3310_; 
lean_inc(v_endExclusive_3283_);
lean_inc(v_startInclusive_3282_);
lean_inc_ref(v_str_3281_);
v_isSharedCheck_3310_ = !lean_is_exclusive(v_s_3268_);
if (v_isSharedCheck_3310_ == 0)
{
lean_object* v_unused_3311_; lean_object* v_unused_3312_; lean_object* v_unused_3313_; 
v_unused_3311_ = lean_ctor_get(v_s_3268_, 2);
lean_dec(v_unused_3311_);
v_unused_3312_ = lean_ctor_get(v_s_3268_, 1);
lean_dec(v_unused_3312_);
v_unused_3313_ = lean_ctor_get(v_s_3268_, 0);
lean_dec(v_unused_3313_);
v___x_3291_ = v_s_3268_;
v_isShared_3292_ = v_isSharedCheck_3310_;
goto v_resetjp_3290_;
}
else
{
lean_dec(v_s_3268_);
v___x_3291_ = lean_box(0);
v_isShared_3292_ = v_isSharedCheck_3310_;
goto v_resetjp_3290_;
}
v_resetjp_3290_:
{
lean_object* v___x_3293_; lean_object* v___x_3294_; lean_object* v___x_3295_; lean_object* v___x_3297_; 
v___x_3293_ = lean_string_utf8_next_fast(v_str_3281_, v_startInclusive_3282_);
v___x_3294_ = lean_nat_sub(v___x_3293_, v_startInclusive_3282_);
v___x_3295_ = lean_nat_add(v_startInclusive_3282_, v___x_3294_);
lean_dec(v___x_3294_);
lean_dec(v_startInclusive_3282_);
if (v_isShared_3292_ == 0)
{
lean_ctor_set(v___x_3291_, 1, v___x_3295_);
v___x_3297_ = v___x_3291_;
goto v_reusejp_3296_;
}
else
{
lean_object* v_reuseFailAlloc_3309_; 
v_reuseFailAlloc_3309_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3309_, 0, v_str_3281_);
lean_ctor_set(v_reuseFailAlloc_3309_, 1, v___x_3295_);
lean_ctor_set(v_reuseFailAlloc_3309_, 2, v_endExclusive_3283_);
v___x_3297_ = v_reuseFailAlloc_3309_;
goto v_reusejp_3296_;
}
v_reusejp_3296_:
{
lean_object* v___x_3298_; 
v___x_3298_ = l_String_Slice_toNat_x3f(v___x_3297_);
lean_dec_ref(v___x_3297_);
if (lean_obj_tag(v___x_3298_) == 0)
{
lean_object* v___x_3299_; 
v___x_3299_ = lean_box(0);
return v___x_3299_;
}
else
{
lean_object* v_val_3300_; lean_object* v___x_3302_; uint8_t v_isShared_3303_; uint8_t v_isSharedCheck_3308_; 
v_val_3300_ = lean_ctor_get(v___x_3298_, 0);
v_isSharedCheck_3308_ = !lean_is_exclusive(v___x_3298_);
if (v_isSharedCheck_3308_ == 0)
{
v___x_3302_ = v___x_3298_;
v_isShared_3303_ = v_isSharedCheck_3308_;
goto v_resetjp_3301_;
}
else
{
lean_inc(v_val_3300_);
lean_dec(v___x_3298_);
v___x_3302_ = lean_box(0);
v_isShared_3303_ = v_isSharedCheck_3308_;
goto v_resetjp_3301_;
}
v_resetjp_3301_:
{
lean_object* v___x_3304_; lean_object* v___x_3306_; 
v___x_3304_ = l_Int_negOfNat(v_val_3300_);
lean_dec(v_val_3300_);
if (v_isShared_3303_ == 0)
{
lean_ctor_set(v___x_3302_, 0, v___x_3304_);
v___x_3306_ = v___x_3302_;
goto v_reusejp_3305_;
}
else
{
lean_object* v_reuseFailAlloc_3307_; 
v_reuseFailAlloc_3307_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3307_, 0, v___x_3304_);
v___x_3306_ = v_reuseFailAlloc_3307_;
goto v_reusejp_3305_;
}
v_reusejp_3305_:
{
return v___x_3306_;
}
}
}
}
}
}
}
else
{
goto v___jp_3269_;
}
v___jp_3269_:
{
lean_object* v___x_3270_; 
v___x_3270_ = l_String_Slice_toNat_x3f(v_s_3268_);
lean_dec_ref(v_s_3268_);
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
v___x_3276_ = lean_nat_to_int(v_val_3272_);
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
LEAN_EXPORT lean_object* l_String_Slice_toInt_x21(lean_object* v_s_3315_){
_start:
{
lean_object* v___x_3316_; 
v___x_3316_ = l_String_Slice_toInt_x3f(v_s_3315_);
if (lean_obj_tag(v___x_3316_) == 0)
{
lean_object* v___x_3317_; lean_object* v___x_3318_; lean_object* v___x_3319_; 
v___x_3317_ = l_Int_instInhabited;
v___x_3318_ = ((lean_object*)(l_String_Slice_toInt_x21___closed__0));
v___x_3319_ = l_panic___redArg(v___x_3317_, v___x_3318_);
return v___x_3319_;
}
else
{
lean_object* v_val_3320_; 
v_val_3320_ = lean_ctor_get(v___x_3316_, 0);
lean_inc(v_val_3320_);
lean_dec_ref_known(v___x_3316_, 1);
return v_val_3320_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object* v_s_3321_){
_start:
{
lean_object* v_startInclusive_3322_; lean_object* v_endExclusive_3323_; lean_object* v___x_3324_; lean_object* v___x_3325_; 
v_startInclusive_3322_ = lean_ctor_get(v_s_3321_, 1);
v_endExclusive_3323_ = lean_ctor_get(v_s_3321_, 2);
v___x_3324_ = lean_nat_sub(v_endExclusive_3323_, v_startInclusive_3322_);
v___x_3325_ = l_String_Slice_Pos_prev_x3f(v_s_3321_, v___x_3324_);
lean_dec(v___x_3324_);
if (lean_obj_tag(v___x_3325_) == 0)
{
lean_object* v___x_3326_; 
v___x_3326_ = lean_box(0);
return v___x_3326_;
}
else
{
lean_object* v_val_3327_; lean_object* v___x_3328_; 
v_val_3327_ = lean_ctor_get(v___x_3325_, 0);
lean_inc(v_val_3327_);
lean_dec_ref_known(v___x_3325_, 1);
v___x_3328_ = l_String_Slice_Pos_get_x3f(v_s_3321_, v_val_3327_);
lean_dec(v_val_3327_);
return v___x_3328_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object* v_s_3329_){
_start:
{
lean_object* v_res_3330_; 
v_res_3330_ = l_String_Slice_back_x3f(v_s_3329_);
lean_dec_ref(v_s_3329_);
return v_res_3330_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_back(lean_object* v_s_3331_){
_start:
{
lean_object* v_startInclusive_3332_; lean_object* v_endExclusive_3333_; lean_object* v___x_3334_; lean_object* v___x_3335_; 
v_startInclusive_3332_ = lean_ctor_get(v_s_3331_, 1);
v_endExclusive_3333_ = lean_ctor_get(v_s_3331_, 2);
v___x_3334_ = lean_nat_sub(v_endExclusive_3333_, v_startInclusive_3332_);
v___x_3335_ = l_String_Slice_Pos_prev_x3f(v_s_3331_, v___x_3334_);
lean_dec(v___x_3334_);
if (lean_obj_tag(v___x_3335_) == 0)
{
uint32_t v___x_3336_; 
v___x_3336_ = 65;
return v___x_3336_;
}
else
{
lean_object* v_val_3337_; lean_object* v___x_3338_; 
v_val_3337_ = lean_ctor_get(v___x_3335_, 0);
lean_inc(v_val_3337_);
lean_dec_ref_known(v___x_3335_, 1);
v___x_3338_ = l_String_Slice_Pos_get_x3f(v_s_3331_, v_val_3337_);
lean_dec(v_val_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
uint32_t v___x_3339_; 
v___x_3339_ = 65;
return v___x_3339_;
}
else
{
lean_object* v_val_3340_; uint32_t v___x_3341_; 
v_val_3340_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v___x_3338_, 1);
v___x_3341_ = lean_unbox_uint32(v_val_3340_);
lean_dec(v_val_3340_);
return v___x_3341_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object* v_s_3342_){
_start:
{
uint32_t v_res_3343_; lean_object* v_r_3344_; 
v_res_3343_ = l_String_Slice_back(v_s_3342_);
lean_dec_ref(v_s_3342_);
v_r_3344_ = lean_box_uint32(v_res_3343_);
return v_r_3344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(lean_object* v_acc_3345_, lean_object* v_s_3346_, lean_object* v_a_3347_){
_start:
{
if (lean_obj_tag(v_a_3347_) == 0)
{
return v_acc_3345_;
}
else
{
lean_object* v_head_3348_; lean_object* v_tail_3349_; lean_object* v_str_3350_; lean_object* v_startInclusive_3351_; lean_object* v_endExclusive_3352_; lean_object* v_str_3353_; lean_object* v_startInclusive_3354_; lean_object* v_endExclusive_3355_; lean_object* v___x_3356_; lean_object* v___x_3357_; lean_object* v___x_3358_; lean_object* v___x_3359_; 
v_head_3348_ = lean_ctor_get(v_a_3347_, 0);
v_tail_3349_ = lean_ctor_get(v_a_3347_, 1);
v_str_3350_ = lean_ctor_get(v_s_3346_, 0);
v_startInclusive_3351_ = lean_ctor_get(v_s_3346_, 1);
v_endExclusive_3352_ = lean_ctor_get(v_s_3346_, 2);
v_str_3353_ = lean_ctor_get(v_head_3348_, 0);
v_startInclusive_3354_ = lean_ctor_get(v_head_3348_, 1);
v_endExclusive_3355_ = lean_ctor_get(v_head_3348_, 2);
v___x_3356_ = lean_string_utf8_extract_fast(v_str_3350_, v_startInclusive_3351_, v_endExclusive_3352_);
v___x_3357_ = lean_string_append(v_acc_3345_, v___x_3356_);
lean_dec_ref(v___x_3356_);
v___x_3358_ = lean_string_utf8_extract_fast(v_str_3353_, v_startInclusive_3354_, v_endExclusive_3355_);
v___x_3359_ = lean_string_append(v___x_3357_, v___x_3358_);
lean_dec_ref(v___x_3358_);
v_acc_3345_ = v___x_3359_;
v_a_3347_ = v_tail_3349_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go___boxed(lean_object* v_acc_3361_, lean_object* v_s_3362_, lean_object* v_a_3363_){
_start:
{
lean_object* v_res_3364_; 
v_res_3364_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v_acc_3361_, v_s_3362_, v_a_3363_);
lean_dec(v_a_3363_);
lean_dec_ref(v_s_3362_);
return v_res_3364_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object* v_s_3365_, lean_object* v_x_3366_){
_start:
{
if (lean_obj_tag(v_x_3366_) == 0)
{
lean_object* v___x_3367_; 
v___x_3367_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
return v___x_3367_;
}
else
{
lean_object* v_head_3368_; lean_object* v_tail_3369_; lean_object* v_str_3370_; lean_object* v_startInclusive_3371_; lean_object* v_endExclusive_3372_; lean_object* v___x_3373_; lean_object* v___x_3374_; 
v_head_3368_ = lean_ctor_get(v_x_3366_, 0);
v_tail_3369_ = lean_ctor_get(v_x_3366_, 1);
v_str_3370_ = lean_ctor_get(v_head_3368_, 0);
v_startInclusive_3371_ = lean_ctor_get(v_head_3368_, 1);
v_endExclusive_3372_ = lean_ctor_get(v_head_3368_, 2);
v___x_3373_ = lean_string_utf8_extract_fast(v_str_3370_, v_startInclusive_3371_, v_endExclusive_3372_);
v___x_3374_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v___x_3373_, v_s_3365_, v_tail_3369_);
return v___x_3374_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object* v_s_3375_, lean_object* v_x_3376_){
_start:
{
lean_object* v_res_3377_; 
v_res_3377_ = l_String_Slice_intercalate(v_s_3375_, v_x_3376_);
lean_dec(v_x_3376_);
lean_dec_ref(v_s_3375_);
return v_res_3377_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0(lean_object* v_x_3378_, lean_object* v_x_3379_){
_start:
{
if (lean_obj_tag(v_x_3379_) == 0)
{
return v_x_3378_;
}
else
{
lean_object* v_head_3380_; lean_object* v_tail_3381_; lean_object* v_str_3382_; lean_object* v_startInclusive_3383_; lean_object* v_endExclusive_3384_; lean_object* v___x_3385_; lean_object* v___x_3386_; 
v_head_3380_ = lean_ctor_get(v_x_3379_, 0);
v_tail_3381_ = lean_ctor_get(v_x_3379_, 1);
v_str_3382_ = lean_ctor_get(v_head_3380_, 0);
v_startInclusive_3383_ = lean_ctor_get(v_head_3380_, 1);
v_endExclusive_3384_ = lean_ctor_get(v_head_3380_, 2);
v___x_3385_ = lean_string_utf8_extract_fast(v_str_3382_, v_startInclusive_3383_, v_endExclusive_3384_);
v___x_3386_ = lean_string_append(v_x_3378_, v___x_3385_);
lean_dec_ref(v___x_3385_);
v_x_3378_ = v___x_3386_;
v_x_3379_ = v_tail_3381_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0___boxed(lean_object* v_x_3388_, lean_object* v_x_3389_){
_start:
{
lean_object* v_res_3390_; 
v_res_3390_ = l_List_foldl___at___00String_Slice_join_spec__0(v_x_3388_, v_x_3389_);
lean_dec(v_x_3389_);
return v_res_3390_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join(lean_object* v_l_3391_){
_start:
{
lean_object* v___x_3392_; lean_object* v___x_3393_; 
v___x_3392_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
v___x_3393_ = l_List_foldl___at___00String_Slice_join_spec__0(v___x_3392_, v_l_3391_);
return v___x_3393_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join___boxed(lean_object* v_l_3394_){
_start:
{
lean_object* v_res_3395_; 
v_res_3395_ = l_String_Slice_join(v_l_3394_);
lean_dec(v_l_3394_);
return v_res_3395_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object* v_s_3396_){
_start:
{
lean_object* v___x_3397_; lean_object* v___x_3398_; 
v___x_3397_ = l_String_Slice_toString(v_s_3396_);
v___x_3398_ = l_String_toName(v___x_3397_);
return v___x_3398_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object* v_s_3399_){
_start:
{
lean_object* v_res_3400_; 
v_res_3400_ = l_String_Slice_toName(v_s_3399_);
lean_dec_ref(v_s_3399_);
return v_res_3400_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object* v_s_3401_){
_start:
{
lean_object* v_str_3402_; lean_object* v_startInclusive_3403_; lean_object* v_endExclusive_3404_; lean_object* v___x_3405_; lean_object* v___x_3406_; 
v_str_3402_ = lean_ctor_get(v_s_3401_, 0);
v_startInclusive_3403_ = lean_ctor_get(v_s_3401_, 1);
v_endExclusive_3404_ = lean_ctor_get(v_s_3401_, 2);
v___x_3405_ = lean_string_utf8_extract_fast(v_str_3402_, v_startInclusive_3403_, v_endExclusive_3404_);
v___x_3406_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3406_, 0, v___x_3405_);
return v___x_3406_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object* v_s_3407_){
_start:
{
lean_object* v_res_3408_; 
v_res_3408_ = l_String_Slice_instToFormat___lam__0(v_s_3407_);
lean_dec_ref(v_s_3407_);
return v_res_3408_;
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
void lean_initialize_runtime_module();
static bool _G_runtime_initialized = false;
LEAN_EXPORT lean_object* runtime_initialize_Init_Data_String_Slice(uint8_t builtin) {
lean_object * res;
if (_G_runtime_initialized) return lean_io_result_mk_ok(lean_box(0));
_G_runtime_initialized = true;
lean_initialize_runtime_module();
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
