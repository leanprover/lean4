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
lean_object* lean_obj_tag_nat(lean_object*);
uint8_t lean_string_memcmp(lean_object*, lean_object*, lean_object*, lean_object*, lean_object*);
lean_object* lean_nat_mul(lean_object*, lean_object*);
lean_object* lean_uint32_to_nat(uint32_t);
lean_object* l_String_Slice_Pos_get_x3f(lean_object*, lean_object*);
lean_object* l_Char_isWhitespace___boxed(lean_object*);
lean_object* l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(lean_object*);
lean_object* l_String_Slice_Pos_prev_x3f(lean_object*, lean_object*);
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
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___redArg(lean_object* v_x_98_){
_start:
{
lean_object* v___x_99_; 
v___x_99_ = lean_obj_tag_nat(v_x_98_);
return v___x_99_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___redArg___boxed(lean_object* v_x_100_){
_start:
{
lean_object* v_res_101_; 
v_res_101_ = l_String_Slice_SplitIterator_ctorIdx___impl___redArg(v_x_100_);
lean_dec(v_x_100_);
return v_res_101_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl(lean_object* v_00_u03c3_102_, lean_object* v_00_u03c1_103_, lean_object* v_pat_104_, lean_object* v_s_105_, lean_object* v_inst_106_, lean_object* v_x_107_){
_start:
{
lean_object* v___x_108_; 
v___x_108_ = lean_obj_tag_nat(v_x_107_);
return v___x_108_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___boxed(lean_object* v_00_u03c3_109_, lean_object* v_00_u03c1_110_, lean_object* v_pat_111_, lean_object* v_s_112_, lean_object* v_inst_113_, lean_object* v_x_114_){
_start:
{
lean_object* v_res_115_; 
v_res_115_ = l_String_Slice_SplitIterator_ctorIdx___impl(v_00_u03c3_109_, v_00_u03c1_110_, v_pat_111_, v_s_112_, v_inst_113_, v_x_114_);
lean_dec(v_x_114_);
lean_dec(v_inst_113_);
lean_dec_ref(v_s_112_);
lean_dec(v_pat_111_);
return v_res_115_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___redArg(lean_object* v_t_116_, lean_object* v_k_117_){
_start:
{
if (lean_obj_tag(v_t_116_) == 0)
{
lean_object* v_currPos_118_; lean_object* v_searcher_119_; lean_object* v___x_120_; 
v_currPos_118_ = lean_ctor_get(v_t_116_, 0);
lean_inc(v_currPos_118_);
v_searcher_119_ = lean_ctor_get(v_t_116_, 1);
lean_inc(v_searcher_119_);
lean_dec_ref_known(v_t_116_, 2);
v___x_120_ = lean_apply_2(v_k_117_, v_currPos_118_, v_searcher_119_);
return v___x_120_;
}
else
{
return v_k_117_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim(lean_object* v_00_u03c3_121_, lean_object* v_00_u03c1_122_, lean_object* v_pat_123_, lean_object* v_s_124_, lean_object* v_inst_125_, lean_object* v_motive_126_, lean_object* v_ctorIdx_127_, lean_object* v_t_128_, lean_object* v_h_129_, lean_object* v_k_130_){
_start:
{
lean_object* v___x_131_; 
v___x_131_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_128_, v_k_130_);
return v___x_131_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_132_, lean_object* v_00_u03c1_133_, lean_object* v_pat_134_, lean_object* v_s_135_, lean_object* v_inst_136_, lean_object* v_motive_137_, lean_object* v_ctorIdx_138_, lean_object* v_t_139_, lean_object* v_h_140_, lean_object* v_k_141_){
_start:
{
lean_object* v_res_142_; 
v_res_142_ = l_String_Slice_SplitIterator_ctorElim(v_00_u03c3_132_, v_00_u03c1_133_, v_pat_134_, v_s_135_, v_inst_136_, v_motive_137_, v_ctorIdx_138_, v_t_139_, v_h_140_, v_k_141_);
lean_dec(v_ctorIdx_138_);
lean_dec(v_inst_136_);
lean_dec_ref(v_s_135_);
lean_dec(v_pat_134_);
return v_res_142_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___redArg(lean_object* v_t_143_, lean_object* v_operating_144_){
_start:
{
lean_object* v___x_145_; 
v___x_145_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_143_, v_operating_144_);
return v___x_145_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim(lean_object* v_00_u03c3_146_, lean_object* v_00_u03c1_147_, lean_object* v_pat_148_, lean_object* v_s_149_, lean_object* v_inst_150_, lean_object* v_motive_151_, lean_object* v_t_152_, lean_object* v_h_153_, lean_object* v_operating_154_){
_start:
{
lean_object* v___x_155_; 
v___x_155_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_152_, v_operating_154_);
return v___x_155_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_156_, lean_object* v_00_u03c1_157_, lean_object* v_pat_158_, lean_object* v_s_159_, lean_object* v_inst_160_, lean_object* v_motive_161_, lean_object* v_t_162_, lean_object* v_h_163_, lean_object* v_operating_164_){
_start:
{
lean_object* v_res_165_; 
v_res_165_ = l_String_Slice_SplitIterator_operating_elim(v_00_u03c3_156_, v_00_u03c1_157_, v_pat_158_, v_s_159_, v_inst_160_, v_motive_161_, v_t_162_, v_h_163_, v_operating_164_);
lean_dec(v_inst_160_);
lean_dec_ref(v_s_159_);
lean_dec(v_pat_158_);
return v_res_165_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___redArg(lean_object* v_t_166_, lean_object* v_atEnd_167_){
_start:
{
lean_object* v___x_168_; 
v___x_168_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_166_, v_atEnd_167_);
return v___x_168_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim(lean_object* v_00_u03c3_169_, lean_object* v_00_u03c1_170_, lean_object* v_pat_171_, lean_object* v_s_172_, lean_object* v_inst_173_, lean_object* v_motive_174_, lean_object* v_t_175_, lean_object* v_h_176_, lean_object* v_atEnd_177_){
_start:
{
lean_object* v___x_178_; 
v___x_178_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_175_, v_atEnd_177_);
return v___x_178_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_179_, lean_object* v_00_u03c1_180_, lean_object* v_pat_181_, lean_object* v_s_182_, lean_object* v_inst_183_, lean_object* v_motive_184_, lean_object* v_t_185_, lean_object* v_h_186_, lean_object* v_atEnd_187_){
_start:
{
lean_object* v_res_188_; 
v_res_188_ = l_String_Slice_SplitIterator_atEnd_elim(v_00_u03c3_179_, v_00_u03c1_180_, v_pat_181_, v_s_182_, v_inst_183_, v_motive_184_, v_t_185_, v_h_186_, v_atEnd_187_);
lean_dec(v_inst_183_);
lean_dec_ref(v_s_182_);
lean_dec(v_pat_181_);
return v_res_188_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg(){
_start:
{
lean_object* v___x_190_; 
v___x_190_ = lean_box(1);
return v___x_190_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg___boxed(lean_object* v___dummy_191_){
_start:
{
lean_object* v_res_192_; 
v_res_192_ = l_String_Slice_instInhabitedSplitIterator_default___redArg();
return v_res_192_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default(lean_object* v_00_u03c3_193_, lean_object* v_00_u03c1_194_, lean_object* v_pat_195_, lean_object* v_s_196_, lean_object* v_inst_197_){
_start:
{
lean_object* v___x_198_; 
v___x_198_ = lean_box(1);
return v___x_198_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___boxed(lean_object* v_00_u03c3_199_, lean_object* v_00_u03c1_200_, lean_object* v_pat_201_, lean_object* v_s_202_, lean_object* v_inst_203_){
_start:
{
lean_object* v_res_204_; 
v_res_204_ = l_String_Slice_instInhabitedSplitIterator_default(v_00_u03c3_199_, v_00_u03c1_200_, v_pat_201_, v_s_202_, v_inst_203_);
lean_dec(v_inst_203_);
lean_dec_ref(v_s_202_);
lean_dec(v_pat_201_);
return v_res_204_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___redArg(){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(1);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___redArg___boxed(lean_object* v___dummy_207_){
_start:
{
lean_object* v_res_208_; 
v_res_208_ = l_String_Slice_instInhabitedSplitIterator___redArg();
return v_res_208_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator(lean_object* v_a_209_, lean_object* v_a_210_, lean_object* v_a_211_, lean_object* v_a_212_, lean_object* v_a_213_){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(1);
return v___x_214_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___boxed(lean_object* v_a_215_, lean_object* v_a_216_, lean_object* v_a_217_, lean_object* v_a_218_, lean_object* v_a_219_){
_start:
{
lean_object* v_res_220_; 
v_res_220_ = l_String_Slice_instInhabitedSplitIterator(v_a_215_, v_a_216_, v_a_217_, v_a_218_, v_a_219_);
lean_dec(v_a_219_);
lean_dec_ref(v_a_218_);
lean_dec(v_a_217_);
return v_res_220_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl(uint8_t v_x_221_){
_start:
{
lean_object* v___x_222_; lean_object* v___x_223_; 
v___x_222_ = lean_box(v_x_221_);
v___x_223_ = lean_obj_tag_nat(v___x_222_);
lean_dec(v___x_222_);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl___boxed(lean_object* v_x_224_){
_start:
{
uint8_t v_x_4__boxed_225_; lean_object* v_res_226_; 
v_x_4__boxed_225_ = lean_unbox(v_x_224_);
v_res_226_ = l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl(v_x_4__boxed_225_);
return v_res_226_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0(lean_object* v_inst_227_, lean_object* v_s_228_, lean_object* v_x_229_){
_start:
{
if (lean_obj_tag(v_x_229_) == 0)
{
lean_object* v_currPos_230_; lean_object* v_searcher_231_; lean_object* v___x_233_; uint8_t v_isShared_234_; uint8_t v_isSharedCheck_274_; 
v_currPos_230_ = lean_ctor_get(v_x_229_, 0);
v_searcher_231_ = lean_ctor_get(v_x_229_, 1);
v_isSharedCheck_274_ = !lean_is_exclusive(v_x_229_);
if (v_isSharedCheck_274_ == 0)
{
v___x_233_ = v_x_229_;
v_isShared_234_ = v_isSharedCheck_274_;
goto v_resetjp_232_;
}
else
{
lean_inc(v_searcher_231_);
lean_inc(v_currPos_230_);
lean_dec(v_x_229_);
v___x_233_ = lean_box(0);
v_isShared_234_ = v_isSharedCheck_274_;
goto v_resetjp_232_;
}
v_resetjp_232_:
{
lean_object* v___x_235_; 
lean_inc_ref(v_s_228_);
v___x_235_ = lean_apply_2(v_inst_227_, v_s_228_, v_searcher_231_);
switch(lean_obj_tag(v___x_235_))
{
case 0:
{
lean_object* v_out_236_; 
v_out_236_ = lean_ctor_get(v___x_235_, 1);
lean_inc(v_out_236_);
if (lean_obj_tag(v_out_236_) == 0)
{
lean_object* v_it_237_; lean_object* v___x_239_; 
lean_dec_ref_known(v_out_236_, 2);
lean_dec_ref(v_s_228_);
v_it_237_ = lean_ctor_get(v___x_235_, 0);
lean_inc(v_it_237_);
lean_dec_ref_known(v___x_235_, 2);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v_it_237_);
v___x_239_ = v___x_233_;
goto v_reusejp_238_;
}
else
{
lean_object* v_reuseFailAlloc_241_; 
v_reuseFailAlloc_241_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_241_, 0, v_currPos_230_);
lean_ctor_set(v_reuseFailAlloc_241_, 1, v_it_237_);
v___x_239_ = v_reuseFailAlloc_241_;
goto v_reusejp_238_;
}
v_reusejp_238_:
{
lean_object* v___x_240_; 
v___x_240_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_240_, 0, v___x_239_);
return v___x_240_;
}
}
else
{
lean_object* v_it_242_; lean_object* v___x_244_; uint8_t v_isShared_245_; uint8_t v_isSharedCheck_255_; 
v_it_242_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_255_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_255_ == 0)
{
lean_object* v_unused_256_; 
v_unused_256_ = lean_ctor_get(v___x_235_, 1);
lean_dec(v_unused_256_);
v___x_244_ = v___x_235_;
v_isShared_245_ = v_isSharedCheck_255_;
goto v_resetjp_243_;
}
else
{
lean_inc(v_it_242_);
lean_dec(v___x_235_);
v___x_244_ = lean_box(0);
v_isShared_245_ = v_isSharedCheck_255_;
goto v_resetjp_243_;
}
v_resetjp_243_:
{
lean_object* v_startPos_246_; lean_object* v_endPos_247_; lean_object* v_slice_248_; lean_object* v_nextIt_250_; 
v_startPos_246_ = lean_ctor_get(v_out_236_, 0);
lean_inc(v_startPos_246_);
v_endPos_247_ = lean_ctor_get(v_out_236_, 1);
lean_inc(v_endPos_247_);
lean_dec_ref_known(v_out_236_, 2);
v_slice_248_ = l_String_Slice_subslice_x21(v_s_228_, v_currPos_230_, v_startPos_246_);
lean_dec_ref(v_s_228_);
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v_it_242_);
lean_ctor_set(v___x_233_, 0, v_endPos_247_);
v_nextIt_250_ = v___x_233_;
goto v_reusejp_249_;
}
else
{
lean_object* v_reuseFailAlloc_254_; 
v_reuseFailAlloc_254_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_254_, 0, v_endPos_247_);
lean_ctor_set(v_reuseFailAlloc_254_, 1, v_it_242_);
v_nextIt_250_ = v_reuseFailAlloc_254_;
goto v_reusejp_249_;
}
v_reusejp_249_:
{
lean_object* v___x_252_; 
if (v_isShared_245_ == 0)
{
lean_ctor_set(v___x_244_, 1, v_slice_248_);
lean_ctor_set(v___x_244_, 0, v_nextIt_250_);
v___x_252_ = v___x_244_;
goto v_reusejp_251_;
}
else
{
lean_object* v_reuseFailAlloc_253_; 
v_reuseFailAlloc_253_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_253_, 0, v_nextIt_250_);
lean_ctor_set(v_reuseFailAlloc_253_, 1, v_slice_248_);
v___x_252_ = v_reuseFailAlloc_253_;
goto v_reusejp_251_;
}
v_reusejp_251_:
{
return v___x_252_;
}
}
}
}
}
case 1:
{
lean_object* v_it_257_; lean_object* v___x_259_; uint8_t v_isShared_260_; uint8_t v_isSharedCheck_267_; 
lean_dec_ref(v_s_228_);
v_it_257_ = lean_ctor_get(v___x_235_, 0);
v_isSharedCheck_267_ = !lean_is_exclusive(v___x_235_);
if (v_isSharedCheck_267_ == 0)
{
v___x_259_ = v___x_235_;
v_isShared_260_ = v_isSharedCheck_267_;
goto v_resetjp_258_;
}
else
{
lean_inc(v_it_257_);
lean_dec(v___x_235_);
v___x_259_ = lean_box(0);
v_isShared_260_ = v_isSharedCheck_267_;
goto v_resetjp_258_;
}
v_resetjp_258_:
{
lean_object* v___x_262_; 
if (v_isShared_234_ == 0)
{
lean_ctor_set(v___x_233_, 1, v_it_257_);
v___x_262_ = v___x_233_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_266_; 
v_reuseFailAlloc_266_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_266_, 0, v_currPos_230_);
lean_ctor_set(v_reuseFailAlloc_266_, 1, v_it_257_);
v___x_262_ = v_reuseFailAlloc_266_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
lean_object* v___x_264_; 
if (v_isShared_260_ == 0)
{
lean_ctor_set(v___x_259_, 0, v___x_262_);
v___x_264_ = v___x_259_;
goto v_reusejp_263_;
}
else
{
lean_object* v_reuseFailAlloc_265_; 
v_reuseFailAlloc_265_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_265_, 0, v___x_262_);
v___x_264_ = v_reuseFailAlloc_265_;
goto v_reusejp_263_;
}
v_reusejp_263_:
{
return v___x_264_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_268_; lean_object* v_endExclusive_269_; lean_object* v___x_270_; lean_object* v_slice_271_; lean_object* v___x_272_; lean_object* v___x_273_; 
lean_del_object(v___x_233_);
v_startInclusive_268_ = lean_ctor_get(v_s_228_, 1);
lean_inc(v_startInclusive_268_);
v_endExclusive_269_ = lean_ctor_get(v_s_228_, 2);
lean_inc(v_endExclusive_269_);
lean_dec_ref(v_s_228_);
v___x_270_ = lean_nat_sub(v_endExclusive_269_, v_startInclusive_268_);
lean_dec(v_startInclusive_268_);
lean_dec(v_endExclusive_269_);
v_slice_271_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_271_, 0, v_currPos_230_);
lean_ctor_set(v_slice_271_, 1, v___x_270_);
v___x_272_ = lean_box(1);
v___x_273_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_273_, 0, v___x_272_);
lean_ctor_set(v___x_273_, 1, v_slice_271_);
return v___x_273_;
}
}
}
}
else
{
lean_object* v___x_275_; 
lean_dec_ref(v_s_228_);
lean_dec(v_inst_227_);
v___x_275_ = lean_box(2);
return v___x_275_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg(lean_object* v_inst_276_, lean_object* v_s_277_){
_start:
{
lean_object* v___f_278_; 
v___f_278_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0), 3, 2);
lean_closure_set(v___f_278_, 0, v_inst_276_);
lean_closure_set(v___f_278_, 1, v_s_277_);
return v___f_278_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice(lean_object* v_00_u03c1_279_, lean_object* v_00_u03c3_280_, lean_object* v_inst_281_, lean_object* v_pat_282_, lean_object* v_inst_283_, lean_object* v_s_284_){
_start:
{
lean_object* v___f_285_; 
v___f_285_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0), 3, 2);
lean_closure_set(v___f_285_, 0, v_inst_281_);
lean_closure_set(v___f_285_, 1, v_s_284_);
return v___f_285_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___boxed(lean_object* v_00_u03c1_286_, lean_object* v_00_u03c3_287_, lean_object* v_inst_288_, lean_object* v_pat_289_, lean_object* v_inst_290_, lean_object* v_s_291_){
_start:
{
lean_object* v_res_292_; 
v_res_292_ = l_String_Slice_SplitIterator_instIteratorIdSubslice(v_00_u03c1_286_, v_00_u03c3_287_, v_inst_288_, v_pat_289_, v_inst_290_, v_s_291_);
lean_dec(v_inst_290_);
lean_dec(v_pat_289_);
return v_res_292_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(lean_object* v_x_293_){
_start:
{
if (lean_obj_tag(v_x_293_) == 0)
{
lean_object* v_searcher_294_; lean_object* v___x_295_; 
v_searcher_294_ = lean_ctor_get(v_x_293_, 1);
lean_inc(v_searcher_294_);
v___x_295_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_295_, 0, v_searcher_294_);
return v___x_295_;
}
else
{
lean_object* v___x_296_; 
v___x_296_ = lean_box(0);
return v___x_296_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg___boxed(lean_object* v_x_297_){
_start:
{
lean_object* v_res_298_; 
v_res_298_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(v_x_297_);
lean_dec(v_x_297_);
return v_res_298_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption(lean_object* v_00_u03c1_299_, lean_object* v_00_u03c3_300_, lean_object* v_pat_301_, lean_object* v_inst_302_, lean_object* v_s_303_, lean_object* v_x_304_){
_start:
{
lean_object* v___x_305_; 
v___x_305_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(v_x_304_);
return v___x_305_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___boxed(lean_object* v_00_u03c1_306_, lean_object* v_00_u03c3_307_, lean_object* v_pat_308_, lean_object* v_inst_309_, lean_object* v_s_310_, lean_object* v_x_311_){
_start:
{
lean_object* v_res_312_; 
v_res_312_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption(v_00_u03c1_306_, v_00_u03c3_307_, v_pat_308_, v_inst_309_, v_s_310_, v_x_311_);
lean_dec(v_x_311_);
lean_dec_ref(v_s_310_);
lean_dec(v_inst_309_);
lean_dec(v_pat_308_);
return v_res_312_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___redArg(lean_object* v_x_313_, lean_object* v_h__1_314_, lean_object* v_h__2_315_){
_start:
{
if (lean_obj_tag(v_x_313_) == 0)
{
lean_object* v_currPos_316_; lean_object* v_searcher_317_; lean_object* v___x_318_; 
lean_dec(v_h__2_315_);
v_currPos_316_ = lean_ctor_get(v_x_313_, 0);
lean_inc(v_currPos_316_);
v_searcher_317_ = lean_ctor_get(v_x_313_, 1);
lean_inc(v_searcher_317_);
lean_dec_ref_known(v_x_313_, 2);
v___x_318_ = lean_apply_2(v_h__1_314_, v_currPos_316_, v_searcher_317_);
return v___x_318_;
}
else
{
lean_object* v___x_319_; lean_object* v___x_320_; 
lean_dec(v_h__1_314_);
v___x_319_ = lean_box(0);
v___x_320_ = lean_apply_1(v_h__2_315_, v___x_319_);
return v___x_320_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(lean_object* v_00_u03c1_321_, lean_object* v_00_u03c3_322_, lean_object* v_pat_323_, lean_object* v_inst_324_, lean_object* v_s_325_, lean_object* v_motive_326_, lean_object* v_x_327_, lean_object* v_h__1_328_, lean_object* v_h__2_329_){
_start:
{
if (lean_obj_tag(v_x_327_) == 0)
{
lean_object* v_currPos_330_; lean_object* v_searcher_331_; lean_object* v___x_332_; 
lean_dec(v_h__2_329_);
v_currPos_330_ = lean_ctor_get(v_x_327_, 0);
lean_inc(v_currPos_330_);
v_searcher_331_ = lean_ctor_get(v_x_327_, 1);
lean_inc(v_searcher_331_);
lean_dec_ref_known(v_x_327_, 2);
v___x_332_ = lean_apply_2(v_h__1_328_, v_currPos_330_, v_searcher_331_);
return v___x_332_;
}
else
{
lean_object* v___x_333_; lean_object* v___x_334_; 
lean_dec(v_h__1_328_);
v___x_333_ = lean_box(0);
v___x_334_ = lean_apply_1(v_h__2_329_, v___x_333_);
return v___x_334_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___boxed(lean_object* v_00_u03c1_335_, lean_object* v_00_u03c3_336_, lean_object* v_pat_337_, lean_object* v_inst_338_, lean_object* v_s_339_, lean_object* v_motive_340_, lean_object* v_x_341_, lean_object* v_h__1_342_, lean_object* v_h__2_343_){
_start:
{
lean_object* v_res_344_; 
v_res_344_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(v_00_u03c1_335_, v_00_u03c3_336_, v_pat_337_, v_inst_338_, v_s_339_, v_motive_340_, v_x_341_, v_h__1_342_, v_h__2_343_);
lean_dec_ref(v_s_339_);
lean_dec(v_inst_338_);
lean_dec(v_pat_337_);
return v_res_344_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object* v_x_345_, lean_object* v_h__1_346_, lean_object* v_h__2_347_, lean_object* v_h__3_348_, lean_object* v_h__4_349_){
_start:
{
switch(lean_obj_tag(v_x_345_))
{
case 0:
{
lean_object* v_out_350_; 
lean_dec(v_h__4_349_);
lean_dec(v_h__3_348_);
v_out_350_ = lean_ctor_get(v_x_345_, 1);
lean_inc(v_out_350_);
if (lean_obj_tag(v_out_350_) == 0)
{
lean_object* v_it_351_; lean_object* v_startPos_352_; lean_object* v_endPos_353_; lean_object* v___x_354_; 
lean_dec(v_h__1_346_);
v_it_351_ = lean_ctor_get(v_x_345_, 0);
lean_inc(v_it_351_);
lean_dec_ref_known(v_x_345_, 2);
v_startPos_352_ = lean_ctor_get(v_out_350_, 0);
lean_inc(v_startPos_352_);
v_endPos_353_ = lean_ctor_get(v_out_350_, 1);
lean_inc(v_endPos_353_);
lean_dec_ref_known(v_out_350_, 2);
v___x_354_ = lean_apply_5(v_h__2_347_, v_it_351_, v_startPos_352_, v_endPos_353_, lean_box(0), lean_box(0));
return v___x_354_;
}
else
{
lean_object* v_it_355_; lean_object* v_startPos_356_; lean_object* v_endPos_357_; lean_object* v___x_358_; 
lean_dec(v_h__2_347_);
v_it_355_ = lean_ctor_get(v_x_345_, 0);
lean_inc(v_it_355_);
lean_dec_ref_known(v_x_345_, 2);
v_startPos_356_ = lean_ctor_get(v_out_350_, 0);
lean_inc(v_startPos_356_);
v_endPos_357_ = lean_ctor_get(v_out_350_, 1);
lean_inc(v_endPos_357_);
lean_dec_ref_known(v_out_350_, 2);
v___x_358_ = lean_apply_5(v_h__1_346_, v_it_355_, v_startPos_356_, v_endPos_357_, lean_box(0), lean_box(0));
return v___x_358_;
}
}
case 1:
{
lean_object* v_it_359_; lean_object* v___x_360_; 
lean_dec(v_h__4_349_);
lean_dec(v_h__2_347_);
lean_dec(v_h__1_346_);
v_it_359_ = lean_ctor_get(v_x_345_, 0);
lean_inc(v_it_359_);
lean_dec_ref_known(v_x_345_, 1);
v___x_360_ = lean_apply_3(v_h__3_348_, v_it_359_, lean_box(0), lean_box(0));
return v___x_360_;
}
default: 
{
lean_object* v___x_361_; 
lean_dec(v_h__3_348_);
lean_dec(v_h__2_347_);
lean_dec(v_h__1_346_);
v___x_361_ = lean_apply_2(v_h__4_349_, lean_box(0), lean_box(0));
return v___x_361_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object* v_00_u03c3_362_, lean_object* v_inst_363_, lean_object* v_s_364_, lean_object* v_searcher_365_, lean_object* v_motive_366_, lean_object* v_x_367_, lean_object* v_h__1_368_, lean_object* v_h__2_369_, lean_object* v_h__3_370_, lean_object* v_h__4_371_){
_start:
{
switch(lean_obj_tag(v_x_367_))
{
case 0:
{
lean_object* v_out_372_; 
lean_dec(v_h__4_371_);
lean_dec(v_h__3_370_);
v_out_372_ = lean_ctor_get(v_x_367_, 1);
lean_inc(v_out_372_);
if (lean_obj_tag(v_out_372_) == 0)
{
lean_object* v_it_373_; lean_object* v_startPos_374_; lean_object* v_endPos_375_; lean_object* v___x_376_; 
lean_dec(v_h__1_368_);
v_it_373_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_it_373_);
lean_dec_ref_known(v_x_367_, 2);
v_startPos_374_ = lean_ctor_get(v_out_372_, 0);
lean_inc(v_startPos_374_);
v_endPos_375_ = lean_ctor_get(v_out_372_, 1);
lean_inc(v_endPos_375_);
lean_dec_ref_known(v_out_372_, 2);
v___x_376_ = lean_apply_5(v_h__2_369_, v_it_373_, v_startPos_374_, v_endPos_375_, lean_box(0), lean_box(0));
return v___x_376_;
}
else
{
lean_object* v_it_377_; lean_object* v_startPos_378_; lean_object* v_endPos_379_; lean_object* v___x_380_; 
lean_dec(v_h__2_369_);
v_it_377_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_it_377_);
lean_dec_ref_known(v_x_367_, 2);
v_startPos_378_ = lean_ctor_get(v_out_372_, 0);
lean_inc(v_startPos_378_);
v_endPos_379_ = lean_ctor_get(v_out_372_, 1);
lean_inc(v_endPos_379_);
lean_dec_ref_known(v_out_372_, 2);
v___x_380_ = lean_apply_5(v_h__1_368_, v_it_377_, v_startPos_378_, v_endPos_379_, lean_box(0), lean_box(0));
return v___x_380_;
}
}
case 1:
{
lean_object* v_it_381_; lean_object* v___x_382_; 
lean_dec(v_h__4_371_);
lean_dec(v_h__2_369_);
lean_dec(v_h__1_368_);
v_it_381_ = lean_ctor_get(v_x_367_, 0);
lean_inc(v_it_381_);
lean_dec_ref_known(v_x_367_, 1);
v___x_382_ = lean_apply_3(v_h__3_370_, v_it_381_, lean_box(0), lean_box(0));
return v___x_382_;
}
default: 
{
lean_object* v___x_383_; 
lean_dec(v_h__3_370_);
lean_dec(v_h__2_369_);
lean_dec(v_h__1_368_);
v___x_383_ = lean_apply_2(v_h__4_371_, lean_box(0), lean_box(0));
return v___x_383_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object* v_00_u03c3_384_, lean_object* v_inst_385_, lean_object* v_s_386_, lean_object* v_searcher_387_, lean_object* v_motive_388_, lean_object* v_x_389_, lean_object* v_h__1_390_, lean_object* v_h__2_391_, lean_object* v_h__3_392_, lean_object* v_h__4_393_){
_start:
{
lean_object* v_res_394_; 
v_res_394_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(v_00_u03c3_384_, v_inst_385_, v_s_386_, v_searcher_387_, v_motive_388_, v_x_389_, v_h__1_390_, v_h__2_391_, v_h__3_392_, v_h__4_393_);
lean_dec(v_searcher_387_);
lean_dec_ref(v_s_386_);
lean_dec(v_inst_385_);
return v_res_394_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___redArg(lean_object* v_x_395_, lean_object* v_x_396_, lean_object* v_h__1_397_, lean_object* v_h__2_398_, lean_object* v_h__3_399_, lean_object* v_h__4_400_, lean_object* v_h__5_401_, lean_object* v_h__6_402_, lean_object* v_h__7_403_, lean_object* v_h__8_404_){
_start:
{
if (lean_obj_tag(v_x_395_) == 0)
{
lean_dec(v_h__8_404_);
lean_dec(v_h__7_403_);
lean_dec(v_h__6_402_);
switch(lean_obj_tag(v_x_396_))
{
case 0:
{
lean_object* v_it_405_; 
lean_dec(v_h__5_401_);
lean_dec(v_h__4_400_);
lean_dec(v_h__3_399_);
v_it_405_ = lean_ctor_get(v_x_396_, 0);
if (lean_obj_tag(v_it_405_) == 0)
{
lean_object* v_currPos_406_; lean_object* v_searcher_407_; lean_object* v_out_408_; lean_object* v_currPos_409_; lean_object* v_searcher_410_; lean_object* v___x_411_; 
lean_inc_ref(v_it_405_);
lean_dec(v_h__2_398_);
v_currPos_406_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_currPos_406_);
v_searcher_407_ = lean_ctor_get(v_x_395_, 1);
lean_inc(v_searcher_407_);
lean_dec_ref_known(v_x_395_, 2);
v_out_408_ = lean_ctor_get(v_x_396_, 1);
lean_inc(v_out_408_);
lean_dec_ref_known(v_x_396_, 2);
v_currPos_409_ = lean_ctor_get(v_it_405_, 0);
lean_inc(v_currPos_409_);
v_searcher_410_ = lean_ctor_get(v_it_405_, 1);
lean_inc(v_searcher_410_);
lean_dec_ref_known(v_it_405_, 2);
v___x_411_ = lean_apply_5(v_h__1_397_, v_currPos_406_, v_searcher_407_, v_currPos_409_, v_searcher_410_, v_out_408_);
return v___x_411_;
}
else
{
lean_object* v_currPos_412_; lean_object* v_searcher_413_; lean_object* v_out_414_; lean_object* v___x_415_; 
lean_dec(v_h__1_397_);
v_currPos_412_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_currPos_412_);
v_searcher_413_ = lean_ctor_get(v_x_395_, 1);
lean_inc(v_searcher_413_);
lean_dec_ref_known(v_x_395_, 2);
v_out_414_ = lean_ctor_get(v_x_396_, 1);
lean_inc(v_out_414_);
lean_dec_ref_known(v_x_396_, 2);
v___x_415_ = lean_apply_3(v_h__2_398_, v_currPos_412_, v_searcher_413_, v_out_414_);
return v___x_415_;
}
}
case 1:
{
lean_object* v_it_416_; 
lean_dec(v_h__5_401_);
lean_dec(v_h__2_398_);
lean_dec(v_h__1_397_);
v_it_416_ = lean_ctor_get(v_x_396_, 0);
lean_inc(v_it_416_);
lean_dec_ref_known(v_x_396_, 1);
if (lean_obj_tag(v_it_416_) == 0)
{
lean_object* v_currPos_417_; lean_object* v_searcher_418_; lean_object* v_currPos_419_; lean_object* v_searcher_420_; lean_object* v___x_421_; 
lean_dec(v_h__4_400_);
v_currPos_417_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_currPos_417_);
v_searcher_418_ = lean_ctor_get(v_x_395_, 1);
lean_inc(v_searcher_418_);
lean_dec_ref_known(v_x_395_, 2);
v_currPos_419_ = lean_ctor_get(v_it_416_, 0);
lean_inc(v_currPos_419_);
v_searcher_420_ = lean_ctor_get(v_it_416_, 1);
lean_inc(v_searcher_420_);
lean_dec_ref_known(v_it_416_, 2);
v___x_421_ = lean_apply_4(v_h__3_399_, v_currPos_417_, v_searcher_418_, v_currPos_419_, v_searcher_420_);
return v___x_421_;
}
else
{
lean_object* v_currPos_422_; lean_object* v_searcher_423_; lean_object* v___x_424_; 
lean_dec(v_h__3_399_);
v_currPos_422_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_currPos_422_);
v_searcher_423_ = lean_ctor_get(v_x_395_, 1);
lean_inc(v_searcher_423_);
lean_dec_ref_known(v_x_395_, 2);
v___x_424_ = lean_apply_2(v_h__4_400_, v_currPos_422_, v_searcher_423_);
return v___x_424_;
}
}
default: 
{
lean_object* v_currPos_425_; lean_object* v_searcher_426_; lean_object* v___x_427_; 
lean_dec(v_h__4_400_);
lean_dec(v_h__3_399_);
lean_dec(v_h__2_398_);
lean_dec(v_h__1_397_);
v_currPos_425_ = lean_ctor_get(v_x_395_, 0);
lean_inc(v_currPos_425_);
v_searcher_426_ = lean_ctor_get(v_x_395_, 1);
lean_inc(v_searcher_426_);
lean_dec_ref_known(v_x_395_, 2);
v___x_427_ = lean_apply_2(v_h__5_401_, v_currPos_425_, v_searcher_426_);
return v___x_427_;
}
}
}
else
{
lean_dec(v_h__5_401_);
lean_dec(v_h__4_400_);
lean_dec(v_h__3_399_);
lean_dec(v_h__2_398_);
lean_dec(v_h__1_397_);
switch(lean_obj_tag(v_x_396_))
{
case 0:
{
lean_object* v_it_428_; lean_object* v_out_429_; lean_object* v___x_430_; 
lean_dec(v_h__8_404_);
lean_dec(v_h__7_403_);
v_it_428_ = lean_ctor_get(v_x_396_, 0);
lean_inc(v_it_428_);
v_out_429_ = lean_ctor_get(v_x_396_, 1);
lean_inc(v_out_429_);
lean_dec_ref_known(v_x_396_, 2);
v___x_430_ = lean_apply_2(v_h__6_402_, v_it_428_, v_out_429_);
return v___x_430_;
}
case 1:
{
lean_object* v_it_431_; lean_object* v___x_432_; 
lean_dec(v_h__8_404_);
lean_dec(v_h__6_402_);
v_it_431_ = lean_ctor_get(v_x_396_, 0);
lean_inc(v_it_431_);
lean_dec_ref_known(v_x_396_, 1);
v___x_432_ = lean_apply_1(v_h__7_403_, v_it_431_);
return v___x_432_;
}
default: 
{
lean_object* v___x_433_; lean_object* v___x_434_; 
lean_dec(v_h__7_403_);
lean_dec(v_h__6_402_);
v___x_433_ = lean_box(0);
v___x_434_ = lean_apply_1(v_h__8_404_, v___x_433_);
return v___x_434_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(lean_object* v_00_u03c1_435_, lean_object* v_00_u03c3_436_, lean_object* v_pat_437_, lean_object* v_inst_438_, lean_object* v_s_439_, lean_object* v_motive_440_, lean_object* v_x_441_, lean_object* v_x_442_, lean_object* v_h__1_443_, lean_object* v_h__2_444_, lean_object* v_h__3_445_, lean_object* v_h__4_446_, lean_object* v_h__5_447_, lean_object* v_h__6_448_, lean_object* v_h__7_449_, lean_object* v_h__8_450_){
_start:
{
if (lean_obj_tag(v_x_441_) == 0)
{
lean_dec(v_h__8_450_);
lean_dec(v_h__7_449_);
lean_dec(v_h__6_448_);
switch(lean_obj_tag(v_x_442_))
{
case 0:
{
lean_object* v_it_451_; 
lean_dec(v_h__5_447_);
lean_dec(v_h__4_446_);
lean_dec(v_h__3_445_);
v_it_451_ = lean_ctor_get(v_x_442_, 0);
if (lean_obj_tag(v_it_451_) == 0)
{
lean_object* v_currPos_452_; lean_object* v_searcher_453_; lean_object* v_out_454_; lean_object* v_currPos_455_; lean_object* v_searcher_456_; lean_object* v___x_457_; 
lean_inc_ref(v_it_451_);
lean_dec(v_h__2_444_);
v_currPos_452_ = lean_ctor_get(v_x_441_, 0);
lean_inc(v_currPos_452_);
v_searcher_453_ = lean_ctor_get(v_x_441_, 1);
lean_inc(v_searcher_453_);
lean_dec_ref_known(v_x_441_, 2);
v_out_454_ = lean_ctor_get(v_x_442_, 1);
lean_inc(v_out_454_);
lean_dec_ref_known(v_x_442_, 2);
v_currPos_455_ = lean_ctor_get(v_it_451_, 0);
lean_inc(v_currPos_455_);
v_searcher_456_ = lean_ctor_get(v_it_451_, 1);
lean_inc(v_searcher_456_);
lean_dec_ref_known(v_it_451_, 2);
v___x_457_ = lean_apply_5(v_h__1_443_, v_currPos_452_, v_searcher_453_, v_currPos_455_, v_searcher_456_, v_out_454_);
return v___x_457_;
}
else
{
lean_object* v_currPos_458_; lean_object* v_searcher_459_; lean_object* v_out_460_; lean_object* v___x_461_; 
lean_dec(v_h__1_443_);
v_currPos_458_ = lean_ctor_get(v_x_441_, 0);
lean_inc(v_currPos_458_);
v_searcher_459_ = lean_ctor_get(v_x_441_, 1);
lean_inc(v_searcher_459_);
lean_dec_ref_known(v_x_441_, 2);
v_out_460_ = lean_ctor_get(v_x_442_, 1);
lean_inc(v_out_460_);
lean_dec_ref_known(v_x_442_, 2);
v___x_461_ = lean_apply_3(v_h__2_444_, v_currPos_458_, v_searcher_459_, v_out_460_);
return v___x_461_;
}
}
case 1:
{
lean_object* v_it_462_; 
lean_dec(v_h__5_447_);
lean_dec(v_h__2_444_);
lean_dec(v_h__1_443_);
v_it_462_ = lean_ctor_get(v_x_442_, 0);
lean_inc(v_it_462_);
lean_dec_ref_known(v_x_442_, 1);
if (lean_obj_tag(v_it_462_) == 0)
{
lean_object* v_currPos_463_; lean_object* v_searcher_464_; lean_object* v_currPos_465_; lean_object* v_searcher_466_; lean_object* v___x_467_; 
lean_dec(v_h__4_446_);
v_currPos_463_ = lean_ctor_get(v_x_441_, 0);
lean_inc(v_currPos_463_);
v_searcher_464_ = lean_ctor_get(v_x_441_, 1);
lean_inc(v_searcher_464_);
lean_dec_ref_known(v_x_441_, 2);
v_currPos_465_ = lean_ctor_get(v_it_462_, 0);
lean_inc(v_currPos_465_);
v_searcher_466_ = lean_ctor_get(v_it_462_, 1);
lean_inc(v_searcher_466_);
lean_dec_ref_known(v_it_462_, 2);
v___x_467_ = lean_apply_4(v_h__3_445_, v_currPos_463_, v_searcher_464_, v_currPos_465_, v_searcher_466_);
return v___x_467_;
}
else
{
lean_object* v_currPos_468_; lean_object* v_searcher_469_; lean_object* v___x_470_; 
lean_dec(v_h__3_445_);
v_currPos_468_ = lean_ctor_get(v_x_441_, 0);
lean_inc(v_currPos_468_);
v_searcher_469_ = lean_ctor_get(v_x_441_, 1);
lean_inc(v_searcher_469_);
lean_dec_ref_known(v_x_441_, 2);
v___x_470_ = lean_apply_2(v_h__4_446_, v_currPos_468_, v_searcher_469_);
return v___x_470_;
}
}
default: 
{
lean_object* v_currPos_471_; lean_object* v_searcher_472_; lean_object* v___x_473_; 
lean_dec(v_h__4_446_);
lean_dec(v_h__3_445_);
lean_dec(v_h__2_444_);
lean_dec(v_h__1_443_);
v_currPos_471_ = lean_ctor_get(v_x_441_, 0);
lean_inc(v_currPos_471_);
v_searcher_472_ = lean_ctor_get(v_x_441_, 1);
lean_inc(v_searcher_472_);
lean_dec_ref_known(v_x_441_, 2);
v___x_473_ = lean_apply_2(v_h__5_447_, v_currPos_471_, v_searcher_472_);
return v___x_473_;
}
}
}
else
{
lean_dec(v_h__5_447_);
lean_dec(v_h__4_446_);
lean_dec(v_h__3_445_);
lean_dec(v_h__2_444_);
lean_dec(v_h__1_443_);
switch(lean_obj_tag(v_x_442_))
{
case 0:
{
lean_object* v_it_474_; lean_object* v_out_475_; lean_object* v___x_476_; 
lean_dec(v_h__8_450_);
lean_dec(v_h__7_449_);
v_it_474_ = lean_ctor_get(v_x_442_, 0);
lean_inc(v_it_474_);
v_out_475_ = lean_ctor_get(v_x_442_, 1);
lean_inc(v_out_475_);
lean_dec_ref_known(v_x_442_, 2);
v___x_476_ = lean_apply_2(v_h__6_448_, v_it_474_, v_out_475_);
return v___x_476_;
}
case 1:
{
lean_object* v_it_477_; lean_object* v___x_478_; 
lean_dec(v_h__8_450_);
lean_dec(v_h__6_448_);
v_it_477_ = lean_ctor_get(v_x_442_, 0);
lean_inc(v_it_477_);
lean_dec_ref_known(v_x_442_, 1);
v___x_478_ = lean_apply_1(v_h__7_449_, v_it_477_);
return v___x_478_;
}
default: 
{
lean_object* v___x_479_; lean_object* v___x_480_; 
lean_dec(v_h__7_449_);
lean_dec(v_h__6_448_);
v___x_479_ = lean_box(0);
v___x_480_ = lean_apply_1(v_h__8_450_, v___x_479_);
return v___x_480_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___boxed(lean_object* v_00_u03c1_481_, lean_object* v_00_u03c3_482_, lean_object* v_pat_483_, lean_object* v_inst_484_, lean_object* v_s_485_, lean_object* v_motive_486_, lean_object* v_x_487_, lean_object* v_x_488_, lean_object* v_h__1_489_, lean_object* v_h__2_490_, lean_object* v_h__3_491_, lean_object* v_h__4_492_, lean_object* v_h__5_493_, lean_object* v_h__6_494_, lean_object* v_h__7_495_, lean_object* v_h__8_496_){
_start:
{
lean_object* v_res_497_; 
v_res_497_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(v_00_u03c1_481_, v_00_u03c3_482_, v_pat_483_, v_inst_484_, v_s_485_, v_motive_486_, v_x_487_, v_x_488_, v_h__1_489_, v_h__2_490_, v_h__3_491_, v_h__4_492_, v_h__5_493_, v_h__6_494_, v_h__7_495_, v_h__8_496_);
lean_dec_ref(v_s_485_);
lean_dec(v_inst_484_);
lean_dec(v_pat_483_);
return v_res_497_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___redArg(lean_object* v_x_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_){
_start:
{
if (lean_obj_tag(v_x_498_) == 0)
{
lean_object* v_currPos_501_; lean_object* v_searcher_502_; lean_object* v___x_503_; 
lean_dec(v_h__2_500_);
v_currPos_501_ = lean_ctor_get(v_x_498_, 0);
lean_inc(v_currPos_501_);
v_searcher_502_ = lean_ctor_get(v_x_498_, 1);
lean_inc(v_searcher_502_);
lean_dec_ref_known(v_x_498_, 2);
v___x_503_ = lean_apply_2(v_h__1_499_, v_currPos_501_, v_searcher_502_);
return v___x_503_;
}
else
{
lean_object* v___x_504_; lean_object* v___x_505_; 
lean_dec(v_h__1_499_);
v___x_504_ = lean_box(0);
v___x_505_ = lean_apply_1(v_h__2_500_, v___x_504_);
return v___x_505_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_506_, lean_object* v_00_u03c3_507_, lean_object* v_pat_508_, lean_object* v_inst_509_, lean_object* v_s_510_, lean_object* v_motive_511_, lean_object* v_x_512_, lean_object* v_h__1_513_, lean_object* v_h__2_514_){
_start:
{
if (lean_obj_tag(v_x_512_) == 0)
{
lean_object* v_currPos_515_; lean_object* v_searcher_516_; lean_object* v___x_517_; 
lean_dec(v_h__2_514_);
v_currPos_515_ = lean_ctor_get(v_x_512_, 0);
lean_inc(v_currPos_515_);
v_searcher_516_ = lean_ctor_get(v_x_512_, 1);
lean_inc(v_searcher_516_);
lean_dec_ref_known(v_x_512_, 2);
v___x_517_ = lean_apply_2(v_h__1_513_, v_currPos_515_, v_searcher_516_);
return v___x_517_;
}
else
{
lean_object* v___x_518_; lean_object* v___x_519_; 
lean_dec(v_h__1_513_);
v___x_518_ = lean_box(0);
v___x_519_ = lean_apply_1(v_h__2_514_, v___x_518_);
return v___x_519_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_520_, lean_object* v_00_u03c3_521_, lean_object* v_pat_522_, lean_object* v_inst_523_, lean_object* v_s_524_, lean_object* v_motive_525_, lean_object* v_x_526_, lean_object* v_h__1_527_, lean_object* v_h__2_528_){
_start:
{
lean_object* v_res_529_; 
v_res_529_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption_match__1_splitter(v_00_u03c1_520_, v_00_u03c3_521_, v_pat_522_, v_inst_523_, v_s_524_, v_motive_525_, v_x_526_, v_h__1_527_, v_h__2_528_);
lean_dec_ref(v_s_524_);
lean_dec(v_inst_523_);
lean_dec(v_pat_522_);
return v_res_529_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_531_; 
v___x_531_ = lean_box(0);
return v___x_531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_532_){
_start:
{
lean_object* v_res_533_; 
v_res_533_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg();
return v_res_533_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(lean_object* v_00_u03c1_534_, lean_object* v_00_u03c3_535_, lean_object* v_inst_536_, lean_object* v_pat_537_, lean_object* v_inst_538_, lean_object* v_s_539_, lean_object* v_inst_540_){
_start:
{
lean_object* v___x_541_; 
v___x_541_ = lean_box(0);
return v___x_541_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_542_, lean_object* v_00_u03c3_543_, lean_object* v_inst_544_, lean_object* v_pat_545_, lean_object* v_inst_546_, lean_object* v_s_547_, lean_object* v_inst_548_){
_start:
{
lean_object* v_res_549_; 
v_res_549_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(v_00_u03c1_542_, v_00_u03c3_543_, v_inst_544_, v_pat_545_, v_inst_546_, v_s_547_, v_inst_548_);
lean_dec_ref(v_s_547_);
lean_dec(v_inst_546_);
lean_dec(v_pat_545_);
lean_dec(v_inst_544_);
return v_res_549_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0(lean_object* v_toPure_550_, lean_object* v_recur_551_, lean_object* v_it_552_, lean_object* v_____do__lift_553_){
_start:
{
if (lean_obj_tag(v_____do__lift_553_) == 0)
{
lean_object* v_a_554_; lean_object* v___x_555_; 
lean_dec(v_it_552_);
lean_dec(v_recur_551_);
v_a_554_ = lean_ctor_get(v_____do__lift_553_, 0);
lean_inc(v_a_554_);
lean_dec_ref_known(v_____do__lift_553_, 1);
v___x_555_ = lean_apply_2(v_toPure_550_, lean_box(0), v_a_554_);
return v___x_555_;
}
else
{
lean_object* v_a_556_; lean_object* v___x_557_; 
lean_dec(v_toPure_550_);
v_a_556_ = lean_ctor_get(v_____do__lift_553_, 0);
lean_inc(v_a_556_);
lean_dec_ref_known(v_____do__lift_553_, 1);
v___x_557_ = lean_apply_4(v_recur_551_, v_it_552_, v_a_556_, lean_box(0), lean_box(0));
return v___x_557_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1(lean_object* v_toPure_558_, lean_object* v_recur_559_, lean_object* v___y_560_, lean_object* v_acc_561_, lean_object* v_toBind_562_, lean_object* v_s_563_){
_start:
{
switch(lean_obj_tag(v_s_563_))
{
case 0:
{
lean_object* v_it_564_; lean_object* v_out_565_; lean_object* v___f_566_; lean_object* v___x_567_; lean_object* v___x_568_; 
v_it_564_ = lean_ctor_get(v_s_563_, 0);
lean_inc(v_it_564_);
v_out_565_ = lean_ctor_get(v_s_563_, 1);
lean_inc(v_out_565_);
lean_dec_ref_known(v_s_563_, 2);
v___f_566_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_566_, 0, v_toPure_558_);
lean_closure_set(v___f_566_, 1, v_recur_559_);
lean_closure_set(v___f_566_, 2, v_it_564_);
v___x_567_ = lean_apply_3(v___y_560_, v_out_565_, lean_box(0), v_acc_561_);
v___x_568_ = lean_apply_4(v_toBind_562_, lean_box(0), lean_box(0), v___x_567_, v___f_566_);
return v___x_568_;
}
case 1:
{
lean_object* v_it_569_; lean_object* v___x_570_; 
lean_dec(v_toBind_562_);
lean_dec(v___y_560_);
lean_dec(v_toPure_558_);
v_it_569_ = lean_ctor_get(v_s_563_, 0);
lean_inc(v_it_569_);
lean_dec_ref_known(v_s_563_, 1);
v___x_570_ = lean_apply_4(v_recur_559_, v_it_569_, v_acc_561_, lean_box(0), lean_box(0));
return v___x_570_;
}
default: 
{
lean_object* v___x_571_; 
lean_dec(v_toBind_562_);
lean_dec(v___y_560_);
lean_dec(v_recur_559_);
v___x_571_ = lean_apply_2(v_toPure_558_, lean_box(0), v_acc_561_);
return v___x_571_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2(lean_object* v_toPure_572_, lean_object* v___y_573_, lean_object* v_toBind_574_, lean_object* v_inst_575_, lean_object* v_s_576_, lean_object* v_lift_577_, lean_object* v_it_578_, lean_object* v_acc_579_, lean_object* v_hP_580_, lean_object* v_recur_581_){
_start:
{
lean_object* v___f_582_; 
v___f_582_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_582_, 0, v_toPure_572_);
lean_closure_set(v___f_582_, 1, v_recur_581_);
lean_closure_set(v___f_582_, 2, v___y_573_);
lean_closure_set(v___f_582_, 3, v_acc_579_);
lean_closure_set(v___f_582_, 4, v_toBind_574_);
if (lean_obj_tag(v_it_578_) == 0)
{
lean_object* v_currPos_583_; lean_object* v_searcher_584_; lean_object* v___x_586_; uint8_t v_isShared_587_; uint8_t v_isSharedCheck_631_; 
v_currPos_583_ = lean_ctor_get(v_it_578_, 0);
v_searcher_584_ = lean_ctor_get(v_it_578_, 1);
v_isSharedCheck_631_ = !lean_is_exclusive(v_it_578_);
if (v_isSharedCheck_631_ == 0)
{
v___x_586_ = v_it_578_;
v_isShared_587_ = v_isSharedCheck_631_;
goto v_resetjp_585_;
}
else
{
lean_inc(v_searcher_584_);
lean_inc(v_currPos_583_);
lean_dec(v_it_578_);
v___x_586_ = lean_box(0);
v_isShared_587_ = v_isSharedCheck_631_;
goto v_resetjp_585_;
}
v_resetjp_585_:
{
lean_object* v___x_588_; 
lean_inc_ref(v_s_576_);
v___x_588_ = lean_apply_2(v_inst_575_, v_s_576_, v_searcher_584_);
switch(lean_obj_tag(v___x_588_))
{
case 0:
{
lean_object* v_out_589_; 
v_out_589_ = lean_ctor_get(v___x_588_, 1);
lean_inc(v_out_589_);
if (lean_obj_tag(v_out_589_) == 0)
{
lean_object* v_it_590_; lean_object* v___x_592_; 
lean_dec_ref_known(v_out_589_, 2);
lean_dec_ref(v_s_576_);
v_it_590_ = lean_ctor_get(v___x_588_, 0);
lean_inc(v_it_590_);
lean_dec_ref_known(v___x_588_, 2);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_it_590_);
v___x_592_ = v___x_586_;
goto v_reusejp_591_;
}
else
{
lean_object* v_reuseFailAlloc_595_; 
v_reuseFailAlloc_595_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_595_, 0, v_currPos_583_);
lean_ctor_set(v_reuseFailAlloc_595_, 1, v_it_590_);
v___x_592_ = v_reuseFailAlloc_595_;
goto v_reusejp_591_;
}
v_reusejp_591_:
{
lean_object* v___x_593_; lean_object* v___x_594_; 
v___x_593_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_593_, 0, v___x_592_);
v___x_594_ = lean_apply_4(v_lift_577_, lean_box(0), lean_box(0), v___f_582_, v___x_593_);
return v___x_594_;
}
}
else
{
lean_object* v_it_596_; lean_object* v___x_598_; uint8_t v_isShared_599_; uint8_t v_isSharedCheck_610_; 
v_it_596_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_610_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_610_ == 0)
{
lean_object* v_unused_611_; 
v_unused_611_ = lean_ctor_get(v___x_588_, 1);
lean_dec(v_unused_611_);
v___x_598_ = v___x_588_;
v_isShared_599_ = v_isSharedCheck_610_;
goto v_resetjp_597_;
}
else
{
lean_inc(v_it_596_);
lean_dec(v___x_588_);
v___x_598_ = lean_box(0);
v_isShared_599_ = v_isSharedCheck_610_;
goto v_resetjp_597_;
}
v_resetjp_597_:
{
lean_object* v_startPos_600_; lean_object* v_endPos_601_; lean_object* v_slice_602_; lean_object* v_nextIt_604_; 
v_startPos_600_ = lean_ctor_get(v_out_589_, 0);
lean_inc(v_startPos_600_);
v_endPos_601_ = lean_ctor_get(v_out_589_, 1);
lean_inc(v_endPos_601_);
lean_dec_ref_known(v_out_589_, 2);
v_slice_602_ = l_String_Slice_subslice_x21(v_s_576_, v_currPos_583_, v_startPos_600_);
lean_dec_ref(v_s_576_);
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_it_596_);
lean_ctor_set(v___x_586_, 0, v_endPos_601_);
v_nextIt_604_ = v___x_586_;
goto v_reusejp_603_;
}
else
{
lean_object* v_reuseFailAlloc_609_; 
v_reuseFailAlloc_609_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_609_, 0, v_endPos_601_);
lean_ctor_set(v_reuseFailAlloc_609_, 1, v_it_596_);
v_nextIt_604_ = v_reuseFailAlloc_609_;
goto v_reusejp_603_;
}
v_reusejp_603_:
{
lean_object* v___x_606_; 
if (v_isShared_599_ == 0)
{
lean_ctor_set(v___x_598_, 1, v_slice_602_);
lean_ctor_set(v___x_598_, 0, v_nextIt_604_);
v___x_606_ = v___x_598_;
goto v_reusejp_605_;
}
else
{
lean_object* v_reuseFailAlloc_608_; 
v_reuseFailAlloc_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_608_, 0, v_nextIt_604_);
lean_ctor_set(v_reuseFailAlloc_608_, 1, v_slice_602_);
v___x_606_ = v_reuseFailAlloc_608_;
goto v_reusejp_605_;
}
v_reusejp_605_:
{
lean_object* v___x_607_; 
v___x_607_ = lean_apply_4(v_lift_577_, lean_box(0), lean_box(0), v___f_582_, v___x_606_);
return v___x_607_;
}
}
}
}
}
case 1:
{
lean_object* v_it_612_; lean_object* v___x_614_; uint8_t v_isShared_615_; uint8_t v_isSharedCheck_623_; 
lean_dec_ref(v_s_576_);
v_it_612_ = lean_ctor_get(v___x_588_, 0);
v_isSharedCheck_623_ = !lean_is_exclusive(v___x_588_);
if (v_isSharedCheck_623_ == 0)
{
v___x_614_ = v___x_588_;
v_isShared_615_ = v_isSharedCheck_623_;
goto v_resetjp_613_;
}
else
{
lean_inc(v_it_612_);
lean_dec(v___x_588_);
v___x_614_ = lean_box(0);
v_isShared_615_ = v_isSharedCheck_623_;
goto v_resetjp_613_;
}
v_resetjp_613_:
{
lean_object* v___x_617_; 
if (v_isShared_587_ == 0)
{
lean_ctor_set(v___x_586_, 1, v_it_612_);
v___x_617_ = v___x_586_;
goto v_reusejp_616_;
}
else
{
lean_object* v_reuseFailAlloc_622_; 
v_reuseFailAlloc_622_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_622_, 0, v_currPos_583_);
lean_ctor_set(v_reuseFailAlloc_622_, 1, v_it_612_);
v___x_617_ = v_reuseFailAlloc_622_;
goto v_reusejp_616_;
}
v_reusejp_616_:
{
lean_object* v___x_619_; 
if (v_isShared_615_ == 0)
{
lean_ctor_set(v___x_614_, 0, v___x_617_);
v___x_619_ = v___x_614_;
goto v_reusejp_618_;
}
else
{
lean_object* v_reuseFailAlloc_621_; 
v_reuseFailAlloc_621_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_621_, 0, v___x_617_);
v___x_619_ = v_reuseFailAlloc_621_;
goto v_reusejp_618_;
}
v_reusejp_618_:
{
lean_object* v___x_620_; 
v___x_620_ = lean_apply_4(v_lift_577_, lean_box(0), lean_box(0), v___f_582_, v___x_619_);
return v___x_620_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_624_; lean_object* v_endExclusive_625_; lean_object* v___x_626_; lean_object* v_slice_627_; lean_object* v___x_628_; lean_object* v___x_629_; lean_object* v___x_630_; 
lean_del_object(v___x_586_);
v_startInclusive_624_ = lean_ctor_get(v_s_576_, 1);
lean_inc(v_startInclusive_624_);
v_endExclusive_625_ = lean_ctor_get(v_s_576_, 2);
lean_inc(v_endExclusive_625_);
lean_dec_ref(v_s_576_);
v___x_626_ = lean_nat_sub(v_endExclusive_625_, v_startInclusive_624_);
lean_dec(v_startInclusive_624_);
lean_dec(v_endExclusive_625_);
v_slice_627_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_627_, 0, v_currPos_583_);
lean_ctor_set(v_slice_627_, 1, v___x_626_);
v___x_628_ = lean_box(1);
v___x_629_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_629_, 0, v___x_628_);
lean_ctor_set(v___x_629_, 1, v_slice_627_);
v___x_630_ = lean_apply_4(v_lift_577_, lean_box(0), lean_box(0), v___f_582_, v___x_629_);
return v___x_630_;
}
}
}
}
else
{
lean_object* v___x_632_; lean_object* v___x_633_; 
lean_dec_ref(v_s_576_);
lean_dec(v_inst_575_);
v___x_632_ = lean_box(2);
v___x_633_ = lean_apply_4(v_lift_577_, lean_box(0), lean_box(0), v___f_582_, v___x_632_);
return v___x_633_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3(lean_object* v_inst_634_, lean_object* v_inst_635_, lean_object* v_s_636_, lean_object* v_lift_637_, lean_object* v_00_u03b3_638_, lean_object* v_Pl_639_, lean_object* v_it_640_, lean_object* v_init_641_, lean_object* v___y_642_){
_start:
{
lean_object* v_toApplicative_643_; lean_object* v_toBind_644_; lean_object* v_toPure_645_; lean_object* v___f_646_; lean_object* v___x_647_; 
v_toApplicative_643_ = lean_ctor_get(v_inst_634_, 0);
lean_inc_ref(v_toApplicative_643_);
v_toBind_644_ = lean_ctor_get(v_inst_634_, 1);
lean_inc(v_toBind_644_);
lean_dec_ref(v_inst_634_);
v_toPure_645_ = lean_ctor_get(v_toApplicative_643_, 1);
lean_inc(v_toPure_645_);
lean_dec_ref(v_toApplicative_643_);
v___f_646_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_646_, 0, v_toPure_645_);
lean_closure_set(v___f_646_, 1, v___y_642_);
lean_closure_set(v___f_646_, 2, v_toBind_644_);
lean_closure_set(v___f_646_, 3, v_inst_635_);
lean_closure_set(v___f_646_, 4, v_s_636_);
lean_closure_set(v___f_646_, 5, v_lift_637_);
v___x_647_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_646_, v_it_640_, v_init_641_, lean_box(0));
return v___x_647_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg(lean_object* v_inst_648_, lean_object* v_s_649_, lean_object* v_inst_650_){
_start:
{
lean_object* v___f_651_; 
v___f_651_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_651_, 0, v_inst_650_);
lean_closure_set(v___f_651_, 1, v_inst_648_);
lean_closure_set(v___f_651_, 2, v_s_649_);
return v___f_651_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(lean_object* v_00_u03c1_652_, lean_object* v_00_u03c3_653_, lean_object* v_inst_654_, lean_object* v_pat_655_, lean_object* v_inst_656_, lean_object* v_n_657_, lean_object* v_s_658_, lean_object* v_inst_659_){
_start:
{
lean_object* v___f_660_; 
v___f_660_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_660_, 0, v_inst_659_);
lean_closure_set(v___f_660_, 1, v_inst_654_);
lean_closure_set(v___f_660_, 2, v_s_658_);
return v___f_660_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___boxed(lean_object* v_00_u03c1_661_, lean_object* v_00_u03c3_662_, lean_object* v_inst_663_, lean_object* v_pat_664_, lean_object* v_inst_665_, lean_object* v_n_666_, lean_object* v_s_667_, lean_object* v_inst_668_){
_start:
{
lean_object* v_res_669_; 
v_res_669_ = l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(v_00_u03c1_661_, v_00_u03c3_662_, v_inst_663_, v_pat_664_, v_inst_665_, v_n_666_, v_s_667_, v_inst_668_);
lean_dec(v_inst_665_);
lean_dec(v_pat_664_);
return v_res_669_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___redArg(lean_object* v_s_670_, lean_object* v_inst_671_){
_start:
{
lean_object* v___x_672_; lean_object* v___x_673_; lean_object* v___x_674_; 
v___x_672_ = lean_unsigned_to_nat(0u);
v___x_673_ = lean_apply_1(v_inst_671_, v_s_670_);
v___x_674_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_674_, 0, v___x_672_);
lean_ctor_set(v___x_674_, 1, v___x_673_);
return v___x_674_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice(lean_object* v_00_u03c1_675_, lean_object* v_00_u03c3_676_, lean_object* v_s_677_, lean_object* v_pat_678_, lean_object* v_inst_679_){
_start:
{
lean_object* v___x_680_; 
v___x_680_ = l_String_Slice_splitToSubslice___redArg(v_s_677_, v_inst_679_);
return v___x_680_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___boxed(lean_object* v_00_u03c1_681_, lean_object* v_00_u03c3_682_, lean_object* v_s_683_, lean_object* v_pat_684_, lean_object* v_inst_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_String_Slice_splitToSubslice(v_00_u03c1_681_, v_00_u03c3_682_, v_s_683_, v_pat_684_, v_inst_685_);
lean_dec(v_pat_684_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___redArg(lean_object* v_s_687_, lean_object* v_inst_688_){
_start:
{
lean_object* v___x_689_; 
v___x_689_ = l_String_Slice_splitToSubslice___redArg(v_s_687_, v_inst_688_);
return v___x_689_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split(lean_object* v_00_u03c1_690_, lean_object* v_00_u03c3_691_, lean_object* v_inst_692_, lean_object* v_s_693_, lean_object* v_pat_694_, lean_object* v_inst_695_){
_start:
{
lean_object* v___x_696_; 
v___x_696_ = l_String_Slice_splitToSubslice___redArg(v_s_693_, v_inst_695_);
return v___x_696_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___boxed(lean_object* v_00_u03c1_697_, lean_object* v_00_u03c3_698_, lean_object* v_inst_699_, lean_object* v_s_700_, lean_object* v_pat_701_, lean_object* v_inst_702_){
_start:
{
lean_object* v_res_703_; 
v_res_703_ = l_String_Slice_split(v_00_u03c1_697_, v_00_u03c3_698_, v_inst_699_, v_s_700_, v_pat_701_, v_inst_702_);
lean_dec(v_pat_701_);
lean_dec(v_inst_699_);
return v_res_703_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg(lean_object* v_x_704_){
_start:
{
lean_object* v___x_705_; 
v___x_705_ = lean_obj_tag_nat(v_x_704_);
return v___x_705_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg___boxed(lean_object* v_x_706_){
_start:
{
lean_object* v_res_707_; 
v_res_707_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg(v_x_706_);
lean_dec(v_x_706_);
return v_res_707_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl(lean_object* v_00_u03c3_708_, lean_object* v_00_u03c1_709_, lean_object* v_pat_710_, lean_object* v_s_711_, lean_object* v_inst_712_, lean_object* v_x_713_){
_start:
{
lean_object* v___x_714_; 
v___x_714_ = lean_obj_tag_nat(v_x_713_);
return v___x_714_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___boxed(lean_object* v_00_u03c3_715_, lean_object* v_00_u03c1_716_, lean_object* v_pat_717_, lean_object* v_s_718_, lean_object* v_inst_719_, lean_object* v_x_720_){
_start:
{
lean_object* v_res_721_; 
v_res_721_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___impl(v_00_u03c3_715_, v_00_u03c1_716_, v_pat_717_, v_s_718_, v_inst_719_, v_x_720_);
lean_dec(v_x_720_);
lean_dec(v_inst_719_);
lean_dec_ref(v_s_718_);
lean_dec(v_pat_717_);
return v_res_721_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(lean_object* v_t_722_, lean_object* v_k_723_){
_start:
{
if (lean_obj_tag(v_t_722_) == 0)
{
lean_object* v_currPos_724_; lean_object* v_searcher_725_; lean_object* v___x_726_; 
v_currPos_724_ = lean_ctor_get(v_t_722_, 0);
lean_inc(v_currPos_724_);
v_searcher_725_ = lean_ctor_get(v_t_722_, 1);
lean_inc(v_searcher_725_);
lean_dec_ref_known(v_t_722_, 2);
v___x_726_ = lean_apply_2(v_k_723_, v_currPos_724_, v_searcher_725_);
return v___x_726_;
}
else
{
return v_k_723_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim(lean_object* v_00_u03c3_727_, lean_object* v_00_u03c1_728_, lean_object* v_pat_729_, lean_object* v_s_730_, lean_object* v_inst_731_, lean_object* v_motive_732_, lean_object* v_ctorIdx_733_, lean_object* v_t_734_, lean_object* v_h_735_, lean_object* v_k_736_){
_start:
{
lean_object* v___x_737_; 
v___x_737_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_734_, v_k_736_);
return v___x_737_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___boxed(lean_object* v_00_u03c3_738_, lean_object* v_00_u03c1_739_, lean_object* v_pat_740_, lean_object* v_s_741_, lean_object* v_inst_742_, lean_object* v_motive_743_, lean_object* v_ctorIdx_744_, lean_object* v_t_745_, lean_object* v_h_746_, lean_object* v_k_747_){
_start:
{
lean_object* v_res_748_; 
v_res_748_ = l_String_Slice_SplitInclusiveIterator_ctorElim(v_00_u03c3_738_, v_00_u03c1_739_, v_pat_740_, v_s_741_, v_inst_742_, v_motive_743_, v_ctorIdx_744_, v_t_745_, v_h_746_, v_k_747_);
lean_dec(v_ctorIdx_744_);
lean_dec(v_inst_742_);
lean_dec_ref(v_s_741_);
lean_dec(v_pat_740_);
return v_res_748_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___redArg(lean_object* v_t_749_, lean_object* v_operating_750_){
_start:
{
lean_object* v___x_751_; 
v___x_751_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_749_, v_operating_750_);
return v___x_751_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim(lean_object* v_00_u03c3_752_, lean_object* v_00_u03c1_753_, lean_object* v_pat_754_, lean_object* v_s_755_, lean_object* v_inst_756_, lean_object* v_motive_757_, lean_object* v_t_758_, lean_object* v_h_759_, lean_object* v_operating_760_){
_start:
{
lean_object* v___x_761_; 
v___x_761_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_758_, v_operating_760_);
return v___x_761_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___boxed(lean_object* v_00_u03c3_762_, lean_object* v_00_u03c1_763_, lean_object* v_pat_764_, lean_object* v_s_765_, lean_object* v_inst_766_, lean_object* v_motive_767_, lean_object* v_t_768_, lean_object* v_h_769_, lean_object* v_operating_770_){
_start:
{
lean_object* v_res_771_; 
v_res_771_ = l_String_Slice_SplitInclusiveIterator_operating_elim(v_00_u03c3_762_, v_00_u03c1_763_, v_pat_764_, v_s_765_, v_inst_766_, v_motive_767_, v_t_768_, v_h_769_, v_operating_770_);
lean_dec(v_inst_766_);
lean_dec_ref(v_s_765_);
lean_dec(v_pat_764_);
return v_res_771_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___redArg(lean_object* v_t_772_, lean_object* v_atEnd_773_){
_start:
{
lean_object* v___x_774_; 
v___x_774_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_772_, v_atEnd_773_);
return v___x_774_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim(lean_object* v_00_u03c3_775_, lean_object* v_00_u03c1_776_, lean_object* v_pat_777_, lean_object* v_s_778_, lean_object* v_inst_779_, lean_object* v_motive_780_, lean_object* v_t_781_, lean_object* v_h_782_, lean_object* v_atEnd_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_781_, v_atEnd_783_);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_785_, lean_object* v_00_u03c1_786_, lean_object* v_pat_787_, lean_object* v_s_788_, lean_object* v_inst_789_, lean_object* v_motive_790_, lean_object* v_t_791_, lean_object* v_h_792_, lean_object* v_atEnd_793_){
_start:
{
lean_object* v_res_794_; 
v_res_794_ = l_String_Slice_SplitInclusiveIterator_atEnd_elim(v_00_u03c3_785_, v_00_u03c1_786_, v_pat_787_, v_s_788_, v_inst_789_, v_motive_790_, v_t_791_, v_h_792_, v_atEnd_793_);
lean_dec(v_inst_789_);
lean_dec_ref(v_s_788_);
lean_dec(v_pat_787_);
return v_res_794_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg(){
_start:
{
lean_object* v___x_796_; 
v___x_796_ = lean_box(1);
return v___x_796_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg___boxed(lean_object* v___dummy_797_){
_start:
{
lean_object* v_res_798_; 
v_res_798_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg();
return v_res_798_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default(lean_object* v_00_u03c3_799_, lean_object* v_00_u03c1_800_, lean_object* v_pat_801_, lean_object* v_s_802_, lean_object* v_inst_803_){
_start:
{
lean_object* v___x_804_; 
v___x_804_ = lean_box(1);
return v___x_804_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___boxed(lean_object* v_00_u03c3_805_, lean_object* v_00_u03c1_806_, lean_object* v_pat_807_, lean_object* v_s_808_, lean_object* v_inst_809_){
_start:
{
lean_object* v_res_810_; 
v_res_810_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default(v_00_u03c3_805_, v_00_u03c1_806_, v_pat_807_, v_s_808_, v_inst_809_);
lean_dec(v_inst_809_);
lean_dec_ref(v_s_808_);
lean_dec(v_pat_807_);
return v_res_810_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg(){
_start:
{
lean_object* v___x_812_; 
v___x_812_ = lean_box(1);
return v___x_812_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg___boxed(lean_object* v___dummy_813_){
_start:
{
lean_object* v_res_814_; 
v_res_814_ = l_String_Slice_instInhabitedSplitInclusiveIterator___redArg();
return v_res_814_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator(lean_object* v_a_815_, lean_object* v_a_816_, lean_object* v_a_817_, lean_object* v_a_818_, lean_object* v_a_819_){
_start:
{
lean_object* v___x_820_; 
v___x_820_ = lean_box(1);
return v___x_820_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___boxed(lean_object* v_a_821_, lean_object* v_a_822_, lean_object* v_a_823_, lean_object* v_a_824_, lean_object* v_a_825_){
_start:
{
lean_object* v_res_826_; 
v_res_826_ = l_String_Slice_instInhabitedSplitInclusiveIterator(v_a_821_, v_a_822_, v_a_823_, v_a_824_, v_a_825_);
lean_dec(v_a_825_);
lean_dec_ref(v_a_824_);
lean_dec(v_a_823_);
return v_res_826_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0(lean_object* v_inst_827_, lean_object* v_s_828_, lean_object* v_x_829_){
_start:
{
if (lean_obj_tag(v_x_829_) == 0)
{
lean_object* v_currPos_830_; lean_object* v_searcher_831_; lean_object* v___x_833_; uint8_t v_isShared_834_; uint8_t v_isSharedCheck_883_; 
v_currPos_830_ = lean_ctor_get(v_x_829_, 0);
v_searcher_831_ = lean_ctor_get(v_x_829_, 1);
v_isSharedCheck_883_ = !lean_is_exclusive(v_x_829_);
if (v_isSharedCheck_883_ == 0)
{
v___x_833_ = v_x_829_;
v_isShared_834_ = v_isSharedCheck_883_;
goto v_resetjp_832_;
}
else
{
lean_inc(v_searcher_831_);
lean_inc(v_currPos_830_);
lean_dec(v_x_829_);
v___x_833_ = lean_box(0);
v_isShared_834_ = v_isSharedCheck_883_;
goto v_resetjp_832_;
}
v_resetjp_832_:
{
lean_object* v___x_835_; 
lean_inc_ref(v_s_828_);
v___x_835_ = lean_apply_2(v_inst_827_, v_s_828_, v_searcher_831_);
switch(lean_obj_tag(v___x_835_))
{
case 0:
{
lean_object* v_out_836_; 
v_out_836_ = lean_ctor_get(v___x_835_, 1);
lean_inc(v_out_836_);
if (lean_obj_tag(v_out_836_) == 0)
{
lean_object* v_it_837_; lean_object* v___x_839_; 
lean_dec_ref_known(v_out_836_, 2);
lean_dec_ref(v_s_828_);
v_it_837_ = lean_ctor_get(v___x_835_, 0);
lean_inc(v_it_837_);
lean_dec_ref_known(v___x_835_, 2);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v_it_837_);
v___x_839_ = v___x_833_;
goto v_reusejp_838_;
}
else
{
lean_object* v_reuseFailAlloc_841_; 
v_reuseFailAlloc_841_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_841_, 0, v_currPos_830_);
lean_ctor_set(v_reuseFailAlloc_841_, 1, v_it_837_);
v___x_839_ = v_reuseFailAlloc_841_;
goto v_reusejp_838_;
}
v_reusejp_838_:
{
lean_object* v___x_840_; 
v___x_840_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_840_, 0, v___x_839_);
return v___x_840_;
}
}
else
{
lean_object* v_it_842_; lean_object* v___x_844_; uint8_t v_isShared_845_; uint8_t v_isSharedCheck_854_; 
v_it_842_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_854_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_854_ == 0)
{
lean_object* v_unused_855_; 
v_unused_855_ = lean_ctor_get(v___x_835_, 1);
lean_dec(v_unused_855_);
v___x_844_ = v___x_835_;
v_isShared_845_ = v_isSharedCheck_854_;
goto v_resetjp_843_;
}
else
{
lean_inc(v_it_842_);
lean_dec(v___x_835_);
v___x_844_ = lean_box(0);
v_isShared_845_ = v_isSharedCheck_854_;
goto v_resetjp_843_;
}
v_resetjp_843_:
{
lean_object* v_endPos_846_; lean_object* v_slice_847_; lean_object* v_nextIt_849_; 
v_endPos_846_ = lean_ctor_get(v_out_836_, 1);
lean_inc(v_endPos_846_);
lean_dec_ref_known(v_out_836_, 2);
v_slice_847_ = l_String_Slice_slice_x21(v_s_828_, v_currPos_830_, v_endPos_846_);
lean_dec(v_currPos_830_);
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v_it_842_);
lean_ctor_set(v___x_833_, 0, v_endPos_846_);
v_nextIt_849_ = v___x_833_;
goto v_reusejp_848_;
}
else
{
lean_object* v_reuseFailAlloc_853_; 
v_reuseFailAlloc_853_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_853_, 0, v_endPos_846_);
lean_ctor_set(v_reuseFailAlloc_853_, 1, v_it_842_);
v_nextIt_849_ = v_reuseFailAlloc_853_;
goto v_reusejp_848_;
}
v_reusejp_848_:
{
lean_object* v___x_851_; 
if (v_isShared_845_ == 0)
{
lean_ctor_set(v___x_844_, 1, v_slice_847_);
lean_ctor_set(v___x_844_, 0, v_nextIt_849_);
v___x_851_ = v___x_844_;
goto v_reusejp_850_;
}
else
{
lean_object* v_reuseFailAlloc_852_; 
v_reuseFailAlloc_852_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_852_, 0, v_nextIt_849_);
lean_ctor_set(v_reuseFailAlloc_852_, 1, v_slice_847_);
v___x_851_ = v_reuseFailAlloc_852_;
goto v_reusejp_850_;
}
v_reusejp_850_:
{
return v___x_851_;
}
}
}
}
}
case 1:
{
lean_object* v_it_856_; lean_object* v___x_858_; uint8_t v_isShared_859_; uint8_t v_isSharedCheck_866_; 
lean_dec_ref(v_s_828_);
v_it_856_ = lean_ctor_get(v___x_835_, 0);
v_isSharedCheck_866_ = !lean_is_exclusive(v___x_835_);
if (v_isSharedCheck_866_ == 0)
{
v___x_858_ = v___x_835_;
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
else
{
lean_inc(v_it_856_);
lean_dec(v___x_835_);
v___x_858_ = lean_box(0);
v_isShared_859_ = v_isSharedCheck_866_;
goto v_resetjp_857_;
}
v_resetjp_857_:
{
lean_object* v___x_861_; 
if (v_isShared_834_ == 0)
{
lean_ctor_set(v___x_833_, 1, v_it_856_);
v___x_861_ = v___x_833_;
goto v_reusejp_860_;
}
else
{
lean_object* v_reuseFailAlloc_865_; 
v_reuseFailAlloc_865_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_865_, 0, v_currPos_830_);
lean_ctor_set(v_reuseFailAlloc_865_, 1, v_it_856_);
v___x_861_ = v_reuseFailAlloc_865_;
goto v_reusejp_860_;
}
v_reusejp_860_:
{
lean_object* v___x_863_; 
if (v_isShared_859_ == 0)
{
lean_ctor_set(v___x_858_, 0, v___x_861_);
v___x_863_ = v___x_858_;
goto v_reusejp_862_;
}
else
{
lean_object* v_reuseFailAlloc_864_; 
v_reuseFailAlloc_864_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_864_, 0, v___x_861_);
v___x_863_ = v_reuseFailAlloc_864_;
goto v_reusejp_862_;
}
v_reusejp_862_:
{
return v___x_863_;
}
}
}
}
default: 
{
lean_object* v_str_867_; lean_object* v_startInclusive_868_; lean_object* v_endExclusive_869_; lean_object* v___x_871_; uint8_t v_isShared_872_; uint8_t v_isSharedCheck_882_; 
lean_del_object(v___x_833_);
v_str_867_ = lean_ctor_get(v_s_828_, 0);
v_startInclusive_868_ = lean_ctor_get(v_s_828_, 1);
v_endExclusive_869_ = lean_ctor_get(v_s_828_, 2);
v_isSharedCheck_882_ = !lean_is_exclusive(v_s_828_);
if (v_isSharedCheck_882_ == 0)
{
v___x_871_ = v_s_828_;
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
else
{
lean_inc(v_endExclusive_869_);
lean_inc(v_startInclusive_868_);
lean_inc(v_str_867_);
lean_dec(v_s_828_);
v___x_871_ = lean_box(0);
v_isShared_872_ = v_isSharedCheck_882_;
goto v_resetjp_870_;
}
v_resetjp_870_:
{
lean_object* v___x_873_; uint8_t v_decide_874_; 
v___x_873_ = lean_nat_sub(v_endExclusive_869_, v_startInclusive_868_);
v_decide_874_ = lean_nat_dec_eq(v_currPos_830_, v___x_873_);
lean_dec(v___x_873_);
if (v_decide_874_ == 0)
{
lean_object* v___x_875_; lean_object* v_slice_877_; 
v___x_875_ = lean_nat_add(v_startInclusive_868_, v_currPos_830_);
lean_dec(v_currPos_830_);
lean_dec(v_startInclusive_868_);
if (v_isShared_872_ == 0)
{
lean_ctor_set(v___x_871_, 1, v___x_875_);
v_slice_877_ = v___x_871_;
goto v_reusejp_876_;
}
else
{
lean_object* v_reuseFailAlloc_880_; 
v_reuseFailAlloc_880_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_880_, 0, v_str_867_);
lean_ctor_set(v_reuseFailAlloc_880_, 1, v___x_875_);
lean_ctor_set(v_reuseFailAlloc_880_, 2, v_endExclusive_869_);
v_slice_877_ = v_reuseFailAlloc_880_;
goto v_reusejp_876_;
}
v_reusejp_876_:
{
lean_object* v___x_878_; lean_object* v___x_879_; 
v___x_878_ = lean_box(1);
v___x_879_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_879_, 0, v___x_878_);
lean_ctor_set(v___x_879_, 1, v_slice_877_);
return v___x_879_;
}
}
else
{
lean_object* v___x_881_; 
lean_del_object(v___x_871_);
lean_dec(v_endExclusive_869_);
lean_dec(v_startInclusive_868_);
lean_dec_ref(v_str_867_);
lean_dec(v_currPos_830_);
v___x_881_ = lean_box(2);
return v___x_881_;
}
}
}
}
}
}
else
{
lean_object* v___x_884_; 
lean_dec_ref(v_s_828_);
lean_dec(v_inst_827_);
v___x_884_ = lean_box(2);
return v___x_884_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg(lean_object* v_inst_885_, lean_object* v_s_886_){
_start:
{
lean_object* v___f_887_; 
v___f_887_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_887_, 0, v_inst_885_);
lean_closure_set(v___f_887_, 1, v_s_886_);
return v___f_887_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId(lean_object* v_00_u03c1_888_, lean_object* v_00_u03c3_889_, lean_object* v_inst_890_, lean_object* v_pat_891_, lean_object* v_inst_892_, lean_object* v_s_893_){
_start:
{
lean_object* v___f_894_; 
v___f_894_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0), 3, 2);
lean_closure_set(v___f_894_, 0, v_inst_890_);
lean_closure_set(v___f_894_, 1, v_s_893_);
return v___f_894_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___boxed(lean_object* v_00_u03c1_895_, lean_object* v_00_u03c3_896_, lean_object* v_inst_897_, lean_object* v_pat_898_, lean_object* v_inst_899_, lean_object* v_s_900_){
_start:
{
lean_object* v_res_901_; 
v_res_901_ = l_String_Slice_SplitInclusiveIterator_instIteratorId(v_00_u03c1_895_, v_00_u03c3_896_, v_inst_897_, v_pat_898_, v_inst_899_, v_s_900_);
lean_dec(v_inst_899_);
lean_dec(v_pat_898_);
return v_res_901_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(lean_object* v_x_902_){
_start:
{
if (lean_obj_tag(v_x_902_) == 0)
{
lean_object* v_searcher_903_; lean_object* v___x_904_; 
v_searcher_903_ = lean_ctor_get(v_x_902_, 1);
lean_inc(v_searcher_903_);
v___x_904_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_904_, 0, v_searcher_903_);
return v___x_904_;
}
else
{
lean_object* v___x_905_; 
v___x_905_ = lean_box(0);
return v___x_905_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg___boxed(lean_object* v_x_906_){
_start:
{
lean_object* v_res_907_; 
v_res_907_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_906_);
lean_dec(v_x_906_);
return v_res_907_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(lean_object* v_00_u03c1_908_, lean_object* v_00_u03c3_909_, lean_object* v_pat_910_, lean_object* v_inst_911_, lean_object* v_s_912_, lean_object* v_x_913_){
_start:
{
lean_object* v___x_914_; 
v___x_914_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___redArg(v_x_913_);
return v___x_914_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption___boxed(lean_object* v_00_u03c1_915_, lean_object* v_00_u03c3_916_, lean_object* v_pat_917_, lean_object* v_inst_918_, lean_object* v_s_919_, lean_object* v_x_920_){
_start:
{
lean_object* v_res_921_; 
v_res_921_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption(v_00_u03c1_915_, v_00_u03c3_916_, v_pat_917_, v_inst_918_, v_s_919_, v_x_920_);
lean_dec(v_x_920_);
lean_dec_ref(v_s_919_);
lean_dec(v_inst_918_);
lean_dec(v_pat_917_);
return v_res_921_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___redArg(lean_object* v_x_922_, lean_object* v_h__1_923_, lean_object* v_h__2_924_){
_start:
{
if (lean_obj_tag(v_x_922_) == 0)
{
lean_object* v_currPos_925_; lean_object* v_searcher_926_; lean_object* v___x_927_; 
lean_dec(v_h__2_924_);
v_currPos_925_ = lean_ctor_get(v_x_922_, 0);
lean_inc(v_currPos_925_);
v_searcher_926_ = lean_ctor_get(v_x_922_, 1);
lean_inc(v_searcher_926_);
lean_dec_ref_known(v_x_922_, 2);
v___x_927_ = lean_apply_2(v_h__1_923_, v_currPos_925_, v_searcher_926_);
return v___x_927_;
}
else
{
lean_object* v___x_928_; lean_object* v___x_929_; 
lean_dec(v_h__1_923_);
v___x_928_ = lean_box(0);
v___x_929_ = lean_apply_1(v_h__2_924_, v___x_928_);
return v___x_929_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(lean_object* v_00_u03c1_930_, lean_object* v_00_u03c3_931_, lean_object* v_pat_932_, lean_object* v_inst_933_, lean_object* v_s_934_, lean_object* v_motive_935_, lean_object* v_x_936_, lean_object* v_h__1_937_, lean_object* v_h__2_938_){
_start:
{
if (lean_obj_tag(v_x_936_) == 0)
{
lean_object* v_currPos_939_; lean_object* v_searcher_940_; lean_object* v___x_941_; 
lean_dec(v_h__2_938_);
v_currPos_939_ = lean_ctor_get(v_x_936_, 0);
lean_inc(v_currPos_939_);
v_searcher_940_ = lean_ctor_get(v_x_936_, 1);
lean_inc(v_searcher_940_);
lean_dec_ref_known(v_x_936_, 2);
v___x_941_ = lean_apply_2(v_h__1_937_, v_currPos_939_, v_searcher_940_);
return v___x_941_;
}
else
{
lean_object* v___x_942_; lean_object* v___x_943_; 
lean_dec(v_h__1_937_);
v___x_942_ = lean_box(0);
v___x_943_ = lean_apply_1(v_h__2_938_, v___x_942_);
return v___x_943_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter___boxed(lean_object* v_00_u03c1_944_, lean_object* v_00_u03c3_945_, lean_object* v_pat_946_, lean_object* v_inst_947_, lean_object* v_s_948_, lean_object* v_motive_949_, lean_object* v_x_950_, lean_object* v_h__1_951_, lean_object* v_h__2_952_){
_start:
{
lean_object* v_res_953_; 
v_res_953_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__3_splitter(v_00_u03c1_944_, v_00_u03c3_945_, v_pat_946_, v_inst_947_, v_s_948_, v_motive_949_, v_x_950_, v_h__1_951_, v_h__2_952_);
lean_dec_ref(v_s_948_);
lean_dec(v_inst_947_);
lean_dec(v_pat_946_);
return v_res_953_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___redArg(lean_object* v_x_954_, lean_object* v_x_955_, lean_object* v_h__1_956_, lean_object* v_h__2_957_, lean_object* v_h__3_958_, lean_object* v_h__4_959_, lean_object* v_h__5_960_, lean_object* v_h__6_961_, lean_object* v_h__7_962_, lean_object* v_h__8_963_){
_start:
{
if (lean_obj_tag(v_x_954_) == 0)
{
lean_dec(v_h__8_963_);
lean_dec(v_h__7_962_);
lean_dec(v_h__6_961_);
switch(lean_obj_tag(v_x_955_))
{
case 0:
{
lean_object* v_it_964_; 
lean_dec(v_h__5_960_);
lean_dec(v_h__4_959_);
lean_dec(v_h__3_958_);
v_it_964_ = lean_ctor_get(v_x_955_, 0);
if (lean_obj_tag(v_it_964_) == 0)
{
lean_object* v_currPos_965_; lean_object* v_searcher_966_; lean_object* v_out_967_; lean_object* v_currPos_968_; lean_object* v_searcher_969_; lean_object* v___x_970_; 
lean_inc_ref(v_it_964_);
lean_dec(v_h__2_957_);
v_currPos_965_ = lean_ctor_get(v_x_954_, 0);
lean_inc(v_currPos_965_);
v_searcher_966_ = lean_ctor_get(v_x_954_, 1);
lean_inc(v_searcher_966_);
lean_dec_ref_known(v_x_954_, 2);
v_out_967_ = lean_ctor_get(v_x_955_, 1);
lean_inc(v_out_967_);
lean_dec_ref_known(v_x_955_, 2);
v_currPos_968_ = lean_ctor_get(v_it_964_, 0);
lean_inc(v_currPos_968_);
v_searcher_969_ = lean_ctor_get(v_it_964_, 1);
lean_inc(v_searcher_969_);
lean_dec_ref_known(v_it_964_, 2);
v___x_970_ = lean_apply_5(v_h__1_956_, v_currPos_965_, v_searcher_966_, v_currPos_968_, v_searcher_969_, v_out_967_);
return v___x_970_;
}
else
{
lean_object* v_currPos_971_; lean_object* v_searcher_972_; lean_object* v_out_973_; lean_object* v___x_974_; 
lean_dec(v_h__1_956_);
v_currPos_971_ = lean_ctor_get(v_x_954_, 0);
lean_inc(v_currPos_971_);
v_searcher_972_ = lean_ctor_get(v_x_954_, 1);
lean_inc(v_searcher_972_);
lean_dec_ref_known(v_x_954_, 2);
v_out_973_ = lean_ctor_get(v_x_955_, 1);
lean_inc(v_out_973_);
lean_dec_ref_known(v_x_955_, 2);
v___x_974_ = lean_apply_3(v_h__2_957_, v_currPos_971_, v_searcher_972_, v_out_973_);
return v___x_974_;
}
}
case 1:
{
lean_object* v_it_975_; 
lean_dec(v_h__5_960_);
lean_dec(v_h__2_957_);
lean_dec(v_h__1_956_);
v_it_975_ = lean_ctor_get(v_x_955_, 0);
lean_inc(v_it_975_);
lean_dec_ref_known(v_x_955_, 1);
if (lean_obj_tag(v_it_975_) == 0)
{
lean_object* v_currPos_976_; lean_object* v_searcher_977_; lean_object* v_currPos_978_; lean_object* v_searcher_979_; lean_object* v___x_980_; 
lean_dec(v_h__4_959_);
v_currPos_976_ = lean_ctor_get(v_x_954_, 0);
lean_inc(v_currPos_976_);
v_searcher_977_ = lean_ctor_get(v_x_954_, 1);
lean_inc(v_searcher_977_);
lean_dec_ref_known(v_x_954_, 2);
v_currPos_978_ = lean_ctor_get(v_it_975_, 0);
lean_inc(v_currPos_978_);
v_searcher_979_ = lean_ctor_get(v_it_975_, 1);
lean_inc(v_searcher_979_);
lean_dec_ref_known(v_it_975_, 2);
v___x_980_ = lean_apply_4(v_h__3_958_, v_currPos_976_, v_searcher_977_, v_currPos_978_, v_searcher_979_);
return v___x_980_;
}
else
{
lean_object* v_currPos_981_; lean_object* v_searcher_982_; lean_object* v___x_983_; 
lean_dec(v_h__3_958_);
v_currPos_981_ = lean_ctor_get(v_x_954_, 0);
lean_inc(v_currPos_981_);
v_searcher_982_ = lean_ctor_get(v_x_954_, 1);
lean_inc(v_searcher_982_);
lean_dec_ref_known(v_x_954_, 2);
v___x_983_ = lean_apply_2(v_h__4_959_, v_currPos_981_, v_searcher_982_);
return v___x_983_;
}
}
default: 
{
lean_object* v_currPos_984_; lean_object* v_searcher_985_; lean_object* v___x_986_; 
lean_dec(v_h__4_959_);
lean_dec(v_h__3_958_);
lean_dec(v_h__2_957_);
lean_dec(v_h__1_956_);
v_currPos_984_ = lean_ctor_get(v_x_954_, 0);
lean_inc(v_currPos_984_);
v_searcher_985_ = lean_ctor_get(v_x_954_, 1);
lean_inc(v_searcher_985_);
lean_dec_ref_known(v_x_954_, 2);
v___x_986_ = lean_apply_2(v_h__5_960_, v_currPos_984_, v_searcher_985_);
return v___x_986_;
}
}
}
else
{
lean_dec(v_h__5_960_);
lean_dec(v_h__4_959_);
lean_dec(v_h__3_958_);
lean_dec(v_h__2_957_);
lean_dec(v_h__1_956_);
switch(lean_obj_tag(v_x_955_))
{
case 0:
{
lean_object* v_it_987_; lean_object* v_out_988_; lean_object* v___x_989_; 
lean_dec(v_h__8_963_);
lean_dec(v_h__7_962_);
v_it_987_ = lean_ctor_get(v_x_955_, 0);
lean_inc(v_it_987_);
v_out_988_ = lean_ctor_get(v_x_955_, 1);
lean_inc(v_out_988_);
lean_dec_ref_known(v_x_955_, 2);
v___x_989_ = lean_apply_2(v_h__6_961_, v_it_987_, v_out_988_);
return v___x_989_;
}
case 1:
{
lean_object* v_it_990_; lean_object* v___x_991_; 
lean_dec(v_h__8_963_);
lean_dec(v_h__6_961_);
v_it_990_ = lean_ctor_get(v_x_955_, 0);
lean_inc(v_it_990_);
lean_dec_ref_known(v_x_955_, 1);
v___x_991_ = lean_apply_1(v_h__7_962_, v_it_990_);
return v___x_991_;
}
default: 
{
lean_object* v___x_992_; lean_object* v___x_993_; 
lean_dec(v_h__7_962_);
lean_dec(v_h__6_961_);
v___x_992_ = lean_box(0);
v___x_993_ = lean_apply_1(v_h__8_963_, v___x_992_);
return v___x_993_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(lean_object* v_00_u03c1_994_, lean_object* v_00_u03c3_995_, lean_object* v_pat_996_, lean_object* v_inst_997_, lean_object* v_s_998_, lean_object* v_motive_999_, lean_object* v_x_1000_, lean_object* v_x_1001_, lean_object* v_h__1_1002_, lean_object* v_h__2_1003_, lean_object* v_h__3_1004_, lean_object* v_h__4_1005_, lean_object* v_h__5_1006_, lean_object* v_h__6_1007_, lean_object* v_h__7_1008_, lean_object* v_h__8_1009_){
_start:
{
if (lean_obj_tag(v_x_1000_) == 0)
{
lean_dec(v_h__8_1009_);
lean_dec(v_h__7_1008_);
lean_dec(v_h__6_1007_);
switch(lean_obj_tag(v_x_1001_))
{
case 0:
{
lean_object* v_it_1010_; 
lean_dec(v_h__5_1006_);
lean_dec(v_h__4_1005_);
lean_dec(v_h__3_1004_);
v_it_1010_ = lean_ctor_get(v_x_1001_, 0);
if (lean_obj_tag(v_it_1010_) == 0)
{
lean_object* v_currPos_1011_; lean_object* v_searcher_1012_; lean_object* v_out_1013_; lean_object* v_currPos_1014_; lean_object* v_searcher_1015_; lean_object* v___x_1016_; 
lean_inc_ref(v_it_1010_);
lean_dec(v_h__2_1003_);
v_currPos_1011_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_currPos_1011_);
v_searcher_1012_ = lean_ctor_get(v_x_1000_, 1);
lean_inc(v_searcher_1012_);
lean_dec_ref_known(v_x_1000_, 2);
v_out_1013_ = lean_ctor_get(v_x_1001_, 1);
lean_inc(v_out_1013_);
lean_dec_ref_known(v_x_1001_, 2);
v_currPos_1014_ = lean_ctor_get(v_it_1010_, 0);
lean_inc(v_currPos_1014_);
v_searcher_1015_ = lean_ctor_get(v_it_1010_, 1);
lean_inc(v_searcher_1015_);
lean_dec_ref_known(v_it_1010_, 2);
v___x_1016_ = lean_apply_5(v_h__1_1002_, v_currPos_1011_, v_searcher_1012_, v_currPos_1014_, v_searcher_1015_, v_out_1013_);
return v___x_1016_;
}
else
{
lean_object* v_currPos_1017_; lean_object* v_searcher_1018_; lean_object* v_out_1019_; lean_object* v___x_1020_; 
lean_dec(v_h__1_1002_);
v_currPos_1017_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_currPos_1017_);
v_searcher_1018_ = lean_ctor_get(v_x_1000_, 1);
lean_inc(v_searcher_1018_);
lean_dec_ref_known(v_x_1000_, 2);
v_out_1019_ = lean_ctor_get(v_x_1001_, 1);
lean_inc(v_out_1019_);
lean_dec_ref_known(v_x_1001_, 2);
v___x_1020_ = lean_apply_3(v_h__2_1003_, v_currPos_1017_, v_searcher_1018_, v_out_1019_);
return v___x_1020_;
}
}
case 1:
{
lean_object* v_it_1021_; 
lean_dec(v_h__5_1006_);
lean_dec(v_h__2_1003_);
lean_dec(v_h__1_1002_);
v_it_1021_ = lean_ctor_get(v_x_1001_, 0);
lean_inc(v_it_1021_);
lean_dec_ref_known(v_x_1001_, 1);
if (lean_obj_tag(v_it_1021_) == 0)
{
lean_object* v_currPos_1022_; lean_object* v_searcher_1023_; lean_object* v_currPos_1024_; lean_object* v_searcher_1025_; lean_object* v___x_1026_; 
lean_dec(v_h__4_1005_);
v_currPos_1022_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_currPos_1022_);
v_searcher_1023_ = lean_ctor_get(v_x_1000_, 1);
lean_inc(v_searcher_1023_);
lean_dec_ref_known(v_x_1000_, 2);
v_currPos_1024_ = lean_ctor_get(v_it_1021_, 0);
lean_inc(v_currPos_1024_);
v_searcher_1025_ = lean_ctor_get(v_it_1021_, 1);
lean_inc(v_searcher_1025_);
lean_dec_ref_known(v_it_1021_, 2);
v___x_1026_ = lean_apply_4(v_h__3_1004_, v_currPos_1022_, v_searcher_1023_, v_currPos_1024_, v_searcher_1025_);
return v___x_1026_;
}
else
{
lean_object* v_currPos_1027_; lean_object* v_searcher_1028_; lean_object* v___x_1029_; 
lean_dec(v_h__3_1004_);
v_currPos_1027_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_currPos_1027_);
v_searcher_1028_ = lean_ctor_get(v_x_1000_, 1);
lean_inc(v_searcher_1028_);
lean_dec_ref_known(v_x_1000_, 2);
v___x_1029_ = lean_apply_2(v_h__4_1005_, v_currPos_1027_, v_searcher_1028_);
return v___x_1029_;
}
}
default: 
{
lean_object* v_currPos_1030_; lean_object* v_searcher_1031_; lean_object* v___x_1032_; 
lean_dec(v_h__4_1005_);
lean_dec(v_h__3_1004_);
lean_dec(v_h__2_1003_);
lean_dec(v_h__1_1002_);
v_currPos_1030_ = lean_ctor_get(v_x_1000_, 0);
lean_inc(v_currPos_1030_);
v_searcher_1031_ = lean_ctor_get(v_x_1000_, 1);
lean_inc(v_searcher_1031_);
lean_dec_ref_known(v_x_1000_, 2);
v___x_1032_ = lean_apply_2(v_h__5_1006_, v_currPos_1030_, v_searcher_1031_);
return v___x_1032_;
}
}
}
else
{
lean_dec(v_h__5_1006_);
lean_dec(v_h__4_1005_);
lean_dec(v_h__3_1004_);
lean_dec(v_h__2_1003_);
lean_dec(v_h__1_1002_);
switch(lean_obj_tag(v_x_1001_))
{
case 0:
{
lean_object* v_it_1033_; lean_object* v_out_1034_; lean_object* v___x_1035_; 
lean_dec(v_h__8_1009_);
lean_dec(v_h__7_1008_);
v_it_1033_ = lean_ctor_get(v_x_1001_, 0);
lean_inc(v_it_1033_);
v_out_1034_ = lean_ctor_get(v_x_1001_, 1);
lean_inc(v_out_1034_);
lean_dec_ref_known(v_x_1001_, 2);
v___x_1035_ = lean_apply_2(v_h__6_1007_, v_it_1033_, v_out_1034_);
return v___x_1035_;
}
case 1:
{
lean_object* v_it_1036_; lean_object* v___x_1037_; 
lean_dec(v_h__8_1009_);
lean_dec(v_h__6_1007_);
v_it_1036_ = lean_ctor_get(v_x_1001_, 0);
lean_inc(v_it_1036_);
lean_dec_ref_known(v_x_1001_, 1);
v___x_1037_ = lean_apply_1(v_h__7_1008_, v_it_1036_);
return v___x_1037_;
}
default: 
{
lean_object* v___x_1038_; lean_object* v___x_1039_; 
lean_dec(v_h__7_1008_);
lean_dec(v_h__6_1007_);
v___x_1038_ = lean_box(0);
v___x_1039_ = lean_apply_1(v_h__8_1009_, v___x_1038_);
return v___x_1039_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter___boxed(lean_object* v_00_u03c1_1040_, lean_object* v_00_u03c3_1041_, lean_object* v_pat_1042_, lean_object* v_inst_1043_, lean_object* v_s_1044_, lean_object* v_motive_1045_, lean_object* v_x_1046_, lean_object* v_x_1047_, lean_object* v_h__1_1048_, lean_object* v_h__2_1049_, lean_object* v_h__3_1050_, lean_object* v_h__4_1051_, lean_object* v_h__5_1052_, lean_object* v_h__6_1053_, lean_object* v_h__7_1054_, lean_object* v_h__8_1055_){
_start:
{
lean_object* v_res_1056_; 
v_res_1056_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_instIteratorId_match__1_splitter(v_00_u03c1_1040_, v_00_u03c3_1041_, v_pat_1042_, v_inst_1043_, v_s_1044_, v_motive_1045_, v_x_1046_, v_x_1047_, v_h__1_1048_, v_h__2_1049_, v_h__3_1050_, v_h__4_1051_, v_h__5_1052_, v_h__6_1053_, v_h__7_1054_, v_h__8_1055_);
lean_dec_ref(v_s_1044_);
lean_dec(v_inst_1043_);
lean_dec(v_pat_1042_);
return v_res_1056_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___redArg(lean_object* v_x_1057_, lean_object* v_h__1_1058_, lean_object* v_h__2_1059_){
_start:
{
if (lean_obj_tag(v_x_1057_) == 0)
{
lean_object* v_currPos_1060_; lean_object* v_searcher_1061_; lean_object* v___x_1062_; 
lean_dec(v_h__2_1059_);
v_currPos_1060_ = lean_ctor_get(v_x_1057_, 0);
lean_inc(v_currPos_1060_);
v_searcher_1061_ = lean_ctor_get(v_x_1057_, 1);
lean_inc(v_searcher_1061_);
lean_dec_ref_known(v_x_1057_, 2);
v___x_1062_ = lean_apply_2(v_h__1_1058_, v_currPos_1060_, v_searcher_1061_);
return v___x_1062_;
}
else
{
lean_object* v___x_1063_; lean_object* v___x_1064_; 
lean_dec(v_h__1_1058_);
v___x_1063_ = lean_box(0);
v___x_1064_ = lean_apply_1(v_h__2_1059_, v___x_1063_);
return v___x_1064_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_1065_, lean_object* v_00_u03c3_1066_, lean_object* v_pat_1067_, lean_object* v_inst_1068_, lean_object* v_s_1069_, lean_object* v_motive_1070_, lean_object* v_x_1071_, lean_object* v_h__1_1072_, lean_object* v_h__2_1073_){
_start:
{
if (lean_obj_tag(v_x_1071_) == 0)
{
lean_object* v_currPos_1074_; lean_object* v_searcher_1075_; lean_object* v___x_1076_; 
lean_dec(v_h__2_1073_);
v_currPos_1074_ = lean_ctor_get(v_x_1071_, 0);
lean_inc(v_currPos_1074_);
v_searcher_1075_ = lean_ctor_get(v_x_1071_, 1);
lean_inc(v_searcher_1075_);
lean_dec_ref_known(v_x_1071_, 2);
v___x_1076_ = lean_apply_2(v_h__1_1072_, v_currPos_1074_, v_searcher_1075_);
return v___x_1076_;
}
else
{
lean_object* v___x_1077_; lean_object* v___x_1078_; 
lean_dec(v_h__1_1072_);
v___x_1077_ = lean_box(0);
v___x_1078_ = lean_apply_1(v_h__2_1073_, v___x_1077_);
return v___x_1078_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_1079_, lean_object* v_00_u03c3_1080_, lean_object* v_pat_1081_, lean_object* v_inst_1082_, lean_object* v_s_1083_, lean_object* v_motive_1084_, lean_object* v_x_1085_, lean_object* v_h__1_1086_, lean_object* v_h__2_1087_){
_start:
{
lean_object* v_res_1088_; 
v_res_1088_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_toOption_match__1_splitter(v_00_u03c1_1079_, v_00_u03c3_1080_, v_pat_1081_, v_inst_1082_, v_s_1083_, v_motive_1084_, v_x_1085_, v_h__1_1086_, v_h__2_1087_);
lean_dec_ref(v_s_1083_);
lean_dec(v_inst_1082_);
lean_dec(v_pat_1081_);
return v_res_1088_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_1090_; 
v___x_1090_ = lean_box(0);
return v___x_1090_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_1091_){
_start:
{
lean_object* v_res_1092_; 
v_res_1092_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg();
return v_res_1092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(lean_object* v_00_u03c1_1093_, lean_object* v_00_u03c3_1094_, lean_object* v_inst_1095_, lean_object* v_pat_1096_, lean_object* v_inst_1097_, lean_object* v_s_1098_, lean_object* v_inst_1099_){
_start:
{
lean_object* v___x_1100_; 
v___x_1100_ = lean_box(0);
return v___x_1100_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_1101_, lean_object* v_00_u03c3_1102_, lean_object* v_inst_1103_, lean_object* v_pat_1104_, lean_object* v_inst_1105_, lean_object* v_s_1106_, lean_object* v_inst_1107_){
_start:
{
lean_object* v_res_1108_; 
v_res_1108_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(v_00_u03c1_1101_, v_00_u03c3_1102_, v_inst_1103_, v_pat_1104_, v_inst_1105_, v_s_1106_, v_inst_1107_);
lean_dec_ref(v_s_1106_);
lean_dec(v_inst_1105_);
lean_dec(v_pat_1104_);
lean_dec(v_inst_1103_);
return v_res_1108_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0(lean_object* v_toPure_1109_, lean_object* v_recur_1110_, lean_object* v_it_1111_, lean_object* v_____do__lift_1112_){
_start:
{
if (lean_obj_tag(v_____do__lift_1112_) == 0)
{
lean_object* v_a_1113_; lean_object* v___x_1114_; 
lean_dec(v_it_1111_);
lean_dec(v_recur_1110_);
v_a_1113_ = lean_ctor_get(v_____do__lift_1112_, 0);
lean_inc(v_a_1113_);
lean_dec_ref_known(v_____do__lift_1112_, 1);
v___x_1114_ = lean_apply_2(v_toPure_1109_, lean_box(0), v_a_1113_);
return v___x_1114_;
}
else
{
lean_object* v_a_1115_; lean_object* v___x_1116_; 
lean_dec(v_toPure_1109_);
v_a_1115_ = lean_ctor_get(v_____do__lift_1112_, 0);
lean_inc(v_a_1115_);
lean_dec_ref_known(v_____do__lift_1112_, 1);
v___x_1116_ = lean_apply_4(v_recur_1110_, v_it_1111_, v_a_1115_, lean_box(0), lean_box(0));
return v___x_1116_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1(lean_object* v_toPure_1117_, lean_object* v_recur_1118_, lean_object* v___y_1119_, lean_object* v_acc_1120_, lean_object* v_toBind_1121_, lean_object* v_s_1122_){
_start:
{
switch(lean_obj_tag(v_s_1122_))
{
case 0:
{
lean_object* v_it_1123_; lean_object* v_out_1124_; lean_object* v___f_1125_; lean_object* v___x_1126_; lean_object* v___x_1127_; 
v_it_1123_ = lean_ctor_get(v_s_1122_, 0);
lean_inc(v_it_1123_);
v_out_1124_ = lean_ctor_get(v_s_1122_, 1);
lean_inc(v_out_1124_);
lean_dec_ref_known(v_s_1122_, 2);
v___f_1125_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1125_, 0, v_toPure_1117_);
lean_closure_set(v___f_1125_, 1, v_recur_1118_);
lean_closure_set(v___f_1125_, 2, v_it_1123_);
v___x_1126_ = lean_apply_3(v___y_1119_, v_out_1124_, lean_box(0), v_acc_1120_);
v___x_1127_ = lean_apply_4(v_toBind_1121_, lean_box(0), lean_box(0), v___x_1126_, v___f_1125_);
return v___x_1127_;
}
case 1:
{
lean_object* v_it_1128_; lean_object* v___x_1129_; 
lean_dec(v_toBind_1121_);
lean_dec(v___y_1119_);
lean_dec(v_toPure_1117_);
v_it_1128_ = lean_ctor_get(v_s_1122_, 0);
lean_inc(v_it_1128_);
lean_dec_ref_known(v_s_1122_, 1);
v___x_1129_ = lean_apply_4(v_recur_1118_, v_it_1128_, v_acc_1120_, lean_box(0), lean_box(0));
return v___x_1129_;
}
default: 
{
lean_object* v___x_1130_; 
lean_dec(v_toBind_1121_);
lean_dec(v___y_1119_);
lean_dec(v_recur_1118_);
v___x_1130_ = lean_apply_2(v_toPure_1117_, lean_box(0), v_acc_1120_);
return v___x_1130_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2(lean_object* v_toPure_1131_, lean_object* v___y_1132_, lean_object* v_toBind_1133_, lean_object* v_inst_1134_, lean_object* v_s_1135_, lean_object* v_lift_1136_, lean_object* v_it_1137_, lean_object* v_acc_1138_, lean_object* v_hP_1139_, lean_object* v_recur_1140_){
_start:
{
lean_object* v___f_1141_; 
v___f_1141_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_1141_, 0, v_toPure_1131_);
lean_closure_set(v___f_1141_, 1, v_recur_1140_);
lean_closure_set(v___f_1141_, 2, v___y_1132_);
lean_closure_set(v___f_1141_, 3, v_acc_1138_);
lean_closure_set(v___f_1141_, 4, v_toBind_1133_);
if (lean_obj_tag(v_it_1137_) == 0)
{
lean_object* v_currPos_1142_; lean_object* v_searcher_1143_; lean_object* v___x_1145_; uint8_t v_isShared_1146_; uint8_t v_isSharedCheck_1200_; 
v_currPos_1142_ = lean_ctor_get(v_it_1137_, 0);
v_searcher_1143_ = lean_ctor_get(v_it_1137_, 1);
v_isSharedCheck_1200_ = !lean_is_exclusive(v_it_1137_);
if (v_isSharedCheck_1200_ == 0)
{
v___x_1145_ = v_it_1137_;
v_isShared_1146_ = v_isSharedCheck_1200_;
goto v_resetjp_1144_;
}
else
{
lean_inc(v_searcher_1143_);
lean_inc(v_currPos_1142_);
lean_dec(v_it_1137_);
v___x_1145_ = lean_box(0);
v_isShared_1146_ = v_isSharedCheck_1200_;
goto v_resetjp_1144_;
}
v_resetjp_1144_:
{
lean_object* v___x_1147_; 
lean_inc_ref(v_s_1135_);
v___x_1147_ = lean_apply_2(v_inst_1134_, v_s_1135_, v_searcher_1143_);
switch(lean_obj_tag(v___x_1147_))
{
case 0:
{
lean_object* v_out_1148_; 
v_out_1148_ = lean_ctor_get(v___x_1147_, 1);
lean_inc(v_out_1148_);
if (lean_obj_tag(v_out_1148_) == 0)
{
lean_object* v_it_1149_; lean_object* v___x_1151_; 
lean_dec_ref_known(v_out_1148_, 2);
lean_dec_ref(v_s_1135_);
v_it_1149_ = lean_ctor_get(v___x_1147_, 0);
lean_inc(v_it_1149_);
lean_dec_ref_known(v___x_1147_, 2);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_it_1149_);
v___x_1151_ = v___x_1145_;
goto v_reusejp_1150_;
}
else
{
lean_object* v_reuseFailAlloc_1154_; 
v_reuseFailAlloc_1154_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1154_, 0, v_currPos_1142_);
lean_ctor_set(v_reuseFailAlloc_1154_, 1, v_it_1149_);
v___x_1151_ = v_reuseFailAlloc_1154_;
goto v_reusejp_1150_;
}
v_reusejp_1150_:
{
lean_object* v___x_1152_; lean_object* v___x_1153_; 
v___x_1152_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1152_, 0, v___x_1151_);
v___x_1153_ = lean_apply_4(v_lift_1136_, lean_box(0), lean_box(0), v___f_1141_, v___x_1152_);
return v___x_1153_;
}
}
else
{
lean_object* v_it_1155_; lean_object* v___x_1157_; uint8_t v_isShared_1158_; uint8_t v_isSharedCheck_1168_; 
v_it_1155_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1168_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1168_ == 0)
{
lean_object* v_unused_1169_; 
v_unused_1169_ = lean_ctor_get(v___x_1147_, 1);
lean_dec(v_unused_1169_);
v___x_1157_ = v___x_1147_;
v_isShared_1158_ = v_isSharedCheck_1168_;
goto v_resetjp_1156_;
}
else
{
lean_inc(v_it_1155_);
lean_dec(v___x_1147_);
v___x_1157_ = lean_box(0);
v_isShared_1158_ = v_isSharedCheck_1168_;
goto v_resetjp_1156_;
}
v_resetjp_1156_:
{
lean_object* v_endPos_1159_; lean_object* v_slice_1160_; lean_object* v_nextIt_1162_; 
v_endPos_1159_ = lean_ctor_get(v_out_1148_, 1);
lean_inc(v_endPos_1159_);
lean_dec_ref_known(v_out_1148_, 2);
v_slice_1160_ = l_String_Slice_slice_x21(v_s_1135_, v_currPos_1142_, v_endPos_1159_);
lean_dec(v_currPos_1142_);
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_it_1155_);
lean_ctor_set(v___x_1145_, 0, v_endPos_1159_);
v_nextIt_1162_ = v___x_1145_;
goto v_reusejp_1161_;
}
else
{
lean_object* v_reuseFailAlloc_1167_; 
v_reuseFailAlloc_1167_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1167_, 0, v_endPos_1159_);
lean_ctor_set(v_reuseFailAlloc_1167_, 1, v_it_1155_);
v_nextIt_1162_ = v_reuseFailAlloc_1167_;
goto v_reusejp_1161_;
}
v_reusejp_1161_:
{
lean_object* v___x_1164_; 
if (v_isShared_1158_ == 0)
{
lean_ctor_set(v___x_1157_, 1, v_slice_1160_);
lean_ctor_set(v___x_1157_, 0, v_nextIt_1162_);
v___x_1164_ = v___x_1157_;
goto v_reusejp_1163_;
}
else
{
lean_object* v_reuseFailAlloc_1166_; 
v_reuseFailAlloc_1166_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1166_, 0, v_nextIt_1162_);
lean_ctor_set(v_reuseFailAlloc_1166_, 1, v_slice_1160_);
v___x_1164_ = v_reuseFailAlloc_1166_;
goto v_reusejp_1163_;
}
v_reusejp_1163_:
{
lean_object* v___x_1165_; 
v___x_1165_ = lean_apply_4(v_lift_1136_, lean_box(0), lean_box(0), v___f_1141_, v___x_1164_);
return v___x_1165_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1170_; lean_object* v___x_1172_; uint8_t v_isShared_1173_; uint8_t v_isSharedCheck_1181_; 
lean_dec_ref(v_s_1135_);
v_it_1170_ = lean_ctor_get(v___x_1147_, 0);
v_isSharedCheck_1181_ = !lean_is_exclusive(v___x_1147_);
if (v_isSharedCheck_1181_ == 0)
{
v___x_1172_ = v___x_1147_;
v_isShared_1173_ = v_isSharedCheck_1181_;
goto v_resetjp_1171_;
}
else
{
lean_inc(v_it_1170_);
lean_dec(v___x_1147_);
v___x_1172_ = lean_box(0);
v_isShared_1173_ = v_isSharedCheck_1181_;
goto v_resetjp_1171_;
}
v_resetjp_1171_:
{
lean_object* v___x_1175_; 
if (v_isShared_1146_ == 0)
{
lean_ctor_set(v___x_1145_, 1, v_it_1170_);
v___x_1175_ = v___x_1145_;
goto v_reusejp_1174_;
}
else
{
lean_object* v_reuseFailAlloc_1180_; 
v_reuseFailAlloc_1180_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1180_, 0, v_currPos_1142_);
lean_ctor_set(v_reuseFailAlloc_1180_, 1, v_it_1170_);
v___x_1175_ = v_reuseFailAlloc_1180_;
goto v_reusejp_1174_;
}
v_reusejp_1174_:
{
lean_object* v___x_1177_; 
if (v_isShared_1173_ == 0)
{
lean_ctor_set(v___x_1172_, 0, v___x_1175_);
v___x_1177_ = v___x_1172_;
goto v_reusejp_1176_;
}
else
{
lean_object* v_reuseFailAlloc_1179_; 
v_reuseFailAlloc_1179_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1179_, 0, v___x_1175_);
v___x_1177_ = v_reuseFailAlloc_1179_;
goto v_reusejp_1176_;
}
v_reusejp_1176_:
{
lean_object* v___x_1178_; 
v___x_1178_ = lean_apply_4(v_lift_1136_, lean_box(0), lean_box(0), v___f_1141_, v___x_1177_);
return v___x_1178_;
}
}
}
}
default: 
{
lean_object* v_str_1182_; lean_object* v_startInclusive_1183_; lean_object* v_endExclusive_1184_; lean_object* v___x_1186_; uint8_t v_isShared_1187_; uint8_t v_isSharedCheck_1199_; 
lean_del_object(v___x_1145_);
v_str_1182_ = lean_ctor_get(v_s_1135_, 0);
v_startInclusive_1183_ = lean_ctor_get(v_s_1135_, 1);
v_endExclusive_1184_ = lean_ctor_get(v_s_1135_, 2);
v_isSharedCheck_1199_ = !lean_is_exclusive(v_s_1135_);
if (v_isSharedCheck_1199_ == 0)
{
v___x_1186_ = v_s_1135_;
v_isShared_1187_ = v_isSharedCheck_1199_;
goto v_resetjp_1185_;
}
else
{
lean_inc(v_endExclusive_1184_);
lean_inc(v_startInclusive_1183_);
lean_inc(v_str_1182_);
lean_dec(v_s_1135_);
v___x_1186_ = lean_box(0);
v_isShared_1187_ = v_isSharedCheck_1199_;
goto v_resetjp_1185_;
}
v_resetjp_1185_:
{
lean_object* v___x_1188_; uint8_t v_decide_1189_; 
v___x_1188_ = lean_nat_sub(v_endExclusive_1184_, v_startInclusive_1183_);
v_decide_1189_ = lean_nat_dec_eq(v_currPos_1142_, v___x_1188_);
lean_dec(v___x_1188_);
if (v_decide_1189_ == 0)
{
lean_object* v___x_1190_; lean_object* v_slice_1192_; 
v___x_1190_ = lean_nat_add(v_startInclusive_1183_, v_currPos_1142_);
lean_dec(v_currPos_1142_);
lean_dec(v_startInclusive_1183_);
if (v_isShared_1187_ == 0)
{
lean_ctor_set(v___x_1186_, 1, v___x_1190_);
v_slice_1192_ = v___x_1186_;
goto v_reusejp_1191_;
}
else
{
lean_object* v_reuseFailAlloc_1196_; 
v_reuseFailAlloc_1196_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1196_, 0, v_str_1182_);
lean_ctor_set(v_reuseFailAlloc_1196_, 1, v___x_1190_);
lean_ctor_set(v_reuseFailAlloc_1196_, 2, v_endExclusive_1184_);
v_slice_1192_ = v_reuseFailAlloc_1196_;
goto v_reusejp_1191_;
}
v_reusejp_1191_:
{
lean_object* v___x_1193_; lean_object* v___x_1194_; lean_object* v___x_1195_; 
v___x_1193_ = lean_box(1);
v___x_1194_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1194_, 0, v___x_1193_);
lean_ctor_set(v___x_1194_, 1, v_slice_1192_);
v___x_1195_ = lean_apply_4(v_lift_1136_, lean_box(0), lean_box(0), v___f_1141_, v___x_1194_);
return v___x_1195_;
}
}
else
{
lean_object* v___x_1197_; lean_object* v___x_1198_; 
lean_del_object(v___x_1186_);
lean_dec(v_endExclusive_1184_);
lean_dec(v_startInclusive_1183_);
lean_dec_ref(v_str_1182_);
lean_dec(v_currPos_1142_);
v___x_1197_ = lean_box(2);
v___x_1198_ = lean_apply_4(v_lift_1136_, lean_box(0), lean_box(0), v___f_1141_, v___x_1197_);
return v___x_1198_;
}
}
}
}
}
}
else
{
lean_object* v___x_1201_; lean_object* v___x_1202_; 
lean_dec_ref(v_s_1135_);
lean_dec(v_inst_1134_);
v___x_1201_ = lean_box(2);
v___x_1202_ = lean_apply_4(v_lift_1136_, lean_box(0), lean_box(0), v___f_1141_, v___x_1201_);
return v___x_1202_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3(lean_object* v_inst_1203_, lean_object* v_inst_1204_, lean_object* v_s_1205_, lean_object* v_lift_1206_, lean_object* v_00_u03b3_1207_, lean_object* v_Pl_1208_, lean_object* v_it_1209_, lean_object* v_init_1210_, lean_object* v___y_1211_){
_start:
{
lean_object* v_toApplicative_1212_; lean_object* v_toBind_1213_; lean_object* v_toPure_1214_; lean_object* v___f_1215_; lean_object* v___x_1216_; 
v_toApplicative_1212_ = lean_ctor_get(v_inst_1203_, 0);
lean_inc_ref(v_toApplicative_1212_);
v_toBind_1213_ = lean_ctor_get(v_inst_1203_, 1);
lean_inc(v_toBind_1213_);
lean_dec_ref(v_inst_1203_);
v_toPure_1214_ = lean_ctor_get(v_toApplicative_1212_, 1);
lean_inc(v_toPure_1214_);
lean_dec_ref(v_toApplicative_1212_);
v___f_1215_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_1215_, 0, v_toPure_1214_);
lean_closure_set(v___f_1215_, 1, v___y_1211_);
lean_closure_set(v___f_1215_, 2, v_toBind_1213_);
lean_closure_set(v___f_1215_, 3, v_inst_1204_);
lean_closure_set(v___f_1215_, 4, v_s_1205_);
lean_closure_set(v___f_1215_, 5, v_lift_1206_);
v___x_1216_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1215_, v_it_1209_, v_init_1210_, lean_box(0));
return v___x_1216_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg(lean_object* v_inst_1217_, lean_object* v_inst_1218_, lean_object* v_s_1219_){
_start:
{
lean_object* v___f_1220_; 
v___f_1220_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1220_, 0, v_inst_1218_);
lean_closure_set(v___f_1220_, 1, v_inst_1217_);
lean_closure_set(v___f_1220_, 2, v_s_1219_);
return v___f_1220_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(lean_object* v_00_u03c1_1221_, lean_object* v_00_u03c3_1222_, lean_object* v_inst_1223_, lean_object* v_pat_1224_, lean_object* v_inst_1225_, lean_object* v_n_1226_, lean_object* v_inst_1227_, lean_object* v_s_1228_){
_start:
{
lean_object* v___f_1229_; 
v___f_1229_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1229_, 0, v_inst_1227_);
lean_closure_set(v___f_1229_, 1, v_inst_1223_);
lean_closure_set(v___f_1229_, 2, v_s_1228_);
return v___f_1229_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___boxed(lean_object* v_00_u03c1_1230_, lean_object* v_00_u03c3_1231_, lean_object* v_inst_1232_, lean_object* v_pat_1233_, lean_object* v_inst_1234_, lean_object* v_n_1235_, lean_object* v_inst_1236_, lean_object* v_s_1237_){
_start:
{
lean_object* v_res_1238_; 
v_res_1238_ = l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(v_00_u03c1_1230_, v_00_u03c3_1231_, v_inst_1232_, v_pat_1233_, v_inst_1234_, v_n_1235_, v_inst_1236_, v_s_1237_);
lean_dec(v_inst_1234_);
lean_dec(v_pat_1233_);
return v_res_1238_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___redArg(lean_object* v_s_1239_, lean_object* v_inst_1240_){
_start:
{
lean_object* v___x_1241_; lean_object* v___x_1242_; lean_object* v___x_1243_; 
v___x_1241_ = lean_unsigned_to_nat(0u);
v___x_1242_ = lean_apply_1(v_inst_1240_, v_s_1239_);
v___x_1243_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1243_, 0, v___x_1241_);
lean_ctor_set(v___x_1243_, 1, v___x_1242_);
return v___x_1243_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive(lean_object* v_00_u03c1_1244_, lean_object* v_00_u03c3_1245_, lean_object* v_s_1246_, lean_object* v_pat_1247_, lean_object* v_inst_1248_){
_start:
{
lean_object* v___x_1249_; 
v___x_1249_ = l_String_Slice_splitInclusive___redArg(v_s_1246_, v_inst_1248_);
return v___x_1249_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___boxed(lean_object* v_00_u03c1_1250_, lean_object* v_00_u03c3_1251_, lean_object* v_s_1252_, lean_object* v_pat_1253_, lean_object* v_inst_1254_){
_start:
{
lean_object* v_res_1255_; 
v_res_1255_ = l_String_Slice_splitInclusive(v_00_u03c1_1250_, v_00_u03c3_1251_, v_s_1252_, v_pat_1253_, v_inst_1254_);
lean_dec(v_pat_1253_);
return v_res_1255_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___redArg(lean_object* v_s_1256_, lean_object* v_inst_1257_){
_start:
{
lean_object* v_skipPrefix_x3f_1258_; lean_object* v___x_1259_; 
v_skipPrefix_x3f_1258_ = lean_ctor_get(v_inst_1257_, 0);
lean_inc_ref(v_skipPrefix_x3f_1258_);
lean_dec_ref(v_inst_1257_);
v___x_1259_ = lean_apply_1(v_skipPrefix_x3f_1258_, v_s_1256_);
return v___x_1259_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f(lean_object* v_00_u03c1_1260_, lean_object* v_s_1261_, lean_object* v_pat_1262_, lean_object* v_inst_1263_){
_start:
{
lean_object* v_skipPrefix_x3f_1264_; lean_object* v___x_1265_; 
v_skipPrefix_x3f_1264_ = lean_ctor_get(v_inst_1263_, 0);
lean_inc_ref(v_skipPrefix_x3f_1264_);
lean_dec_ref(v_inst_1263_);
v___x_1265_ = lean_apply_1(v_skipPrefix_x3f_1264_, v_s_1261_);
return v___x_1265_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___boxed(lean_object* v_00_u03c1_1266_, lean_object* v_s_1267_, lean_object* v_pat_1268_, lean_object* v_inst_1269_){
_start:
{
lean_object* v_res_1270_; 
v_res_1270_ = l_String_Slice_skipPrefix_x3f(v_00_u03c1_1266_, v_s_1267_, v_pat_1268_, v_inst_1269_);
lean_dec(v_pat_1268_);
return v_res_1270_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg(lean_object* v_s_1271_, lean_object* v_pos_1272_, lean_object* v_inst_1273_){
_start:
{
lean_object* v_str_1274_; lean_object* v_startInclusive_1275_; lean_object* v_endExclusive_1276_; lean_object* v___x_1278_; uint8_t v_isShared_1279_; uint8_t v_isSharedCheck_1295_; 
v_str_1274_ = lean_ctor_get(v_s_1271_, 0);
v_startInclusive_1275_ = lean_ctor_get(v_s_1271_, 1);
v_endExclusive_1276_ = lean_ctor_get(v_s_1271_, 2);
v_isSharedCheck_1295_ = !lean_is_exclusive(v_s_1271_);
if (v_isSharedCheck_1295_ == 0)
{
v___x_1278_ = v_s_1271_;
v_isShared_1279_ = v_isSharedCheck_1295_;
goto v_resetjp_1277_;
}
else
{
lean_inc(v_endExclusive_1276_);
lean_inc(v_startInclusive_1275_);
lean_inc(v_str_1274_);
lean_dec(v_s_1271_);
v___x_1278_ = lean_box(0);
v_isShared_1279_ = v_isSharedCheck_1295_;
goto v_resetjp_1277_;
}
v_resetjp_1277_:
{
lean_object* v_skipPrefix_x3f_1280_; lean_object* v___x_1281_; lean_object* v___x_1283_; 
v_skipPrefix_x3f_1280_ = lean_ctor_get(v_inst_1273_, 0);
lean_inc_ref(v_skipPrefix_x3f_1280_);
lean_dec_ref(v_inst_1273_);
v___x_1281_ = lean_nat_add(v_startInclusive_1275_, v_pos_1272_);
lean_dec(v_startInclusive_1275_);
if (v_isShared_1279_ == 0)
{
lean_ctor_set(v___x_1278_, 1, v___x_1281_);
v___x_1283_ = v___x_1278_;
goto v_reusejp_1282_;
}
else
{
lean_object* v_reuseFailAlloc_1294_; 
v_reuseFailAlloc_1294_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1294_, 0, v_str_1274_);
lean_ctor_set(v_reuseFailAlloc_1294_, 1, v___x_1281_);
lean_ctor_set(v_reuseFailAlloc_1294_, 2, v_endExclusive_1276_);
v___x_1283_ = v_reuseFailAlloc_1294_;
goto v_reusejp_1282_;
}
v_reusejp_1282_:
{
lean_object* v___x_1284_; 
v___x_1284_ = lean_apply_1(v_skipPrefix_x3f_1280_, v___x_1283_);
if (lean_obj_tag(v___x_1284_) == 0)
{
return v___x_1284_;
}
else
{
lean_object* v_val_1285_; lean_object* v___x_1287_; uint8_t v_isShared_1288_; uint8_t v_isSharedCheck_1293_; 
v_val_1285_ = lean_ctor_get(v___x_1284_, 0);
v_isSharedCheck_1293_ = !lean_is_exclusive(v___x_1284_);
if (v_isSharedCheck_1293_ == 0)
{
v___x_1287_ = v___x_1284_;
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
else
{
lean_inc(v_val_1285_);
lean_dec(v___x_1284_);
v___x_1287_ = lean_box(0);
v_isShared_1288_ = v_isSharedCheck_1293_;
goto v_resetjp_1286_;
}
v_resetjp_1286_:
{
lean_object* v___x_1289_; lean_object* v___x_1291_; 
v___x_1289_ = lean_nat_add(v_pos_1272_, v_val_1285_);
lean_dec(v_val_1285_);
if (v_isShared_1288_ == 0)
{
lean_ctor_set(v___x_1287_, 0, v___x_1289_);
v___x_1291_ = v___x_1287_;
goto v_reusejp_1290_;
}
else
{
lean_object* v_reuseFailAlloc_1292_; 
v_reuseFailAlloc_1292_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1292_, 0, v___x_1289_);
v___x_1291_ = v_reuseFailAlloc_1292_;
goto v_reusejp_1290_;
}
v_reusejp_1290_:
{
return v___x_1291_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg___boxed(lean_object* v_s_1296_, lean_object* v_pos_1297_, lean_object* v_inst_1298_){
_start:
{
lean_object* v_res_1299_; 
v_res_1299_ = l_String_Slice_Pos_skip_x3f___redArg(v_s_1296_, v_pos_1297_, v_inst_1298_);
lean_dec(v_pos_1297_);
return v_res_1299_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f(lean_object* v_00_u03c1_1300_, lean_object* v_s_1301_, lean_object* v_pos_1302_, lean_object* v_pat_1303_, lean_object* v_inst_1304_){
_start:
{
lean_object* v_str_1305_; lean_object* v_startInclusive_1306_; lean_object* v_endExclusive_1307_; lean_object* v___x_1309_; uint8_t v_isShared_1310_; uint8_t v_isSharedCheck_1326_; 
v_str_1305_ = lean_ctor_get(v_s_1301_, 0);
v_startInclusive_1306_ = lean_ctor_get(v_s_1301_, 1);
v_endExclusive_1307_ = lean_ctor_get(v_s_1301_, 2);
v_isSharedCheck_1326_ = !lean_is_exclusive(v_s_1301_);
if (v_isSharedCheck_1326_ == 0)
{
v___x_1309_ = v_s_1301_;
v_isShared_1310_ = v_isSharedCheck_1326_;
goto v_resetjp_1308_;
}
else
{
lean_inc(v_endExclusive_1307_);
lean_inc(v_startInclusive_1306_);
lean_inc(v_str_1305_);
lean_dec(v_s_1301_);
v___x_1309_ = lean_box(0);
v_isShared_1310_ = v_isSharedCheck_1326_;
goto v_resetjp_1308_;
}
v_resetjp_1308_:
{
lean_object* v_skipPrefix_x3f_1311_; lean_object* v___x_1312_; lean_object* v___x_1314_; 
v_skipPrefix_x3f_1311_ = lean_ctor_get(v_inst_1304_, 0);
lean_inc_ref(v_skipPrefix_x3f_1311_);
lean_dec_ref(v_inst_1304_);
v___x_1312_ = lean_nat_add(v_startInclusive_1306_, v_pos_1302_);
lean_dec(v_startInclusive_1306_);
if (v_isShared_1310_ == 0)
{
lean_ctor_set(v___x_1309_, 1, v___x_1312_);
v___x_1314_ = v___x_1309_;
goto v_reusejp_1313_;
}
else
{
lean_object* v_reuseFailAlloc_1325_; 
v_reuseFailAlloc_1325_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1325_, 0, v_str_1305_);
lean_ctor_set(v_reuseFailAlloc_1325_, 1, v___x_1312_);
lean_ctor_set(v_reuseFailAlloc_1325_, 2, v_endExclusive_1307_);
v___x_1314_ = v_reuseFailAlloc_1325_;
goto v_reusejp_1313_;
}
v_reusejp_1313_:
{
lean_object* v___x_1315_; 
v___x_1315_ = lean_apply_1(v_skipPrefix_x3f_1311_, v___x_1314_);
if (lean_obj_tag(v___x_1315_) == 0)
{
return v___x_1315_;
}
else
{
lean_object* v_val_1316_; lean_object* v___x_1318_; uint8_t v_isShared_1319_; uint8_t v_isSharedCheck_1324_; 
v_val_1316_ = lean_ctor_get(v___x_1315_, 0);
v_isSharedCheck_1324_ = !lean_is_exclusive(v___x_1315_);
if (v_isSharedCheck_1324_ == 0)
{
v___x_1318_ = v___x_1315_;
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
else
{
lean_inc(v_val_1316_);
lean_dec(v___x_1315_);
v___x_1318_ = lean_box(0);
v_isShared_1319_ = v_isSharedCheck_1324_;
goto v_resetjp_1317_;
}
v_resetjp_1317_:
{
lean_object* v___x_1320_; lean_object* v___x_1322_; 
v___x_1320_ = lean_nat_add(v_pos_1302_, v_val_1316_);
lean_dec(v_val_1316_);
if (v_isShared_1319_ == 0)
{
lean_ctor_set(v___x_1318_, 0, v___x_1320_);
v___x_1322_ = v___x_1318_;
goto v_reusejp_1321_;
}
else
{
lean_object* v_reuseFailAlloc_1323_; 
v_reuseFailAlloc_1323_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1323_, 0, v___x_1320_);
v___x_1322_ = v_reuseFailAlloc_1323_;
goto v_reusejp_1321_;
}
v_reusejp_1321_:
{
return v___x_1322_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_1327_, lean_object* v_s_1328_, lean_object* v_pos_1329_, lean_object* v_pat_1330_, lean_object* v_inst_1331_){
_start:
{
lean_object* v_res_1332_; 
v_res_1332_ = l_String_Slice_Pos_skip_x3f(v_00_u03c1_1327_, v_s_1328_, v_pos_1329_, v_pat_1330_, v_inst_1331_);
lean_dec(v_pat_1330_);
lean_dec(v_pos_1329_);
return v_res_1332_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___redArg(lean_object* v_s_1333_, lean_object* v_inst_1334_){
_start:
{
lean_object* v_skipPrefix_x3f_1335_; lean_object* v___x_1336_; 
v_skipPrefix_x3f_1335_ = lean_ctor_get(v_inst_1334_, 0);
lean_inc_ref(v_skipPrefix_x3f_1335_);
lean_dec_ref(v_inst_1334_);
lean_inc_ref(v_s_1333_);
v___x_1336_ = lean_apply_1(v_skipPrefix_x3f_1335_, v_s_1333_);
if (lean_obj_tag(v___x_1336_) == 0)
{
lean_object* v___x_1337_; 
lean_dec_ref(v_s_1333_);
v___x_1337_ = lean_box(0);
return v___x_1337_;
}
else
{
lean_object* v_val_1338_; lean_object* v___x_1340_; uint8_t v_isShared_1341_; uint8_t v_isSharedCheck_1356_; 
v_val_1338_ = lean_ctor_get(v___x_1336_, 0);
v_isSharedCheck_1356_ = !lean_is_exclusive(v___x_1336_);
if (v_isSharedCheck_1356_ == 0)
{
v___x_1340_ = v___x_1336_;
v_isShared_1341_ = v_isSharedCheck_1356_;
goto v_resetjp_1339_;
}
else
{
lean_inc(v_val_1338_);
lean_dec(v___x_1336_);
v___x_1340_ = lean_box(0);
v_isShared_1341_ = v_isSharedCheck_1356_;
goto v_resetjp_1339_;
}
v_resetjp_1339_:
{
lean_object* v_str_1342_; lean_object* v_startInclusive_1343_; lean_object* v_endExclusive_1344_; lean_object* v___x_1346_; uint8_t v_isShared_1347_; uint8_t v_isSharedCheck_1355_; 
v_str_1342_ = lean_ctor_get(v_s_1333_, 0);
v_startInclusive_1343_ = lean_ctor_get(v_s_1333_, 1);
v_endExclusive_1344_ = lean_ctor_get(v_s_1333_, 2);
v_isSharedCheck_1355_ = !lean_is_exclusive(v_s_1333_);
if (v_isSharedCheck_1355_ == 0)
{
v___x_1346_ = v_s_1333_;
v_isShared_1347_ = v_isSharedCheck_1355_;
goto v_resetjp_1345_;
}
else
{
lean_inc(v_endExclusive_1344_);
lean_inc(v_startInclusive_1343_);
lean_inc(v_str_1342_);
lean_dec(v_s_1333_);
v___x_1346_ = lean_box(0);
v_isShared_1347_ = v_isSharedCheck_1355_;
goto v_resetjp_1345_;
}
v_resetjp_1345_:
{
lean_object* v___x_1348_; lean_object* v___x_1350_; 
v___x_1348_ = lean_nat_add(v_startInclusive_1343_, v_val_1338_);
lean_dec(v_val_1338_);
lean_dec(v_startInclusive_1343_);
if (v_isShared_1347_ == 0)
{
lean_ctor_set(v___x_1346_, 1, v___x_1348_);
v___x_1350_ = v___x_1346_;
goto v_reusejp_1349_;
}
else
{
lean_object* v_reuseFailAlloc_1354_; 
v_reuseFailAlloc_1354_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1354_, 0, v_str_1342_);
lean_ctor_set(v_reuseFailAlloc_1354_, 1, v___x_1348_);
lean_ctor_set(v_reuseFailAlloc_1354_, 2, v_endExclusive_1344_);
v___x_1350_ = v_reuseFailAlloc_1354_;
goto v_reusejp_1349_;
}
v_reusejp_1349_:
{
lean_object* v___x_1352_; 
if (v_isShared_1341_ == 0)
{
lean_ctor_set(v___x_1340_, 0, v___x_1350_);
v___x_1352_ = v___x_1340_;
goto v_reusejp_1351_;
}
else
{
lean_object* v_reuseFailAlloc_1353_; 
v_reuseFailAlloc_1353_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1353_, 0, v___x_1350_);
v___x_1352_ = v_reuseFailAlloc_1353_;
goto v_reusejp_1351_;
}
v_reusejp_1351_:
{
return v___x_1352_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f(lean_object* v_00_u03c1_1357_, lean_object* v_s_1358_, lean_object* v_pat_1359_, lean_object* v_inst_1360_){
_start:
{
lean_object* v_skipPrefix_x3f_1361_; lean_object* v___x_1362_; 
v_skipPrefix_x3f_1361_ = lean_ctor_get(v_inst_1360_, 0);
lean_inc_ref(v_skipPrefix_x3f_1361_);
lean_dec_ref(v_inst_1360_);
lean_inc_ref(v_s_1358_);
v___x_1362_ = lean_apply_1(v_skipPrefix_x3f_1361_, v_s_1358_);
if (lean_obj_tag(v___x_1362_) == 0)
{
lean_object* v___x_1363_; 
lean_dec_ref(v_s_1358_);
v___x_1363_ = lean_box(0);
return v___x_1363_;
}
else
{
lean_object* v_val_1364_; lean_object* v___x_1366_; uint8_t v_isShared_1367_; uint8_t v_isSharedCheck_1382_; 
v_val_1364_ = lean_ctor_get(v___x_1362_, 0);
v_isSharedCheck_1382_ = !lean_is_exclusive(v___x_1362_);
if (v_isSharedCheck_1382_ == 0)
{
v___x_1366_ = v___x_1362_;
v_isShared_1367_ = v_isSharedCheck_1382_;
goto v_resetjp_1365_;
}
else
{
lean_inc(v_val_1364_);
lean_dec(v___x_1362_);
v___x_1366_ = lean_box(0);
v_isShared_1367_ = v_isSharedCheck_1382_;
goto v_resetjp_1365_;
}
v_resetjp_1365_:
{
lean_object* v_str_1368_; lean_object* v_startInclusive_1369_; lean_object* v_endExclusive_1370_; lean_object* v___x_1372_; uint8_t v_isShared_1373_; uint8_t v_isSharedCheck_1381_; 
v_str_1368_ = lean_ctor_get(v_s_1358_, 0);
v_startInclusive_1369_ = lean_ctor_get(v_s_1358_, 1);
v_endExclusive_1370_ = lean_ctor_get(v_s_1358_, 2);
v_isSharedCheck_1381_ = !lean_is_exclusive(v_s_1358_);
if (v_isSharedCheck_1381_ == 0)
{
v___x_1372_ = v_s_1358_;
v_isShared_1373_ = v_isSharedCheck_1381_;
goto v_resetjp_1371_;
}
else
{
lean_inc(v_endExclusive_1370_);
lean_inc(v_startInclusive_1369_);
lean_inc(v_str_1368_);
lean_dec(v_s_1358_);
v___x_1372_ = lean_box(0);
v_isShared_1373_ = v_isSharedCheck_1381_;
goto v_resetjp_1371_;
}
v_resetjp_1371_:
{
lean_object* v___x_1374_; lean_object* v___x_1376_; 
v___x_1374_ = lean_nat_add(v_startInclusive_1369_, v_val_1364_);
lean_dec(v_val_1364_);
lean_dec(v_startInclusive_1369_);
if (v_isShared_1373_ == 0)
{
lean_ctor_set(v___x_1372_, 1, v___x_1374_);
v___x_1376_ = v___x_1372_;
goto v_reusejp_1375_;
}
else
{
lean_object* v_reuseFailAlloc_1380_; 
v_reuseFailAlloc_1380_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1380_, 0, v_str_1368_);
lean_ctor_set(v_reuseFailAlloc_1380_, 1, v___x_1374_);
lean_ctor_set(v_reuseFailAlloc_1380_, 2, v_endExclusive_1370_);
v___x_1376_ = v_reuseFailAlloc_1380_;
goto v_reusejp_1375_;
}
v_reusejp_1375_:
{
lean_object* v___x_1378_; 
if (v_isShared_1367_ == 0)
{
lean_ctor_set(v___x_1366_, 0, v___x_1376_);
v___x_1378_ = v___x_1366_;
goto v_reusejp_1377_;
}
else
{
lean_object* v_reuseFailAlloc_1379_; 
v_reuseFailAlloc_1379_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1379_, 0, v___x_1376_);
v___x_1378_ = v_reuseFailAlloc_1379_;
goto v_reusejp_1377_;
}
v_reusejp_1377_:
{
return v___x_1378_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_1383_, lean_object* v_s_1384_, lean_object* v_pat_1385_, lean_object* v_inst_1386_){
_start:
{
lean_object* v_res_1387_; 
v_res_1387_ = l_String_Slice_dropPrefix_x3f(v_00_u03c1_1383_, v_s_1384_, v_pat_1385_, v_inst_1386_);
lean_dec(v_pat_1385_);
return v_res_1387_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___redArg(lean_object* v_s_1388_, lean_object* v_inst_1389_){
_start:
{
lean_object* v_skipPrefix_x3f_1390_; lean_object* v___x_1391_; 
v_skipPrefix_x3f_1390_ = lean_ctor_get(v_inst_1389_, 0);
lean_inc_ref(v_skipPrefix_x3f_1390_);
lean_dec_ref(v_inst_1389_);
lean_inc_ref(v_s_1388_);
v___x_1391_ = lean_apply_1(v_skipPrefix_x3f_1390_, v_s_1388_);
if (lean_obj_tag(v___x_1391_) == 0)
{
return v_s_1388_;
}
else
{
lean_object* v_val_1392_; lean_object* v_str_1393_; lean_object* v_startInclusive_1394_; lean_object* v_endExclusive_1395_; lean_object* v___x_1397_; uint8_t v_isShared_1398_; uint8_t v_isSharedCheck_1403_; 
v_val_1392_ = lean_ctor_get(v___x_1391_, 0);
lean_inc(v_val_1392_);
lean_dec_ref_known(v___x_1391_, 1);
v_str_1393_ = lean_ctor_get(v_s_1388_, 0);
v_startInclusive_1394_ = lean_ctor_get(v_s_1388_, 1);
v_endExclusive_1395_ = lean_ctor_get(v_s_1388_, 2);
v_isSharedCheck_1403_ = !lean_is_exclusive(v_s_1388_);
if (v_isSharedCheck_1403_ == 0)
{
v___x_1397_ = v_s_1388_;
v_isShared_1398_ = v_isSharedCheck_1403_;
goto v_resetjp_1396_;
}
else
{
lean_inc(v_endExclusive_1395_);
lean_inc(v_startInclusive_1394_);
lean_inc(v_str_1393_);
lean_dec(v_s_1388_);
v___x_1397_ = lean_box(0);
v_isShared_1398_ = v_isSharedCheck_1403_;
goto v_resetjp_1396_;
}
v_resetjp_1396_:
{
lean_object* v___x_1399_; lean_object* v___x_1401_; 
v___x_1399_ = lean_nat_add(v_startInclusive_1394_, v_val_1392_);
lean_dec(v_val_1392_);
lean_dec(v_startInclusive_1394_);
if (v_isShared_1398_ == 0)
{
lean_ctor_set(v___x_1397_, 1, v___x_1399_);
v___x_1401_ = v___x_1397_;
goto v_reusejp_1400_;
}
else
{
lean_object* v_reuseFailAlloc_1402_; 
v_reuseFailAlloc_1402_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1402_, 0, v_str_1393_);
lean_ctor_set(v_reuseFailAlloc_1402_, 1, v___x_1399_);
lean_ctor_set(v_reuseFailAlloc_1402_, 2, v_endExclusive_1395_);
v___x_1401_ = v_reuseFailAlloc_1402_;
goto v_reusejp_1400_;
}
v_reusejp_1400_:
{
return v___x_1401_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix(lean_object* v_00_u03c1_1404_, lean_object* v_s_1405_, lean_object* v_pat_1406_, lean_object* v_inst_1407_){
_start:
{
lean_object* v___x_1408_; 
v___x_1408_ = l_String_Slice_dropPrefix___redArg(v_s_1405_, v_inst_1407_);
return v___x_1408_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___boxed(lean_object* v_00_u03c1_1409_, lean_object* v_s_1410_, lean_object* v_pat_1411_, lean_object* v_inst_1412_){
_start:
{
lean_object* v_res_1413_; 
v_res_1413_ = l_String_Slice_dropPrefix(v_00_u03c1_1409_, v_s_1410_, v_pat_1411_, v_inst_1412_);
lean_dec(v_pat_1411_);
return v_res_1413_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__0(lean_object* v_x_1414_, lean_object* v_x_1415_, lean_object* v_f_1416_, lean_object* v_c_1417_){
_start:
{
lean_object* v___x_1418_; 
v___x_1418_ = lean_apply_1(v_f_1416_, v_c_1417_);
return v___x_1418_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1(lean_object* v_s_1419_, lean_object* v_inst_1420_, lean_object* v_replacement_1421_, lean_object* v_x1_1422_, lean_object* v_x2_1423_, lean_object* v_x3_1424_){
_start:
{
if (lean_obj_tag(v_x1_1422_) == 0)
{
lean_object* v_startPos_1425_; lean_object* v_endPos_1426_; lean_object* v___x_1427_; lean_object* v_str_1428_; lean_object* v_startInclusive_1429_; lean_object* v_endExclusive_1430_; lean_object* v___x_1431_; lean_object* v___x_1432_; lean_object* v___x_1433_; 
lean_dec(v_replacement_1421_);
lean_dec_ref(v_inst_1420_);
v_startPos_1425_ = lean_ctor_get(v_x1_1422_, 0);
v_endPos_1426_ = lean_ctor_get(v_x1_1422_, 1);
v___x_1427_ = l_String_Slice_slice_x21(v_s_1419_, v_startPos_1425_, v_endPos_1426_);
v_str_1428_ = lean_ctor_get(v___x_1427_, 0);
lean_inc_ref(v_str_1428_);
v_startInclusive_1429_ = lean_ctor_get(v___x_1427_, 1);
lean_inc(v_startInclusive_1429_);
v_endExclusive_1430_ = lean_ctor_get(v___x_1427_, 2);
lean_inc(v_endExclusive_1430_);
lean_dec_ref(v___x_1427_);
v___x_1431_ = lean_string_utf8_extract_fast(v_str_1428_, v_startInclusive_1429_, v_endExclusive_1430_);
lean_dec(v_endExclusive_1430_);
lean_dec(v_startInclusive_1429_);
lean_dec_ref(v_str_1428_);
v___x_1432_ = lean_string_append(v_x3_1424_, v___x_1431_);
lean_dec_ref(v___x_1431_);
v___x_1433_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1433_, 0, v___x_1432_);
return v___x_1433_;
}
else
{
lean_object* v___x_1434_; lean_object* v_str_1435_; lean_object* v_startInclusive_1436_; lean_object* v_endExclusive_1437_; lean_object* v___x_1438_; lean_object* v___x_1439_; lean_object* v___x_1440_; 
lean_dec_ref(v_s_1419_);
v___x_1434_ = lean_apply_1(v_inst_1420_, v_replacement_1421_);
v_str_1435_ = lean_ctor_get(v___x_1434_, 0);
lean_inc_ref(v_str_1435_);
v_startInclusive_1436_ = lean_ctor_get(v___x_1434_, 1);
lean_inc(v_startInclusive_1436_);
v_endExclusive_1437_ = lean_ctor_get(v___x_1434_, 2);
lean_inc(v_endExclusive_1437_);
lean_dec_ref(v___x_1434_);
v___x_1438_ = lean_string_utf8_extract_fast(v_str_1435_, v_startInclusive_1436_, v_endExclusive_1437_);
lean_dec(v_endExclusive_1437_);
lean_dec(v_startInclusive_1436_);
lean_dec_ref(v_str_1435_);
v___x_1439_ = lean_string_append(v_x3_1424_, v___x_1438_);
lean_dec_ref(v___x_1438_);
v___x_1440_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1440_, 0, v___x_1439_);
return v___x_1440_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1___boxed(lean_object* v_s_1441_, lean_object* v_inst_1442_, lean_object* v_replacement_1443_, lean_object* v_x1_1444_, lean_object* v_x2_1445_, lean_object* v_x3_1446_){
_start:
{
lean_object* v_res_1447_; 
v_res_1447_ = l_String_Slice_replace___redArg___lam__1(v_s_1441_, v_inst_1442_, v_replacement_1443_, v_x1_1444_, v_x2_1445_, v_x3_1446_);
lean_dec_ref(v_x1_1444_);
return v_res_1447_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg(lean_object* v_inst_1450_, lean_object* v_inst_1451_, lean_object* v_s_1452_, lean_object* v_inst_1453_, lean_object* v_replacement_1454_){
_start:
{
lean_object* v___f_1455_; lean_object* v___f_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v___f_1455_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1452_, 2);
v___f_1456_ = lean_alloc_closure((void*)(l_String_Slice_replace___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1456_, 0, v_s_1452_);
lean_closure_set(v___f_1456_, 1, v_inst_1451_);
lean_closure_set(v___f_1456_, 2, v_replacement_1454_);
v___x_1457_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
v___x_1458_ = lean_apply_1(v_inst_1453_, v_s_1452_);
v___x_1459_ = lean_apply_7(v_inst_1450_, v_s_1452_, v___f_1455_, lean_box(0), lean_box(0), v___x_1458_, v___x_1457_, v___f_1456_);
return v___x_1459_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace(lean_object* v_00_u03c1_1460_, lean_object* v_00_u03c3_1461_, lean_object* v_inst_1462_, lean_object* v_inst_1463_, lean_object* v_00_u03b1_1464_, lean_object* v_inst_1465_, lean_object* v_s_1466_, lean_object* v_pattern_1467_, lean_object* v_inst_1468_, lean_object* v_replacement_1469_){
_start:
{
lean_object* v___x_1470_; 
v___x_1470_ = l_String_Slice_replace___redArg(v_inst_1463_, v_inst_1465_, v_s_1466_, v_inst_1468_, v_replacement_1469_);
return v___x_1470_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___boxed(lean_object* v_00_u03c1_1471_, lean_object* v_00_u03c3_1472_, lean_object* v_inst_1473_, lean_object* v_inst_1474_, lean_object* v_00_u03b1_1475_, lean_object* v_inst_1476_, lean_object* v_s_1477_, lean_object* v_pattern_1478_, lean_object* v_inst_1479_, lean_object* v_replacement_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_String_Slice_replace(v_00_u03c1_1471_, v_00_u03c3_1472_, v_inst_1473_, v_inst_1474_, v_00_u03b1_1475_, v_inst_1476_, v_s_1477_, v_pattern_1478_, v_inst_1479_, v_replacement_1480_);
lean_dec(v_pattern_1478_);
lean_dec(v_inst_1473_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object* v_s_1482_, lean_object* v_n_1483_){
_start:
{
lean_object* v_str_1484_; lean_object* v_startInclusive_1485_; lean_object* v_endExclusive_1486_; lean_object* v___x_1487_; lean_object* v___x_1488_; lean_object* v___x_1490_; uint8_t v_isShared_1491_; uint8_t v_isSharedCheck_1496_; 
v_str_1484_ = lean_ctor_get(v_s_1482_, 0);
lean_inc_ref(v_str_1484_);
v_startInclusive_1485_ = lean_ctor_get(v_s_1482_, 1);
lean_inc(v_startInclusive_1485_);
v_endExclusive_1486_ = lean_ctor_get(v_s_1482_, 2);
lean_inc(v_endExclusive_1486_);
v___x_1487_ = lean_unsigned_to_nat(0u);
v___x_1488_ = l_String_Slice_Pos_nextn(v_s_1482_, v___x_1487_, v_n_1483_);
v_isSharedCheck_1496_ = !lean_is_exclusive(v_s_1482_);
if (v_isSharedCheck_1496_ == 0)
{
lean_object* v_unused_1497_; lean_object* v_unused_1498_; lean_object* v_unused_1499_; 
v_unused_1497_ = lean_ctor_get(v_s_1482_, 2);
lean_dec(v_unused_1497_);
v_unused_1498_ = lean_ctor_get(v_s_1482_, 1);
lean_dec(v_unused_1498_);
v_unused_1499_ = lean_ctor_get(v_s_1482_, 0);
lean_dec(v_unused_1499_);
v___x_1490_ = v_s_1482_;
v_isShared_1491_ = v_isSharedCheck_1496_;
goto v_resetjp_1489_;
}
else
{
lean_dec(v_s_1482_);
v___x_1490_ = lean_box(0);
v_isShared_1491_ = v_isSharedCheck_1496_;
goto v_resetjp_1489_;
}
v_resetjp_1489_:
{
lean_object* v___x_1492_; lean_object* v___x_1494_; 
v___x_1492_ = lean_nat_add(v_startInclusive_1485_, v___x_1488_);
lean_dec(v___x_1488_);
lean_dec(v_startInclusive_1485_);
if (v_isShared_1491_ == 0)
{
lean_ctor_set(v___x_1490_, 1, v___x_1492_);
v___x_1494_ = v___x_1490_;
goto v_reusejp_1493_;
}
else
{
lean_object* v_reuseFailAlloc_1495_; 
v_reuseFailAlloc_1495_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1495_, 0, v_str_1484_);
lean_ctor_set(v_reuseFailAlloc_1495_, 1, v___x_1492_);
lean_ctor_set(v_reuseFailAlloc_1495_, 2, v_endExclusive_1486_);
v___x_1494_ = v_reuseFailAlloc_1495_;
goto v_reusejp_1493_;
}
v_reusejp_1493_:
{
return v___x_1494_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object* v_s_1500_, lean_object* v_pos_1501_, lean_object* v_inst_1502_){
_start:
{
lean_object* v_str_1503_; lean_object* v_startInclusive_1504_; lean_object* v_endExclusive_1505_; lean_object* v_skipPrefix_x3f_1506_; lean_object* v___x_1507_; lean_object* v___x_1508_; lean_object* v___x_1509_; 
v_str_1503_ = lean_ctor_get(v_s_1500_, 0);
v_startInclusive_1504_ = lean_ctor_get(v_s_1500_, 1);
v_endExclusive_1505_ = lean_ctor_get(v_s_1500_, 2);
v_skipPrefix_x3f_1506_ = lean_ctor_get(v_inst_1502_, 0);
v___x_1507_ = lean_nat_add(v_startInclusive_1504_, v_pos_1501_);
lean_inc(v_endExclusive_1505_);
lean_inc_ref(v_str_1503_);
v___x_1508_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1508_, 0, v_str_1503_);
lean_ctor_set(v___x_1508_, 1, v___x_1507_);
lean_ctor_set(v___x_1508_, 2, v_endExclusive_1505_);
lean_inc_ref(v_skipPrefix_x3f_1506_);
v___x_1509_ = lean_apply_1(v_skipPrefix_x3f_1506_, v___x_1508_);
if (lean_obj_tag(v___x_1509_) == 0)
{
lean_dec_ref(v_inst_1502_);
return v_pos_1501_;
}
else
{
lean_object* v_val_1510_; lean_object* v___x_1511_; lean_object* v___x_1512_; lean_object* v___x_1513_; uint8_t v___x_1514_; 
v_val_1510_ = lean_ctor_get(v___x_1509_, 0);
lean_inc(v_val_1510_);
lean_dec_ref_known(v___x_1509_, 1);
v___x_1511_ = lean_nat_add(v_pos_1501_, v_val_1510_);
lean_dec(v_val_1510_);
v___x_1512_ = lean_unsigned_to_nat(1u);
v___x_1513_ = lean_nat_add(v_pos_1501_, v___x_1512_);
v___x_1514_ = lean_nat_dec_le(v___x_1513_, v___x_1511_);
lean_dec(v___x_1513_);
if (v___x_1514_ == 0)
{
lean_dec(v___x_1511_);
lean_dec_ref(v_inst_1502_);
return v_pos_1501_;
}
else
{
lean_dec(v_pos_1501_);
v_pos_1501_ = v___x_1511_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg___boxed(lean_object* v_s_1516_, lean_object* v_pos_1517_, lean_object* v_inst_1518_){
_start:
{
lean_object* v_res_1519_; 
v_res_1519_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1516_, v_pos_1517_, v_inst_1518_);
lean_dec_ref(v_s_1516_);
return v_res_1519_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile(lean_object* v_00_u03c1_1520_, lean_object* v_s_1521_, lean_object* v_pos_1522_, lean_object* v_pat_1523_, lean_object* v_inst_1524_){
_start:
{
lean_object* v___x_1525_; 
v___x_1525_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1521_, v_pos_1522_, v_inst_1524_);
return v___x_1525_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___boxed(lean_object* v_00_u03c1_1526_, lean_object* v_s_1527_, lean_object* v_pos_1528_, lean_object* v_pat_1529_, lean_object* v_inst_1530_){
_start:
{
lean_object* v_res_1531_; 
v_res_1531_ = l_String_Slice_Pos_skipWhile(v_00_u03c1_1526_, v_s_1527_, v_pos_1528_, v_pat_1529_, v_inst_1530_);
lean_dec(v_pat_1529_);
lean_dec_ref(v_s_1527_);
return v_res_1531_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object* v_x_1532_, lean_object* v_h__1_1533_, lean_object* v_h__2_1534_){
_start:
{
if (lean_obj_tag(v_x_1532_) == 0)
{
lean_object* v___x_1535_; lean_object* v___x_1536_; 
lean_dec(v_h__1_1533_);
v___x_1535_ = lean_box(0);
v___x_1536_ = lean_apply_1(v_h__2_1534_, v___x_1535_);
return v___x_1536_;
}
else
{
lean_object* v_val_1537_; lean_object* v___x_1538_; 
lean_dec(v_h__2_1534_);
v_val_1537_ = lean_ctor_get(v_x_1532_, 0);
lean_inc(v_val_1537_);
lean_dec_ref_known(v_x_1532_, 1);
v___x_1538_ = lean_apply_1(v_h__1_1533_, v_val_1537_);
return v___x_1538_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object* v_s_1539_, lean_object* v_motive_1540_, lean_object* v_x_1541_, lean_object* v_h__1_1542_, lean_object* v_h__2_1543_){
_start:
{
if (lean_obj_tag(v_x_1541_) == 0)
{
lean_object* v___x_1544_; lean_object* v___x_1545_; 
lean_dec(v_h__1_1542_);
v___x_1544_ = lean_box(0);
v___x_1545_ = lean_apply_1(v_h__2_1543_, v___x_1544_);
return v___x_1545_;
}
else
{
lean_object* v_val_1546_; lean_object* v___x_1547_; 
lean_dec(v_h__2_1543_);
v_val_1546_ = lean_ctor_get(v_x_1541_, 0);
lean_inc(v_val_1546_);
lean_dec_ref_known(v_x_1541_, 1);
v___x_1547_ = lean_apply_1(v_h__1_1542_, v_val_1546_);
return v___x_1547_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object* v_s_1548_, lean_object* v_motive_1549_, lean_object* v_x_1550_, lean_object* v_h__1_1551_, lean_object* v_h__2_1552_){
_start:
{
lean_object* v_res_1553_; 
v_res_1553_ = l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_1548_, v_motive_1549_, v_x_1550_, v_h__1_1551_, v_h__2_1552_);
lean_dec_ref(v_s_1548_);
return v_res_1553_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg(lean_object* v_s_1554_, lean_object* v_inst_1555_){
_start:
{
lean_object* v___x_1556_; lean_object* v___x_1557_; 
v___x_1556_ = lean_unsigned_to_nat(0u);
v___x_1557_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1554_, v___x_1556_, v_inst_1555_);
return v___x_1557_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg___boxed(lean_object* v_s_1558_, lean_object* v_inst_1559_){
_start:
{
lean_object* v_res_1560_; 
v_res_1560_ = l_String_Slice_skipPrefixWhile___redArg(v_s_1558_, v_inst_1559_);
lean_dec_ref(v_s_1558_);
return v_res_1560_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile(lean_object* v_00_u03c1_1561_, lean_object* v_s_1562_, lean_object* v_pat_1563_, lean_object* v_inst_1564_){
_start:
{
lean_object* v___x_1565_; lean_object* v___x_1566_; 
v___x_1565_ = lean_unsigned_to_nat(0u);
v___x_1566_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1562_, v___x_1565_, v_inst_1564_);
return v___x_1566_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___boxed(lean_object* v_00_u03c1_1567_, lean_object* v_s_1568_, lean_object* v_pat_1569_, lean_object* v_inst_1570_){
_start:
{
lean_object* v_res_1571_; 
v_res_1571_ = l_String_Slice_skipPrefixWhile(v_00_u03c1_1567_, v_s_1568_, v_pat_1569_, v_inst_1570_);
lean_dec(v_pat_1569_);
lean_dec_ref(v_s_1568_);
return v_res_1571_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg(lean_object* v_s_1572_, lean_object* v_inst_1573_){
_start:
{
lean_object* v_str_1574_; lean_object* v_startInclusive_1575_; lean_object* v_endExclusive_1576_; lean_object* v___x_1577_; lean_object* v___x_1578_; lean_object* v___x_1580_; uint8_t v_isShared_1581_; uint8_t v_isSharedCheck_1586_; 
v_str_1574_ = lean_ctor_get(v_s_1572_, 0);
lean_inc_ref(v_str_1574_);
v_startInclusive_1575_ = lean_ctor_get(v_s_1572_, 1);
lean_inc(v_startInclusive_1575_);
v_endExclusive_1576_ = lean_ctor_get(v_s_1572_, 2);
lean_inc(v_endExclusive_1576_);
v___x_1577_ = lean_unsigned_to_nat(0u);
v___x_1578_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1572_, v___x_1577_, v_inst_1573_);
v_isSharedCheck_1586_ = !lean_is_exclusive(v_s_1572_);
if (v_isSharedCheck_1586_ == 0)
{
lean_object* v_unused_1587_; lean_object* v_unused_1588_; lean_object* v_unused_1589_; 
v_unused_1587_ = lean_ctor_get(v_s_1572_, 2);
lean_dec(v_unused_1587_);
v_unused_1588_ = lean_ctor_get(v_s_1572_, 1);
lean_dec(v_unused_1588_);
v_unused_1589_ = lean_ctor_get(v_s_1572_, 0);
lean_dec(v_unused_1589_);
v___x_1580_ = v_s_1572_;
v_isShared_1581_ = v_isSharedCheck_1586_;
goto v_resetjp_1579_;
}
else
{
lean_dec(v_s_1572_);
v___x_1580_ = lean_box(0);
v_isShared_1581_ = v_isSharedCheck_1586_;
goto v_resetjp_1579_;
}
v_resetjp_1579_:
{
lean_object* v___x_1582_; lean_object* v___x_1584_; 
v___x_1582_ = lean_nat_add(v_startInclusive_1575_, v___x_1578_);
lean_dec(v___x_1578_);
lean_dec(v_startInclusive_1575_);
if (v_isShared_1581_ == 0)
{
lean_ctor_set(v___x_1580_, 1, v___x_1582_);
v___x_1584_ = v___x_1580_;
goto v_reusejp_1583_;
}
else
{
lean_object* v_reuseFailAlloc_1585_; 
v_reuseFailAlloc_1585_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1585_, 0, v_str_1574_);
lean_ctor_set(v_reuseFailAlloc_1585_, 1, v___x_1582_);
lean_ctor_set(v_reuseFailAlloc_1585_, 2, v_endExclusive_1576_);
v___x_1584_ = v_reuseFailAlloc_1585_;
goto v_reusejp_1583_;
}
v_reusejp_1583_:
{
return v___x_1584_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile(lean_object* v_00_u03c1_1590_, lean_object* v_s_1591_, lean_object* v_pat_1592_, lean_object* v_inst_1593_){
_start:
{
lean_object* v_str_1594_; lean_object* v_startInclusive_1595_; lean_object* v_endExclusive_1596_; lean_object* v___x_1597_; lean_object* v___x_1598_; lean_object* v___x_1600_; uint8_t v_isShared_1601_; uint8_t v_isSharedCheck_1606_; 
v_str_1594_ = lean_ctor_get(v_s_1591_, 0);
lean_inc_ref(v_str_1594_);
v_startInclusive_1595_ = lean_ctor_get(v_s_1591_, 1);
lean_inc(v_startInclusive_1595_);
v_endExclusive_1596_ = lean_ctor_get(v_s_1591_, 2);
lean_inc(v_endExclusive_1596_);
v___x_1597_ = lean_unsigned_to_nat(0u);
v___x_1598_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1591_, v___x_1597_, v_inst_1593_);
v_isSharedCheck_1606_ = !lean_is_exclusive(v_s_1591_);
if (v_isSharedCheck_1606_ == 0)
{
lean_object* v_unused_1607_; lean_object* v_unused_1608_; lean_object* v_unused_1609_; 
v_unused_1607_ = lean_ctor_get(v_s_1591_, 2);
lean_dec(v_unused_1607_);
v_unused_1608_ = lean_ctor_get(v_s_1591_, 1);
lean_dec(v_unused_1608_);
v_unused_1609_ = lean_ctor_get(v_s_1591_, 0);
lean_dec(v_unused_1609_);
v___x_1600_ = v_s_1591_;
v_isShared_1601_ = v_isSharedCheck_1606_;
goto v_resetjp_1599_;
}
else
{
lean_dec(v_s_1591_);
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
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___boxed(lean_object* v_00_u03c1_1610_, lean_object* v_s_1611_, lean_object* v_pat_1612_, lean_object* v_inst_1613_){
_start:
{
lean_object* v_res_1614_; 
v_res_1614_ = l_String_Slice_dropWhile(v_00_u03c1_1610_, v_s_1611_, v_pat_1612_, v_inst_1613_);
lean_dec(v_pat_1612_);
return v_res_1614_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiStart___closed__1(void){
_start:
{
lean_object* v___x_1616_; lean_object* v___x_1617_; 
v___x_1616_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_1617_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1616_);
return v___x_1617_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart(lean_object* v_s_1618_){
_start:
{
lean_object* v___x_1619_; lean_object* v_str_1620_; lean_object* v_startInclusive_1621_; lean_object* v_endExclusive_1622_; lean_object* v___x_1623_; lean_object* v___x_1624_; lean_object* v___x_1626_; uint8_t v_isShared_1627_; uint8_t v_isSharedCheck_1632_; 
v___x_1619_ = lean_obj_once(&l_String_Slice_trimAsciiStart___closed__1, &l_String_Slice_trimAsciiStart___closed__1_once, _init_l_String_Slice_trimAsciiStart___closed__1);
v_str_1620_ = lean_ctor_get(v_s_1618_, 0);
lean_inc_ref(v_str_1620_);
v_startInclusive_1621_ = lean_ctor_get(v_s_1618_, 1);
lean_inc(v_startInclusive_1621_);
v_endExclusive_1622_ = lean_ctor_get(v_s_1618_, 2);
lean_inc(v_endExclusive_1622_);
v___x_1623_ = lean_unsigned_to_nat(0u);
v___x_1624_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1618_, v___x_1623_, v___x_1619_);
v_isSharedCheck_1632_ = !lean_is_exclusive(v_s_1618_);
if (v_isSharedCheck_1632_ == 0)
{
lean_object* v_unused_1633_; lean_object* v_unused_1634_; lean_object* v_unused_1635_; 
v_unused_1633_ = lean_ctor_get(v_s_1618_, 2);
lean_dec(v_unused_1633_);
v_unused_1634_ = lean_ctor_get(v_s_1618_, 1);
lean_dec(v_unused_1634_);
v_unused_1635_ = lean_ctor_get(v_s_1618_, 0);
lean_dec(v_unused_1635_);
v___x_1626_ = v_s_1618_;
v_isShared_1627_ = v_isSharedCheck_1632_;
goto v_resetjp_1625_;
}
else
{
lean_dec(v_s_1618_);
v___x_1626_ = lean_box(0);
v_isShared_1627_ = v_isSharedCheck_1632_;
goto v_resetjp_1625_;
}
v_resetjp_1625_:
{
lean_object* v___x_1628_; lean_object* v___x_1630_; 
v___x_1628_ = lean_nat_add(v_startInclusive_1621_, v___x_1624_);
lean_dec(v___x_1624_);
lean_dec(v_startInclusive_1621_);
if (v_isShared_1627_ == 0)
{
lean_ctor_set(v___x_1626_, 1, v___x_1628_);
v___x_1630_ = v___x_1626_;
goto v_reusejp_1629_;
}
else
{
lean_object* v_reuseFailAlloc_1631_; 
v_reuseFailAlloc_1631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1631_, 0, v_str_1620_);
lean_ctor_set(v_reuseFailAlloc_1631_, 1, v___x_1628_);
lean_ctor_set(v_reuseFailAlloc_1631_, 2, v_endExclusive_1622_);
v___x_1630_ = v_reuseFailAlloc_1631_;
goto v_reusejp_1629_;
}
v_reusejp_1629_:
{
return v___x_1630_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object* v_s_1636_, lean_object* v_n_1637_){
_start:
{
lean_object* v_str_1638_; lean_object* v_startInclusive_1639_; lean_object* v___x_1640_; lean_object* v___x_1641_; lean_object* v___x_1643_; uint8_t v_isShared_1644_; uint8_t v_isSharedCheck_1649_; 
v_str_1638_ = lean_ctor_get(v_s_1636_, 0);
lean_inc_ref(v_str_1638_);
v_startInclusive_1639_ = lean_ctor_get(v_s_1636_, 1);
lean_inc(v_startInclusive_1639_);
v___x_1640_ = lean_unsigned_to_nat(0u);
v___x_1641_ = l_String_Slice_Pos_nextn(v_s_1636_, v___x_1640_, v_n_1637_);
v_isSharedCheck_1649_ = !lean_is_exclusive(v_s_1636_);
if (v_isSharedCheck_1649_ == 0)
{
lean_object* v_unused_1650_; lean_object* v_unused_1651_; lean_object* v_unused_1652_; 
v_unused_1650_ = lean_ctor_get(v_s_1636_, 2);
lean_dec(v_unused_1650_);
v_unused_1651_ = lean_ctor_get(v_s_1636_, 1);
lean_dec(v_unused_1651_);
v_unused_1652_ = lean_ctor_get(v_s_1636_, 0);
lean_dec(v_unused_1652_);
v___x_1643_ = v_s_1636_;
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
else
{
lean_dec(v_s_1636_);
v___x_1643_ = lean_box(0);
v_isShared_1644_ = v_isSharedCheck_1649_;
goto v_resetjp_1642_;
}
v_resetjp_1642_:
{
lean_object* v___x_1645_; lean_object* v___x_1647_; 
v___x_1645_ = lean_nat_add(v_startInclusive_1639_, v___x_1641_);
lean_dec(v___x_1641_);
if (v_isShared_1644_ == 0)
{
lean_ctor_set(v___x_1643_, 2, v___x_1645_);
v___x_1647_ = v___x_1643_;
goto v_reusejp_1646_;
}
else
{
lean_object* v_reuseFailAlloc_1648_; 
v_reuseFailAlloc_1648_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1648_, 0, v_str_1638_);
lean_ctor_set(v_reuseFailAlloc_1648_, 1, v_startInclusive_1639_);
lean_ctor_set(v_reuseFailAlloc_1648_, 2, v___x_1645_);
v___x_1647_ = v_reuseFailAlloc_1648_;
goto v_reusejp_1646_;
}
v_reusejp_1646_:
{
return v___x_1647_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___redArg(lean_object* v_s_1653_, lean_object* v_inst_1654_){
_start:
{
lean_object* v_str_1655_; lean_object* v_startInclusive_1656_; lean_object* v___x_1657_; lean_object* v___x_1658_; lean_object* v___x_1660_; uint8_t v_isShared_1661_; uint8_t v_isSharedCheck_1666_; 
v_str_1655_ = lean_ctor_get(v_s_1653_, 0);
lean_inc_ref(v_str_1655_);
v_startInclusive_1656_ = lean_ctor_get(v_s_1653_, 1);
lean_inc(v_startInclusive_1656_);
v___x_1657_ = lean_unsigned_to_nat(0u);
v___x_1658_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1653_, v___x_1657_, v_inst_1654_);
v_isSharedCheck_1666_ = !lean_is_exclusive(v_s_1653_);
if (v_isSharedCheck_1666_ == 0)
{
lean_object* v_unused_1667_; lean_object* v_unused_1668_; lean_object* v_unused_1669_; 
v_unused_1667_ = lean_ctor_get(v_s_1653_, 2);
lean_dec(v_unused_1667_);
v_unused_1668_ = lean_ctor_get(v_s_1653_, 1);
lean_dec(v_unused_1668_);
v_unused_1669_ = lean_ctor_get(v_s_1653_, 0);
lean_dec(v_unused_1669_);
v___x_1660_ = v_s_1653_;
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
else
{
lean_dec(v_s_1653_);
v___x_1660_ = lean_box(0);
v_isShared_1661_ = v_isSharedCheck_1666_;
goto v_resetjp_1659_;
}
v_resetjp_1659_:
{
lean_object* v___x_1662_; lean_object* v___x_1664_; 
v___x_1662_ = lean_nat_add(v_startInclusive_1656_, v___x_1658_);
lean_dec(v___x_1658_);
if (v_isShared_1661_ == 0)
{
lean_ctor_set(v___x_1660_, 2, v___x_1662_);
v___x_1664_ = v___x_1660_;
goto v_reusejp_1663_;
}
else
{
lean_object* v_reuseFailAlloc_1665_; 
v_reuseFailAlloc_1665_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1665_, 0, v_str_1655_);
lean_ctor_set(v_reuseFailAlloc_1665_, 1, v_startInclusive_1656_);
lean_ctor_set(v_reuseFailAlloc_1665_, 2, v___x_1662_);
v___x_1664_ = v_reuseFailAlloc_1665_;
goto v_reusejp_1663_;
}
v_reusejp_1663_:
{
return v___x_1664_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile(lean_object* v_00_u03c1_1670_, lean_object* v_s_1671_, lean_object* v_pat_1672_, lean_object* v_inst_1673_){
_start:
{
lean_object* v_str_1674_; lean_object* v_startInclusive_1675_; lean_object* v___x_1676_; lean_object* v___x_1677_; lean_object* v___x_1679_; uint8_t v_isShared_1680_; uint8_t v_isSharedCheck_1685_; 
v_str_1674_ = lean_ctor_get(v_s_1671_, 0);
lean_inc_ref(v_str_1674_);
v_startInclusive_1675_ = lean_ctor_get(v_s_1671_, 1);
lean_inc(v_startInclusive_1675_);
v___x_1676_ = lean_unsigned_to_nat(0u);
v___x_1677_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1671_, v___x_1676_, v_inst_1673_);
v_isSharedCheck_1685_ = !lean_is_exclusive(v_s_1671_);
if (v_isSharedCheck_1685_ == 0)
{
lean_object* v_unused_1686_; lean_object* v_unused_1687_; lean_object* v_unused_1688_; 
v_unused_1686_ = lean_ctor_get(v_s_1671_, 2);
lean_dec(v_unused_1686_);
v_unused_1687_ = lean_ctor_get(v_s_1671_, 1);
lean_dec(v_unused_1687_);
v_unused_1688_ = lean_ctor_get(v_s_1671_, 0);
lean_dec(v_unused_1688_);
v___x_1679_ = v_s_1671_;
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
else
{
lean_dec(v_s_1671_);
v___x_1679_ = lean_box(0);
v_isShared_1680_ = v_isSharedCheck_1685_;
goto v_resetjp_1678_;
}
v_resetjp_1678_:
{
lean_object* v___x_1681_; lean_object* v___x_1683_; 
v___x_1681_ = lean_nat_add(v_startInclusive_1675_, v___x_1677_);
lean_dec(v___x_1677_);
if (v_isShared_1680_ == 0)
{
lean_ctor_set(v___x_1679_, 2, v___x_1681_);
v___x_1683_ = v___x_1679_;
goto v_reusejp_1682_;
}
else
{
lean_object* v_reuseFailAlloc_1684_; 
v_reuseFailAlloc_1684_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1684_, 0, v_str_1674_);
lean_ctor_set(v_reuseFailAlloc_1684_, 1, v_startInclusive_1675_);
lean_ctor_set(v_reuseFailAlloc_1684_, 2, v___x_1681_);
v___x_1683_ = v_reuseFailAlloc_1684_;
goto v_reusejp_1682_;
}
v_reusejp_1682_:
{
return v___x_1683_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___boxed(lean_object* v_00_u03c1_1689_, lean_object* v_s_1690_, lean_object* v_pat_1691_, lean_object* v_inst_1692_){
_start:
{
lean_object* v_res_1693_; 
v_res_1693_ = l_String_Slice_takeWhile(v_00_u03c1_1689_, v_s_1690_, v_pat_1691_, v_inst_1692_);
lean_dec(v_pat_1691_);
return v_res_1693_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1(lean_object* v___x_1694_, lean_object* v_x1_1695_, lean_object* v_x2_1696_, lean_object* v_x3_1697_){
_start:
{
if (lean_obj_tag(v_x1_1695_) == 0)
{
lean_object* v___x_1698_; 
v___x_1698_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1698_, 0, v___x_1694_);
return v___x_1698_;
}
else
{
lean_object* v_startPos_1699_; lean_object* v___x_1700_; lean_object* v___x_1701_; 
lean_dec(v___x_1694_);
v_startPos_1699_ = lean_ctor_get(v_x1_1695_, 0);
lean_inc(v_startPos_1699_);
v___x_1700_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1700_, 0, v_startPos_1699_);
v___x_1701_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1701_, 0, v___x_1700_);
return v___x_1701_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1___boxed(lean_object* v___x_1702_, lean_object* v_x1_1703_, lean_object* v_x2_1704_, lean_object* v_x3_1705_){
_start:
{
lean_object* v_res_1706_; 
v_res_1706_ = l_String_Slice_find_x3f___redArg___lam__1(v___x_1702_, v_x1_1703_, v_x2_1704_, v_x3_1705_);
lean_dec(v_x3_1705_);
lean_dec_ref(v_x1_1703_);
return v_res_1706_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg(lean_object* v_inst_1709_, lean_object* v_s_1710_, lean_object* v_inst_1711_){
_start:
{
lean_object* v___f_1712_; lean_object* v_searcher_1713_; lean_object* v___x_1714_; lean_object* v___f_1715_; lean_object* v___x_1716_; 
v___f_1712_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1710_);
v_searcher_1713_ = lean_apply_1(v_inst_1711_, v_s_1710_);
v___x_1714_ = lean_box(0);
v___f_1715_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1716_ = lean_apply_7(v_inst_1709_, v_s_1710_, v___f_1712_, lean_box(0), lean_box(0), v_searcher_1713_, v___x_1714_, v___f_1715_);
return v___x_1716_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f(lean_object* v_00_u03c1_1717_, lean_object* v_00_u03c3_1718_, lean_object* v_inst_1719_, lean_object* v_inst_1720_, lean_object* v_s_1721_, lean_object* v_pat_1722_, lean_object* v_inst_1723_){
_start:
{
lean_object* v___f_1724_; lean_object* v_searcher_1725_; lean_object* v___x_1726_; lean_object* v___f_1727_; lean_object* v___x_1728_; 
v___f_1724_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1721_);
v_searcher_1725_ = lean_apply_1(v_inst_1723_, v_s_1721_);
v___x_1726_ = lean_box(0);
v___f_1727_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1728_ = lean_apply_7(v_inst_1720_, v_s_1721_, v___f_1724_, lean_box(0), lean_box(0), v_searcher_1725_, v___x_1726_, v___f_1727_);
return v___x_1728_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___boxed(lean_object* v_00_u03c1_1729_, lean_object* v_00_u03c3_1730_, lean_object* v_inst_1731_, lean_object* v_inst_1732_, lean_object* v_s_1733_, lean_object* v_pat_1734_, lean_object* v_inst_1735_){
_start:
{
lean_object* v_res_1736_; 
v_res_1736_ = l_String_Slice_find_x3f(v_00_u03c1_1729_, v_00_u03c3_1730_, v_inst_1731_, v_inst_1732_, v_s_1733_, v_pat_1734_, v_inst_1735_);
lean_dec(v_pat_1734_);
lean_dec(v_inst_1731_);
return v_res_1736_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___redArg(lean_object* v_inst_1737_, lean_object* v_s_1738_, lean_object* v_inst_1739_){
_start:
{
lean_object* v___f_1740_; lean_object* v_searcher_1741_; lean_object* v___x_1742_; lean_object* v___f_1743_; lean_object* v___x_1744_; 
v___f_1740_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1738_, 2);
v_searcher_1741_ = lean_apply_1(v_inst_1739_, v_s_1738_);
v___x_1742_ = lean_box(0);
v___f_1743_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1744_ = lean_apply_7(v_inst_1737_, v_s_1738_, v___f_1740_, lean_box(0), lean_box(0), v_searcher_1741_, v___x_1742_, v___f_1743_);
if (lean_obj_tag(v___x_1744_) == 0)
{
lean_object* v_startInclusive_1745_; lean_object* v_endExclusive_1746_; lean_object* v___x_1747_; 
v_startInclusive_1745_ = lean_ctor_get(v_s_1738_, 1);
lean_inc(v_startInclusive_1745_);
v_endExclusive_1746_ = lean_ctor_get(v_s_1738_, 2);
lean_inc(v_endExclusive_1746_);
lean_dec_ref(v_s_1738_);
v___x_1747_ = lean_nat_sub(v_endExclusive_1746_, v_startInclusive_1745_);
lean_dec(v_startInclusive_1745_);
lean_dec(v_endExclusive_1746_);
return v___x_1747_;
}
else
{
lean_object* v_val_1748_; 
lean_dec_ref(v_s_1738_);
v_val_1748_ = lean_ctor_get(v___x_1744_, 0);
lean_inc(v_val_1748_);
lean_dec_ref_known(v___x_1744_, 1);
return v_val_1748_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find(lean_object* v_00_u03c1_1749_, lean_object* v_00_u03c3_1750_, lean_object* v_inst_1751_, lean_object* v_inst_1752_, lean_object* v_s_1753_, lean_object* v_pat_1754_, lean_object* v_inst_1755_){
_start:
{
lean_object* v___f_1756_; lean_object* v_searcher_1757_; lean_object* v___x_1758_; lean_object* v___f_1759_; lean_object* v___x_1760_; 
v___f_1756_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1753_, 2);
v_searcher_1757_ = lean_apply_1(v_inst_1755_, v_s_1753_);
v___x_1758_ = lean_box(0);
v___f_1759_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1760_ = lean_apply_7(v_inst_1752_, v_s_1753_, v___f_1756_, lean_box(0), lean_box(0), v_searcher_1757_, v___x_1758_, v___f_1759_);
if (lean_obj_tag(v___x_1760_) == 0)
{
lean_object* v_startInclusive_1761_; lean_object* v_endExclusive_1762_; lean_object* v___x_1763_; 
v_startInclusive_1761_ = lean_ctor_get(v_s_1753_, 1);
lean_inc(v_startInclusive_1761_);
v_endExclusive_1762_ = lean_ctor_get(v_s_1753_, 2);
lean_inc(v_endExclusive_1762_);
lean_dec_ref(v_s_1753_);
v___x_1763_ = lean_nat_sub(v_endExclusive_1762_, v_startInclusive_1761_);
lean_dec(v_startInclusive_1761_);
lean_dec(v_endExclusive_1762_);
return v___x_1763_;
}
else
{
lean_object* v_val_1764_; 
lean_dec_ref(v_s_1753_);
v_val_1764_ = lean_ctor_get(v___x_1760_, 0);
lean_inc(v_val_1764_);
lean_dec_ref_known(v___x_1760_, 1);
return v_val_1764_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___boxed(lean_object* v_00_u03c1_1765_, lean_object* v_00_u03c3_1766_, lean_object* v_inst_1767_, lean_object* v_inst_1768_, lean_object* v_s_1769_, lean_object* v_pat_1770_, lean_object* v_inst_1771_){
_start:
{
lean_object* v_res_1772_; 
v_res_1772_ = l_String_Slice_find(v_00_u03c1_1765_, v_00_u03c3_1766_, v_inst_1767_, v_inst_1768_, v_s_1769_, v_pat_1770_, v_inst_1771_);
lean_dec(v_pat_1770_);
lean_dec(v_inst_1767_);
return v_res_1772_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1(uint8_t v___x_1776_, lean_object* v_x1_1777_, lean_object* v_x2_1778_, uint8_t v_x3_1779_){
_start:
{
if (lean_obj_tag(v_x1_1777_) == 1)
{
lean_object* v___x_1780_; 
v___x_1780_ = ((lean_object*)(l_String_Slice_contains___redArg___lam__1___closed__0));
return v___x_1780_;
}
else
{
lean_object* v___x_1781_; lean_object* v___x_1782_; 
v___x_1781_ = lean_box(v___x_1776_);
v___x_1782_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1782_, 0, v___x_1781_);
return v___x_1782_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1___boxed(lean_object* v___x_1783_, lean_object* v_x1_1784_, lean_object* v_x2_1785_, lean_object* v_x3_1786_){
_start:
{
uint8_t v___x_82__boxed_1787_; uint8_t v_x3_85__boxed_1788_; lean_object* v_res_1789_; 
v___x_82__boxed_1787_ = lean_unbox(v___x_1783_);
v_x3_85__boxed_1788_ = lean_unbox(v_x3_1786_);
v_res_1789_ = l_String_Slice_contains___redArg___lam__1(v___x_82__boxed_1787_, v_x1_1784_, v_x2_1785_, v_x3_85__boxed_1788_);
lean_dec_ref(v_x1_1784_);
return v_res_1789_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains___redArg(lean_object* v_inst_1793_, lean_object* v_s_1794_, lean_object* v_inst_1795_){
_start:
{
lean_object* v___f_1796_; lean_object* v_searcher_1797_; uint8_t v___x_1798_; lean_object* v___f_1799_; lean_object* v___x_1800_; lean_object* v___x_1801_; uint8_t v___x_1802_; 
v___f_1796_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1794_);
v_searcher_1797_ = lean_apply_1(v_inst_1795_, v_s_1794_);
v___x_1798_ = 0;
v___f_1799_ = ((lean_object*)(l_String_Slice_contains___redArg___closed__0));
v___x_1800_ = lean_box(v___x_1798_);
v___x_1801_ = lean_apply_7(v_inst_1793_, v_s_1794_, v___f_1796_, lean_box(0), lean_box(0), v_searcher_1797_, v___x_1800_, v___f_1799_);
v___x_1802_ = lean_unbox(v___x_1801_);
return v___x_1802_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___boxed(lean_object* v_inst_1803_, lean_object* v_s_1804_, lean_object* v_inst_1805_){
_start:
{
uint8_t v_res_1806_; lean_object* v_r_1807_; 
v_res_1806_ = l_String_Slice_contains___redArg(v_inst_1803_, v_s_1804_, v_inst_1805_);
v_r_1807_ = lean_box(v_res_1806_);
return v_r_1807_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_contains(lean_object* v_00_u03c1_1808_, lean_object* v_00_u03c3_1809_, lean_object* v_inst_1810_, lean_object* v_inst_1811_, lean_object* v_s_1812_, lean_object* v_pat_1813_, lean_object* v_inst_1814_){
_start:
{
uint8_t v___x_1815_; 
v___x_1815_ = l_String_Slice_contains___redArg(v_inst_1811_, v_s_1812_, v_inst_1814_);
return v___x_1815_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_contains___boxed(lean_object* v_00_u03c1_1816_, lean_object* v_00_u03c3_1817_, lean_object* v_inst_1818_, lean_object* v_inst_1819_, lean_object* v_s_1820_, lean_object* v_pat_1821_, lean_object* v_inst_1822_){
_start:
{
uint8_t v_res_1823_; lean_object* v_r_1824_; 
v_res_1823_ = l_String_Slice_contains(v_00_u03c1_1816_, v_00_u03c3_1817_, v_inst_1818_, v_inst_1819_, v_s_1820_, v_pat_1821_, v_inst_1822_);
lean_dec(v_pat_1821_);
lean_dec(v_inst_1818_);
v_r_1824_ = lean_box(v_res_1823_);
return v_r_1824_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any___redArg(lean_object* v_inst_1825_, lean_object* v_s_1826_, lean_object* v_inst_1827_){
_start:
{
uint8_t v___x_1828_; 
v___x_1828_ = l_String_Slice_contains___redArg(v_inst_1825_, v_s_1826_, v_inst_1827_);
return v___x_1828_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___redArg___boxed(lean_object* v_inst_1829_, lean_object* v_s_1830_, lean_object* v_inst_1831_){
_start:
{
uint8_t v_res_1832_; lean_object* v_r_1833_; 
v_res_1832_ = l_String_Slice_any___redArg(v_inst_1829_, v_s_1830_, v_inst_1831_);
v_r_1833_ = lean_box(v_res_1832_);
return v_r_1833_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_any(lean_object* v_00_u03c1_1834_, lean_object* v_00_u03c3_1835_, lean_object* v_inst_1836_, lean_object* v_inst_1837_, lean_object* v_s_1838_, lean_object* v_pat_1839_, lean_object* v_inst_1840_){
_start:
{
uint8_t v___x_1841_; 
v___x_1841_ = l_String_Slice_contains___redArg(v_inst_1837_, v_s_1838_, v_inst_1840_);
return v___x_1841_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_any___boxed(lean_object* v_00_u03c1_1842_, lean_object* v_00_u03c3_1843_, lean_object* v_inst_1844_, lean_object* v_inst_1845_, lean_object* v_s_1846_, lean_object* v_pat_1847_, lean_object* v_inst_1848_){
_start:
{
uint8_t v_res_1849_; lean_object* v_r_1850_; 
v_res_1849_ = l_String_Slice_any(v_00_u03c1_1842_, v_00_u03c3_1843_, v_inst_1844_, v_inst_1845_, v_s_1846_, v_pat_1847_, v_inst_1848_);
lean_dec(v_pat_1847_);
lean_dec(v_inst_1844_);
v_r_1850_ = lean_box(v_res_1849_);
return v_r_1850_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all___redArg(lean_object* v_s_1851_, lean_object* v_inst_1852_){
_start:
{
lean_object* v_startInclusive_1853_; lean_object* v_endExclusive_1854_; lean_object* v___x_1855_; lean_object* v___x_1856_; lean_object* v___x_1857_; uint8_t v_decide_1858_; 
v_startInclusive_1853_ = lean_ctor_get(v_s_1851_, 1);
v_endExclusive_1854_ = lean_ctor_get(v_s_1851_, 2);
v___x_1855_ = lean_unsigned_to_nat(0u);
v___x_1856_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1851_, v___x_1855_, v_inst_1852_);
v___x_1857_ = lean_nat_sub(v_endExclusive_1854_, v_startInclusive_1853_);
v_decide_1858_ = lean_nat_dec_eq(v___x_1856_, v___x_1857_);
lean_dec(v___x_1857_);
lean_dec(v___x_1856_);
return v_decide_1858_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___redArg___boxed(lean_object* v_s_1859_, lean_object* v_inst_1860_){
_start:
{
uint8_t v_res_1861_; lean_object* v_r_1862_; 
v_res_1861_ = l_String_Slice_all___redArg(v_s_1859_, v_inst_1860_);
lean_dec_ref(v_s_1859_);
v_r_1862_ = lean_box(v_res_1861_);
return v_r_1862_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_all(lean_object* v_00_u03c1_1863_, lean_object* v_s_1864_, lean_object* v_pat_1865_, lean_object* v_inst_1866_){
_start:
{
lean_object* v_startInclusive_1867_; lean_object* v_endExclusive_1868_; lean_object* v___x_1869_; lean_object* v___x_1870_; lean_object* v___x_1871_; uint8_t v_decide_1872_; 
v_startInclusive_1867_ = lean_ctor_get(v_s_1864_, 1);
v_endExclusive_1868_ = lean_ctor_get(v_s_1864_, 2);
v___x_1869_ = lean_unsigned_to_nat(0u);
v___x_1870_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1864_, v___x_1869_, v_inst_1866_);
v___x_1871_ = lean_nat_sub(v_endExclusive_1868_, v_startInclusive_1867_);
v_decide_1872_ = lean_nat_dec_eq(v___x_1870_, v___x_1871_);
lean_dec(v___x_1871_);
lean_dec(v___x_1870_);
return v_decide_1872_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_all___boxed(lean_object* v_00_u03c1_1873_, lean_object* v_s_1874_, lean_object* v_pat_1875_, lean_object* v_inst_1876_){
_start:
{
uint8_t v_res_1877_; lean_object* v_r_1878_; 
v_res_1877_ = l_String_Slice_all(v_00_u03c1_1873_, v_s_1874_, v_pat_1875_, v_inst_1876_);
lean_dec(v_pat_1875_);
lean_dec_ref(v_s_1874_);
v_r_1878_ = lean_box(v_res_1877_);
return v_r_1878_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith___redArg(lean_object* v_s_1879_, lean_object* v_inst_1880_){
_start:
{
lean_object* v_endsWith_1881_; lean_object* v___x_1882_; uint8_t v___x_1883_; 
v_endsWith_1881_ = lean_ctor_get(v_inst_1880_, 2);
lean_inc_ref(v_endsWith_1881_);
lean_dec_ref(v_inst_1880_);
v___x_1882_ = lean_apply_1(v_endsWith_1881_, v_s_1879_);
v___x_1883_ = lean_unbox(v___x_1882_);
return v___x_1883_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___redArg___boxed(lean_object* v_s_1884_, lean_object* v_inst_1885_){
_start:
{
uint8_t v_res_1886_; lean_object* v_r_1887_; 
v_res_1886_ = l_String_Slice_endsWith___redArg(v_s_1884_, v_inst_1885_);
v_r_1887_ = lean_box(v_res_1886_);
return v_r_1887_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_endsWith(lean_object* v_00_u03c1_1888_, lean_object* v_s_1889_, lean_object* v_pat_1890_, lean_object* v_inst_1891_){
_start:
{
lean_object* v_endsWith_1892_; lean_object* v___x_1893_; uint8_t v___x_1894_; 
v_endsWith_1892_ = lean_ctor_get(v_inst_1891_, 2);
lean_inc_ref(v_endsWith_1892_);
lean_dec_ref(v_inst_1891_);
v___x_1893_ = lean_apply_1(v_endsWith_1892_, v_s_1889_);
v___x_1894_ = lean_unbox(v___x_1893_);
return v___x_1894_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___boxed(lean_object* v_00_u03c1_1895_, lean_object* v_s_1896_, lean_object* v_pat_1897_, lean_object* v_inst_1898_){
_start:
{
uint8_t v_res_1899_; lean_object* v_r_1900_; 
v_res_1899_ = l_String_Slice_endsWith(v_00_u03c1_1895_, v_s_1896_, v_pat_1897_, v_inst_1898_);
lean_dec(v_pat_1897_);
v_r_1900_ = lean_box(v_res_1899_);
return v_r_1900_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg(lean_object* v_x_1901_){
_start:
{
lean_object* v___x_1902_; 
v___x_1902_ = lean_obj_tag_nat(v_x_1901_);
return v___x_1902_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg___boxed(lean_object* v_x_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg(v_x_1903_);
lean_dec(v_x_1903_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl(lean_object* v_00_u03c3_1905_, lean_object* v_00_u03c1_1906_, lean_object* v_pat_1907_, lean_object* v_s_1908_, lean_object* v_inst_1909_, lean_object* v_x_1910_){
_start:
{
lean_object* v___x_1911_; 
v___x_1911_ = lean_obj_tag_nat(v_x_1910_);
return v___x_1911_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___boxed(lean_object* v_00_u03c3_1912_, lean_object* v_00_u03c1_1913_, lean_object* v_pat_1914_, lean_object* v_s_1915_, lean_object* v_inst_1916_, lean_object* v_x_1917_){
_start:
{
lean_object* v_res_1918_; 
v_res_1918_ = l_String_Slice_RevSplitIterator_ctorIdx___impl(v_00_u03c3_1912_, v_00_u03c1_1913_, v_pat_1914_, v_s_1915_, v_inst_1916_, v_x_1917_);
lean_dec(v_x_1917_);
lean_dec(v_inst_1916_);
lean_dec_ref(v_s_1915_);
lean_dec(v_pat_1914_);
return v_res_1918_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___redArg(lean_object* v_t_1919_, lean_object* v_k_1920_){
_start:
{
if (lean_obj_tag(v_t_1919_) == 0)
{
lean_object* v_currPos_1921_; lean_object* v_searcher_1922_; lean_object* v___x_1923_; 
v_currPos_1921_ = lean_ctor_get(v_t_1919_, 0);
lean_inc(v_currPos_1921_);
v_searcher_1922_ = lean_ctor_get(v_t_1919_, 1);
lean_inc(v_searcher_1922_);
lean_dec_ref_known(v_t_1919_, 2);
v___x_1923_ = lean_apply_2(v_k_1920_, v_currPos_1921_, v_searcher_1922_);
return v___x_1923_;
}
else
{
return v_k_1920_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim(lean_object* v_00_u03c3_1924_, lean_object* v_00_u03c1_1925_, lean_object* v_pat_1926_, lean_object* v_s_1927_, lean_object* v_inst_1928_, lean_object* v_motive_1929_, lean_object* v_ctorIdx_1930_, lean_object* v_t_1931_, lean_object* v_h_1932_, lean_object* v_k_1933_){
_start:
{
lean_object* v___x_1934_; 
v___x_1934_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1931_, v_k_1933_);
return v___x_1934_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_1935_, lean_object* v_00_u03c1_1936_, lean_object* v_pat_1937_, lean_object* v_s_1938_, lean_object* v_inst_1939_, lean_object* v_motive_1940_, lean_object* v_ctorIdx_1941_, lean_object* v_t_1942_, lean_object* v_h_1943_, lean_object* v_k_1944_){
_start:
{
lean_object* v_res_1945_; 
v_res_1945_ = l_String_Slice_RevSplitIterator_ctorElim(v_00_u03c3_1935_, v_00_u03c1_1936_, v_pat_1937_, v_s_1938_, v_inst_1939_, v_motive_1940_, v_ctorIdx_1941_, v_t_1942_, v_h_1943_, v_k_1944_);
lean_dec(v_ctorIdx_1941_);
lean_dec(v_inst_1939_);
lean_dec_ref(v_s_1938_);
lean_dec(v_pat_1937_);
return v_res_1945_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___redArg(lean_object* v_t_1946_, lean_object* v_operating_1947_){
_start:
{
lean_object* v___x_1948_; 
v___x_1948_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1946_, v_operating_1947_);
return v___x_1948_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim(lean_object* v_00_u03c3_1949_, lean_object* v_00_u03c1_1950_, lean_object* v_pat_1951_, lean_object* v_s_1952_, lean_object* v_inst_1953_, lean_object* v_motive_1954_, lean_object* v_t_1955_, lean_object* v_h_1956_, lean_object* v_operating_1957_){
_start:
{
lean_object* v___x_1958_; 
v___x_1958_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1955_, v_operating_1957_);
return v___x_1958_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_1959_, lean_object* v_00_u03c1_1960_, lean_object* v_pat_1961_, lean_object* v_s_1962_, lean_object* v_inst_1963_, lean_object* v_motive_1964_, lean_object* v_t_1965_, lean_object* v_h_1966_, lean_object* v_operating_1967_){
_start:
{
lean_object* v_res_1968_; 
v_res_1968_ = l_String_Slice_RevSplitIterator_operating_elim(v_00_u03c3_1959_, v_00_u03c1_1960_, v_pat_1961_, v_s_1962_, v_inst_1963_, v_motive_1964_, v_t_1965_, v_h_1966_, v_operating_1967_);
lean_dec(v_inst_1963_);
lean_dec_ref(v_s_1962_);
lean_dec(v_pat_1961_);
return v_res_1968_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___redArg(lean_object* v_t_1969_, lean_object* v_atEnd_1970_){
_start:
{
lean_object* v___x_1971_; 
v___x_1971_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1969_, v_atEnd_1970_);
return v___x_1971_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim(lean_object* v_00_u03c3_1972_, lean_object* v_00_u03c1_1973_, lean_object* v_pat_1974_, lean_object* v_s_1975_, lean_object* v_inst_1976_, lean_object* v_motive_1977_, lean_object* v_t_1978_, lean_object* v_h_1979_, lean_object* v_atEnd_1980_){
_start:
{
lean_object* v___x_1981_; 
v___x_1981_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1978_, v_atEnd_1980_);
return v___x_1981_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_1982_, lean_object* v_00_u03c1_1983_, lean_object* v_pat_1984_, lean_object* v_s_1985_, lean_object* v_inst_1986_, lean_object* v_motive_1987_, lean_object* v_t_1988_, lean_object* v_h_1989_, lean_object* v_atEnd_1990_){
_start:
{
lean_object* v_res_1991_; 
v_res_1991_ = l_String_Slice_RevSplitIterator_atEnd_elim(v_00_u03c3_1982_, v_00_u03c1_1983_, v_pat_1984_, v_s_1985_, v_inst_1986_, v_motive_1987_, v_t_1988_, v_h_1989_, v_atEnd_1990_);
lean_dec(v_inst_1986_);
lean_dec_ref(v_s_1985_);
lean_dec(v_pat_1984_);
return v_res_1991_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg(){
_start:
{
lean_object* v___x_1993_; 
v___x_1993_ = lean_box(1);
return v___x_1993_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg___boxed(lean_object* v___dummy_1994_){
_start:
{
lean_object* v_res_1995_; 
v_res_1995_ = l_String_Slice_instInhabitedRevSplitIterator_default___redArg();
return v_res_1995_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default(lean_object* v_00_u03c3_1996_, lean_object* v_00_u03c1_1997_, lean_object* v_pat_1998_, lean_object* v_s_1999_, lean_object* v_inst_2000_){
_start:
{
lean_object* v___x_2001_; 
v___x_2001_ = lean_box(1);
return v___x_2001_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___boxed(lean_object* v_00_u03c3_2002_, lean_object* v_00_u03c1_2003_, lean_object* v_pat_2004_, lean_object* v_s_2005_, lean_object* v_inst_2006_){
_start:
{
lean_object* v_res_2007_; 
v_res_2007_ = l_String_Slice_instInhabitedRevSplitIterator_default(v_00_u03c3_2002_, v_00_u03c1_2003_, v_pat_2004_, v_s_2005_, v_inst_2006_);
lean_dec(v_inst_2006_);
lean_dec_ref(v_s_2005_);
lean_dec(v_pat_2004_);
return v_res_2007_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg(){
_start:
{
lean_object* v___x_2009_; 
v___x_2009_ = lean_box(1);
return v___x_2009_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg___boxed(lean_object* v___dummy_2010_){
_start:
{
lean_object* v_res_2011_; 
v_res_2011_ = l_String_Slice_instInhabitedRevSplitIterator___redArg();
return v_res_2011_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator(lean_object* v_a_2012_, lean_object* v_a_2013_, lean_object* v_a_2014_, lean_object* v_a_2015_, lean_object* v_a_2016_){
_start:
{
lean_object* v___x_2017_; 
v___x_2017_ = lean_box(1);
return v___x_2017_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___boxed(lean_object* v_a_2018_, lean_object* v_a_2019_, lean_object* v_a_2020_, lean_object* v_a_2021_, lean_object* v_a_2022_){
_start:
{
lean_object* v_res_2023_; 
v_res_2023_ = l_String_Slice_instInhabitedRevSplitIterator(v_a_2018_, v_a_2019_, v_a_2020_, v_a_2021_, v_a_2022_);
lean_dec(v_a_2022_);
lean_dec_ref(v_a_2021_);
lean_dec(v_a_2020_);
return v_res_2023_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0(lean_object* v_inst_2024_, lean_object* v_s_2025_, lean_object* v_inst_2026_, lean_object* v_x_2027_){
_start:
{
if (lean_obj_tag(v_x_2027_) == 0)
{
lean_object* v_currPos_2028_; lean_object* v_searcher_2029_; lean_object* v___x_2031_; uint8_t v_isShared_2032_; uint8_t v_isSharedCheck_2087_; 
v_currPos_2028_ = lean_ctor_get(v_x_2027_, 0);
v_searcher_2029_ = lean_ctor_get(v_x_2027_, 1);
v_isSharedCheck_2087_ = !lean_is_exclusive(v_x_2027_);
if (v_isSharedCheck_2087_ == 0)
{
v___x_2031_ = v_x_2027_;
v_isShared_2032_ = v_isSharedCheck_2087_;
goto v_resetjp_2030_;
}
else
{
lean_inc(v_searcher_2029_);
lean_inc(v_currPos_2028_);
lean_dec(v_x_2027_);
v___x_2031_ = lean_box(0);
v_isShared_2032_ = v_isSharedCheck_2087_;
goto v_resetjp_2030_;
}
v_resetjp_2030_:
{
lean_object* v___x_2033_; 
lean_inc_ref(v_s_2025_);
v___x_2033_ = lean_apply_2(v_inst_2024_, v_s_2025_, v_searcher_2029_);
switch(lean_obj_tag(v___x_2033_))
{
case 0:
{
lean_object* v_out_2034_; 
v_out_2034_ = lean_ctor_get(v___x_2033_, 1);
lean_inc(v_out_2034_);
if (lean_obj_tag(v_out_2034_) == 0)
{
lean_object* v_it_2035_; lean_object* v___x_2037_; 
lean_dec_ref_known(v_out_2034_, 2);
lean_dec_ref(v_s_2025_);
v_it_2035_ = lean_ctor_get(v___x_2033_, 0);
lean_inc(v_it_2035_);
lean_dec_ref_known(v___x_2033_, 2);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v_it_2035_);
v___x_2037_ = v___x_2031_;
goto v_reusejp_2036_;
}
else
{
lean_object* v_reuseFailAlloc_2040_; 
v_reuseFailAlloc_2040_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2040_, 0, v_currPos_2028_);
lean_ctor_set(v_reuseFailAlloc_2040_, 1, v_it_2035_);
v___x_2037_ = v_reuseFailAlloc_2040_;
goto v_reusejp_2036_;
}
v_reusejp_2036_:
{
lean_object* v___x_2038_; lean_object* v___x_2039_; 
v___x_2038_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2038_, 0, v___x_2037_);
v___x_2039_ = lean_apply_2(v_inst_2026_, lean_box(0), v___x_2038_);
return v___x_2039_;
}
}
else
{
lean_object* v_it_2041_; lean_object* v___x_2043_; uint8_t v_isShared_2044_; uint8_t v_isSharedCheck_2055_; 
v_it_2041_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2055_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2055_ == 0)
{
lean_object* v_unused_2056_; 
v_unused_2056_ = lean_ctor_get(v___x_2033_, 1);
lean_dec(v_unused_2056_);
v___x_2043_ = v___x_2033_;
v_isShared_2044_ = v_isSharedCheck_2055_;
goto v_resetjp_2042_;
}
else
{
lean_inc(v_it_2041_);
lean_dec(v___x_2033_);
v___x_2043_ = lean_box(0);
v_isShared_2044_ = v_isSharedCheck_2055_;
goto v_resetjp_2042_;
}
v_resetjp_2042_:
{
lean_object* v_startPos_2045_; lean_object* v_endPos_2046_; lean_object* v_slice_2047_; lean_object* v_nextIt_2049_; 
v_startPos_2045_ = lean_ctor_get(v_out_2034_, 0);
lean_inc(v_startPos_2045_);
v_endPos_2046_ = lean_ctor_get(v_out_2034_, 1);
lean_inc(v_endPos_2046_);
lean_dec_ref_known(v_out_2034_, 2);
v_slice_2047_ = l_String_Slice_slice_x21(v_s_2025_, v_endPos_2046_, v_currPos_2028_);
lean_dec(v_currPos_2028_);
lean_dec(v_endPos_2046_);
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v_it_2041_);
lean_ctor_set(v___x_2031_, 0, v_startPos_2045_);
v_nextIt_2049_ = v___x_2031_;
goto v_reusejp_2048_;
}
else
{
lean_object* v_reuseFailAlloc_2054_; 
v_reuseFailAlloc_2054_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2054_, 0, v_startPos_2045_);
lean_ctor_set(v_reuseFailAlloc_2054_, 1, v_it_2041_);
v_nextIt_2049_ = v_reuseFailAlloc_2054_;
goto v_reusejp_2048_;
}
v_reusejp_2048_:
{
lean_object* v___x_2051_; 
if (v_isShared_2044_ == 0)
{
lean_ctor_set(v___x_2043_, 1, v_slice_2047_);
lean_ctor_set(v___x_2043_, 0, v_nextIt_2049_);
v___x_2051_ = v___x_2043_;
goto v_reusejp_2050_;
}
else
{
lean_object* v_reuseFailAlloc_2053_; 
v_reuseFailAlloc_2053_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2053_, 0, v_nextIt_2049_);
lean_ctor_set(v_reuseFailAlloc_2053_, 1, v_slice_2047_);
v___x_2051_ = v_reuseFailAlloc_2053_;
goto v_reusejp_2050_;
}
v_reusejp_2050_:
{
lean_object* v___x_2052_; 
v___x_2052_ = lean_apply_2(v_inst_2026_, lean_box(0), v___x_2051_);
return v___x_2052_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2057_; lean_object* v___x_2059_; uint8_t v_isShared_2060_; uint8_t v_isSharedCheck_2068_; 
lean_dec_ref(v_s_2025_);
v_it_2057_ = lean_ctor_get(v___x_2033_, 0);
v_isSharedCheck_2068_ = !lean_is_exclusive(v___x_2033_);
if (v_isSharedCheck_2068_ == 0)
{
v___x_2059_ = v___x_2033_;
v_isShared_2060_ = v_isSharedCheck_2068_;
goto v_resetjp_2058_;
}
else
{
lean_inc(v_it_2057_);
lean_dec(v___x_2033_);
v___x_2059_ = lean_box(0);
v_isShared_2060_ = v_isSharedCheck_2068_;
goto v_resetjp_2058_;
}
v_resetjp_2058_:
{
lean_object* v___x_2062_; 
if (v_isShared_2032_ == 0)
{
lean_ctor_set(v___x_2031_, 1, v_it_2057_);
v___x_2062_ = v___x_2031_;
goto v_reusejp_2061_;
}
else
{
lean_object* v_reuseFailAlloc_2067_; 
v_reuseFailAlloc_2067_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2067_, 0, v_currPos_2028_);
lean_ctor_set(v_reuseFailAlloc_2067_, 1, v_it_2057_);
v___x_2062_ = v_reuseFailAlloc_2067_;
goto v_reusejp_2061_;
}
v_reusejp_2061_:
{
lean_object* v___x_2064_; 
if (v_isShared_2060_ == 0)
{
lean_ctor_set(v___x_2059_, 0, v___x_2062_);
v___x_2064_ = v___x_2059_;
goto v_reusejp_2063_;
}
else
{
lean_object* v_reuseFailAlloc_2066_; 
v_reuseFailAlloc_2066_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2066_, 0, v___x_2062_);
v___x_2064_ = v_reuseFailAlloc_2066_;
goto v_reusejp_2063_;
}
v_reusejp_2063_:
{
lean_object* v___x_2065_; 
v___x_2065_ = lean_apply_2(v_inst_2026_, lean_box(0), v___x_2064_);
return v___x_2065_;
}
}
}
}
default: 
{
lean_object* v___x_2069_; uint8_t v_decide_2070_; 
lean_del_object(v___x_2031_);
v___x_2069_ = lean_unsigned_to_nat(0u);
v_decide_2070_ = lean_nat_dec_eq(v_currPos_2028_, v___x_2069_);
if (v_decide_2070_ == 0)
{
lean_object* v_str_2071_; lean_object* v_startInclusive_2072_; lean_object* v___x_2074_; uint8_t v_isShared_2075_; uint8_t v_isSharedCheck_2083_; 
v_str_2071_ = lean_ctor_get(v_s_2025_, 0);
v_startInclusive_2072_ = lean_ctor_get(v_s_2025_, 1);
v_isSharedCheck_2083_ = !lean_is_exclusive(v_s_2025_);
if (v_isSharedCheck_2083_ == 0)
{
lean_object* v_unused_2084_; 
v_unused_2084_ = lean_ctor_get(v_s_2025_, 2);
lean_dec(v_unused_2084_);
v___x_2074_ = v_s_2025_;
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
else
{
lean_inc(v_startInclusive_2072_);
lean_inc(v_str_2071_);
lean_dec(v_s_2025_);
v___x_2074_ = lean_box(0);
v_isShared_2075_ = v_isSharedCheck_2083_;
goto v_resetjp_2073_;
}
v_resetjp_2073_:
{
lean_object* v___x_2076_; lean_object* v_slice_2078_; 
v___x_2076_ = lean_nat_add(v_startInclusive_2072_, v_currPos_2028_);
lean_dec(v_currPos_2028_);
if (v_isShared_2075_ == 0)
{
lean_ctor_set(v___x_2074_, 2, v___x_2076_);
v_slice_2078_ = v___x_2074_;
goto v_reusejp_2077_;
}
else
{
lean_object* v_reuseFailAlloc_2082_; 
v_reuseFailAlloc_2082_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2082_, 0, v_str_2071_);
lean_ctor_set(v_reuseFailAlloc_2082_, 1, v_startInclusive_2072_);
lean_ctor_set(v_reuseFailAlloc_2082_, 2, v___x_2076_);
v_slice_2078_ = v_reuseFailAlloc_2082_;
goto v_reusejp_2077_;
}
v_reusejp_2077_:
{
lean_object* v___x_2079_; lean_object* v___x_2080_; lean_object* v___x_2081_; 
v___x_2079_ = lean_box(1);
v___x_2080_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2080_, 0, v___x_2079_);
lean_ctor_set(v___x_2080_, 1, v_slice_2078_);
v___x_2081_ = lean_apply_2(v_inst_2026_, lean_box(0), v___x_2080_);
return v___x_2081_;
}
}
}
else
{
lean_object* v___x_2085_; lean_object* v___x_2086_; 
lean_dec(v_currPos_2028_);
lean_dec_ref(v_s_2025_);
v___x_2085_ = lean_box(2);
v___x_2086_ = lean_apply_2(v_inst_2026_, lean_box(0), v___x_2085_);
return v___x_2086_;
}
}
}
}
}
else
{
lean_object* v___x_2088_; lean_object* v___x_2089_; 
lean_dec_ref(v_s_2025_);
lean_dec(v_inst_2024_);
v___x_2088_ = lean_box(2);
v___x_2089_ = lean_apply_2(v_inst_2026_, lean_box(0), v___x_2088_);
return v___x_2089_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg(lean_object* v_inst_2090_, lean_object* v_s_2091_, lean_object* v_inst_2092_){
_start:
{
lean_object* v___f_2093_; 
v___f_2093_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2093_, 0, v_inst_2090_);
lean_closure_set(v___f_2093_, 1, v_s_2091_);
lean_closure_set(v___f_2093_, 2, v_inst_2092_);
return v___f_2093_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure(lean_object* v_00_u03c1_2094_, lean_object* v_00_u03c1_2095_, lean_object* v_00_u03c3_2096_, lean_object* v_inst_2097_, lean_object* v_inst_2098_, lean_object* v_m_2099_, lean_object* v_s_2100_, lean_object* v_inst_2101_){
_start:
{
lean_object* v___f_2102_; 
v___f_2102_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2102_, 0, v_inst_2097_);
lean_closure_set(v___f_2102_, 1, v_s_2100_);
lean_closure_set(v___f_2102_, 2, v_inst_2101_);
return v___f_2102_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___boxed(lean_object* v_00_u03c1_2103_, lean_object* v_00_u03c1_2104_, lean_object* v_00_u03c3_2105_, lean_object* v_inst_2106_, lean_object* v_inst_2107_, lean_object* v_m_2108_, lean_object* v_s_2109_, lean_object* v_inst_2110_){
_start:
{
lean_object* v_res_2111_; 
v_res_2111_ = l_String_Slice_RevSplitIterator_instIteratorOfPure(v_00_u03c1_2103_, v_00_u03c1_2104_, v_00_u03c3_2105_, v_inst_2106_, v_inst_2107_, v_m_2108_, v_s_2109_, v_inst_2110_);
lean_dec(v_inst_2107_);
lean_dec(v_00_u03c1_2104_);
return v_res_2111_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(lean_object* v_x_2112_){
_start:
{
if (lean_obj_tag(v_x_2112_) == 0)
{
lean_object* v_searcher_2113_; lean_object* v___x_2114_; 
v_searcher_2113_ = lean_ctor_get(v_x_2112_, 1);
lean_inc(v_searcher_2113_);
v___x_2114_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2114_, 0, v_searcher_2113_);
return v___x_2114_;
}
else
{
lean_object* v___x_2115_; 
v___x_2115_ = lean_box(0);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg___boxed(lean_object* v_x_2116_){
_start:
{
lean_object* v_res_2117_; 
v_res_2117_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2116_);
lean_dec(v_x_2116_);
return v_res_2117_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(lean_object* v_00_u03c1_2118_, lean_object* v_00_u03c1_2119_, lean_object* v_00_u03c3_2120_, lean_object* v_inst_2121_, lean_object* v_s_2122_, lean_object* v_x_2123_){
_start:
{
lean_object* v___x_2124_; 
v___x_2124_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2123_);
return v___x_2124_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___boxed(lean_object* v_00_u03c1_2125_, lean_object* v_00_u03c1_2126_, lean_object* v_00_u03c3_2127_, lean_object* v_inst_2128_, lean_object* v_s_2129_, lean_object* v_x_2130_){
_start:
{
lean_object* v_res_2131_; 
v_res_2131_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(v_00_u03c1_2125_, v_00_u03c1_2126_, v_00_u03c3_2127_, v_inst_2128_, v_s_2129_, v_x_2130_);
lean_dec(v_x_2130_);
lean_dec_ref(v_s_2129_);
lean_dec(v_inst_2128_);
lean_dec(v_00_u03c1_2126_);
return v_res_2131_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(lean_object* v_x_2132_, lean_object* v_h__1_2133_, lean_object* v_h__2_2134_){
_start:
{
if (lean_obj_tag(v_x_2132_) == 0)
{
lean_object* v_currPos_2135_; lean_object* v_searcher_2136_; lean_object* v___x_2137_; 
lean_dec(v_h__2_2134_);
v_currPos_2135_ = lean_ctor_get(v_x_2132_, 0);
lean_inc(v_currPos_2135_);
v_searcher_2136_ = lean_ctor_get(v_x_2132_, 1);
lean_inc(v_searcher_2136_);
lean_dec_ref_known(v_x_2132_, 2);
v___x_2137_ = lean_apply_2(v_h__1_2133_, v_currPos_2135_, v_searcher_2136_);
return v___x_2137_;
}
else
{
lean_object* v___x_2138_; lean_object* v___x_2139_; 
lean_dec(v_h__1_2133_);
v___x_2138_ = lean_box(0);
v___x_2139_ = lean_apply_1(v_h__2_2134_, v___x_2138_);
return v___x_2139_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(lean_object* v_00_u03c1_2140_, lean_object* v_00_u03c1_2141_, lean_object* v_00_u03c3_2142_, lean_object* v_inst_2143_, lean_object* v_m_2144_, lean_object* v_s_2145_, lean_object* v_motive_2146_, lean_object* v_x_2147_, lean_object* v_h__1_2148_, lean_object* v_h__2_2149_){
_start:
{
if (lean_obj_tag(v_x_2147_) == 0)
{
lean_object* v_currPos_2150_; lean_object* v_searcher_2151_; lean_object* v___x_2152_; 
lean_dec(v_h__2_2149_);
v_currPos_2150_ = lean_ctor_get(v_x_2147_, 0);
lean_inc(v_currPos_2150_);
v_searcher_2151_ = lean_ctor_get(v_x_2147_, 1);
lean_inc(v_searcher_2151_);
lean_dec_ref_known(v_x_2147_, 2);
v___x_2152_ = lean_apply_2(v_h__1_2148_, v_currPos_2150_, v_searcher_2151_);
return v___x_2152_;
}
else
{
lean_object* v___x_2153_; lean_object* v___x_2154_; 
lean_dec(v_h__1_2148_);
v___x_2153_ = lean_box(0);
v___x_2154_ = lean_apply_1(v_h__2_2149_, v___x_2153_);
return v___x_2154_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___boxed(lean_object* v_00_u03c1_2155_, lean_object* v_00_u03c1_2156_, lean_object* v_00_u03c3_2157_, lean_object* v_inst_2158_, lean_object* v_m_2159_, lean_object* v_s_2160_, lean_object* v_motive_2161_, lean_object* v_x_2162_, lean_object* v_h__1_2163_, lean_object* v_h__2_2164_){
_start:
{
lean_object* v_res_2165_; 
v_res_2165_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(v_00_u03c1_2155_, v_00_u03c1_2156_, v_00_u03c3_2157_, v_inst_2158_, v_m_2159_, v_s_2160_, v_motive_2161_, v_x_2162_, v_h__1_2163_, v_h__2_2164_);
lean_dec_ref(v_s_2160_);
lean_dec(v_inst_2158_);
lean_dec(v_00_u03c1_2156_);
return v_res_2165_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(lean_object* v_x_2166_, lean_object* v_x_2167_, lean_object* v_h__1_2168_, lean_object* v_h__2_2169_, lean_object* v_h__3_2170_, lean_object* v_h__4_2171_, lean_object* v_h__5_2172_, lean_object* v_h__6_2173_, lean_object* v_h__7_2174_, lean_object* v_h__8_2175_){
_start:
{
if (lean_obj_tag(v_x_2166_) == 0)
{
lean_dec(v_h__8_2175_);
lean_dec(v_h__7_2174_);
lean_dec(v_h__6_2173_);
switch(lean_obj_tag(v_x_2167_))
{
case 0:
{
lean_object* v_it_2176_; 
lean_dec(v_h__5_2172_);
lean_dec(v_h__4_2171_);
lean_dec(v_h__3_2170_);
v_it_2176_ = lean_ctor_get(v_x_2167_, 0);
if (lean_obj_tag(v_it_2176_) == 0)
{
lean_object* v_currPos_2177_; lean_object* v_searcher_2178_; lean_object* v_out_2179_; lean_object* v_currPos_2180_; lean_object* v_searcher_2181_; lean_object* v___x_2182_; 
lean_inc_ref(v_it_2176_);
lean_dec(v_h__2_2169_);
v_currPos_2177_ = lean_ctor_get(v_x_2166_, 0);
lean_inc(v_currPos_2177_);
v_searcher_2178_ = lean_ctor_get(v_x_2166_, 1);
lean_inc(v_searcher_2178_);
lean_dec_ref_known(v_x_2166_, 2);
v_out_2179_ = lean_ctor_get(v_x_2167_, 1);
lean_inc(v_out_2179_);
lean_dec_ref_known(v_x_2167_, 2);
v_currPos_2180_ = lean_ctor_get(v_it_2176_, 0);
lean_inc(v_currPos_2180_);
v_searcher_2181_ = lean_ctor_get(v_it_2176_, 1);
lean_inc(v_searcher_2181_);
lean_dec_ref_known(v_it_2176_, 2);
v___x_2182_ = lean_apply_5(v_h__1_2168_, v_currPos_2177_, v_searcher_2178_, v_currPos_2180_, v_searcher_2181_, v_out_2179_);
return v___x_2182_;
}
else
{
lean_object* v_currPos_2183_; lean_object* v_searcher_2184_; lean_object* v_out_2185_; lean_object* v___x_2186_; 
lean_dec(v_h__1_2168_);
v_currPos_2183_ = lean_ctor_get(v_x_2166_, 0);
lean_inc(v_currPos_2183_);
v_searcher_2184_ = lean_ctor_get(v_x_2166_, 1);
lean_inc(v_searcher_2184_);
lean_dec_ref_known(v_x_2166_, 2);
v_out_2185_ = lean_ctor_get(v_x_2167_, 1);
lean_inc(v_out_2185_);
lean_dec_ref_known(v_x_2167_, 2);
v___x_2186_ = lean_apply_3(v_h__2_2169_, v_currPos_2183_, v_searcher_2184_, v_out_2185_);
return v___x_2186_;
}
}
case 1:
{
lean_object* v_it_2187_; 
lean_dec(v_h__5_2172_);
lean_dec(v_h__2_2169_);
lean_dec(v_h__1_2168_);
v_it_2187_ = lean_ctor_get(v_x_2167_, 0);
lean_inc(v_it_2187_);
lean_dec_ref_known(v_x_2167_, 1);
if (lean_obj_tag(v_it_2187_) == 0)
{
lean_object* v_currPos_2188_; lean_object* v_searcher_2189_; lean_object* v_currPos_2190_; lean_object* v_searcher_2191_; lean_object* v___x_2192_; 
lean_dec(v_h__4_2171_);
v_currPos_2188_ = lean_ctor_get(v_x_2166_, 0);
lean_inc(v_currPos_2188_);
v_searcher_2189_ = lean_ctor_get(v_x_2166_, 1);
lean_inc(v_searcher_2189_);
lean_dec_ref_known(v_x_2166_, 2);
v_currPos_2190_ = lean_ctor_get(v_it_2187_, 0);
lean_inc(v_currPos_2190_);
v_searcher_2191_ = lean_ctor_get(v_it_2187_, 1);
lean_inc(v_searcher_2191_);
lean_dec_ref_known(v_it_2187_, 2);
v___x_2192_ = lean_apply_4(v_h__3_2170_, v_currPos_2188_, v_searcher_2189_, v_currPos_2190_, v_searcher_2191_);
return v___x_2192_;
}
else
{
lean_object* v_currPos_2193_; lean_object* v_searcher_2194_; lean_object* v___x_2195_; 
lean_dec(v_h__3_2170_);
v_currPos_2193_ = lean_ctor_get(v_x_2166_, 0);
lean_inc(v_currPos_2193_);
v_searcher_2194_ = lean_ctor_get(v_x_2166_, 1);
lean_inc(v_searcher_2194_);
lean_dec_ref_known(v_x_2166_, 2);
v___x_2195_ = lean_apply_2(v_h__4_2171_, v_currPos_2193_, v_searcher_2194_);
return v___x_2195_;
}
}
default: 
{
lean_object* v_currPos_2196_; lean_object* v_searcher_2197_; lean_object* v___x_2198_; 
lean_dec(v_h__4_2171_);
lean_dec(v_h__3_2170_);
lean_dec(v_h__2_2169_);
lean_dec(v_h__1_2168_);
v_currPos_2196_ = lean_ctor_get(v_x_2166_, 0);
lean_inc(v_currPos_2196_);
v_searcher_2197_ = lean_ctor_get(v_x_2166_, 1);
lean_inc(v_searcher_2197_);
lean_dec_ref_known(v_x_2166_, 2);
v___x_2198_ = lean_apply_2(v_h__5_2172_, v_currPos_2196_, v_searcher_2197_);
return v___x_2198_;
}
}
}
else
{
lean_dec(v_h__5_2172_);
lean_dec(v_h__4_2171_);
lean_dec(v_h__3_2170_);
lean_dec(v_h__2_2169_);
lean_dec(v_h__1_2168_);
switch(lean_obj_tag(v_x_2167_))
{
case 0:
{
lean_object* v_it_2199_; lean_object* v_out_2200_; lean_object* v___x_2201_; 
lean_dec(v_h__8_2175_);
lean_dec(v_h__7_2174_);
v_it_2199_ = lean_ctor_get(v_x_2167_, 0);
lean_inc(v_it_2199_);
v_out_2200_ = lean_ctor_get(v_x_2167_, 1);
lean_inc(v_out_2200_);
lean_dec_ref_known(v_x_2167_, 2);
v___x_2201_ = lean_apply_2(v_h__6_2173_, v_it_2199_, v_out_2200_);
return v___x_2201_;
}
case 1:
{
lean_object* v_it_2202_; lean_object* v___x_2203_; 
lean_dec(v_h__8_2175_);
lean_dec(v_h__6_2173_);
v_it_2202_ = lean_ctor_get(v_x_2167_, 0);
lean_inc(v_it_2202_);
lean_dec_ref_known(v_x_2167_, 1);
v___x_2203_ = lean_apply_1(v_h__7_2174_, v_it_2202_);
return v___x_2203_;
}
default: 
{
lean_object* v___x_2204_; lean_object* v___x_2205_; 
lean_dec(v_h__7_2174_);
lean_dec(v_h__6_2173_);
v___x_2204_ = lean_box(0);
v___x_2205_ = lean_apply_1(v_h__8_2175_, v___x_2204_);
return v___x_2205_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(lean_object* v_00_u03c1_2206_, lean_object* v_00_u03c1_2207_, lean_object* v_00_u03c3_2208_, lean_object* v_inst_2209_, lean_object* v_m_2210_, lean_object* v_s_2211_, lean_object* v_motive_2212_, lean_object* v_x_2213_, lean_object* v_x_2214_, lean_object* v_h__1_2215_, lean_object* v_h__2_2216_, lean_object* v_h__3_2217_, lean_object* v_h__4_2218_, lean_object* v_h__5_2219_, lean_object* v_h__6_2220_, lean_object* v_h__7_2221_, lean_object* v_h__8_2222_){
_start:
{
if (lean_obj_tag(v_x_2213_) == 0)
{
lean_dec(v_h__8_2222_);
lean_dec(v_h__7_2221_);
lean_dec(v_h__6_2220_);
switch(lean_obj_tag(v_x_2214_))
{
case 0:
{
lean_object* v_it_2223_; 
lean_dec(v_h__5_2219_);
lean_dec(v_h__4_2218_);
lean_dec(v_h__3_2217_);
v_it_2223_ = lean_ctor_get(v_x_2214_, 0);
if (lean_obj_tag(v_it_2223_) == 0)
{
lean_object* v_currPos_2224_; lean_object* v_searcher_2225_; lean_object* v_out_2226_; lean_object* v_currPos_2227_; lean_object* v_searcher_2228_; lean_object* v___x_2229_; 
lean_inc_ref(v_it_2223_);
lean_dec(v_h__2_2216_);
v_currPos_2224_ = lean_ctor_get(v_x_2213_, 0);
lean_inc(v_currPos_2224_);
v_searcher_2225_ = lean_ctor_get(v_x_2213_, 1);
lean_inc(v_searcher_2225_);
lean_dec_ref_known(v_x_2213_, 2);
v_out_2226_ = lean_ctor_get(v_x_2214_, 1);
lean_inc(v_out_2226_);
lean_dec_ref_known(v_x_2214_, 2);
v_currPos_2227_ = lean_ctor_get(v_it_2223_, 0);
lean_inc(v_currPos_2227_);
v_searcher_2228_ = lean_ctor_get(v_it_2223_, 1);
lean_inc(v_searcher_2228_);
lean_dec_ref_known(v_it_2223_, 2);
v___x_2229_ = lean_apply_5(v_h__1_2215_, v_currPos_2224_, v_searcher_2225_, v_currPos_2227_, v_searcher_2228_, v_out_2226_);
return v___x_2229_;
}
else
{
lean_object* v_currPos_2230_; lean_object* v_searcher_2231_; lean_object* v_out_2232_; lean_object* v___x_2233_; 
lean_dec(v_h__1_2215_);
v_currPos_2230_ = lean_ctor_get(v_x_2213_, 0);
lean_inc(v_currPos_2230_);
v_searcher_2231_ = lean_ctor_get(v_x_2213_, 1);
lean_inc(v_searcher_2231_);
lean_dec_ref_known(v_x_2213_, 2);
v_out_2232_ = lean_ctor_get(v_x_2214_, 1);
lean_inc(v_out_2232_);
lean_dec_ref_known(v_x_2214_, 2);
v___x_2233_ = lean_apply_3(v_h__2_2216_, v_currPos_2230_, v_searcher_2231_, v_out_2232_);
return v___x_2233_;
}
}
case 1:
{
lean_object* v_it_2234_; 
lean_dec(v_h__5_2219_);
lean_dec(v_h__2_2216_);
lean_dec(v_h__1_2215_);
v_it_2234_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_it_2234_);
lean_dec_ref_known(v_x_2214_, 1);
if (lean_obj_tag(v_it_2234_) == 0)
{
lean_object* v_currPos_2235_; lean_object* v_searcher_2236_; lean_object* v_currPos_2237_; lean_object* v_searcher_2238_; lean_object* v___x_2239_; 
lean_dec(v_h__4_2218_);
v_currPos_2235_ = lean_ctor_get(v_x_2213_, 0);
lean_inc(v_currPos_2235_);
v_searcher_2236_ = lean_ctor_get(v_x_2213_, 1);
lean_inc(v_searcher_2236_);
lean_dec_ref_known(v_x_2213_, 2);
v_currPos_2237_ = lean_ctor_get(v_it_2234_, 0);
lean_inc(v_currPos_2237_);
v_searcher_2238_ = lean_ctor_get(v_it_2234_, 1);
lean_inc(v_searcher_2238_);
lean_dec_ref_known(v_it_2234_, 2);
v___x_2239_ = lean_apply_4(v_h__3_2217_, v_currPos_2235_, v_searcher_2236_, v_currPos_2237_, v_searcher_2238_);
return v___x_2239_;
}
else
{
lean_object* v_currPos_2240_; lean_object* v_searcher_2241_; lean_object* v___x_2242_; 
lean_dec(v_h__3_2217_);
v_currPos_2240_ = lean_ctor_get(v_x_2213_, 0);
lean_inc(v_currPos_2240_);
v_searcher_2241_ = lean_ctor_get(v_x_2213_, 1);
lean_inc(v_searcher_2241_);
lean_dec_ref_known(v_x_2213_, 2);
v___x_2242_ = lean_apply_2(v_h__4_2218_, v_currPos_2240_, v_searcher_2241_);
return v___x_2242_;
}
}
default: 
{
lean_object* v_currPos_2243_; lean_object* v_searcher_2244_; lean_object* v___x_2245_; 
lean_dec(v_h__4_2218_);
lean_dec(v_h__3_2217_);
lean_dec(v_h__2_2216_);
lean_dec(v_h__1_2215_);
v_currPos_2243_ = lean_ctor_get(v_x_2213_, 0);
lean_inc(v_currPos_2243_);
v_searcher_2244_ = lean_ctor_get(v_x_2213_, 1);
lean_inc(v_searcher_2244_);
lean_dec_ref_known(v_x_2213_, 2);
v___x_2245_ = lean_apply_2(v_h__5_2219_, v_currPos_2243_, v_searcher_2244_);
return v___x_2245_;
}
}
}
else
{
lean_dec(v_h__5_2219_);
lean_dec(v_h__4_2218_);
lean_dec(v_h__3_2217_);
lean_dec(v_h__2_2216_);
lean_dec(v_h__1_2215_);
switch(lean_obj_tag(v_x_2214_))
{
case 0:
{
lean_object* v_it_2246_; lean_object* v_out_2247_; lean_object* v___x_2248_; 
lean_dec(v_h__8_2222_);
lean_dec(v_h__7_2221_);
v_it_2246_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_it_2246_);
v_out_2247_ = lean_ctor_get(v_x_2214_, 1);
lean_inc(v_out_2247_);
lean_dec_ref_known(v_x_2214_, 2);
v___x_2248_ = lean_apply_2(v_h__6_2220_, v_it_2246_, v_out_2247_);
return v___x_2248_;
}
case 1:
{
lean_object* v_it_2249_; lean_object* v___x_2250_; 
lean_dec(v_h__8_2222_);
lean_dec(v_h__6_2220_);
v_it_2249_ = lean_ctor_get(v_x_2214_, 0);
lean_inc(v_it_2249_);
lean_dec_ref_known(v_x_2214_, 1);
v___x_2250_ = lean_apply_1(v_h__7_2221_, v_it_2249_);
return v___x_2250_;
}
default: 
{
lean_object* v___x_2251_; lean_object* v___x_2252_; 
lean_dec(v_h__7_2221_);
lean_dec(v_h__6_2220_);
v___x_2251_ = lean_box(0);
v___x_2252_ = lean_apply_1(v_h__8_2222_, v___x_2251_);
return v___x_2252_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___boxed(lean_object** _args){
lean_object* v_00_u03c1_2253_ = _args[0];
lean_object* v_00_u03c1_2254_ = _args[1];
lean_object* v_00_u03c3_2255_ = _args[2];
lean_object* v_inst_2256_ = _args[3];
lean_object* v_m_2257_ = _args[4];
lean_object* v_s_2258_ = _args[5];
lean_object* v_motive_2259_ = _args[6];
lean_object* v_x_2260_ = _args[7];
lean_object* v_x_2261_ = _args[8];
lean_object* v_h__1_2262_ = _args[9];
lean_object* v_h__2_2263_ = _args[10];
lean_object* v_h__3_2264_ = _args[11];
lean_object* v_h__4_2265_ = _args[12];
lean_object* v_h__5_2266_ = _args[13];
lean_object* v_h__6_2267_ = _args[14];
lean_object* v_h__7_2268_ = _args[15];
lean_object* v_h__8_2269_ = _args[16];
_start:
{
lean_object* v_res_2270_; 
v_res_2270_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(v_00_u03c1_2253_, v_00_u03c1_2254_, v_00_u03c3_2255_, v_inst_2256_, v_m_2257_, v_s_2258_, v_motive_2259_, v_x_2260_, v_x_2261_, v_h__1_2262_, v_h__2_2263_, v_h__3_2264_, v_h__4_2265_, v_h__5_2266_, v_h__6_2267_, v_h__7_2268_, v_h__8_2269_);
lean_dec_ref(v_s_2258_);
lean_dec(v_inst_2256_);
lean_dec(v_00_u03c1_2254_);
return v_res_2270_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___redArg(lean_object* v_x_2271_, lean_object* v_h__1_2272_, lean_object* v_h__2_2273_){
_start:
{
if (lean_obj_tag(v_x_2271_) == 0)
{
lean_object* v_currPos_2274_; lean_object* v_searcher_2275_; lean_object* v___x_2276_; 
lean_dec(v_h__2_2273_);
v_currPos_2274_ = lean_ctor_get(v_x_2271_, 0);
lean_inc(v_currPos_2274_);
v_searcher_2275_ = lean_ctor_get(v_x_2271_, 1);
lean_inc(v_searcher_2275_);
lean_dec_ref_known(v_x_2271_, 2);
v___x_2276_ = lean_apply_2(v_h__1_2272_, v_currPos_2274_, v_searcher_2275_);
return v___x_2276_;
}
else
{
lean_object* v___x_2277_; lean_object* v___x_2278_; 
lean_dec(v_h__1_2272_);
v___x_2277_ = lean_box(0);
v___x_2278_ = lean_apply_1(v_h__2_2273_, v___x_2277_);
return v___x_2278_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(lean_object* v_00_u03c1_2279_, lean_object* v_00_u03c1_2280_, lean_object* v_00_u03c3_2281_, lean_object* v_inst_2282_, lean_object* v_s_2283_, lean_object* v_motive_2284_, lean_object* v_x_2285_, lean_object* v_h__1_2286_, lean_object* v_h__2_2287_){
_start:
{
if (lean_obj_tag(v_x_2285_) == 0)
{
lean_object* v_currPos_2288_; lean_object* v_searcher_2289_; lean_object* v___x_2290_; 
lean_dec(v_h__2_2287_);
v_currPos_2288_ = lean_ctor_get(v_x_2285_, 0);
lean_inc(v_currPos_2288_);
v_searcher_2289_ = lean_ctor_get(v_x_2285_, 1);
lean_inc(v_searcher_2289_);
lean_dec_ref_known(v_x_2285_, 2);
v___x_2290_ = lean_apply_2(v_h__1_2286_, v_currPos_2288_, v_searcher_2289_);
return v___x_2290_;
}
else
{
lean_object* v___x_2291_; lean_object* v___x_2292_; 
lean_dec(v_h__1_2286_);
v___x_2291_ = lean_box(0);
v___x_2292_ = lean_apply_1(v_h__2_2287_, v___x_2291_);
return v___x_2292_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter___boxed(lean_object* v_00_u03c1_2293_, lean_object* v_00_u03c1_2294_, lean_object* v_00_u03c3_2295_, lean_object* v_inst_2296_, lean_object* v_s_2297_, lean_object* v_motive_2298_, lean_object* v_x_2299_, lean_object* v_h__1_2300_, lean_object* v_h__2_2301_){
_start:
{
lean_object* v_res_2302_; 
v_res_2302_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption_match__1_splitter(v_00_u03c1_2293_, v_00_u03c1_2294_, v_00_u03c3_2295_, v_inst_2296_, v_s_2297_, v_motive_2298_, v_x_2299_, v_h__1_2300_, v_h__2_2301_);
lean_dec_ref(v_s_2297_);
lean_dec(v_inst_2296_);
lean_dec(v_00_u03c1_2294_);
return v_res_2302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_2304_; 
v___x_2304_ = lean_box(0);
return v___x_2304_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_2305_){
_start:
{
lean_object* v_res_2306_; 
v_res_2306_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg();
return v_res_2306_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(lean_object* v_00_u03c1_2307_, lean_object* v_00_u03c1_2308_, lean_object* v_00_u03c3_2309_, lean_object* v_inst_2310_, lean_object* v_inst_2311_, lean_object* v_s_2312_, lean_object* v_inst_2313_){
_start:
{
lean_object* v___x_2314_; 
v___x_2314_ = lean_box(0);
return v___x_2314_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_2315_, lean_object* v_00_u03c1_2316_, lean_object* v_00_u03c3_2317_, lean_object* v_inst_2318_, lean_object* v_inst_2319_, lean_object* v_s_2320_, lean_object* v_inst_2321_){
_start:
{
lean_object* v_res_2322_; 
v_res_2322_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(v_00_u03c1_2315_, v_00_u03c1_2316_, v_00_u03c3_2317_, v_inst_2318_, v_inst_2319_, v_s_2320_, v_inst_2321_);
lean_dec_ref(v_s_2320_);
lean_dec(v_inst_2319_);
lean_dec(v_inst_2318_);
lean_dec(v_00_u03c1_2316_);
return v_res_2322_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object* v_toPure_2323_, lean_object* v_recur_2324_, lean_object* v_it_2325_, lean_object* v_____do__lift_2326_){
_start:
{
if (lean_obj_tag(v_____do__lift_2326_) == 0)
{
lean_object* v_a_2327_; lean_object* v___x_2328_; 
lean_dec(v_it_2325_);
lean_dec(v_recur_2324_);
v_a_2327_ = lean_ctor_get(v_____do__lift_2326_, 0);
lean_inc(v_a_2327_);
lean_dec_ref_known(v_____do__lift_2326_, 1);
v___x_2328_ = lean_apply_2(v_toPure_2323_, lean_box(0), v_a_2327_);
return v___x_2328_;
}
else
{
lean_object* v_a_2329_; lean_object* v___x_2330_; 
lean_dec(v_toPure_2323_);
v_a_2329_ = lean_ctor_get(v_____do__lift_2326_, 0);
lean_inc(v_a_2329_);
lean_dec_ref_known(v_____do__lift_2326_, 1);
v___x_2330_ = lean_apply_4(v_recur_2324_, v_it_2325_, v_a_2329_, lean_box(0), lean_box(0));
return v___x_2330_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object* v_toPure_2331_, lean_object* v_recur_2332_, lean_object* v___y_2333_, lean_object* v_acc_2334_, lean_object* v_toBind_2335_, lean_object* v_s_2336_){
_start:
{
switch(lean_obj_tag(v_s_2336_))
{
case 0:
{
lean_object* v_it_2337_; lean_object* v_out_2338_; lean_object* v___f_2339_; lean_object* v___x_2340_; lean_object* v___x_2341_; 
v_it_2337_ = lean_ctor_get(v_s_2336_, 0);
lean_inc(v_it_2337_);
v_out_2338_ = lean_ctor_get(v_s_2336_, 1);
lean_inc(v_out_2338_);
lean_dec_ref_known(v_s_2336_, 2);
v___f_2339_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2339_, 0, v_toPure_2331_);
lean_closure_set(v___f_2339_, 1, v_recur_2332_);
lean_closure_set(v___f_2339_, 2, v_it_2337_);
v___x_2340_ = lean_apply_3(v___y_2333_, v_out_2338_, lean_box(0), v_acc_2334_);
v___x_2341_ = lean_apply_4(v_toBind_2335_, lean_box(0), lean_box(0), v___x_2340_, v___f_2339_);
return v___x_2341_;
}
case 1:
{
lean_object* v_it_2342_; lean_object* v___x_2343_; 
lean_dec(v_toBind_2335_);
lean_dec(v___y_2333_);
lean_dec(v_toPure_2331_);
v_it_2342_ = lean_ctor_get(v_s_2336_, 0);
lean_inc(v_it_2342_);
lean_dec_ref_known(v_s_2336_, 1);
v___x_2343_ = lean_apply_4(v_recur_2332_, v_it_2342_, v_acc_2334_, lean_box(0), lean_box(0));
return v___x_2343_;
}
default: 
{
lean_object* v___x_2344_; 
lean_dec(v_toBind_2335_);
lean_dec(v___y_2333_);
lean_dec(v_recur_2332_);
v___x_2344_ = lean_apply_2(v_toPure_2331_, lean_box(0), v_acc_2334_);
return v___x_2344_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object* v_toPure_2345_, lean_object* v___y_2346_, lean_object* v_toBind_2347_, lean_object* v_inst_2348_, lean_object* v_s_2349_, lean_object* v_toPure_2350_, lean_object* v_lift_2351_, lean_object* v_it_2352_, lean_object* v_acc_2353_, lean_object* v_hP_2354_, lean_object* v_recur_2355_){
_start:
{
lean_object* v___f_2356_; 
v___f_2356_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2356_, 0, v_toPure_2345_);
lean_closure_set(v___f_2356_, 1, v_recur_2355_);
lean_closure_set(v___f_2356_, 2, v___y_2346_);
lean_closure_set(v___f_2356_, 3, v_acc_2353_);
lean_closure_set(v___f_2356_, 4, v_toBind_2347_);
if (lean_obj_tag(v_it_2352_) == 0)
{
lean_object* v_currPos_2357_; lean_object* v_searcher_2358_; lean_object* v___x_2360_; uint8_t v_isShared_2361_; uint8_t v_isSharedCheck_2421_; 
v_currPos_2357_ = lean_ctor_get(v_it_2352_, 0);
v_searcher_2358_ = lean_ctor_get(v_it_2352_, 1);
v_isSharedCheck_2421_ = !lean_is_exclusive(v_it_2352_);
if (v_isSharedCheck_2421_ == 0)
{
v___x_2360_ = v_it_2352_;
v_isShared_2361_ = v_isSharedCheck_2421_;
goto v_resetjp_2359_;
}
else
{
lean_inc(v_searcher_2358_);
lean_inc(v_currPos_2357_);
lean_dec(v_it_2352_);
v___x_2360_ = lean_box(0);
v_isShared_2361_ = v_isSharedCheck_2421_;
goto v_resetjp_2359_;
}
v_resetjp_2359_:
{
lean_object* v___x_2362_; 
lean_inc_ref(v_s_2349_);
v___x_2362_ = lean_apply_2(v_inst_2348_, v_s_2349_, v_searcher_2358_);
switch(lean_obj_tag(v___x_2362_))
{
case 0:
{
lean_object* v_out_2363_; 
v_out_2363_ = lean_ctor_get(v___x_2362_, 1);
lean_inc(v_out_2363_);
if (lean_obj_tag(v_out_2363_) == 0)
{
lean_object* v_it_2364_; lean_object* v___x_2366_; 
lean_dec_ref_known(v_out_2363_, 2);
lean_dec_ref(v_s_2349_);
v_it_2364_ = lean_ctor_get(v___x_2362_, 0);
lean_inc(v_it_2364_);
lean_dec_ref_known(v___x_2362_, 2);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v_it_2364_);
v___x_2366_ = v___x_2360_;
goto v_reusejp_2365_;
}
else
{
lean_object* v_reuseFailAlloc_2370_; 
v_reuseFailAlloc_2370_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2370_, 0, v_currPos_2357_);
lean_ctor_set(v_reuseFailAlloc_2370_, 1, v_it_2364_);
v___x_2366_ = v_reuseFailAlloc_2370_;
goto v_reusejp_2365_;
}
v_reusejp_2365_:
{
lean_object* v___x_2367_; lean_object* v___x_2368_; lean_object* v___x_2369_; 
v___x_2367_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2367_, 0, v___x_2366_);
v___x_2368_ = lean_apply_2(v_toPure_2350_, lean_box(0), v___x_2367_);
v___x_2369_ = lean_apply_4(v_lift_2351_, lean_box(0), lean_box(0), v___f_2356_, v___x_2368_);
return v___x_2369_;
}
}
else
{
lean_object* v_it_2371_; lean_object* v___x_2373_; uint8_t v_isShared_2374_; uint8_t v_isSharedCheck_2386_; 
v_it_2371_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2386_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2386_ == 0)
{
lean_object* v_unused_2387_; 
v_unused_2387_ = lean_ctor_get(v___x_2362_, 1);
lean_dec(v_unused_2387_);
v___x_2373_ = v___x_2362_;
v_isShared_2374_ = v_isSharedCheck_2386_;
goto v_resetjp_2372_;
}
else
{
lean_inc(v_it_2371_);
lean_dec(v___x_2362_);
v___x_2373_ = lean_box(0);
v_isShared_2374_ = v_isSharedCheck_2386_;
goto v_resetjp_2372_;
}
v_resetjp_2372_:
{
lean_object* v_startPos_2375_; lean_object* v_endPos_2376_; lean_object* v_slice_2377_; lean_object* v_nextIt_2379_; 
v_startPos_2375_ = lean_ctor_get(v_out_2363_, 0);
lean_inc(v_startPos_2375_);
v_endPos_2376_ = lean_ctor_get(v_out_2363_, 1);
lean_inc(v_endPos_2376_);
lean_dec_ref_known(v_out_2363_, 2);
v_slice_2377_ = l_String_Slice_slice_x21(v_s_2349_, v_endPos_2376_, v_currPos_2357_);
lean_dec(v_currPos_2357_);
lean_dec(v_endPos_2376_);
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v_it_2371_);
lean_ctor_set(v___x_2360_, 0, v_startPos_2375_);
v_nextIt_2379_ = v___x_2360_;
goto v_reusejp_2378_;
}
else
{
lean_object* v_reuseFailAlloc_2385_; 
v_reuseFailAlloc_2385_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2385_, 0, v_startPos_2375_);
lean_ctor_set(v_reuseFailAlloc_2385_, 1, v_it_2371_);
v_nextIt_2379_ = v_reuseFailAlloc_2385_;
goto v_reusejp_2378_;
}
v_reusejp_2378_:
{
lean_object* v___x_2381_; 
if (v_isShared_2374_ == 0)
{
lean_ctor_set(v___x_2373_, 1, v_slice_2377_);
lean_ctor_set(v___x_2373_, 0, v_nextIt_2379_);
v___x_2381_ = v___x_2373_;
goto v_reusejp_2380_;
}
else
{
lean_object* v_reuseFailAlloc_2384_; 
v_reuseFailAlloc_2384_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2384_, 0, v_nextIt_2379_);
lean_ctor_set(v_reuseFailAlloc_2384_, 1, v_slice_2377_);
v___x_2381_ = v_reuseFailAlloc_2384_;
goto v_reusejp_2380_;
}
v_reusejp_2380_:
{
lean_object* v___x_2382_; lean_object* v___x_2383_; 
v___x_2382_ = lean_apply_2(v_toPure_2350_, lean_box(0), v___x_2381_);
v___x_2383_ = lean_apply_4(v_lift_2351_, lean_box(0), lean_box(0), v___f_2356_, v___x_2382_);
return v___x_2383_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2388_; lean_object* v___x_2390_; uint8_t v_isShared_2391_; uint8_t v_isSharedCheck_2400_; 
lean_dec_ref(v_s_2349_);
v_it_2388_ = lean_ctor_get(v___x_2362_, 0);
v_isSharedCheck_2400_ = !lean_is_exclusive(v___x_2362_);
if (v_isSharedCheck_2400_ == 0)
{
v___x_2390_ = v___x_2362_;
v_isShared_2391_ = v_isSharedCheck_2400_;
goto v_resetjp_2389_;
}
else
{
lean_inc(v_it_2388_);
lean_dec(v___x_2362_);
v___x_2390_ = lean_box(0);
v_isShared_2391_ = v_isSharedCheck_2400_;
goto v_resetjp_2389_;
}
v_resetjp_2389_:
{
lean_object* v___x_2393_; 
if (v_isShared_2361_ == 0)
{
lean_ctor_set(v___x_2360_, 1, v_it_2388_);
v___x_2393_ = v___x_2360_;
goto v_reusejp_2392_;
}
else
{
lean_object* v_reuseFailAlloc_2399_; 
v_reuseFailAlloc_2399_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2399_, 0, v_currPos_2357_);
lean_ctor_set(v_reuseFailAlloc_2399_, 1, v_it_2388_);
v___x_2393_ = v_reuseFailAlloc_2399_;
goto v_reusejp_2392_;
}
v_reusejp_2392_:
{
lean_object* v___x_2395_; 
if (v_isShared_2391_ == 0)
{
lean_ctor_set(v___x_2390_, 0, v___x_2393_);
v___x_2395_ = v___x_2390_;
goto v_reusejp_2394_;
}
else
{
lean_object* v_reuseFailAlloc_2398_; 
v_reuseFailAlloc_2398_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2398_, 0, v___x_2393_);
v___x_2395_ = v_reuseFailAlloc_2398_;
goto v_reusejp_2394_;
}
v_reusejp_2394_:
{
lean_object* v___x_2396_; lean_object* v___x_2397_; 
v___x_2396_ = lean_apply_2(v_toPure_2350_, lean_box(0), v___x_2395_);
v___x_2397_ = lean_apply_4(v_lift_2351_, lean_box(0), lean_box(0), v___f_2356_, v___x_2396_);
return v___x_2397_;
}
}
}
}
default: 
{
lean_object* v___x_2401_; uint8_t v_decide_2402_; 
lean_del_object(v___x_2360_);
v___x_2401_ = lean_unsigned_to_nat(0u);
v_decide_2402_ = lean_nat_dec_eq(v_currPos_2357_, v___x_2401_);
if (v_decide_2402_ == 0)
{
lean_object* v_str_2403_; lean_object* v_startInclusive_2404_; lean_object* v___x_2406_; uint8_t v_isShared_2407_; uint8_t v_isSharedCheck_2416_; 
v_str_2403_ = lean_ctor_get(v_s_2349_, 0);
v_startInclusive_2404_ = lean_ctor_get(v_s_2349_, 1);
v_isSharedCheck_2416_ = !lean_is_exclusive(v_s_2349_);
if (v_isSharedCheck_2416_ == 0)
{
lean_object* v_unused_2417_; 
v_unused_2417_ = lean_ctor_get(v_s_2349_, 2);
lean_dec(v_unused_2417_);
v___x_2406_ = v_s_2349_;
v_isShared_2407_ = v_isSharedCheck_2416_;
goto v_resetjp_2405_;
}
else
{
lean_inc(v_startInclusive_2404_);
lean_inc(v_str_2403_);
lean_dec(v_s_2349_);
v___x_2406_ = lean_box(0);
v_isShared_2407_ = v_isSharedCheck_2416_;
goto v_resetjp_2405_;
}
v_resetjp_2405_:
{
lean_object* v___x_2408_; lean_object* v_slice_2410_; 
v___x_2408_ = lean_nat_add(v_startInclusive_2404_, v_currPos_2357_);
lean_dec(v_currPos_2357_);
if (v_isShared_2407_ == 0)
{
lean_ctor_set(v___x_2406_, 2, v___x_2408_);
v_slice_2410_ = v___x_2406_;
goto v_reusejp_2409_;
}
else
{
lean_object* v_reuseFailAlloc_2415_; 
v_reuseFailAlloc_2415_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2415_, 0, v_str_2403_);
lean_ctor_set(v_reuseFailAlloc_2415_, 1, v_startInclusive_2404_);
lean_ctor_set(v_reuseFailAlloc_2415_, 2, v___x_2408_);
v_slice_2410_ = v_reuseFailAlloc_2415_;
goto v_reusejp_2409_;
}
v_reusejp_2409_:
{
lean_object* v___x_2411_; lean_object* v___x_2412_; lean_object* v___x_2413_; lean_object* v___x_2414_; 
v___x_2411_ = lean_box(1);
v___x_2412_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2412_, 0, v___x_2411_);
lean_ctor_set(v___x_2412_, 1, v_slice_2410_);
v___x_2413_ = lean_apply_2(v_toPure_2350_, lean_box(0), v___x_2412_);
v___x_2414_ = lean_apply_4(v_lift_2351_, lean_box(0), lean_box(0), v___f_2356_, v___x_2413_);
return v___x_2414_;
}
}
}
else
{
lean_object* v___x_2418_; lean_object* v___x_2419_; lean_object* v___x_2420_; 
lean_dec(v_currPos_2357_);
lean_dec_ref(v_s_2349_);
v___x_2418_ = lean_box(2);
v___x_2419_ = lean_apply_2(v_toPure_2350_, lean_box(0), v___x_2418_);
v___x_2420_ = lean_apply_4(v_lift_2351_, lean_box(0), lean_box(0), v___f_2356_, v___x_2419_);
return v___x_2420_;
}
}
}
}
}
else
{
lean_object* v___x_2422_; lean_object* v___x_2423_; lean_object* v___x_2424_; 
lean_dec_ref(v_s_2349_);
lean_dec(v_inst_2348_);
v___x_2422_ = lean_box(2);
v___x_2423_ = lean_apply_2(v_toPure_2350_, lean_box(0), v___x_2422_);
v___x_2424_ = lean_apply_4(v_lift_2351_, lean_box(0), lean_box(0), v___f_2356_, v___x_2423_);
return v___x_2424_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object* v_inst_2425_, lean_object* v_inst_2426_, lean_object* v_s_2427_, lean_object* v_toPure_2428_, lean_object* v_lift_2429_, lean_object* v_00_u03b3_2430_, lean_object* v_Pl_2431_, lean_object* v_it_2432_, lean_object* v_init_2433_, lean_object* v___y_2434_){
_start:
{
lean_object* v_toApplicative_2435_; lean_object* v_toBind_2436_; lean_object* v_toPure_2437_; lean_object* v___f_2438_; lean_object* v___x_2439_; 
v_toApplicative_2435_ = lean_ctor_get(v_inst_2425_, 0);
lean_inc_ref(v_toApplicative_2435_);
v_toBind_2436_ = lean_ctor_get(v_inst_2425_, 1);
lean_inc(v_toBind_2436_);
lean_dec_ref(v_inst_2425_);
v_toPure_2437_ = lean_ctor_get(v_toApplicative_2435_, 1);
lean_inc(v_toPure_2437_);
lean_dec_ref(v_toApplicative_2435_);
v___f_2438_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2), 11, 7);
lean_closure_set(v___f_2438_, 0, v_toPure_2437_);
lean_closure_set(v___f_2438_, 1, v___y_2434_);
lean_closure_set(v___f_2438_, 2, v_toBind_2436_);
lean_closure_set(v___f_2438_, 3, v_inst_2426_);
lean_closure_set(v___f_2438_, 4, v_s_2427_);
lean_closure_set(v___f_2438_, 5, v_toPure_2428_);
lean_closure_set(v___f_2438_, 6, v_lift_2429_);
v___x_2439_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2438_, v_it_2432_, v_init_2433_, lean_box(0));
return v___x_2439_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(lean_object* v_inst_2440_, lean_object* v_s_2441_, lean_object* v_inst_2442_, lean_object* v_inst_2443_){
_start:
{
lean_object* v_toApplicative_2444_; lean_object* v_toPure_2445_; lean_object* v___f_2446_; 
v_toApplicative_2444_ = lean_ctor_get(v_inst_2442_, 0);
lean_inc_ref(v_toApplicative_2444_);
lean_dec_ref(v_inst_2442_);
v_toPure_2445_ = lean_ctor_get(v_toApplicative_2444_, 1);
lean_inc(v_toPure_2445_);
lean_dec_ref(v_toApplicative_2444_);
v___f_2446_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3), 10, 4);
lean_closure_set(v___f_2446_, 0, v_inst_2443_);
lean_closure_set(v___f_2446_, 1, v_inst_2440_);
lean_closure_set(v___f_2446_, 2, v_s_2441_);
lean_closure_set(v___f_2446_, 3, v_toPure_2445_);
return v___f_2446_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(lean_object* v_00_u03c1_2447_, lean_object* v_00_u03c1_2448_, lean_object* v_00_u03c3_2449_, lean_object* v_inst_2450_, lean_object* v_inst_2451_, lean_object* v_m_2452_, lean_object* v_n_2453_, lean_object* v_s_2454_, lean_object* v_inst_2455_, lean_object* v_inst_2456_){
_start:
{
lean_object* v___x_2457_; 
v___x_2457_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(v_inst_2450_, v_s_2454_, v_inst_2455_, v_inst_2456_);
return v___x_2457_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___boxed(lean_object* v_00_u03c1_2458_, lean_object* v_00_u03c1_2459_, lean_object* v_00_u03c3_2460_, lean_object* v_inst_2461_, lean_object* v_inst_2462_, lean_object* v_m_2463_, lean_object* v_n_2464_, lean_object* v_s_2465_, lean_object* v_inst_2466_, lean_object* v_inst_2467_){
_start:
{
lean_object* v_res_2468_; 
v_res_2468_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(v_00_u03c1_2458_, v_00_u03c1_2459_, v_00_u03c3_2460_, v_inst_2461_, v_inst_2462_, v_m_2463_, v_n_2464_, v_s_2465_, v_inst_2466_, v_inst_2467_);
lean_dec(v_inst_2462_);
lean_dec(v_00_u03c1_2459_);
return v_res_2468_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___redArg(lean_object* v_s_2469_, lean_object* v_inst_2470_){
_start:
{
lean_object* v_startInclusive_2471_; lean_object* v_endExclusive_2472_; lean_object* v___x_2473_; lean_object* v___x_2474_; lean_object* v___x_2475_; 
v_startInclusive_2471_ = lean_ctor_get(v_s_2469_, 1);
v_endExclusive_2472_ = lean_ctor_get(v_s_2469_, 2);
v___x_2473_ = lean_nat_sub(v_endExclusive_2472_, v_startInclusive_2471_);
v___x_2474_ = lean_apply_1(v_inst_2470_, v_s_2469_);
v___x_2475_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2475_, 0, v___x_2473_);
lean_ctor_set(v___x_2475_, 1, v___x_2474_);
return v___x_2475_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit(lean_object* v_00_u03c3_2476_, lean_object* v_00_u03c1_2477_, lean_object* v_s_2478_, lean_object* v_pat_2479_, lean_object* v_inst_2480_){
_start:
{
lean_object* v___x_2481_; 
v___x_2481_ = l_String_Slice_revSplit___redArg(v_s_2478_, v_inst_2480_);
return v___x_2481_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___boxed(lean_object* v_00_u03c3_2482_, lean_object* v_00_u03c1_2483_, lean_object* v_s_2484_, lean_object* v_pat_2485_, lean_object* v_inst_2486_){
_start:
{
lean_object* v_res_2487_; 
v_res_2487_ = l_String_Slice_revSplit(v_00_u03c3_2482_, v_00_u03c1_2483_, v_s_2484_, v_pat_2485_, v_inst_2486_);
lean_dec(v_pat_2485_);
return v_res_2487_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___redArg(lean_object* v_s_2488_, lean_object* v_inst_2489_){
_start:
{
lean_object* v_skipSuffix_x3f_2490_; lean_object* v___x_2491_; 
v_skipSuffix_x3f_2490_ = lean_ctor_get(v_inst_2489_, 0);
lean_inc_ref(v_skipSuffix_x3f_2490_);
lean_dec_ref(v_inst_2489_);
v___x_2491_ = lean_apply_1(v_skipSuffix_x3f_2490_, v_s_2488_);
return v___x_2491_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f(lean_object* v_00_u03c1_2492_, lean_object* v_s_2493_, lean_object* v_pat_2494_, lean_object* v_inst_2495_){
_start:
{
lean_object* v_skipSuffix_x3f_2496_; lean_object* v___x_2497_; 
v_skipSuffix_x3f_2496_ = lean_ctor_get(v_inst_2495_, 0);
lean_inc_ref(v_skipSuffix_x3f_2496_);
lean_dec_ref(v_inst_2495_);
v___x_2497_ = lean_apply_1(v_skipSuffix_x3f_2496_, v_s_2493_);
return v___x_2497_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___boxed(lean_object* v_00_u03c1_2498_, lean_object* v_s_2499_, lean_object* v_pat_2500_, lean_object* v_inst_2501_){
_start:
{
lean_object* v_res_2502_; 
v_res_2502_ = l_String_Slice_skipSuffix_x3f(v_00_u03c1_2498_, v_s_2499_, v_pat_2500_, v_inst_2501_);
lean_dec(v_pat_2500_);
return v_res_2502_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg(lean_object* v_s_2503_, lean_object* v_pos_2504_, lean_object* v_inst_2505_){
_start:
{
lean_object* v_str_2506_; lean_object* v_startInclusive_2507_; lean_object* v___x_2509_; uint8_t v_isShared_2510_; uint8_t v_isSharedCheck_2525_; 
v_str_2506_ = lean_ctor_get(v_s_2503_, 0);
v_startInclusive_2507_ = lean_ctor_get(v_s_2503_, 1);
v_isSharedCheck_2525_ = !lean_is_exclusive(v_s_2503_);
if (v_isSharedCheck_2525_ == 0)
{
lean_object* v_unused_2526_; 
v_unused_2526_ = lean_ctor_get(v_s_2503_, 2);
lean_dec(v_unused_2526_);
v___x_2509_ = v_s_2503_;
v_isShared_2510_ = v_isSharedCheck_2525_;
goto v_resetjp_2508_;
}
else
{
lean_inc(v_startInclusive_2507_);
lean_inc(v_str_2506_);
lean_dec(v_s_2503_);
v___x_2509_ = lean_box(0);
v_isShared_2510_ = v_isSharedCheck_2525_;
goto v_resetjp_2508_;
}
v_resetjp_2508_:
{
lean_object* v_skipSuffix_x3f_2511_; lean_object* v___x_2512_; lean_object* v___x_2514_; 
v_skipSuffix_x3f_2511_ = lean_ctor_get(v_inst_2505_, 0);
lean_inc_ref(v_skipSuffix_x3f_2511_);
lean_dec_ref(v_inst_2505_);
v___x_2512_ = lean_nat_add(v_startInclusive_2507_, v_pos_2504_);
if (v_isShared_2510_ == 0)
{
lean_ctor_set(v___x_2509_, 2, v___x_2512_);
v___x_2514_ = v___x_2509_;
goto v_reusejp_2513_;
}
else
{
lean_object* v_reuseFailAlloc_2524_; 
v_reuseFailAlloc_2524_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2524_, 0, v_str_2506_);
lean_ctor_set(v_reuseFailAlloc_2524_, 1, v_startInclusive_2507_);
lean_ctor_set(v_reuseFailAlloc_2524_, 2, v___x_2512_);
v___x_2514_ = v_reuseFailAlloc_2524_;
goto v_reusejp_2513_;
}
v_reusejp_2513_:
{
lean_object* v___x_2515_; 
v___x_2515_ = lean_apply_1(v_skipSuffix_x3f_2511_, v___x_2514_);
if (lean_obj_tag(v___x_2515_) == 0)
{
return v___x_2515_;
}
else
{
lean_object* v_val_2516_; lean_object* v___x_2518_; uint8_t v_isShared_2519_; uint8_t v_isSharedCheck_2523_; 
v_val_2516_ = lean_ctor_get(v___x_2515_, 0);
v_isSharedCheck_2523_ = !lean_is_exclusive(v___x_2515_);
if (v_isSharedCheck_2523_ == 0)
{
v___x_2518_ = v___x_2515_;
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
else
{
lean_inc(v_val_2516_);
lean_dec(v___x_2515_);
v___x_2518_ = lean_box(0);
v_isShared_2519_ = v_isSharedCheck_2523_;
goto v_resetjp_2517_;
}
v_resetjp_2517_:
{
lean_object* v___x_2521_; 
if (v_isShared_2519_ == 0)
{
v___x_2521_ = v___x_2518_;
goto v_reusejp_2520_;
}
else
{
lean_object* v_reuseFailAlloc_2522_; 
v_reuseFailAlloc_2522_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2522_, 0, v_val_2516_);
v___x_2521_ = v_reuseFailAlloc_2522_;
goto v_reusejp_2520_;
}
v_reusejp_2520_:
{
return v___x_2521_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg___boxed(lean_object* v_s_2527_, lean_object* v_pos_2528_, lean_object* v_inst_2529_){
_start:
{
lean_object* v_res_2530_; 
v_res_2530_ = l_String_Slice_Pos_revSkip_x3f___redArg(v_s_2527_, v_pos_2528_, v_inst_2529_);
lean_dec(v_pos_2528_);
return v_res_2530_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f(lean_object* v_00_u03c1_2531_, lean_object* v_s_2532_, lean_object* v_pos_2533_, lean_object* v_pat_2534_, lean_object* v_inst_2535_){
_start:
{
lean_object* v_str_2536_; lean_object* v_startInclusive_2537_; lean_object* v___x_2539_; uint8_t v_isShared_2540_; uint8_t v_isSharedCheck_2555_; 
v_str_2536_ = lean_ctor_get(v_s_2532_, 0);
v_startInclusive_2537_ = lean_ctor_get(v_s_2532_, 1);
v_isSharedCheck_2555_ = !lean_is_exclusive(v_s_2532_);
if (v_isSharedCheck_2555_ == 0)
{
lean_object* v_unused_2556_; 
v_unused_2556_ = lean_ctor_get(v_s_2532_, 2);
lean_dec(v_unused_2556_);
v___x_2539_ = v_s_2532_;
v_isShared_2540_ = v_isSharedCheck_2555_;
goto v_resetjp_2538_;
}
else
{
lean_inc(v_startInclusive_2537_);
lean_inc(v_str_2536_);
lean_dec(v_s_2532_);
v___x_2539_ = lean_box(0);
v_isShared_2540_ = v_isSharedCheck_2555_;
goto v_resetjp_2538_;
}
v_resetjp_2538_:
{
lean_object* v_skipSuffix_x3f_2541_; lean_object* v___x_2542_; lean_object* v___x_2544_; 
v_skipSuffix_x3f_2541_ = lean_ctor_get(v_inst_2535_, 0);
lean_inc_ref(v_skipSuffix_x3f_2541_);
lean_dec_ref(v_inst_2535_);
v___x_2542_ = lean_nat_add(v_startInclusive_2537_, v_pos_2533_);
if (v_isShared_2540_ == 0)
{
lean_ctor_set(v___x_2539_, 2, v___x_2542_);
v___x_2544_ = v___x_2539_;
goto v_reusejp_2543_;
}
else
{
lean_object* v_reuseFailAlloc_2554_; 
v_reuseFailAlloc_2554_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2554_, 0, v_str_2536_);
lean_ctor_set(v_reuseFailAlloc_2554_, 1, v_startInclusive_2537_);
lean_ctor_set(v_reuseFailAlloc_2554_, 2, v___x_2542_);
v___x_2544_ = v_reuseFailAlloc_2554_;
goto v_reusejp_2543_;
}
v_reusejp_2543_:
{
lean_object* v___x_2545_; 
v___x_2545_ = lean_apply_1(v_skipSuffix_x3f_2541_, v___x_2544_);
if (lean_obj_tag(v___x_2545_) == 0)
{
return v___x_2545_;
}
else
{
lean_object* v_val_2546_; lean_object* v___x_2548_; uint8_t v_isShared_2549_; uint8_t v_isSharedCheck_2553_; 
v_val_2546_ = lean_ctor_get(v___x_2545_, 0);
v_isSharedCheck_2553_ = !lean_is_exclusive(v___x_2545_);
if (v_isSharedCheck_2553_ == 0)
{
v___x_2548_ = v___x_2545_;
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
else
{
lean_inc(v_val_2546_);
lean_dec(v___x_2545_);
v___x_2548_ = lean_box(0);
v_isShared_2549_ = v_isSharedCheck_2553_;
goto v_resetjp_2547_;
}
v_resetjp_2547_:
{
lean_object* v___x_2551_; 
if (v_isShared_2549_ == 0)
{
v___x_2551_ = v___x_2548_;
goto v_reusejp_2550_;
}
else
{
lean_object* v_reuseFailAlloc_2552_; 
v_reuseFailAlloc_2552_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2552_, 0, v_val_2546_);
v___x_2551_ = v_reuseFailAlloc_2552_;
goto v_reusejp_2550_;
}
v_reusejp_2550_:
{
return v___x_2551_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_2557_, lean_object* v_s_2558_, lean_object* v_pos_2559_, lean_object* v_pat_2560_, lean_object* v_inst_2561_){
_start:
{
lean_object* v_res_2562_; 
v_res_2562_ = l_String_Slice_Pos_revSkip_x3f(v_00_u03c1_2557_, v_s_2558_, v_pos_2559_, v_pat_2560_, v_inst_2561_);
lean_dec(v_pat_2560_);
lean_dec(v_pos_2559_);
return v_res_2562_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___redArg(lean_object* v_s_2563_, lean_object* v_inst_2564_){
_start:
{
lean_object* v_skipSuffix_x3f_2565_; lean_object* v___x_2566_; 
v_skipSuffix_x3f_2565_ = lean_ctor_get(v_inst_2564_, 0);
lean_inc_ref(v_skipSuffix_x3f_2565_);
lean_dec_ref(v_inst_2564_);
lean_inc_ref(v_s_2563_);
v___x_2566_ = lean_apply_1(v_skipSuffix_x3f_2565_, v_s_2563_);
if (lean_obj_tag(v___x_2566_) == 0)
{
lean_object* v___x_2567_; 
lean_dec_ref(v_s_2563_);
v___x_2567_ = lean_box(0);
return v___x_2567_;
}
else
{
lean_object* v_val_2568_; lean_object* v___x_2570_; uint8_t v_isShared_2571_; uint8_t v_isSharedCheck_2586_; 
v_val_2568_ = lean_ctor_get(v___x_2566_, 0);
v_isSharedCheck_2586_ = !lean_is_exclusive(v___x_2566_);
if (v_isSharedCheck_2586_ == 0)
{
v___x_2570_ = v___x_2566_;
v_isShared_2571_ = v_isSharedCheck_2586_;
goto v_resetjp_2569_;
}
else
{
lean_inc(v_val_2568_);
lean_dec(v___x_2566_);
v___x_2570_ = lean_box(0);
v_isShared_2571_ = v_isSharedCheck_2586_;
goto v_resetjp_2569_;
}
v_resetjp_2569_:
{
lean_object* v_str_2572_; lean_object* v_startInclusive_2573_; lean_object* v___x_2575_; uint8_t v_isShared_2576_; uint8_t v_isSharedCheck_2584_; 
v_str_2572_ = lean_ctor_get(v_s_2563_, 0);
v_startInclusive_2573_ = lean_ctor_get(v_s_2563_, 1);
v_isSharedCheck_2584_ = !lean_is_exclusive(v_s_2563_);
if (v_isSharedCheck_2584_ == 0)
{
lean_object* v_unused_2585_; 
v_unused_2585_ = lean_ctor_get(v_s_2563_, 2);
lean_dec(v_unused_2585_);
v___x_2575_ = v_s_2563_;
v_isShared_2576_ = v_isSharedCheck_2584_;
goto v_resetjp_2574_;
}
else
{
lean_inc(v_startInclusive_2573_);
lean_inc(v_str_2572_);
lean_dec(v_s_2563_);
v___x_2575_ = lean_box(0);
v_isShared_2576_ = v_isSharedCheck_2584_;
goto v_resetjp_2574_;
}
v_resetjp_2574_:
{
lean_object* v___x_2577_; lean_object* v___x_2579_; 
v___x_2577_ = lean_nat_add(v_startInclusive_2573_, v_val_2568_);
lean_dec(v_val_2568_);
if (v_isShared_2576_ == 0)
{
lean_ctor_set(v___x_2575_, 2, v___x_2577_);
v___x_2579_ = v___x_2575_;
goto v_reusejp_2578_;
}
else
{
lean_object* v_reuseFailAlloc_2583_; 
v_reuseFailAlloc_2583_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2583_, 0, v_str_2572_);
lean_ctor_set(v_reuseFailAlloc_2583_, 1, v_startInclusive_2573_);
lean_ctor_set(v_reuseFailAlloc_2583_, 2, v___x_2577_);
v___x_2579_ = v_reuseFailAlloc_2583_;
goto v_reusejp_2578_;
}
v_reusejp_2578_:
{
lean_object* v___x_2581_; 
if (v_isShared_2571_ == 0)
{
lean_ctor_set(v___x_2570_, 0, v___x_2579_);
v___x_2581_ = v___x_2570_;
goto v_reusejp_2580_;
}
else
{
lean_object* v_reuseFailAlloc_2582_; 
v_reuseFailAlloc_2582_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2582_, 0, v___x_2579_);
v___x_2581_ = v_reuseFailAlloc_2582_;
goto v_reusejp_2580_;
}
v_reusejp_2580_:
{
return v___x_2581_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f(lean_object* v_00_u03c1_2587_, lean_object* v_s_2588_, lean_object* v_pat_2589_, lean_object* v_inst_2590_){
_start:
{
lean_object* v_skipSuffix_x3f_2591_; lean_object* v___x_2592_; 
v_skipSuffix_x3f_2591_ = lean_ctor_get(v_inst_2590_, 0);
lean_inc_ref(v_skipSuffix_x3f_2591_);
lean_dec_ref(v_inst_2590_);
lean_inc_ref(v_s_2588_);
v___x_2592_ = lean_apply_1(v_skipSuffix_x3f_2591_, v_s_2588_);
if (lean_obj_tag(v___x_2592_) == 0)
{
lean_object* v___x_2593_; 
lean_dec_ref(v_s_2588_);
v___x_2593_ = lean_box(0);
return v___x_2593_;
}
else
{
lean_object* v_val_2594_; lean_object* v___x_2596_; uint8_t v_isShared_2597_; uint8_t v_isSharedCheck_2612_; 
v_val_2594_ = lean_ctor_get(v___x_2592_, 0);
v_isSharedCheck_2612_ = !lean_is_exclusive(v___x_2592_);
if (v_isSharedCheck_2612_ == 0)
{
v___x_2596_ = v___x_2592_;
v_isShared_2597_ = v_isSharedCheck_2612_;
goto v_resetjp_2595_;
}
else
{
lean_inc(v_val_2594_);
lean_dec(v___x_2592_);
v___x_2596_ = lean_box(0);
v_isShared_2597_ = v_isSharedCheck_2612_;
goto v_resetjp_2595_;
}
v_resetjp_2595_:
{
lean_object* v_str_2598_; lean_object* v_startInclusive_2599_; lean_object* v___x_2601_; uint8_t v_isShared_2602_; uint8_t v_isSharedCheck_2610_; 
v_str_2598_ = lean_ctor_get(v_s_2588_, 0);
v_startInclusive_2599_ = lean_ctor_get(v_s_2588_, 1);
v_isSharedCheck_2610_ = !lean_is_exclusive(v_s_2588_);
if (v_isSharedCheck_2610_ == 0)
{
lean_object* v_unused_2611_; 
v_unused_2611_ = lean_ctor_get(v_s_2588_, 2);
lean_dec(v_unused_2611_);
v___x_2601_ = v_s_2588_;
v_isShared_2602_ = v_isSharedCheck_2610_;
goto v_resetjp_2600_;
}
else
{
lean_inc(v_startInclusive_2599_);
lean_inc(v_str_2598_);
lean_dec(v_s_2588_);
v___x_2601_ = lean_box(0);
v_isShared_2602_ = v_isSharedCheck_2610_;
goto v_resetjp_2600_;
}
v_resetjp_2600_:
{
lean_object* v___x_2603_; lean_object* v___x_2605_; 
v___x_2603_ = lean_nat_add(v_startInclusive_2599_, v_val_2594_);
lean_dec(v_val_2594_);
if (v_isShared_2602_ == 0)
{
lean_ctor_set(v___x_2601_, 2, v___x_2603_);
v___x_2605_ = v___x_2601_;
goto v_reusejp_2604_;
}
else
{
lean_object* v_reuseFailAlloc_2609_; 
v_reuseFailAlloc_2609_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2609_, 0, v_str_2598_);
lean_ctor_set(v_reuseFailAlloc_2609_, 1, v_startInclusive_2599_);
lean_ctor_set(v_reuseFailAlloc_2609_, 2, v___x_2603_);
v___x_2605_ = v_reuseFailAlloc_2609_;
goto v_reusejp_2604_;
}
v_reusejp_2604_:
{
lean_object* v___x_2607_; 
if (v_isShared_2597_ == 0)
{
lean_ctor_set(v___x_2596_, 0, v___x_2605_);
v___x_2607_ = v___x_2596_;
goto v_reusejp_2606_;
}
else
{
lean_object* v_reuseFailAlloc_2608_; 
v_reuseFailAlloc_2608_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2608_, 0, v___x_2605_);
v___x_2607_ = v_reuseFailAlloc_2608_;
goto v_reusejp_2606_;
}
v_reusejp_2606_:
{
return v___x_2607_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_2613_, lean_object* v_s_2614_, lean_object* v_pat_2615_, lean_object* v_inst_2616_){
_start:
{
lean_object* v_res_2617_; 
v_res_2617_ = l_String_Slice_dropSuffix_x3f(v_00_u03c1_2613_, v_s_2614_, v_pat_2615_, v_inst_2616_);
lean_dec(v_pat_2615_);
return v_res_2617_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___redArg(lean_object* v_s_2618_, lean_object* v_inst_2619_){
_start:
{
lean_object* v_skipSuffix_x3f_2620_; lean_object* v___x_2621_; 
v_skipSuffix_x3f_2620_ = lean_ctor_get(v_inst_2619_, 0);
lean_inc_ref(v_skipSuffix_x3f_2620_);
lean_dec_ref(v_inst_2619_);
lean_inc_ref(v_s_2618_);
v___x_2621_ = lean_apply_1(v_skipSuffix_x3f_2620_, v_s_2618_);
if (lean_obj_tag(v___x_2621_) == 0)
{
return v_s_2618_;
}
else
{
lean_object* v_val_2622_; lean_object* v_str_2623_; lean_object* v_startInclusive_2624_; lean_object* v___x_2626_; uint8_t v_isShared_2627_; uint8_t v_isSharedCheck_2632_; 
v_val_2622_ = lean_ctor_get(v___x_2621_, 0);
lean_inc(v_val_2622_);
lean_dec_ref_known(v___x_2621_, 1);
v_str_2623_ = lean_ctor_get(v_s_2618_, 0);
v_startInclusive_2624_ = lean_ctor_get(v_s_2618_, 1);
v_isSharedCheck_2632_ = !lean_is_exclusive(v_s_2618_);
if (v_isSharedCheck_2632_ == 0)
{
lean_object* v_unused_2633_; 
v_unused_2633_ = lean_ctor_get(v_s_2618_, 2);
lean_dec(v_unused_2633_);
v___x_2626_ = v_s_2618_;
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
else
{
lean_inc(v_startInclusive_2624_);
lean_inc(v_str_2623_);
lean_dec(v_s_2618_);
v___x_2626_ = lean_box(0);
v_isShared_2627_ = v_isSharedCheck_2632_;
goto v_resetjp_2625_;
}
v_resetjp_2625_:
{
lean_object* v___x_2628_; lean_object* v___x_2630_; 
v___x_2628_ = lean_nat_add(v_startInclusive_2624_, v_val_2622_);
lean_dec(v_val_2622_);
if (v_isShared_2627_ == 0)
{
lean_ctor_set(v___x_2626_, 2, v___x_2628_);
v___x_2630_ = v___x_2626_;
goto v_reusejp_2629_;
}
else
{
lean_object* v_reuseFailAlloc_2631_; 
v_reuseFailAlloc_2631_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2631_, 0, v_str_2623_);
lean_ctor_set(v_reuseFailAlloc_2631_, 1, v_startInclusive_2624_);
lean_ctor_set(v_reuseFailAlloc_2631_, 2, v___x_2628_);
v___x_2630_ = v_reuseFailAlloc_2631_;
goto v_reusejp_2629_;
}
v_reusejp_2629_:
{
return v___x_2630_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix(lean_object* v_00_u03c1_2634_, lean_object* v_s_2635_, lean_object* v_pat_2636_, lean_object* v_inst_2637_){
_start:
{
lean_object* v___x_2638_; 
v___x_2638_ = l_String_Slice_dropSuffix___redArg(v_s_2635_, v_inst_2637_);
return v___x_2638_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___boxed(lean_object* v_00_u03c1_2639_, lean_object* v_s_2640_, lean_object* v_pat_2641_, lean_object* v_inst_2642_){
_start:
{
lean_object* v_res_2643_; 
v_res_2643_ = l_String_Slice_dropSuffix(v_00_u03c1_2639_, v_s_2640_, v_pat_2641_, v_inst_2642_);
lean_dec(v_pat_2641_);
return v_res_2643_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object* v_s_2644_, lean_object* v_n_2645_){
_start:
{
lean_object* v_str_2646_; lean_object* v_startInclusive_2647_; lean_object* v_endExclusive_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2652_; uint8_t v_isShared_2653_; uint8_t v_isSharedCheck_2658_; 
v_str_2646_ = lean_ctor_get(v_s_2644_, 0);
lean_inc_ref(v_str_2646_);
v_startInclusive_2647_ = lean_ctor_get(v_s_2644_, 1);
lean_inc(v_startInclusive_2647_);
v_endExclusive_2648_ = lean_ctor_get(v_s_2644_, 2);
v___x_2649_ = lean_nat_sub(v_endExclusive_2648_, v_startInclusive_2647_);
v___x_2650_ = l_String_Slice_Pos_prevn(v_s_2644_, v___x_2649_, v_n_2645_);
v_isSharedCheck_2658_ = !lean_is_exclusive(v_s_2644_);
if (v_isSharedCheck_2658_ == 0)
{
lean_object* v_unused_2659_; lean_object* v_unused_2660_; lean_object* v_unused_2661_; 
v_unused_2659_ = lean_ctor_get(v_s_2644_, 2);
lean_dec(v_unused_2659_);
v_unused_2660_ = lean_ctor_get(v_s_2644_, 1);
lean_dec(v_unused_2660_);
v_unused_2661_ = lean_ctor_get(v_s_2644_, 0);
lean_dec(v_unused_2661_);
v___x_2652_ = v_s_2644_;
v_isShared_2653_ = v_isSharedCheck_2658_;
goto v_resetjp_2651_;
}
else
{
lean_dec(v_s_2644_);
v___x_2652_ = lean_box(0);
v_isShared_2653_ = v_isSharedCheck_2658_;
goto v_resetjp_2651_;
}
v_resetjp_2651_:
{
lean_object* v___x_2654_; lean_object* v___x_2656_; 
v___x_2654_ = lean_nat_add(v_startInclusive_2647_, v___x_2650_);
lean_dec(v___x_2650_);
if (v_isShared_2653_ == 0)
{
lean_ctor_set(v___x_2652_, 2, v___x_2654_);
v___x_2656_ = v___x_2652_;
goto v_reusejp_2655_;
}
else
{
lean_object* v_reuseFailAlloc_2657_; 
v_reuseFailAlloc_2657_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2657_, 0, v_str_2646_);
lean_ctor_set(v_reuseFailAlloc_2657_, 1, v_startInclusive_2647_);
lean_ctor_set(v_reuseFailAlloc_2657_, 2, v___x_2654_);
v___x_2656_ = v_reuseFailAlloc_2657_;
goto v_reusejp_2655_;
}
v_reusejp_2655_:
{
return v___x_2656_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object* v_s_2662_, lean_object* v_pos_2663_, lean_object* v_inst_2664_){
_start:
{
lean_object* v_str_2665_; lean_object* v_startInclusive_2666_; lean_object* v_skipSuffix_x3f_2667_; lean_object* v___x_2668_; lean_object* v___x_2669_; lean_object* v___x_2670_; 
v_str_2665_ = lean_ctor_get(v_s_2662_, 0);
v_startInclusive_2666_ = lean_ctor_get(v_s_2662_, 1);
v_skipSuffix_x3f_2667_ = lean_ctor_get(v_inst_2664_, 0);
v___x_2668_ = lean_nat_add(v_startInclusive_2666_, v_pos_2663_);
lean_inc(v_startInclusive_2666_);
lean_inc_ref(v_str_2665_);
v___x_2669_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2669_, 0, v_str_2665_);
lean_ctor_set(v___x_2669_, 1, v_startInclusive_2666_);
lean_ctor_set(v___x_2669_, 2, v___x_2668_);
lean_inc_ref(v_skipSuffix_x3f_2667_);
v___x_2670_ = lean_apply_1(v_skipSuffix_x3f_2667_, v___x_2669_);
if (lean_obj_tag(v___x_2670_) == 0)
{
lean_dec_ref(v_inst_2664_);
return v_pos_2663_;
}
else
{
lean_object* v_val_2671_; lean_object* v___x_2672_; lean_object* v___x_2673_; uint8_t v___x_2674_; 
v_val_2671_ = lean_ctor_get(v___x_2670_, 0);
lean_inc(v_val_2671_);
lean_dec_ref_known(v___x_2670_, 1);
v___x_2672_ = lean_unsigned_to_nat(1u);
v___x_2673_ = lean_nat_add(v_val_2671_, v___x_2672_);
v___x_2674_ = lean_nat_dec_le(v___x_2673_, v_pos_2663_);
lean_dec(v___x_2673_);
if (v___x_2674_ == 0)
{
lean_dec(v_val_2671_);
lean_dec_ref(v_inst_2664_);
return v_pos_2663_;
}
else
{
lean_dec(v_pos_2663_);
v_pos_2663_ = v_val_2671_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg___boxed(lean_object* v_s_2676_, lean_object* v_pos_2677_, lean_object* v_inst_2678_){
_start:
{
lean_object* v_res_2679_; 
v_res_2679_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2676_, v_pos_2677_, v_inst_2678_);
lean_dec_ref(v_s_2676_);
return v_res_2679_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile(lean_object* v_00_u03c1_2680_, lean_object* v_s_2681_, lean_object* v_pos_2682_, lean_object* v_pat_2683_, lean_object* v_inst_2684_){
_start:
{
lean_object* v___x_2685_; 
v___x_2685_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2681_, v_pos_2682_, v_inst_2684_);
return v___x_2685_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_2686_, lean_object* v_s_2687_, lean_object* v_pos_2688_, lean_object* v_pat_2689_, lean_object* v_inst_2690_){
_start:
{
lean_object* v_res_2691_; 
v_res_2691_ = l_String_Slice_Pos_revSkipWhile(v_00_u03c1_2686_, v_s_2687_, v_pos_2688_, v_pat_2689_, v_inst_2690_);
lean_dec(v_pat_2689_);
lean_dec_ref(v_s_2687_);
return v_res_2691_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg(lean_object* v_s_2692_, lean_object* v_inst_2693_){
_start:
{
lean_object* v_startInclusive_2694_; lean_object* v_endExclusive_2695_; lean_object* v___x_2696_; lean_object* v___x_2697_; 
v_startInclusive_2694_ = lean_ctor_get(v_s_2692_, 1);
v_endExclusive_2695_ = lean_ctor_get(v_s_2692_, 2);
v___x_2696_ = lean_nat_sub(v_endExclusive_2695_, v_startInclusive_2694_);
v___x_2697_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2692_, v___x_2696_, v_inst_2693_);
return v___x_2697_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg___boxed(lean_object* v_s_2698_, lean_object* v_inst_2699_){
_start:
{
lean_object* v_res_2700_; 
v_res_2700_ = l_String_Slice_skipSuffixWhile___redArg(v_s_2698_, v_inst_2699_);
lean_dec_ref(v_s_2698_);
return v_res_2700_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile(lean_object* v_00_u03c1_2701_, lean_object* v_s_2702_, lean_object* v_pat_2703_, lean_object* v_inst_2704_){
_start:
{
lean_object* v_startInclusive_2705_; lean_object* v_endExclusive_2706_; lean_object* v___x_2707_; lean_object* v___x_2708_; 
v_startInclusive_2705_ = lean_ctor_get(v_s_2702_, 1);
v_endExclusive_2706_ = lean_ctor_get(v_s_2702_, 2);
v___x_2707_ = lean_nat_sub(v_endExclusive_2706_, v_startInclusive_2705_);
v___x_2708_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2702_, v___x_2707_, v_inst_2704_);
return v___x_2708_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___boxed(lean_object* v_00_u03c1_2709_, lean_object* v_s_2710_, lean_object* v_pat_2711_, lean_object* v_inst_2712_){
_start:
{
lean_object* v_res_2713_; 
v_res_2713_ = l_String_Slice_skipSuffixWhile(v_00_u03c1_2709_, v_s_2710_, v_pat_2711_, v_inst_2712_);
lean_dec(v_pat_2711_);
lean_dec_ref(v_s_2710_);
return v_res_2713_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_revAll___redArg(lean_object* v_s_2714_, lean_object* v_inst_2715_){
_start:
{
lean_object* v_startInclusive_2716_; lean_object* v_endExclusive_2717_; lean_object* v___x_2718_; lean_object* v___x_2719_; lean_object* v___x_2720_; uint8_t v_decide_2721_; 
v_startInclusive_2716_ = lean_ctor_get(v_s_2714_, 1);
v_endExclusive_2717_ = lean_ctor_get(v_s_2714_, 2);
v___x_2718_ = lean_nat_sub(v_endExclusive_2717_, v_startInclusive_2716_);
v___x_2719_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2714_, v___x_2718_, v_inst_2715_);
v___x_2720_ = lean_unsigned_to_nat(0u);
v_decide_2721_ = lean_nat_dec_eq(v___x_2719_, v___x_2720_);
lean_dec(v___x_2719_);
return v_decide_2721_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___redArg___boxed(lean_object* v_s_2722_, lean_object* v_inst_2723_){
_start:
{
uint8_t v_res_2724_; lean_object* v_r_2725_; 
v_res_2724_ = l_String_Slice_revAll___redArg(v_s_2722_, v_inst_2723_);
lean_dec_ref(v_s_2722_);
v_r_2725_ = lean_box(v_res_2724_);
return v_r_2725_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_revAll(lean_object* v_00_u03c1_2726_, lean_object* v_s_2727_, lean_object* v_pat_2728_, lean_object* v_inst_2729_){
_start:
{
lean_object* v_startInclusive_2730_; lean_object* v_endExclusive_2731_; lean_object* v___x_2732_; lean_object* v___x_2733_; lean_object* v___x_2734_; uint8_t v_decide_2735_; 
v_startInclusive_2730_ = lean_ctor_get(v_s_2727_, 1);
v_endExclusive_2731_ = lean_ctor_get(v_s_2727_, 2);
v___x_2732_ = lean_nat_sub(v_endExclusive_2731_, v_startInclusive_2730_);
v___x_2733_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2727_, v___x_2732_, v_inst_2729_);
v___x_2734_ = lean_unsigned_to_nat(0u);
v_decide_2735_ = lean_nat_dec_eq(v___x_2733_, v___x_2734_);
lean_dec(v___x_2733_);
return v_decide_2735_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___boxed(lean_object* v_00_u03c1_2736_, lean_object* v_s_2737_, lean_object* v_pat_2738_, lean_object* v_inst_2739_){
_start:
{
uint8_t v_res_2740_; lean_object* v_r_2741_; 
v_res_2740_ = l_String_Slice_revAll(v_00_u03c1_2736_, v_s_2737_, v_pat_2738_, v_inst_2739_);
lean_dec(v_pat_2738_);
lean_dec_ref(v_s_2737_);
v_r_2741_ = lean_box(v_res_2740_);
return v_r_2741_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object* v_s_2742_, lean_object* v_inst_2743_){
_start:
{
lean_object* v_str_2744_; lean_object* v_startInclusive_2745_; lean_object* v_endExclusive_2746_; lean_object* v___x_2747_; lean_object* v___x_2748_; lean_object* v___x_2750_; uint8_t v_isShared_2751_; uint8_t v_isSharedCheck_2756_; 
v_str_2744_ = lean_ctor_get(v_s_2742_, 0);
lean_inc_ref(v_str_2744_);
v_startInclusive_2745_ = lean_ctor_get(v_s_2742_, 1);
lean_inc(v_startInclusive_2745_);
v_endExclusive_2746_ = lean_ctor_get(v_s_2742_, 2);
v___x_2747_ = lean_nat_sub(v_endExclusive_2746_, v_startInclusive_2745_);
v___x_2748_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2742_, v___x_2747_, v_inst_2743_);
v_isSharedCheck_2756_ = !lean_is_exclusive(v_s_2742_);
if (v_isSharedCheck_2756_ == 0)
{
lean_object* v_unused_2757_; lean_object* v_unused_2758_; lean_object* v_unused_2759_; 
v_unused_2757_ = lean_ctor_get(v_s_2742_, 2);
lean_dec(v_unused_2757_);
v_unused_2758_ = lean_ctor_get(v_s_2742_, 1);
lean_dec(v_unused_2758_);
v_unused_2759_ = lean_ctor_get(v_s_2742_, 0);
lean_dec(v_unused_2759_);
v___x_2750_ = v_s_2742_;
v_isShared_2751_ = v_isSharedCheck_2756_;
goto v_resetjp_2749_;
}
else
{
lean_dec(v_s_2742_);
v___x_2750_ = lean_box(0);
v_isShared_2751_ = v_isSharedCheck_2756_;
goto v_resetjp_2749_;
}
v_resetjp_2749_:
{
lean_object* v___x_2752_; lean_object* v___x_2754_; 
v___x_2752_ = lean_nat_add(v_startInclusive_2745_, v___x_2748_);
lean_dec(v___x_2748_);
if (v_isShared_2751_ == 0)
{
lean_ctor_set(v___x_2750_, 2, v___x_2752_);
v___x_2754_ = v___x_2750_;
goto v_reusejp_2753_;
}
else
{
lean_object* v_reuseFailAlloc_2755_; 
v_reuseFailAlloc_2755_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2755_, 0, v_str_2744_);
lean_ctor_set(v_reuseFailAlloc_2755_, 1, v_startInclusive_2745_);
lean_ctor_set(v_reuseFailAlloc_2755_, 2, v___x_2752_);
v___x_2754_ = v_reuseFailAlloc_2755_;
goto v_reusejp_2753_;
}
v_reusejp_2753_:
{
return v___x_2754_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object* v_00_u03c1_2760_, lean_object* v_s_2761_, lean_object* v_pat_2762_, lean_object* v_inst_2763_){
_start:
{
lean_object* v_str_2764_; lean_object* v_startInclusive_2765_; lean_object* v_endExclusive_2766_; lean_object* v___x_2767_; lean_object* v___x_2768_; lean_object* v___x_2770_; uint8_t v_isShared_2771_; uint8_t v_isSharedCheck_2776_; 
v_str_2764_ = lean_ctor_get(v_s_2761_, 0);
lean_inc_ref(v_str_2764_);
v_startInclusive_2765_ = lean_ctor_get(v_s_2761_, 1);
lean_inc(v_startInclusive_2765_);
v_endExclusive_2766_ = lean_ctor_get(v_s_2761_, 2);
v___x_2767_ = lean_nat_sub(v_endExclusive_2766_, v_startInclusive_2765_);
v___x_2768_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2761_, v___x_2767_, v_inst_2763_);
v_isSharedCheck_2776_ = !lean_is_exclusive(v_s_2761_);
if (v_isSharedCheck_2776_ == 0)
{
lean_object* v_unused_2777_; lean_object* v_unused_2778_; lean_object* v_unused_2779_; 
v_unused_2777_ = lean_ctor_get(v_s_2761_, 2);
lean_dec(v_unused_2777_);
v_unused_2778_ = lean_ctor_get(v_s_2761_, 1);
lean_dec(v_unused_2778_);
v_unused_2779_ = lean_ctor_get(v_s_2761_, 0);
lean_dec(v_unused_2779_);
v___x_2770_ = v_s_2761_;
v_isShared_2771_ = v_isSharedCheck_2776_;
goto v_resetjp_2769_;
}
else
{
lean_dec(v_s_2761_);
v___x_2770_ = lean_box(0);
v_isShared_2771_ = v_isSharedCheck_2776_;
goto v_resetjp_2769_;
}
v_resetjp_2769_:
{
lean_object* v___x_2772_; lean_object* v___x_2774_; 
v___x_2772_ = lean_nat_add(v_startInclusive_2765_, v___x_2768_);
lean_dec(v___x_2768_);
if (v_isShared_2771_ == 0)
{
lean_ctor_set(v___x_2770_, 2, v___x_2772_);
v___x_2774_ = v___x_2770_;
goto v_reusejp_2773_;
}
else
{
lean_object* v_reuseFailAlloc_2775_; 
v_reuseFailAlloc_2775_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2775_, 0, v_str_2764_);
lean_ctor_set(v_reuseFailAlloc_2775_, 1, v_startInclusive_2765_);
lean_ctor_set(v_reuseFailAlloc_2775_, 2, v___x_2772_);
v___x_2774_ = v_reuseFailAlloc_2775_;
goto v_reusejp_2773_;
}
v_reusejp_2773_:
{
return v___x_2774_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object* v_00_u03c1_2780_, lean_object* v_s_2781_, lean_object* v_pat_2782_, lean_object* v_inst_2783_){
_start:
{
lean_object* v_res_2784_; 
v_res_2784_ = l_String_Slice_dropEndWhile(v_00_u03c1_2780_, v_s_2781_, v_pat_2782_, v_inst_2783_);
lean_dec(v_pat_2782_);
return v_res_2784_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiEnd___closed__0(void){
_start:
{
lean_object* v___x_2785_; lean_object* v___x_2786_; 
v___x_2785_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_2786_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_2785_);
return v___x_2786_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object* v_s_2787_){
_start:
{
lean_object* v___x_2788_; lean_object* v_str_2789_; lean_object* v_startInclusive_2790_; lean_object* v_endExclusive_2791_; lean_object* v___x_2792_; lean_object* v___x_2793_; lean_object* v___x_2795_; uint8_t v_isShared_2796_; uint8_t v_isSharedCheck_2801_; 
v___x_2788_ = lean_obj_once(&l_String_Slice_trimAsciiEnd___closed__0, &l_String_Slice_trimAsciiEnd___closed__0_once, _init_l_String_Slice_trimAsciiEnd___closed__0);
v_str_2789_ = lean_ctor_get(v_s_2787_, 0);
lean_inc_ref(v_str_2789_);
v_startInclusive_2790_ = lean_ctor_get(v_s_2787_, 1);
lean_inc(v_startInclusive_2790_);
v_endExclusive_2791_ = lean_ctor_get(v_s_2787_, 2);
v___x_2792_ = lean_nat_sub(v_endExclusive_2791_, v_startInclusive_2790_);
v___x_2793_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2787_, v___x_2792_, v___x_2788_);
v_isSharedCheck_2801_ = !lean_is_exclusive(v_s_2787_);
if (v_isSharedCheck_2801_ == 0)
{
lean_object* v_unused_2802_; lean_object* v_unused_2803_; lean_object* v_unused_2804_; 
v_unused_2802_ = lean_ctor_get(v_s_2787_, 2);
lean_dec(v_unused_2802_);
v_unused_2803_ = lean_ctor_get(v_s_2787_, 1);
lean_dec(v_unused_2803_);
v_unused_2804_ = lean_ctor_get(v_s_2787_, 0);
lean_dec(v_unused_2804_);
v___x_2795_ = v_s_2787_;
v_isShared_2796_ = v_isSharedCheck_2801_;
goto v_resetjp_2794_;
}
else
{
lean_dec(v_s_2787_);
v___x_2795_ = lean_box(0);
v_isShared_2796_ = v_isSharedCheck_2801_;
goto v_resetjp_2794_;
}
v_resetjp_2794_:
{
lean_object* v___x_2797_; lean_object* v___x_2799_; 
v___x_2797_ = lean_nat_add(v_startInclusive_2790_, v___x_2793_);
lean_dec(v___x_2793_);
if (v_isShared_2796_ == 0)
{
lean_ctor_set(v___x_2795_, 2, v___x_2797_);
v___x_2799_ = v___x_2795_;
goto v_reusejp_2798_;
}
else
{
lean_object* v_reuseFailAlloc_2800_; 
v_reuseFailAlloc_2800_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2800_, 0, v_str_2789_);
lean_ctor_set(v_reuseFailAlloc_2800_, 1, v_startInclusive_2790_);
lean_ctor_set(v_reuseFailAlloc_2800_, 2, v___x_2797_);
v___x_2799_ = v_reuseFailAlloc_2800_;
goto v_reusejp_2798_;
}
v_reusejp_2798_:
{
return v___x_2799_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object* v_s_2805_, lean_object* v_n_2806_){
_start:
{
lean_object* v_str_2807_; lean_object* v_startInclusive_2808_; lean_object* v_endExclusive_2809_; lean_object* v___x_2810_; lean_object* v___x_2811_; lean_object* v___x_2813_; uint8_t v_isShared_2814_; uint8_t v_isSharedCheck_2819_; 
v_str_2807_ = lean_ctor_get(v_s_2805_, 0);
lean_inc_ref(v_str_2807_);
v_startInclusive_2808_ = lean_ctor_get(v_s_2805_, 1);
lean_inc(v_startInclusive_2808_);
v_endExclusive_2809_ = lean_ctor_get(v_s_2805_, 2);
lean_inc(v_endExclusive_2809_);
v___x_2810_ = lean_nat_sub(v_endExclusive_2809_, v_startInclusive_2808_);
v___x_2811_ = l_String_Slice_Pos_prevn(v_s_2805_, v___x_2810_, v_n_2806_);
v_isSharedCheck_2819_ = !lean_is_exclusive(v_s_2805_);
if (v_isSharedCheck_2819_ == 0)
{
lean_object* v_unused_2820_; lean_object* v_unused_2821_; lean_object* v_unused_2822_; 
v_unused_2820_ = lean_ctor_get(v_s_2805_, 2);
lean_dec(v_unused_2820_);
v_unused_2821_ = lean_ctor_get(v_s_2805_, 1);
lean_dec(v_unused_2821_);
v_unused_2822_ = lean_ctor_get(v_s_2805_, 0);
lean_dec(v_unused_2822_);
v___x_2813_ = v_s_2805_;
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
else
{
lean_dec(v_s_2805_);
v___x_2813_ = lean_box(0);
v_isShared_2814_ = v_isSharedCheck_2819_;
goto v_resetjp_2812_;
}
v_resetjp_2812_:
{
lean_object* v___x_2815_; lean_object* v___x_2817_; 
v___x_2815_ = lean_nat_add(v_startInclusive_2808_, v___x_2811_);
lean_dec(v___x_2811_);
lean_dec(v_startInclusive_2808_);
if (v_isShared_2814_ == 0)
{
lean_ctor_set(v___x_2813_, 1, v___x_2815_);
v___x_2817_ = v___x_2813_;
goto v_reusejp_2816_;
}
else
{
lean_object* v_reuseFailAlloc_2818_; 
v_reuseFailAlloc_2818_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2818_, 0, v_str_2807_);
lean_ctor_set(v_reuseFailAlloc_2818_, 1, v___x_2815_);
lean_ctor_set(v_reuseFailAlloc_2818_, 2, v_endExclusive_2809_);
v___x_2817_ = v_reuseFailAlloc_2818_;
goto v_reusejp_2816_;
}
v_reusejp_2816_:
{
return v___x_2817_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___redArg(lean_object* v_s_2823_, lean_object* v_inst_2824_){
_start:
{
lean_object* v_str_2825_; lean_object* v_startInclusive_2826_; lean_object* v_endExclusive_2827_; lean_object* v___x_2828_; lean_object* v___x_2829_; lean_object* v___x_2831_; uint8_t v_isShared_2832_; uint8_t v_isSharedCheck_2837_; 
v_str_2825_ = lean_ctor_get(v_s_2823_, 0);
lean_inc_ref(v_str_2825_);
v_startInclusive_2826_ = lean_ctor_get(v_s_2823_, 1);
lean_inc(v_startInclusive_2826_);
v_endExclusive_2827_ = lean_ctor_get(v_s_2823_, 2);
lean_inc(v_endExclusive_2827_);
v___x_2828_ = lean_nat_sub(v_endExclusive_2827_, v_startInclusive_2826_);
v___x_2829_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2823_, v___x_2828_, v_inst_2824_);
v_isSharedCheck_2837_ = !lean_is_exclusive(v_s_2823_);
if (v_isSharedCheck_2837_ == 0)
{
lean_object* v_unused_2838_; lean_object* v_unused_2839_; lean_object* v_unused_2840_; 
v_unused_2838_ = lean_ctor_get(v_s_2823_, 2);
lean_dec(v_unused_2838_);
v_unused_2839_ = lean_ctor_get(v_s_2823_, 1);
lean_dec(v_unused_2839_);
v_unused_2840_ = lean_ctor_get(v_s_2823_, 0);
lean_dec(v_unused_2840_);
v___x_2831_ = v_s_2823_;
v_isShared_2832_ = v_isSharedCheck_2837_;
goto v_resetjp_2830_;
}
else
{
lean_dec(v_s_2823_);
v___x_2831_ = lean_box(0);
v_isShared_2832_ = v_isSharedCheck_2837_;
goto v_resetjp_2830_;
}
v_resetjp_2830_:
{
lean_object* v___x_2833_; lean_object* v___x_2835_; 
v___x_2833_ = lean_nat_add(v_startInclusive_2826_, v___x_2829_);
lean_dec(v___x_2829_);
lean_dec(v_startInclusive_2826_);
if (v_isShared_2832_ == 0)
{
lean_ctor_set(v___x_2831_, 1, v___x_2833_);
v___x_2835_ = v___x_2831_;
goto v_reusejp_2834_;
}
else
{
lean_object* v_reuseFailAlloc_2836_; 
v_reuseFailAlloc_2836_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2836_, 0, v_str_2825_);
lean_ctor_set(v_reuseFailAlloc_2836_, 1, v___x_2833_);
lean_ctor_set(v_reuseFailAlloc_2836_, 2, v_endExclusive_2827_);
v___x_2835_ = v_reuseFailAlloc_2836_;
goto v_reusejp_2834_;
}
v_reusejp_2834_:
{
return v___x_2835_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile(lean_object* v_00_u03c1_2841_, lean_object* v_s_2842_, lean_object* v_pat_2843_, lean_object* v_inst_2844_){
_start:
{
lean_object* v_str_2845_; lean_object* v_startInclusive_2846_; lean_object* v_endExclusive_2847_; lean_object* v___x_2848_; lean_object* v___x_2849_; lean_object* v___x_2851_; uint8_t v_isShared_2852_; uint8_t v_isSharedCheck_2857_; 
v_str_2845_ = lean_ctor_get(v_s_2842_, 0);
lean_inc_ref(v_str_2845_);
v_startInclusive_2846_ = lean_ctor_get(v_s_2842_, 1);
lean_inc(v_startInclusive_2846_);
v_endExclusive_2847_ = lean_ctor_get(v_s_2842_, 2);
lean_inc(v_endExclusive_2847_);
v___x_2848_ = lean_nat_sub(v_endExclusive_2847_, v_startInclusive_2846_);
v___x_2849_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2842_, v___x_2848_, v_inst_2844_);
v_isSharedCheck_2857_ = !lean_is_exclusive(v_s_2842_);
if (v_isSharedCheck_2857_ == 0)
{
lean_object* v_unused_2858_; lean_object* v_unused_2859_; lean_object* v_unused_2860_; 
v_unused_2858_ = lean_ctor_get(v_s_2842_, 2);
lean_dec(v_unused_2858_);
v_unused_2859_ = lean_ctor_get(v_s_2842_, 1);
lean_dec(v_unused_2859_);
v_unused_2860_ = lean_ctor_get(v_s_2842_, 0);
lean_dec(v_unused_2860_);
v___x_2851_ = v_s_2842_;
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
else
{
lean_dec(v_s_2842_);
v___x_2851_ = lean_box(0);
v_isShared_2852_ = v_isSharedCheck_2857_;
goto v_resetjp_2850_;
}
v_resetjp_2850_:
{
lean_object* v___x_2853_; lean_object* v___x_2855_; 
v___x_2853_ = lean_nat_add(v_startInclusive_2846_, v___x_2849_);
lean_dec(v___x_2849_);
lean_dec(v_startInclusive_2846_);
if (v_isShared_2852_ == 0)
{
lean_ctor_set(v___x_2851_, 1, v___x_2853_);
v___x_2855_ = v___x_2851_;
goto v_reusejp_2854_;
}
else
{
lean_object* v_reuseFailAlloc_2856_; 
v_reuseFailAlloc_2856_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2856_, 0, v_str_2845_);
lean_ctor_set(v_reuseFailAlloc_2856_, 1, v___x_2853_);
lean_ctor_set(v_reuseFailAlloc_2856_, 2, v_endExclusive_2847_);
v___x_2855_ = v_reuseFailAlloc_2856_;
goto v_reusejp_2854_;
}
v_reusejp_2854_:
{
return v___x_2855_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___boxed(lean_object* v_00_u03c1_2861_, lean_object* v_s_2862_, lean_object* v_pat_2863_, lean_object* v_inst_2864_){
_start:
{
lean_object* v_res_2865_; 
v_res_2865_ = l_String_Slice_takeEndWhile(v_00_u03c1_2861_, v_s_2862_, v_pat_2863_, v_inst_2864_);
lean_dec(v_pat_2863_);
return v_res_2865_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___redArg(lean_object* v_inst_2866_, lean_object* v_s_2867_, lean_object* v_inst_2868_){
_start:
{
lean_object* v___f_2869_; lean_object* v_searcher_2870_; lean_object* v___x_2871_; lean_object* v___f_2872_; lean_object* v___x_2873_; 
v___f_2869_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_2867_);
v_searcher_2870_ = lean_apply_1(v_inst_2868_, v_s_2867_);
v___x_2871_ = lean_box(0);
v___f_2872_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_2873_ = lean_apply_7(v_inst_2866_, v_s_2867_, v___f_2869_, lean_box(0), lean_box(0), v_searcher_2870_, v___x_2871_, v___f_2872_);
return v___x_2873_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f(lean_object* v_00_u03c3_2874_, lean_object* v_inst_2875_, lean_object* v_inst_2876_, lean_object* v_00_u03c1_2877_, lean_object* v_s_2878_, lean_object* v_pat_2879_, lean_object* v_inst_2880_){
_start:
{
lean_object* v___x_2881_; 
v___x_2881_ = l_String_Slice_revFind_x3f___redArg(v_inst_2876_, v_s_2878_, v_inst_2880_);
return v___x_2881_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___boxed(lean_object* v_00_u03c3_2882_, lean_object* v_inst_2883_, lean_object* v_inst_2884_, lean_object* v_00_u03c1_2885_, lean_object* v_s_2886_, lean_object* v_pat_2887_, lean_object* v_inst_2888_){
_start:
{
lean_object* v_res_2889_; 
v_res_2889_ = l_String_Slice_revFind_x3f(v_00_u03c3_2882_, v_inst_2883_, v_inst_2884_, v_00_u03c1_2885_, v_s_2886_, v_pat_2887_, v_inst_2888_);
lean_dec(v_pat_2887_);
lean_dec(v_inst_2883_);
return v_res_2889_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(lean_object* v_s_2890_, lean_object* v_pos_2891_){
_start:
{
lean_object* v_str_2892_; lean_object* v_startInclusive_2893_; lean_object* v_endExclusive_2894_; lean_object* v___x_2895_; lean_object* v___x_2904_; lean_object* v___x_2905_; uint8_t v_decide_2906_; 
v_str_2892_ = lean_ctor_get(v_s_2890_, 0);
v_startInclusive_2893_ = lean_ctor_get(v_s_2890_, 1);
v_endExclusive_2894_ = lean_ctor_get(v_s_2890_, 2);
v___x_2895_ = lean_nat_add(v_startInclusive_2893_, v_pos_2891_);
v___x_2904_ = lean_unsigned_to_nat(0u);
v___x_2905_ = lean_nat_sub(v_endExclusive_2894_, v___x_2895_);
v_decide_2906_ = lean_nat_dec_eq(v___x_2904_, v___x_2905_);
lean_dec(v___x_2905_);
if (v_decide_2906_ == 0)
{
uint32_t v___x_2907_; uint32_t v___x_2908_; uint8_t v___x_2909_; 
v___x_2907_ = lean_string_utf8_get_fast(v_str_2892_, v___x_2895_);
v___x_2908_ = 32;
v___x_2909_ = lean_uint32_dec_eq(v___x_2907_, v___x_2908_);
if (v___x_2909_ == 0)
{
uint32_t v___x_2910_; uint8_t v___x_2911_; 
v___x_2910_ = 9;
v___x_2911_ = lean_uint32_dec_eq(v___x_2907_, v___x_2910_);
if (v___x_2911_ == 0)
{
uint32_t v___x_2912_; uint8_t v___x_2913_; 
v___x_2912_ = 13;
v___x_2913_ = lean_uint32_dec_eq(v___x_2907_, v___x_2912_);
if (v___x_2913_ == 0)
{
uint32_t v___x_2914_; uint8_t v___x_2915_; 
v___x_2914_ = 10;
v___x_2915_ = lean_uint32_dec_eq(v___x_2907_, v___x_2914_);
if (v___x_2915_ == 0)
{
lean_dec(v___x_2895_);
return v_pos_2891_;
}
else
{
goto v___jp_2896_;
}
}
else
{
goto v___jp_2896_;
}
}
else
{
goto v___jp_2896_;
}
}
else
{
goto v___jp_2896_;
}
}
else
{
lean_dec(v___x_2895_);
return v_pos_2891_;
}
v___jp_2896_:
{
lean_object* v___x_2897_; lean_object* v___x_2898_; lean_object* v___x_2899_; lean_object* v___x_2900_; lean_object* v___x_2901_; uint8_t v___x_2902_; 
v___x_2897_ = lean_string_utf8_next_fast(v_str_2892_, v___x_2895_);
v___x_2898_ = lean_nat_sub(v___x_2897_, v___x_2895_);
lean_dec(v___x_2895_);
v___x_2899_ = lean_nat_add(v_pos_2891_, v___x_2898_);
lean_dec(v___x_2898_);
v___x_2900_ = lean_unsigned_to_nat(1u);
v___x_2901_ = lean_nat_add(v_pos_2891_, v___x_2900_);
v___x_2902_ = lean_nat_dec_le(v___x_2901_, v___x_2899_);
lean_dec(v___x_2901_);
if (v___x_2902_ == 0)
{
lean_dec(v___x_2899_);
return v_pos_2891_;
}
else
{
lean_dec(v_pos_2891_);
v_pos_2891_ = v___x_2899_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0___boxed(lean_object* v_s_2916_, lean_object* v_pos_2917_){
_start:
{
lean_object* v_res_2918_; 
v_res_2918_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2916_, v_pos_2917_);
lean_dec_ref(v_s_2916_);
return v_res_2918_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(lean_object* v_s_2919_, lean_object* v_pos_2920_){
_start:
{
lean_object* v_str_2921_; lean_object* v_startInclusive_2922_; lean_object* v___x_2923_; lean_object* v___x_2924_; lean_object* v___x_2925_; uint8_t v_decide_2926_; 
v_str_2921_ = lean_ctor_get(v_s_2919_, 0);
v_startInclusive_2922_ = lean_ctor_get(v_s_2919_, 1);
v___x_2923_ = lean_nat_add(v_startInclusive_2922_, v_pos_2920_);
v___x_2924_ = lean_nat_sub(v___x_2923_, v_startInclusive_2922_);
v___x_2925_ = lean_unsigned_to_nat(0u);
v_decide_2926_ = lean_nat_dec_eq(v___x_2924_, v___x_2925_);
if (v_decide_2926_ == 0)
{
lean_object* v___x_2927_; lean_object* v___x_2928_; lean_object* v___x_2929_; lean_object* v___x_2930_; lean_object* v___x_2935_; uint32_t v___x_2936_; uint32_t v___x_2937_; uint8_t v___x_2938_; 
lean_inc(v_startInclusive_2922_);
lean_inc_ref(v_str_2921_);
v___x_2927_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2927_, 0, v_str_2921_);
lean_ctor_set(v___x_2927_, 1, v_startInclusive_2922_);
lean_ctor_set(v___x_2927_, 2, v___x_2923_);
v___x_2928_ = lean_unsigned_to_nat(1u);
v___x_2929_ = lean_nat_sub(v___x_2924_, v___x_2928_);
lean_dec(v___x_2924_);
v___x_2930_ = l_String_Slice_posLE(v___x_2927_, v___x_2929_);
lean_dec_ref_known(v___x_2927_, 3);
v___x_2935_ = lean_nat_add(v_startInclusive_2922_, v___x_2930_);
v___x_2936_ = lean_string_utf8_get_fast(v_str_2921_, v___x_2935_);
lean_dec(v___x_2935_);
v___x_2937_ = 32;
v___x_2938_ = lean_uint32_dec_eq(v___x_2936_, v___x_2937_);
if (v___x_2938_ == 0)
{
uint32_t v___x_2939_; uint8_t v___x_2940_; 
v___x_2939_ = 9;
v___x_2940_ = lean_uint32_dec_eq(v___x_2936_, v___x_2939_);
if (v___x_2940_ == 0)
{
uint32_t v___x_2941_; uint8_t v___x_2942_; 
v___x_2941_ = 13;
v___x_2942_ = lean_uint32_dec_eq(v___x_2936_, v___x_2941_);
if (v___x_2942_ == 0)
{
uint32_t v___x_2943_; uint8_t v___x_2944_; 
v___x_2943_ = 10;
v___x_2944_ = lean_uint32_dec_eq(v___x_2936_, v___x_2943_);
if (v___x_2944_ == 0)
{
lean_dec(v___x_2930_);
return v_pos_2920_;
}
else
{
goto v___jp_2931_;
}
}
else
{
goto v___jp_2931_;
}
}
else
{
goto v___jp_2931_;
}
}
else
{
goto v___jp_2931_;
}
v___jp_2931_:
{
lean_object* v___x_2932_; uint8_t v___x_2933_; 
v___x_2932_ = lean_nat_add(v___x_2930_, v___x_2928_);
v___x_2933_ = lean_nat_dec_le(v___x_2932_, v_pos_2920_);
lean_dec(v___x_2932_);
if (v___x_2933_ == 0)
{
lean_dec(v___x_2930_);
return v_pos_2920_;
}
else
{
lean_dec(v_pos_2920_);
v_pos_2920_ = v___x_2930_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2924_);
lean_dec(v___x_2923_);
return v_pos_2920_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1___boxed(lean_object* v_s_2945_, lean_object* v_pos_2946_){
_start:
{
lean_object* v_res_2947_; 
v_res_2947_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v_s_2945_, v_pos_2946_);
lean_dec_ref(v_s_2945_);
return v_res_2947_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAscii(lean_object* v_s_2948_){
_start:
{
lean_object* v_str_2949_; lean_object* v_startInclusive_2950_; lean_object* v_endExclusive_2951_; lean_object* v___x_2952_; lean_object* v___x_2953_; lean_object* v___x_2955_; uint8_t v_isShared_2956_; uint8_t v_isSharedCheck_2965_; 
v_str_2949_ = lean_ctor_get(v_s_2948_, 0);
lean_inc_ref(v_str_2949_);
v_startInclusive_2950_ = lean_ctor_get(v_s_2948_, 1);
lean_inc(v_startInclusive_2950_);
v_endExclusive_2951_ = lean_ctor_get(v_s_2948_, 2);
lean_inc(v_endExclusive_2951_);
v___x_2952_ = lean_unsigned_to_nat(0u);
v___x_2953_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2948_, v___x_2952_);
v_isSharedCheck_2965_ = !lean_is_exclusive(v_s_2948_);
if (v_isSharedCheck_2965_ == 0)
{
lean_object* v_unused_2966_; lean_object* v_unused_2967_; lean_object* v_unused_2968_; 
v_unused_2966_ = lean_ctor_get(v_s_2948_, 2);
lean_dec(v_unused_2966_);
v_unused_2967_ = lean_ctor_get(v_s_2948_, 1);
lean_dec(v_unused_2967_);
v_unused_2968_ = lean_ctor_get(v_s_2948_, 0);
lean_dec(v_unused_2968_);
v___x_2955_ = v_s_2948_;
v_isShared_2956_ = v_isSharedCheck_2965_;
goto v_resetjp_2954_;
}
else
{
lean_dec(v_s_2948_);
v___x_2955_ = lean_box(0);
v_isShared_2956_ = v_isSharedCheck_2965_;
goto v_resetjp_2954_;
}
v_resetjp_2954_:
{
lean_object* v___x_2957_; lean_object* v___x_2959_; 
v___x_2957_ = lean_nat_add(v_startInclusive_2950_, v___x_2953_);
lean_dec(v___x_2953_);
lean_dec(v_startInclusive_2950_);
lean_inc(v_endExclusive_2951_);
lean_inc(v___x_2957_);
lean_inc_ref(v_str_2949_);
if (v_isShared_2956_ == 0)
{
lean_ctor_set(v___x_2955_, 1, v___x_2957_);
v___x_2959_ = v___x_2955_;
goto v_reusejp_2958_;
}
else
{
lean_object* v_reuseFailAlloc_2964_; 
v_reuseFailAlloc_2964_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2964_, 0, v_str_2949_);
lean_ctor_set(v_reuseFailAlloc_2964_, 1, v___x_2957_);
lean_ctor_set(v_reuseFailAlloc_2964_, 2, v_endExclusive_2951_);
v___x_2959_ = v_reuseFailAlloc_2964_;
goto v_reusejp_2958_;
}
v_reusejp_2958_:
{
lean_object* v___x_2960_; lean_object* v___x_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; 
v___x_2960_ = lean_nat_sub(v_endExclusive_2951_, v___x_2957_);
lean_dec(v_endExclusive_2951_);
v___x_2961_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v___x_2959_, v___x_2960_);
lean_dec_ref(v___x_2959_);
v___x_2962_ = lean_nat_add(v___x_2957_, v___x_2961_);
lean_dec(v___x_2961_);
v___x_2963_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2963_, 0, v_str_2949_);
lean_ctor_set(v___x_2963_, 1, v___x_2957_);
lean_ctor_set(v___x_2963_, 2, v___x_2962_);
return v___x_2963_;
}
}
}
}
LEAN_EXPORT uint8_t l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(lean_object* v_s1_2969_, lean_object* v_s1Curr_2970_, lean_object* v_s2_2971_, lean_object* v_s2Curr_2972_){
_start:
{
lean_object* v_str_2973_; lean_object* v_startInclusive_2974_; lean_object* v_endExclusive_2975_; lean_object* v___x_2976_; uint8_t v___y_2978_; lean_object* v___x_3008_; lean_object* v___x_3009_; uint8_t v___x_3010_; 
v_str_2973_ = lean_ctor_get(v_s1_2969_, 0);
v_startInclusive_2974_ = lean_ctor_get(v_s1_2969_, 1);
v_endExclusive_2975_ = lean_ctor_get(v_s1_2969_, 2);
v___x_2976_ = lean_nat_sub(v_endExclusive_2975_, v_startInclusive_2974_);
v___x_3008_ = lean_unsigned_to_nat(1u);
v___x_3009_ = lean_nat_add(v_s1Curr_2970_, v___x_3008_);
v___x_3010_ = lean_nat_dec_le(v___x_3009_, v___x_2976_);
lean_dec(v___x_3009_);
if (v___x_3010_ == 0)
{
v___y_2978_ = v___x_3010_;
goto v___jp_2977_;
}
else
{
lean_object* v_startInclusive_3011_; lean_object* v_endExclusive_3012_; lean_object* v___x_3013_; lean_object* v___x_3014_; uint8_t v___x_3015_; 
v_startInclusive_3011_ = lean_ctor_get(v_s2_2971_, 1);
v_endExclusive_3012_ = lean_ctor_get(v_s2_2971_, 2);
v___x_3013_ = lean_nat_sub(v_endExclusive_3012_, v_startInclusive_3011_);
v___x_3014_ = lean_nat_add(v_s2Curr_2972_, v___x_3008_);
v___x_3015_ = lean_nat_dec_le(v___x_3014_, v___x_3013_);
lean_dec(v___x_3013_);
lean_dec(v___x_3014_);
v___y_2978_ = v___x_3015_;
goto v___jp_2977_;
}
v___jp_2977_:
{
if (v___y_2978_ == 0)
{
uint8_t v_decide_2979_; 
v_decide_2979_ = lean_nat_dec_eq(v_s1Curr_2970_, v___x_2976_);
lean_dec(v___x_2976_);
lean_dec(v_s1Curr_2970_);
if (v_decide_2979_ == 0)
{
lean_dec(v_s2Curr_2972_);
return v_decide_2979_;
}
else
{
lean_object* v_startInclusive_2980_; lean_object* v_endExclusive_2981_; lean_object* v___x_2982_; uint8_t v_decide_2983_; 
v_startInclusive_2980_ = lean_ctor_get(v_s2_2971_, 1);
v_endExclusive_2981_ = lean_ctor_get(v_s2_2971_, 2);
v___x_2982_ = lean_nat_sub(v_endExclusive_2981_, v_startInclusive_2980_);
v_decide_2983_ = lean_nat_dec_eq(v_s2Curr_2972_, v___x_2982_);
lean_dec(v___x_2982_);
lean_dec(v_s2Curr_2972_);
return v_decide_2983_;
}
}
else
{
lean_object* v_str_2984_; lean_object* v_startInclusive_2985_; lean_object* v___x_2986_; uint8_t v___x_2987_; uint8_t v___x_2988_; uint8_t v___x_2989_; uint8_t v___x_2990_; uint8_t v___x_2991_; uint8_t v___x_2992_; uint8_t v___x_2993_; uint8_t v___x_2994_; uint8_t v_c1_2995_; lean_object* v___x_2996_; uint8_t v___x_2997_; uint8_t v___x_2998_; uint8_t v___x_2999_; uint8_t v___x_3000_; uint8_t v___x_3001_; uint8_t v_c2_3002_; uint8_t v___x_3003_; 
lean_dec(v___x_2976_);
v_str_2984_ = lean_ctor_get(v_s2_2971_, 0);
v_startInclusive_2985_ = lean_ctor_get(v_s2_2971_, 1);
v___x_2986_ = lean_nat_add(v_startInclusive_2974_, v_s1Curr_2970_);
v___x_2987_ = lean_string_get_byte_fast(v_str_2973_, v___x_2986_);
v___x_2988_ = 65;
v___x_2989_ = lean_uint8_sub(v___x_2987_, v___x_2988_);
v___x_2990_ = 26;
v___x_2991_ = lean_uint8_dec_lt(v___x_2989_, v___x_2990_);
v___x_2992_ = lean_bool_to_uint8(v___x_2991_);
v___x_2993_ = 5;
v___x_2994_ = lean_uint8_shift_left(v___x_2992_, v___x_2993_);
v_c1_2995_ = lean_uint8_add(v___x_2987_, v___x_2994_);
v___x_2996_ = lean_nat_add(v_startInclusive_2985_, v_s2Curr_2972_);
v___x_2997_ = lean_string_get_byte_fast(v_str_2984_, v___x_2996_);
v___x_2998_ = lean_uint8_sub(v___x_2997_, v___x_2988_);
v___x_2999_ = lean_uint8_dec_lt(v___x_2998_, v___x_2990_);
v___x_3000_ = lean_bool_to_uint8(v___x_2999_);
v___x_3001_ = lean_uint8_shift_left(v___x_3000_, v___x_2993_);
v_c2_3002_ = lean_uint8_add(v___x_2997_, v___x_3001_);
v___x_3003_ = lean_uint8_dec_eq(v_c1_2995_, v_c2_3002_);
if (v___x_3003_ == 0)
{
lean_dec(v_s2Curr_2972_);
lean_dec(v_s1Curr_2970_);
return v___x_3003_;
}
else
{
lean_object* v___x_3004_; lean_object* v___x_3005_; lean_object* v___x_3006_; 
v___x_3004_ = lean_unsigned_to_nat(1u);
v___x_3005_ = lean_nat_add(v_s1Curr_2970_, v___x_3004_);
lean_dec(v_s1Curr_2970_);
v___x_3006_ = lean_nat_add(v_s2Curr_2972_, v___x_3004_);
lean_dec(v_s2Curr_2972_);
v_s1Curr_2970_ = v___x_3005_;
v_s2Curr_2972_ = v___x_3006_;
goto _start;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object* v_s1_3016_, lean_object* v_s1Curr_3017_, lean_object* v_s2_3018_, lean_object* v_s2Curr_3019_){
_start:
{
uint8_t v_res_3020_; lean_object* v_r_3021_; 
v_res_3020_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_3016_, v_s1Curr_3017_, v_s2_3018_, v_s2Curr_3019_);
lean_dec_ref(v_s2_3018_);
lean_dec_ref(v_s1_3016_);
v_r_3021_ = lean_box(v_res_3020_);
return v_r_3021_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object* v_s1_3022_, lean_object* v_s2_3023_){
_start:
{
lean_object* v_startInclusive_3024_; lean_object* v_endExclusive_3025_; lean_object* v_startInclusive_3026_; lean_object* v_endExclusive_3027_; lean_object* v___x_3028_; lean_object* v___x_3029_; uint8_t v___x_3030_; 
v_startInclusive_3024_ = lean_ctor_get(v_s1_3022_, 1);
v_endExclusive_3025_ = lean_ctor_get(v_s1_3022_, 2);
v_startInclusive_3026_ = lean_ctor_get(v_s2_3023_, 1);
v_endExclusive_3027_ = lean_ctor_get(v_s2_3023_, 2);
v___x_3028_ = lean_nat_sub(v_endExclusive_3025_, v_startInclusive_3024_);
v___x_3029_ = lean_nat_sub(v_endExclusive_3027_, v_startInclusive_3026_);
v___x_3030_ = lean_nat_dec_eq(v___x_3028_, v___x_3029_);
lean_dec(v___x_3029_);
lean_dec(v___x_3028_);
if (v___x_3030_ == 0)
{
return v___x_3030_;
}
else
{
lean_object* v___x_3031_; uint8_t v___x_3032_; 
v___x_3031_ = lean_unsigned_to_nat(0u);
v___x_3032_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_3022_, v___x_3031_, v_s2_3023_, v___x_3031_);
return v___x_3032_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object* v_s1_3033_, lean_object* v_s2_3034_){
_start:
{
uint8_t v_res_3035_; lean_object* v_r_3036_; 
v_res_3035_ = l_String_Slice_eqIgnoreAsciiCase(v_s1_3033_, v_s2_3034_);
lean_dec_ref(v_s2_3034_);
lean_dec_ref(v_s1_3033_);
v_r_3036_ = lean_box(v_res_3035_);
return v_r_3036_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines_lineMap(lean_object* v_s_3037_){
_start:
{
lean_object* v_str_3038_; lean_object* v_startInclusive_3039_; lean_object* v_endExclusive_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; uint8_t v_decide_3043_; 
v_str_3038_ = lean_ctor_get(v_s_3037_, 0);
v_startInclusive_3039_ = lean_ctor_get(v_s_3037_, 1);
v_endExclusive_3040_ = lean_ctor_get(v_s_3037_, 2);
v___x_3041_ = lean_nat_sub(v_endExclusive_3040_, v_startInclusive_3039_);
v___x_3042_ = lean_unsigned_to_nat(0u);
v_decide_3043_ = lean_nat_dec_eq(v___x_3041_, v___x_3042_);
if (v_decide_3043_ == 0)
{
uint32_t v___x_3044_; lean_object* v___x_3045_; lean_object* v___x_3046_; lean_object* v___x_3047_; lean_object* v___x_3048_; uint32_t v___x_3049_; uint8_t v___x_3050_; 
v___x_3044_ = 10;
v___x_3045_ = lean_unsigned_to_nat(1u);
v___x_3046_ = lean_nat_sub(v___x_3041_, v___x_3045_);
lean_dec(v___x_3041_);
v___x_3047_ = l_String_Slice_posLE(v_s_3037_, v___x_3046_);
v___x_3048_ = lean_nat_add(v_startInclusive_3039_, v___x_3047_);
lean_dec(v___x_3047_);
v___x_3049_ = lean_string_utf8_get_fast(v_str_3038_, v___x_3048_);
v___x_3050_ = lean_uint32_dec_eq(v___x_3049_, v___x_3044_);
if (v___x_3050_ == 0)
{
lean_dec(v___x_3048_);
return v_s_3037_;
}
else
{
lean_object* v___x_3052_; uint8_t v_isShared_3053_; uint8_t v_isSharedCheck_3066_; 
lean_inc(v_startInclusive_3039_);
lean_inc_ref(v_str_3038_);
v_isSharedCheck_3066_ = !lean_is_exclusive(v_s_3037_);
if (v_isSharedCheck_3066_ == 0)
{
lean_object* v_unused_3067_; lean_object* v_unused_3068_; lean_object* v_unused_3069_; 
v_unused_3067_ = lean_ctor_get(v_s_3037_, 2);
lean_dec(v_unused_3067_);
v_unused_3068_ = lean_ctor_get(v_s_3037_, 1);
lean_dec(v_unused_3068_);
v_unused_3069_ = lean_ctor_get(v_s_3037_, 0);
lean_dec(v_unused_3069_);
v___x_3052_ = v_s_3037_;
v_isShared_3053_ = v_isSharedCheck_3066_;
goto v_resetjp_3051_;
}
else
{
lean_dec(v_s_3037_);
v___x_3052_ = lean_box(0);
v_isShared_3053_ = v_isSharedCheck_3066_;
goto v_resetjp_3051_;
}
v_resetjp_3051_:
{
lean_object* v___x_3055_; 
lean_inc(v___x_3048_);
lean_inc(v_startInclusive_3039_);
lean_inc_ref(v_str_3038_);
if (v_isShared_3053_ == 0)
{
lean_ctor_set(v___x_3052_, 2, v___x_3048_);
v___x_3055_ = v___x_3052_;
goto v_reusejp_3054_;
}
else
{
lean_object* v_reuseFailAlloc_3065_; 
v_reuseFailAlloc_3065_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3065_, 0, v_str_3038_);
lean_ctor_set(v_reuseFailAlloc_3065_, 1, v_startInclusive_3039_);
lean_ctor_set(v_reuseFailAlloc_3065_, 2, v___x_3048_);
v___x_3055_ = v_reuseFailAlloc_3065_;
goto v_reusejp_3054_;
}
v_reusejp_3054_:
{
lean_object* v___x_3056_; uint8_t v_decide_3057_; 
v___x_3056_ = lean_nat_sub(v___x_3048_, v_startInclusive_3039_);
lean_dec(v___x_3048_);
v_decide_3057_ = lean_nat_dec_eq(v___x_3056_, v___x_3042_);
if (v_decide_3057_ == 0)
{
uint32_t v___x_3058_; lean_object* v___x_3059_; lean_object* v___x_3060_; lean_object* v___x_3061_; uint32_t v___x_3062_; uint8_t v___x_3063_; 
v___x_3058_ = 13;
v___x_3059_ = lean_nat_sub(v___x_3056_, v___x_3045_);
lean_dec(v___x_3056_);
v___x_3060_ = l_String_Slice_posLE(v___x_3055_, v___x_3059_);
v___x_3061_ = lean_nat_add(v_startInclusive_3039_, v___x_3060_);
lean_dec(v___x_3060_);
v___x_3062_ = lean_string_utf8_get_fast(v_str_3038_, v___x_3061_);
v___x_3063_ = lean_uint32_dec_eq(v___x_3062_, v___x_3058_);
if (v___x_3063_ == 0)
{
lean_dec(v___x_3061_);
lean_dec(v_startInclusive_3039_);
lean_dec_ref(v_str_3038_);
return v___x_3055_;
}
else
{
lean_object* v___x_3064_; 
lean_dec_ref(v___x_3055_);
v___x_3064_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_3064_, 0, v_str_3038_);
lean_ctor_set(v___x_3064_, 1, v_startInclusive_3039_);
lean_ctor_set(v___x_3064_, 2, v___x_3061_);
return v___x_3064_;
}
}
else
{
lean_dec(v___x_3056_);
lean_dec(v_startInclusive_3039_);
lean_dec_ref(v_str_3038_);
return v___x_3055_;
}
}
}
}
}
else
{
lean_dec(v___x_3041_);
return v_s_3037_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg(){
_start:
{
lean_object* v___x_3073_; 
v___x_3073_ = ((lean_object*)(l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___closed__0));
return v___x_3073_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___boxed(lean_object* v___dummy_3074_){
_start:
{
lean_object* v_res_3075_; 
v_res_3075_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
return v_res_3075_;
}
}
static lean_object* _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3076_; 
v___x_3076_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
return v___x_3076_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(lean_object* v_s_3077_){
_start:
{
lean_object* v___x_3078_; 
v___x_3078_ = lean_obj_once(&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0, &l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_once, _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0);
return v___x_3078_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(lean_object* v_s_3079_){
_start:
{
lean_object* v_res_3080_; 
v_res_3080_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_3079_);
lean_dec_ref(v_s_3079_);
return v_res_3080_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines(lean_object* v_s_3081_){
_start:
{
lean_object* v___x_3082_; 
v___x_3082_ = lean_obj_once(&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0, &l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_once, _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0);
return v___x_3082_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines___boxed(lean_object* v_s_3083_){
_start:
{
lean_object* v_res_3084_; 
v_res_3084_ = l_String_Slice_lines(v_s_3083_);
lean_dec_ref(v_s_3083_);
return v_res_3084_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(lean_object* v_s_3085_, lean_object* v_a_3086_, lean_object* v_b_3087_){
_start:
{
lean_object* v_str_3088_; lean_object* v_startInclusive_3089_; lean_object* v_endExclusive_3090_; lean_object* v___x_3091_; uint8_t v_decide_3092_; 
v_str_3088_ = lean_ctor_get(v_s_3085_, 0);
v_startInclusive_3089_ = lean_ctor_get(v_s_3085_, 1);
v_endExclusive_3090_ = lean_ctor_get(v_s_3085_, 2);
v___x_3091_ = lean_nat_sub(v_endExclusive_3090_, v_startInclusive_3089_);
v_decide_3092_ = lean_nat_dec_eq(v_a_3086_, v___x_3091_);
lean_dec(v___x_3091_);
if (v_decide_3092_ == 0)
{
lean_object* v_snd_3093_; lean_object* v___x_3095_; uint8_t v_isShared_3096_; uint8_t v_isSharedCheck_3124_; 
v_snd_3093_ = lean_ctor_get(v_b_3087_, 1);
v_isSharedCheck_3124_ = !lean_is_exclusive(v_b_3087_);
if (v_isSharedCheck_3124_ == 0)
{
lean_object* v_unused_3125_; 
v_unused_3125_ = lean_ctor_get(v_b_3087_, 0);
lean_dec(v_unused_3125_);
v___x_3095_ = v_b_3087_;
v_isShared_3096_ = v_isSharedCheck_3124_;
goto v_resetjp_3094_;
}
else
{
lean_inc(v_snd_3093_);
lean_dec(v_b_3087_);
v___x_3095_ = lean_box(0);
v_isShared_3096_ = v_isSharedCheck_3124_;
goto v_resetjp_3094_;
}
v_resetjp_3094_:
{
lean_object* v___x_3103_; lean_object* v___x_3104_; lean_object* v___x_3105_; lean_object* v___x_3106_; uint32_t v___x_3107_; uint32_t v___x_3108_; uint8_t v___x_3109_; 
v___x_3103_ = lean_box(0);
v___x_3104_ = lean_nat_add(v_startInclusive_3089_, v_a_3086_);
lean_dec(v_a_3086_);
v___x_3105_ = lean_string_utf8_next_fast(v_str_3088_, v___x_3104_);
v___x_3106_ = lean_nat_sub(v___x_3105_, v_startInclusive_3089_);
v___x_3107_ = lean_string_utf8_get_fast(v_str_3088_, v___x_3104_);
lean_dec(v___x_3104_);
v___x_3108_ = 95;
v___x_3109_ = lean_uint32_dec_eq(v___x_3107_, v___x_3108_);
if (v___x_3109_ == 0)
{
uint32_t v___x_3110_; uint8_t v___x_3111_; 
v___x_3110_ = 48;
v___x_3111_ = lean_uint32_dec_le(v___x_3110_, v___x_3107_);
if (v___x_3111_ == 0)
{
lean_dec(v___x_3106_);
goto v___jp_3097_;
}
else
{
uint32_t v___x_3112_; uint8_t v___x_3113_; 
v___x_3112_ = 57;
v___x_3113_ = lean_uint32_dec_le(v___x_3107_, v___x_3112_);
if (v___x_3113_ == 0)
{
lean_dec(v___x_3106_);
goto v___jp_3097_;
}
else
{
lean_object* v___x_3114_; lean_object* v___x_3115_; 
lean_del_object(v___x_3095_);
lean_dec(v_snd_3093_);
v___x_3114_ = lean_box(v___x_3111_);
v___x_3115_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3115_, 0, v___x_3103_);
lean_ctor_set(v___x_3115_, 1, v___x_3114_);
v_a_3086_ = v___x_3106_;
v_b_3087_ = v___x_3115_;
goto _start;
}
}
}
else
{
uint8_t v___x_3117_; 
lean_del_object(v___x_3095_);
v___x_3117_ = lean_unbox(v_snd_3093_);
if (v___x_3117_ == 0)
{
lean_object* v___x_3118_; lean_object* v___x_3119_; lean_object* v___x_3120_; 
lean_dec(v___x_3106_);
v___x_3118_ = lean_box(v_decide_3092_);
v___x_3119_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3119_, 0, v___x_3118_);
v___x_3120_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3120_, 0, v___x_3119_);
lean_ctor_set(v___x_3120_, 1, v_snd_3093_);
return v___x_3120_;
}
else
{
lean_object* v___x_3121_; lean_object* v___x_3122_; 
lean_dec(v_snd_3093_);
v___x_3121_ = lean_box(v_decide_3092_);
v___x_3122_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3122_, 0, v___x_3103_);
lean_ctor_set(v___x_3122_, 1, v___x_3121_);
v_a_3086_ = v___x_3106_;
v_b_3087_ = v___x_3122_;
goto _start;
}
}
v___jp_3097_:
{
lean_object* v___x_3098_; lean_object* v___x_3099_; lean_object* v___x_3101_; 
v___x_3098_ = lean_box(v_decide_3092_);
v___x_3099_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3099_, 0, v___x_3098_);
if (v_isShared_3096_ == 0)
{
lean_ctor_set(v___x_3095_, 0, v___x_3099_);
v___x_3101_ = v___x_3095_;
goto v_reusejp_3100_;
}
else
{
lean_object* v_reuseFailAlloc_3102_; 
v_reuseFailAlloc_3102_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3102_, 0, v___x_3099_);
lean_ctor_set(v_reuseFailAlloc_3102_, 1, v_snd_3093_);
v___x_3101_ = v_reuseFailAlloc_3102_;
goto v_reusejp_3100_;
}
v_reusejp_3100_:
{
return v___x_3101_;
}
}
}
}
else
{
lean_dec(v_a_3086_);
return v_b_3087_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg___boxed(lean_object* v_s_3126_, lean_object* v_a_3127_, lean_object* v_b_3128_){
_start:
{
lean_object* v_res_3129_; 
v_res_3129_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3126_, v_a_3127_, v_b_3128_);
lean_dec_ref(v_s_3126_);
return v_res_3129_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isNat(lean_object* v_s_3134_){
_start:
{
lean_object* v___x_3135_; lean_object* v___x_3136_; lean_object* v___x_3137_; lean_object* v_fst_3138_; 
v___x_3135_ = ((lean_object*)(l_String_Slice_isNat___closed__0));
v___x_3136_ = lean_unsigned_to_nat(0u);
v___x_3137_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3134_, v___x_3136_, v___x_3135_);
v_fst_3138_ = lean_ctor_get(v___x_3137_, 0);
if (lean_obj_tag(v_fst_3138_) == 0)
{
lean_object* v_snd_3139_; uint8_t v___x_3140_; 
v_snd_3139_ = lean_ctor_get(v___x_3137_, 1);
lean_inc(v_snd_3139_);
lean_dec_ref(v___x_3137_);
v___x_3140_ = lean_unbox(v_snd_3139_);
lean_dec(v_snd_3139_);
return v___x_3140_;
}
else
{
lean_object* v_val_3141_; uint8_t v___x_3142_; 
lean_inc_ref(v_fst_3138_);
lean_dec_ref(v___x_3137_);
v_val_3141_ = lean_ctor_get(v_fst_3138_, 0);
lean_inc(v_val_3141_);
lean_dec_ref_known(v_fst_3138_, 1);
v___x_3142_ = lean_unbox(v_val_3141_);
lean_dec(v_val_3141_);
return v___x_3142_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object* v_s_3143_){
_start:
{
uint8_t v_res_3144_; lean_object* v_r_3145_; 
v_res_3144_ = l_String_Slice_isNat(v_s_3143_);
lean_dec_ref(v_s_3143_);
v_r_3145_ = lean_box(v_res_3144_);
return v_r_3145_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(lean_object* v_s_3146_, lean_object* v_inst_3147_, lean_object* v_R_3148_, lean_object* v_a_3149_, lean_object* v_b_3150_, lean_object* v_c_3151_){
_start:
{
lean_object* v___x_3152_; 
v___x_3152_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3146_, v_a_3149_, v_b_3150_);
return v___x_3152_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___boxed(lean_object* v_s_3153_, lean_object* v_inst_3154_, lean_object* v_R_3155_, lean_object* v_a_3156_, lean_object* v_b_3157_, lean_object* v_c_3158_){
_start:
{
lean_object* v_res_3159_; 
v_res_3159_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(v_s_3153_, v_inst_3154_, v_R_3155_, v_a_3156_, v_b_3157_, v_c_3158_);
lean_dec_ref(v_s_3153_);
return v_res_3159_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object* v_s_3160_, lean_object* v_a_3161_, lean_object* v_b_3162_){
_start:
{
lean_object* v_str_3163_; lean_object* v_startInclusive_3164_; lean_object* v_endExclusive_3165_; lean_object* v___x_3166_; uint8_t v_decide_3167_; 
v_str_3163_ = lean_ctor_get(v_s_3160_, 0);
v_startInclusive_3164_ = lean_ctor_get(v_s_3160_, 1);
v_endExclusive_3165_ = lean_ctor_get(v_s_3160_, 2);
v___x_3166_ = lean_nat_sub(v_endExclusive_3165_, v_startInclusive_3164_);
v_decide_3167_ = lean_nat_dec_eq(v_a_3161_, v___x_3166_);
lean_dec(v___x_3166_);
if (v_decide_3167_ == 0)
{
lean_object* v___x_3168_; lean_object* v___x_3169_; lean_object* v___x_3170_; uint32_t v___x_3171_; uint32_t v___x_3172_; uint8_t v___x_3173_; 
v___x_3168_ = lean_nat_add(v_startInclusive_3164_, v_a_3161_);
lean_dec(v_a_3161_);
v___x_3169_ = lean_string_utf8_next_fast(v_str_3163_, v___x_3168_);
v___x_3170_ = lean_nat_sub(v___x_3169_, v_startInclusive_3164_);
v___x_3171_ = lean_string_utf8_get_fast(v_str_3163_, v___x_3168_);
lean_dec(v___x_3168_);
v___x_3172_ = 95;
v___x_3173_ = lean_uint32_dec_eq(v___x_3171_, v___x_3172_);
if (v___x_3173_ == 0)
{
lean_object* v___x_3174_; lean_object* v___x_3175_; lean_object* v___x_3176_; lean_object* v___x_3177_; lean_object* v___x_3178_; lean_object* v___x_3179_; 
v___x_3174_ = lean_unsigned_to_nat(10u);
v___x_3175_ = lean_nat_mul(v_b_3162_, v___x_3174_);
lean_dec(v_b_3162_);
v___x_3176_ = lean_uint32_to_nat(v___x_3171_);
v___x_3177_ = lean_unsigned_to_nat(48u);
v___x_3178_ = lean_nat_sub(v___x_3176_, v___x_3177_);
lean_dec(v___x_3176_);
v___x_3179_ = lean_nat_add(v___x_3175_, v___x_3178_);
lean_dec(v___x_3178_);
lean_dec(v___x_3175_);
v_a_3161_ = v___x_3170_;
v_b_3162_ = v___x_3179_;
goto _start;
}
else
{
v_a_3161_ = v___x_3170_;
goto _start;
}
}
else
{
lean_dec(v_a_3161_);
return v_b_3162_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object* v_s_3182_, lean_object* v_a_3183_, lean_object* v_b_3184_){
_start:
{
lean_object* v_res_3185_; 
v_res_3185_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3182_, v_a_3183_, v_b_3184_);
lean_dec_ref(v_s_3182_);
return v_res_3185_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object* v_s_3186_){
_start:
{
uint8_t v___x_3187_; 
v___x_3187_ = l_String_Slice_isNat(v_s_3186_);
if (v___x_3187_ == 0)
{
lean_object* v___x_3188_; 
v___x_3188_ = lean_box(0);
return v___x_3188_;
}
else
{
lean_object* v___x_3189_; lean_object* v___x_3190_; lean_object* v___x_3191_; 
v___x_3189_ = lean_unsigned_to_nat(0u);
v___x_3190_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3186_, v___x_3189_, v___x_3189_);
v___x_3191_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3191_, 0, v___x_3190_);
return v___x_3191_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object* v_s_3192_){
_start:
{
lean_object* v_res_3193_; 
v_res_3193_ = l_String_Slice_toNat_x3f(v_s_3192_);
lean_dec_ref(v_s_3192_);
return v_res_3193_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object* v_s_3194_, lean_object* v_inst_3195_, lean_object* v_R_3196_, lean_object* v_a_3197_, lean_object* v_b_3198_, lean_object* v_c_3199_){
_start:
{
lean_object* v___x_3200_; 
v___x_3200_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3194_, v_a_3197_, v_b_3198_);
return v___x_3200_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object* v_s_3201_, lean_object* v_inst_3202_, lean_object* v_R_3203_, lean_object* v_a_3204_, lean_object* v_b_3205_, lean_object* v_c_3206_){
_start:
{
lean_object* v_res_3207_; 
v_res_3207_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(v_s_3201_, v_inst_3202_, v_R_3203_, v_a_3204_, v_b_3205_, v_c_3206_);
lean_dec_ref(v_s_3201_);
return v_res_3207_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_toNat_x21_spec__0(lean_object* v_msg_3208_){
_start:
{
lean_object* v___x_3209_; lean_object* v___x_3210_; 
v___x_3209_ = lean_unsigned_to_nat(0u);
v___x_3210_ = lean_panic_fn_borrowed(v___x_3209_, v_msg_3208_);
return v___x_3210_;
}
}
static lean_object* _init_l_String_Slice_toNat_x21___closed__3(void){
_start:
{
lean_object* v___x_3214_; lean_object* v___x_3215_; lean_object* v___x_3216_; lean_object* v___x_3217_; lean_object* v___x_3218_; lean_object* v___x_3219_; 
v___x_3214_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__2));
v___x_3215_ = lean_unsigned_to_nat(4u);
v___x_3216_ = lean_unsigned_to_nat(1040u);
v___x_3217_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__1));
v___x_3218_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__0));
v___x_3219_ = l_mkPanicMessageWithDecl(v___x_3218_, v___x_3217_, v___x_3216_, v___x_3215_, v___x_3214_);
return v___x_3219_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21(lean_object* v_s_3220_){
_start:
{
uint8_t v___x_3221_; 
v___x_3221_ = l_String_Slice_isNat(v_s_3220_);
if (v___x_3221_ == 0)
{
lean_object* v___x_3222_; lean_object* v___x_3223_; 
v___x_3222_ = lean_obj_once(&l_String_Slice_toNat_x21___closed__3, &l_String_Slice_toNat_x21___closed__3_once, _init_l_String_Slice_toNat_x21___closed__3);
v___x_3223_ = l_panic___at___00String_Slice_toNat_x21_spec__0(v___x_3222_);
return v___x_3223_;
}
else
{
lean_object* v___x_3224_; lean_object* v___x_3225_; 
v___x_3224_ = lean_unsigned_to_nat(0u);
v___x_3225_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3220_, v___x_3224_, v___x_3224_);
return v___x_3225_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21___boxed(lean_object* v_s_3226_){
_start:
{
lean_object* v_res_3227_; 
v_res_3227_ = l_String_Slice_toNat_x21(v_s_3226_);
lean_dec_ref(v_s_3226_);
return v_res_3227_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object* v_s_3228_){
_start:
{
lean_object* v___x_3229_; lean_object* v___x_3230_; 
v___x_3229_ = lean_unsigned_to_nat(0u);
v___x_3230_ = l_String_Slice_Pos_get_x3f(v_s_3228_, v___x_3229_);
return v___x_3230_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object* v_s_3231_){
_start:
{
lean_object* v_res_3232_; 
v_res_3232_ = l_String_Slice_front_x3f(v_s_3231_);
lean_dec_ref(v_s_3231_);
return v_res_3232_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_front(lean_object* v_s_3233_){
_start:
{
lean_object* v___x_3234_; lean_object* v___x_3235_; 
v___x_3234_ = lean_unsigned_to_nat(0u);
v___x_3235_ = l_String_Slice_Pos_get_x3f(v_s_3233_, v___x_3234_);
if (lean_obj_tag(v___x_3235_) == 0)
{
uint32_t v___x_3236_; 
v___x_3236_ = 65;
return v___x_3236_;
}
else
{
lean_object* v_val_3237_; uint32_t v___x_3238_; 
v_val_3237_ = lean_ctor_get(v___x_3235_, 0);
lean_inc(v_val_3237_);
lean_dec_ref_known(v___x_3235_, 1);
v___x_3238_ = lean_unbox_uint32(v_val_3237_);
lean_dec(v_val_3237_);
return v___x_3238_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object* v_s_3239_){
_start:
{
uint32_t v_res_3240_; lean_object* v_r_3241_; 
v_res_3240_ = l_String_Slice_front(v_s_3239_);
lean_dec_ref(v_s_3239_);
v_r_3241_ = lean_box_uint32(v_res_3240_);
return v_r_3241_;
}
}
LEAN_EXPORT uint8_t l_String_Slice_isInt(lean_object* v_s_3242_){
_start:
{
lean_object* v_str_3243_; lean_object* v_startInclusive_3244_; lean_object* v_endExclusive_3245_; lean_object* v___x_3246_; lean_object* v___x_3247_; uint8_t v_decide_3248_; 
v_str_3243_ = lean_ctor_get(v_s_3242_, 0);
v_startInclusive_3244_ = lean_ctor_get(v_s_3242_, 1);
v_endExclusive_3245_ = lean_ctor_get(v_s_3242_, 2);
v___x_3246_ = lean_unsigned_to_nat(0u);
v___x_3247_ = lean_nat_sub(v_endExclusive_3245_, v_startInclusive_3244_);
v_decide_3248_ = lean_nat_dec_eq(v___x_3246_, v___x_3247_);
lean_dec(v___x_3247_);
if (v_decide_3248_ == 0)
{
uint32_t v___x_3249_; uint32_t v___x_3250_; uint8_t v___x_3251_; 
v___x_3249_ = 45;
v___x_3250_ = lean_string_utf8_get_fast(v_str_3243_, v_startInclusive_3244_);
v___x_3251_ = lean_uint32_dec_eq(v___x_3250_, v___x_3249_);
if (v___x_3251_ == 0)
{
uint8_t v___x_3252_; 
v___x_3252_ = l_String_Slice_isNat(v_s_3242_);
lean_dec_ref(v_s_3242_);
return v___x_3252_;
}
else
{
lean_object* v___x_3254_; uint8_t v_isShared_3255_; uint8_t v_isSharedCheck_3263_; 
lean_inc(v_endExclusive_3245_);
lean_inc(v_startInclusive_3244_);
lean_inc_ref(v_str_3243_);
v_isSharedCheck_3263_ = !lean_is_exclusive(v_s_3242_);
if (v_isSharedCheck_3263_ == 0)
{
lean_object* v_unused_3264_; lean_object* v_unused_3265_; lean_object* v_unused_3266_; 
v_unused_3264_ = lean_ctor_get(v_s_3242_, 2);
lean_dec(v_unused_3264_);
v_unused_3265_ = lean_ctor_get(v_s_3242_, 1);
lean_dec(v_unused_3265_);
v_unused_3266_ = lean_ctor_get(v_s_3242_, 0);
lean_dec(v_unused_3266_);
v___x_3254_ = v_s_3242_;
v_isShared_3255_ = v_isSharedCheck_3263_;
goto v_resetjp_3253_;
}
else
{
lean_dec(v_s_3242_);
v___x_3254_ = lean_box(0);
v_isShared_3255_ = v_isSharedCheck_3263_;
goto v_resetjp_3253_;
}
v_resetjp_3253_:
{
lean_object* v___x_3256_; lean_object* v___x_3257_; lean_object* v___x_3258_; lean_object* v___x_3260_; 
v___x_3256_ = lean_string_utf8_next_fast(v_str_3243_, v_startInclusive_3244_);
v___x_3257_ = lean_nat_sub(v___x_3256_, v_startInclusive_3244_);
v___x_3258_ = lean_nat_add(v_startInclusive_3244_, v___x_3257_);
lean_dec(v___x_3257_);
lean_dec(v_startInclusive_3244_);
if (v_isShared_3255_ == 0)
{
lean_ctor_set(v___x_3254_, 1, v___x_3258_);
v___x_3260_ = v___x_3254_;
goto v_reusejp_3259_;
}
else
{
lean_object* v_reuseFailAlloc_3262_; 
v_reuseFailAlloc_3262_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3262_, 0, v_str_3243_);
lean_ctor_set(v_reuseFailAlloc_3262_, 1, v___x_3258_);
lean_ctor_set(v_reuseFailAlloc_3262_, 2, v_endExclusive_3245_);
v___x_3260_ = v_reuseFailAlloc_3262_;
goto v_reusejp_3259_;
}
v_reusejp_3259_:
{
uint8_t v___x_3261_; 
v___x_3261_ = l_String_Slice_isNat(v___x_3260_);
lean_dec_ref(v___x_3260_);
return v___x_3261_;
}
}
}
}
else
{
uint8_t v___x_3267_; 
v___x_3267_ = l_String_Slice_isNat(v_s_3242_);
lean_dec_ref(v_s_3242_);
return v___x_3267_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object* v_s_3268_){
_start:
{
uint8_t v_res_3269_; lean_object* v_r_3270_; 
v_res_3269_ = l_String_Slice_isInt(v_s_3268_);
v_r_3270_ = lean_box(v_res_3269_);
return v_r_3270_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x3f(lean_object* v_s_3271_){
_start:
{
lean_object* v_str_3284_; lean_object* v_startInclusive_3285_; lean_object* v_endExclusive_3286_; lean_object* v___x_3287_; lean_object* v___x_3288_; uint8_t v_decide_3289_; 
v_str_3284_ = lean_ctor_get(v_s_3271_, 0);
v_startInclusive_3285_ = lean_ctor_get(v_s_3271_, 1);
v_endExclusive_3286_ = lean_ctor_get(v_s_3271_, 2);
v___x_3287_ = lean_unsigned_to_nat(0u);
v___x_3288_ = lean_nat_sub(v_endExclusive_3286_, v_startInclusive_3285_);
v_decide_3289_ = lean_nat_dec_eq(v___x_3287_, v___x_3288_);
lean_dec(v___x_3288_);
if (v_decide_3289_ == 0)
{
uint32_t v___x_3290_; uint32_t v___x_3291_; uint8_t v___x_3292_; 
v___x_3290_ = 45;
v___x_3291_ = lean_string_utf8_get_fast(v_str_3284_, v_startInclusive_3285_);
v___x_3292_ = lean_uint32_dec_eq(v___x_3291_, v___x_3290_);
if (v___x_3292_ == 0)
{
goto v___jp_3272_;
}
else
{
lean_object* v___x_3294_; uint8_t v_isShared_3295_; uint8_t v_isSharedCheck_3313_; 
lean_inc(v_endExclusive_3286_);
lean_inc(v_startInclusive_3285_);
lean_inc_ref(v_str_3284_);
v_isSharedCheck_3313_ = !lean_is_exclusive(v_s_3271_);
if (v_isSharedCheck_3313_ == 0)
{
lean_object* v_unused_3314_; lean_object* v_unused_3315_; lean_object* v_unused_3316_; 
v_unused_3314_ = lean_ctor_get(v_s_3271_, 2);
lean_dec(v_unused_3314_);
v_unused_3315_ = lean_ctor_get(v_s_3271_, 1);
lean_dec(v_unused_3315_);
v_unused_3316_ = lean_ctor_get(v_s_3271_, 0);
lean_dec(v_unused_3316_);
v___x_3294_ = v_s_3271_;
v_isShared_3295_ = v_isSharedCheck_3313_;
goto v_resetjp_3293_;
}
else
{
lean_dec(v_s_3271_);
v___x_3294_ = lean_box(0);
v_isShared_3295_ = v_isSharedCheck_3313_;
goto v_resetjp_3293_;
}
v_resetjp_3293_:
{
lean_object* v___x_3296_; lean_object* v___x_3297_; lean_object* v___x_3298_; lean_object* v___x_3300_; 
v___x_3296_ = lean_string_utf8_next_fast(v_str_3284_, v_startInclusive_3285_);
v___x_3297_ = lean_nat_sub(v___x_3296_, v_startInclusive_3285_);
v___x_3298_ = lean_nat_add(v_startInclusive_3285_, v___x_3297_);
lean_dec(v___x_3297_);
lean_dec(v_startInclusive_3285_);
if (v_isShared_3295_ == 0)
{
lean_ctor_set(v___x_3294_, 1, v___x_3298_);
v___x_3300_ = v___x_3294_;
goto v_reusejp_3299_;
}
else
{
lean_object* v_reuseFailAlloc_3312_; 
v_reuseFailAlloc_3312_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3312_, 0, v_str_3284_);
lean_ctor_set(v_reuseFailAlloc_3312_, 1, v___x_3298_);
lean_ctor_set(v_reuseFailAlloc_3312_, 2, v_endExclusive_3286_);
v___x_3300_ = v_reuseFailAlloc_3312_;
goto v_reusejp_3299_;
}
v_reusejp_3299_:
{
lean_object* v___x_3301_; 
v___x_3301_ = l_String_Slice_toNat_x3f(v___x_3300_);
lean_dec_ref(v___x_3300_);
if (lean_obj_tag(v___x_3301_) == 0)
{
lean_object* v___x_3302_; 
v___x_3302_ = lean_box(0);
return v___x_3302_;
}
else
{
lean_object* v_val_3303_; lean_object* v___x_3305_; uint8_t v_isShared_3306_; uint8_t v_isSharedCheck_3311_; 
v_val_3303_ = lean_ctor_get(v___x_3301_, 0);
v_isSharedCheck_3311_ = !lean_is_exclusive(v___x_3301_);
if (v_isSharedCheck_3311_ == 0)
{
v___x_3305_ = v___x_3301_;
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
else
{
lean_inc(v_val_3303_);
lean_dec(v___x_3301_);
v___x_3305_ = lean_box(0);
v_isShared_3306_ = v_isSharedCheck_3311_;
goto v_resetjp_3304_;
}
v_resetjp_3304_:
{
lean_object* v___x_3307_; lean_object* v___x_3309_; 
v___x_3307_ = l_Int_negOfNat(v_val_3303_);
lean_dec(v_val_3303_);
if (v_isShared_3306_ == 0)
{
lean_ctor_set(v___x_3305_, 0, v___x_3307_);
v___x_3309_ = v___x_3305_;
goto v_reusejp_3308_;
}
else
{
lean_object* v_reuseFailAlloc_3310_; 
v_reuseFailAlloc_3310_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3310_, 0, v___x_3307_);
v___x_3309_ = v_reuseFailAlloc_3310_;
goto v_reusejp_3308_;
}
v_reusejp_3308_:
{
return v___x_3309_;
}
}
}
}
}
}
}
else
{
goto v___jp_3272_;
}
v___jp_3272_:
{
lean_object* v___x_3273_; 
v___x_3273_ = l_String_Slice_toNat_x3f(v_s_3271_);
lean_dec_ref(v_s_3271_);
if (lean_obj_tag(v___x_3273_) == 0)
{
lean_object* v___x_3274_; 
v___x_3274_ = lean_box(0);
return v___x_3274_;
}
else
{
lean_object* v_val_3275_; lean_object* v___x_3277_; uint8_t v_isShared_3278_; uint8_t v_isSharedCheck_3283_; 
v_val_3275_ = lean_ctor_get(v___x_3273_, 0);
v_isSharedCheck_3283_ = !lean_is_exclusive(v___x_3273_);
if (v_isSharedCheck_3283_ == 0)
{
v___x_3277_ = v___x_3273_;
v_isShared_3278_ = v_isSharedCheck_3283_;
goto v_resetjp_3276_;
}
else
{
lean_inc(v_val_3275_);
lean_dec(v___x_3273_);
v___x_3277_ = lean_box(0);
v_isShared_3278_ = v_isSharedCheck_3283_;
goto v_resetjp_3276_;
}
v_resetjp_3276_:
{
lean_object* v___x_3279_; lean_object* v___x_3281_; 
v___x_3279_ = lean_nat_to_int(v_val_3275_);
if (v_isShared_3278_ == 0)
{
lean_ctor_set(v___x_3277_, 0, v___x_3279_);
v___x_3281_ = v___x_3277_;
goto v_reusejp_3280_;
}
else
{
lean_object* v_reuseFailAlloc_3282_; 
v_reuseFailAlloc_3282_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3282_, 0, v___x_3279_);
v___x_3281_ = v_reuseFailAlloc_3282_;
goto v_reusejp_3280_;
}
v_reusejp_3280_:
{
return v___x_3281_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x21(lean_object* v_s_3318_){
_start:
{
lean_object* v___x_3319_; 
v___x_3319_ = l_String_Slice_toInt_x3f(v_s_3318_);
if (lean_obj_tag(v___x_3319_) == 0)
{
lean_object* v___x_3320_; lean_object* v___x_3321_; lean_object* v___x_3322_; 
v___x_3320_ = l_Int_instInhabited;
v___x_3321_ = ((lean_object*)(l_String_Slice_toInt_x21___closed__0));
v___x_3322_ = l_panic___redArg(v___x_3320_, v___x_3321_);
return v___x_3322_;
}
else
{
lean_object* v_val_3323_; 
v_val_3323_ = lean_ctor_get(v___x_3319_, 0);
lean_inc(v_val_3323_);
lean_dec_ref_known(v___x_3319_, 1);
return v_val_3323_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object* v_s_3324_){
_start:
{
lean_object* v_startInclusive_3325_; lean_object* v_endExclusive_3326_; lean_object* v___x_3327_; lean_object* v___x_3328_; 
v_startInclusive_3325_ = lean_ctor_get(v_s_3324_, 1);
v_endExclusive_3326_ = lean_ctor_get(v_s_3324_, 2);
v___x_3327_ = lean_nat_sub(v_endExclusive_3326_, v_startInclusive_3325_);
v___x_3328_ = l_String_Slice_Pos_prev_x3f(v_s_3324_, v___x_3327_);
lean_dec(v___x_3327_);
if (lean_obj_tag(v___x_3328_) == 0)
{
lean_object* v___x_3329_; 
v___x_3329_ = lean_box(0);
return v___x_3329_;
}
else
{
lean_object* v_val_3330_; lean_object* v___x_3331_; 
v_val_3330_ = lean_ctor_get(v___x_3328_, 0);
lean_inc(v_val_3330_);
lean_dec_ref_known(v___x_3328_, 1);
v___x_3331_ = l_String_Slice_Pos_get_x3f(v_s_3324_, v_val_3330_);
lean_dec(v_val_3330_);
return v___x_3331_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object* v_s_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_String_Slice_back_x3f(v_s_3332_);
lean_dec_ref(v_s_3332_);
return v_res_3333_;
}
}
LEAN_EXPORT uint32_t l_String_Slice_back(lean_object* v_s_3334_){
_start:
{
lean_object* v_startInclusive_3335_; lean_object* v_endExclusive_3336_; lean_object* v___x_3337_; lean_object* v___x_3338_; 
v_startInclusive_3335_ = lean_ctor_get(v_s_3334_, 1);
v_endExclusive_3336_ = lean_ctor_get(v_s_3334_, 2);
v___x_3337_ = lean_nat_sub(v_endExclusive_3336_, v_startInclusive_3335_);
v___x_3338_ = l_String_Slice_Pos_prev_x3f(v_s_3334_, v___x_3337_);
lean_dec(v___x_3337_);
if (lean_obj_tag(v___x_3338_) == 0)
{
uint32_t v___x_3339_; 
v___x_3339_ = 65;
return v___x_3339_;
}
else
{
lean_object* v_val_3340_; lean_object* v___x_3341_; 
v_val_3340_ = lean_ctor_get(v___x_3338_, 0);
lean_inc(v_val_3340_);
lean_dec_ref_known(v___x_3338_, 1);
v___x_3341_ = l_String_Slice_Pos_get_x3f(v_s_3334_, v_val_3340_);
lean_dec(v_val_3340_);
if (lean_obj_tag(v___x_3341_) == 0)
{
uint32_t v___x_3342_; 
v___x_3342_ = 65;
return v___x_3342_;
}
else
{
lean_object* v_val_3343_; uint32_t v___x_3344_; 
v_val_3343_ = lean_ctor_get(v___x_3341_, 0);
lean_inc(v_val_3343_);
lean_dec_ref_known(v___x_3341_, 1);
v___x_3344_ = lean_unbox_uint32(v_val_3343_);
lean_dec(v_val_3343_);
return v___x_3344_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object* v_s_3345_){
_start:
{
uint32_t v_res_3346_; lean_object* v_r_3347_; 
v_res_3346_ = l_String_Slice_back(v_s_3345_);
lean_dec_ref(v_s_3345_);
v_r_3347_ = lean_box_uint32(v_res_3346_);
return v_r_3347_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(lean_object* v_acc_3348_, lean_object* v_s_3349_, lean_object* v_a_3350_){
_start:
{
if (lean_obj_tag(v_a_3350_) == 0)
{
return v_acc_3348_;
}
else
{
lean_object* v_head_3351_; lean_object* v_tail_3352_; lean_object* v_str_3353_; lean_object* v_startInclusive_3354_; lean_object* v_endExclusive_3355_; lean_object* v_str_3356_; lean_object* v_startInclusive_3357_; lean_object* v_endExclusive_3358_; lean_object* v___x_3359_; lean_object* v___x_3360_; lean_object* v___x_3361_; lean_object* v___x_3362_; 
v_head_3351_ = lean_ctor_get(v_a_3350_, 0);
v_tail_3352_ = lean_ctor_get(v_a_3350_, 1);
v_str_3353_ = lean_ctor_get(v_s_3349_, 0);
v_startInclusive_3354_ = lean_ctor_get(v_s_3349_, 1);
v_endExclusive_3355_ = lean_ctor_get(v_s_3349_, 2);
v_str_3356_ = lean_ctor_get(v_head_3351_, 0);
v_startInclusive_3357_ = lean_ctor_get(v_head_3351_, 1);
v_endExclusive_3358_ = lean_ctor_get(v_head_3351_, 2);
v___x_3359_ = lean_string_utf8_extract_fast(v_str_3353_, v_startInclusive_3354_, v_endExclusive_3355_);
v___x_3360_ = lean_string_append(v_acc_3348_, v___x_3359_);
lean_dec_ref(v___x_3359_);
v___x_3361_ = lean_string_utf8_extract_fast(v_str_3356_, v_startInclusive_3357_, v_endExclusive_3358_);
v___x_3362_ = lean_string_append(v___x_3360_, v___x_3361_);
lean_dec_ref(v___x_3361_);
v_acc_3348_ = v___x_3362_;
v_a_3350_ = v_tail_3352_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go___boxed(lean_object* v_acc_3364_, lean_object* v_s_3365_, lean_object* v_a_3366_){
_start:
{
lean_object* v_res_3367_; 
v_res_3367_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v_acc_3364_, v_s_3365_, v_a_3366_);
lean_dec(v_a_3366_);
lean_dec_ref(v_s_3365_);
return v_res_3367_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object* v_s_3368_, lean_object* v_x_3369_){
_start:
{
if (lean_obj_tag(v_x_3369_) == 0)
{
lean_object* v___x_3370_; 
v___x_3370_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
return v___x_3370_;
}
else
{
lean_object* v_head_3371_; lean_object* v_tail_3372_; lean_object* v_str_3373_; lean_object* v_startInclusive_3374_; lean_object* v_endExclusive_3375_; lean_object* v___x_3376_; lean_object* v___x_3377_; 
v_head_3371_ = lean_ctor_get(v_x_3369_, 0);
v_tail_3372_ = lean_ctor_get(v_x_3369_, 1);
v_str_3373_ = lean_ctor_get(v_head_3371_, 0);
v_startInclusive_3374_ = lean_ctor_get(v_head_3371_, 1);
v_endExclusive_3375_ = lean_ctor_get(v_head_3371_, 2);
v___x_3376_ = lean_string_utf8_extract_fast(v_str_3373_, v_startInclusive_3374_, v_endExclusive_3375_);
v___x_3377_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v___x_3376_, v_s_3368_, v_tail_3372_);
return v___x_3377_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object* v_s_3378_, lean_object* v_x_3379_){
_start:
{
lean_object* v_res_3380_; 
v_res_3380_ = l_String_Slice_intercalate(v_s_3378_, v_x_3379_);
lean_dec(v_x_3379_);
lean_dec_ref(v_s_3378_);
return v_res_3380_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0(lean_object* v_x_3381_, lean_object* v_x_3382_){
_start:
{
if (lean_obj_tag(v_x_3382_) == 0)
{
return v_x_3381_;
}
else
{
lean_object* v_head_3383_; lean_object* v_tail_3384_; lean_object* v_str_3385_; lean_object* v_startInclusive_3386_; lean_object* v_endExclusive_3387_; lean_object* v___x_3388_; lean_object* v___x_3389_; 
v_head_3383_ = lean_ctor_get(v_x_3382_, 0);
v_tail_3384_ = lean_ctor_get(v_x_3382_, 1);
v_str_3385_ = lean_ctor_get(v_head_3383_, 0);
v_startInclusive_3386_ = lean_ctor_get(v_head_3383_, 1);
v_endExclusive_3387_ = lean_ctor_get(v_head_3383_, 2);
v___x_3388_ = lean_string_utf8_extract_fast(v_str_3385_, v_startInclusive_3386_, v_endExclusive_3387_);
v___x_3389_ = lean_string_append(v_x_3381_, v___x_3388_);
lean_dec_ref(v___x_3388_);
v_x_3381_ = v___x_3389_;
v_x_3382_ = v_tail_3384_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0___boxed(lean_object* v_x_3391_, lean_object* v_x_3392_){
_start:
{
lean_object* v_res_3393_; 
v_res_3393_ = l_List_foldl___at___00String_Slice_join_spec__0(v_x_3391_, v_x_3392_);
lean_dec(v_x_3392_);
return v_res_3393_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join(lean_object* v_l_3394_){
_start:
{
lean_object* v___x_3395_; lean_object* v___x_3396_; 
v___x_3395_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
v___x_3396_ = l_List_foldl___at___00String_Slice_join_spec__0(v___x_3395_, v_l_3394_);
return v___x_3396_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join___boxed(lean_object* v_l_3397_){
_start:
{
lean_object* v_res_3398_; 
v_res_3398_ = l_String_Slice_join(v_l_3397_);
lean_dec(v_l_3397_);
return v_res_3398_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object* v_s_3399_){
_start:
{
lean_object* v___x_3400_; lean_object* v___x_3401_; 
v___x_3400_ = l_String_Slice_toString(v_s_3399_);
v___x_3401_ = l_String_toName(v___x_3400_);
return v___x_3401_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object* v_s_3402_){
_start:
{
lean_object* v_res_3403_; 
v_res_3403_ = l_String_Slice_toName(v_s_3402_);
lean_dec_ref(v_s_3402_);
return v_res_3403_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object* v_s_3404_){
_start:
{
lean_object* v_str_3405_; lean_object* v_startInclusive_3406_; lean_object* v_endExclusive_3407_; lean_object* v___x_3408_; lean_object* v___x_3409_; 
v_str_3405_ = lean_ctor_get(v_s_3404_, 0);
v_startInclusive_3406_ = lean_ctor_get(v_s_3404_, 1);
v_endExclusive_3407_ = lean_ctor_get(v_s_3404_, 2);
v___x_3408_ = lean_string_utf8_extract_fast(v_str_3405_, v_startInclusive_3406_, v_endExclusive_3407_);
v___x_3409_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3409_, 0, v___x_3408_);
return v___x_3409_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object* v_s_3410_){
_start:
{
lean_object* v_res_3411_; 
v_res_3411_ = l_String_Slice_instToFormat___lam__0(v_s_3410_);
lean_dec_ref(v_s_3410_);
return v_res_3411_;
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
