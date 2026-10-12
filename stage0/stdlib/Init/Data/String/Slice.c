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
uint8_t l_String_Slice_beq(lean_object* v_s1_13_, lean_object* v_s2_14_){
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
LEAN_EXPORT void l_String_Slice_beq_0interp(lean_interpreter_value* stack)
{
lean_object* v_s1_13_ = stack[0].m_obj;
lean_object* v_s2_14_ = stack[1].m_obj;
uint8_t v_res_25_;
v_res_25_ = l_String_Slice_beq(v_s1_13_, v_s2_14_);
stack->m_num = v_res_25_;
}
LEAN_EXPORT lean_object* l_String_Slice_beq___boxed(lean_object* v_s1_26_, lean_object* v_s2_27_){
_start:
{
uint8_t v_res_28_; lean_object* v_r_29_; 
v_res_28_ = l_String_Slice_beq(v_s1_26_, v_s2_27_);
lean_dec_ref(v_s2_27_);
lean_dec_ref(v_s1_26_);
v_r_29_ = lean_box(v_res_28_);
return v_r_29_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toString(lean_object* v_s_32_){
_start:
{
lean_object* v_str_33_; lean_object* v_startInclusive_34_; lean_object* v_endExclusive_35_; lean_object* v___x_36_; 
v_str_33_ = lean_ctor_get(v_s_32_, 0);
v_startInclusive_34_ = lean_ctor_get(v_s_32_, 1);
v_endExclusive_35_ = lean_ctor_get(v_s_32_, 2);
v___x_36_ = lean_string_utf8_extract_fast(v_str_33_, v_startInclusive_34_, v_endExclusive_35_);
return v___x_36_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toString___boxed(lean_object* v_s_37_){
_start:
{
lean_object* v_res_38_; 
v_res_38_ = l_String_Slice_toString(v_s_37_);
lean_dec_ref(v_s_37_);
return v_res_38_;
}
}
LEAN_EXPORT void l_String_Slice_hash_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_41_ = stack[0].m_obj;
uint64_t v_res_42_;
v_res_42_ = lean_slice_hash(v_s_41_);
stack->m_num = v_res_42_;
}
LEAN_EXPORT lean_object* l_String_Slice_hash___boxed(lean_object* v_s_43_){
_start:
{
uint64_t v_res_44_; lean_object* v_r_45_; 
v_res_44_ = lean_slice_hash(v_s_43_);
lean_dec_ref(v_s_43_);
v_r_45_ = lean_box_uint64(v_res_44_);
return v_r_45_;
}
}
static lean_object* _init_l_String_Slice_instLT(void){
_start:
{
lean_object* v___x_48_; 
v___x_48_ = lean_box(0);
return v___x_48_;
}
}
LEAN_EXPORT void l_String_Slice_instDecidableLt_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_49_ = stack[0].m_obj;
lean_object* v_y_50_ = stack[1].m_obj;
uint8_t v_res_51_;
v_res_51_ = lean_slice_dec_lt(v_x_49_, v_y_50_);
stack->m_num = v_res_51_;
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLt___boxed(lean_object* v_x_52_, lean_object* v_y_53_){
_start:
{
uint8_t v_res_54_; lean_object* v_r_55_; 
v_res_54_ = lean_slice_dec_lt(v_x_52_, v_y_53_);
lean_dec_ref(v_y_53_);
lean_dec_ref(v_x_52_);
v_r_55_ = lean_box(v_res_54_);
return v_r_55_;
}
}
uint8_t l_String_Slice_instOrd___lam__0(lean_object* v_x_56_, lean_object* v_y_57_){
_start:
{
uint8_t v___x_58_; 
v___x_58_ = lean_slice_dec_lt(v_x_56_, v_y_57_);
if (v___x_58_ == 0)
{
uint8_t v___x_59_; 
v___x_59_ = l_String_Slice_beq(v_x_56_, v_y_57_);
if (v___x_59_ == 0)
{
uint8_t v___x_60_; 
v___x_60_ = 2;
return v___x_60_;
}
else
{
uint8_t v___x_61_; 
v___x_61_ = 1;
return v___x_61_;
}
}
else
{
uint8_t v___x_62_; 
v___x_62_ = 0;
return v___x_62_;
}
}
}
LEAN_EXPORT void l_String_Slice_instOrd___lam__0_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_56_ = stack[0].m_obj;
lean_object* v_y_57_ = stack[1].m_obj;
uint8_t v_res_63_;
v_res_63_ = l_String_Slice_instOrd___lam__0(v_x_56_, v_y_57_);
stack->m_num = v_res_63_;
}
LEAN_EXPORT lean_object* l_String_Slice_instOrd___lam__0___boxed(lean_object* v_x_64_, lean_object* v_y_65_){
_start:
{
uint8_t v_res_66_; lean_object* v_r_67_; 
v_res_66_ = l_String_Slice_instOrd___lam__0(v_x_64_, v_y_65_);
lean_dec_ref(v_y_65_);
lean_dec_ref(v_x_64_);
v_r_67_ = lean_box(v_res_66_);
return v_r_67_;
}
}
static lean_object* _init_l_String_Slice_instLE(void){
_start:
{
lean_object* v___x_70_; 
v___x_70_ = lean_box(0);
return v___x_70_;
}
}
uint8_t l_String_Slice_instDecidableLE(lean_object* v_x_71_, lean_object* v_y_72_){
_start:
{
uint8_t v___x_73_; 
v___x_73_ = lean_slice_dec_lt(v_x_71_, v_y_72_);
if (v___x_73_ == 0)
{
uint8_t v___x_74_; 
v___x_74_ = 1;
return v___x_74_;
}
else
{
uint8_t v___x_75_; 
v___x_75_ = 0;
return v___x_75_;
}
}
}
LEAN_EXPORT void l_String_Slice_instDecidableLE_0interp(lean_interpreter_value* stack)
{
lean_object* v_x_71_ = stack[0].m_obj;
lean_object* v_y_72_ = stack[1].m_obj;
uint8_t v_res_76_;
v_res_76_ = l_String_Slice_instDecidableLE(v_x_71_, v_y_72_);
stack->m_num = v_res_76_;
}
LEAN_EXPORT lean_object* l_String_Slice_instDecidableLE___boxed(lean_object* v_x_77_, lean_object* v_y_78_){
_start:
{
uint8_t v_res_79_; lean_object* v_r_80_; 
v_res_79_ = l_String_Slice_instDecidableLE(v_x_77_, v_y_78_);
lean_dec_ref(v_y_78_);
lean_dec_ref(v_x_77_);
v_r_80_ = lean_box(v_res_79_);
return v_r_80_;
}
}
uint8_t l_String_Slice_startsWith___redArg(lean_object* v_s_81_, lean_object* v_inst_82_){
_start:
{
lean_object* v_startsWith_83_; lean_object* v___x_84_; uint8_t v___x_85_; 
v_startsWith_83_ = lean_ctor_get(v_inst_82_, 2);
lean_inc_ref(v_startsWith_83_);
lean_dec_ref(v_inst_82_);
v___x_84_ = lean_apply_1(v_startsWith_83_, v_s_81_);
v___x_85_ = lean_unbox(v___x_84_);
return v___x_85_;
}
}
LEAN_EXPORT void l_String_Slice_startsWith___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_81_ = stack[0].m_obj;
lean_object* v_inst_82_ = stack[1].m_obj;
uint8_t v_res_86_;
v_res_86_ = l_String_Slice_startsWith___redArg(v_s_81_, v_inst_82_);
stack->m_num = v_res_86_;
}
LEAN_EXPORT lean_object* l_String_Slice_startsWith___redArg___boxed(lean_object* v_s_87_, lean_object* v_inst_88_){
_start:
{
uint8_t v_res_89_; lean_object* v_r_90_; 
v_res_89_ = l_String_Slice_startsWith___redArg(v_s_87_, v_inst_88_);
v_r_90_ = lean_box(v_res_89_);
return v_r_90_;
}
}
uint8_t l_String_Slice_startsWith(lean_object* v_00_u03c1_91_, lean_object* v_s_92_, lean_object* v_pat_93_, lean_object* v_inst_94_){
_start:
{
lean_object* v_startsWith_95_; lean_object* v___x_96_; uint8_t v___x_97_; 
v_startsWith_95_ = lean_ctor_get(v_inst_94_, 2);
lean_inc_ref(v_startsWith_95_);
lean_dec_ref(v_inst_94_);
v___x_96_ = lean_apply_1(v_startsWith_95_, v_s_92_);
v___x_97_ = lean_unbox(v___x_96_);
return v___x_97_;
}
}
LEAN_EXPORT void l_String_Slice_startsWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_92_ = stack[1].m_obj;
lean_object* v_pat_93_ = stack[2].m_obj;
lean_object* v_inst_94_ = stack[3].m_obj;
uint8_t v_res_98_;
v_res_98_ = l_String_Slice_startsWith(lean_box(0), v_s_92_, v_pat_93_, v_inst_94_);
stack->m_num = v_res_98_;
}
LEAN_EXPORT lean_object* l_String_Slice_startsWith___boxed(lean_object* v_00_u03c1_99_, lean_object* v_s_100_, lean_object* v_pat_101_, lean_object* v_inst_102_){
_start:
{
uint8_t v_res_103_; lean_object* v_r_104_; 
v_res_103_ = l_String_Slice_startsWith(v_00_u03c1_99_, v_s_100_, v_pat_101_, v_inst_102_);
lean_dec(v_pat_101_);
v_r_104_ = lean_box(v_res_103_);
return v_r_104_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___redArg(lean_object* v_x_105_){
_start:
{
lean_object* v___x_106_; 
v___x_106_ = lean_obj_tag_nat(v_x_105_);
return v___x_106_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___redArg___boxed(lean_object* v_x_107_){
_start:
{
lean_object* v_res_108_; 
v_res_108_ = l_String_Slice_SplitIterator_ctorIdx___impl___redArg(v_x_107_);
lean_dec(v_x_107_);
return v_res_108_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl(lean_object* v_00_u03c3_109_, lean_object* v_00_u03c1_110_, lean_object* v_pat_111_, lean_object* v_s_112_, lean_object* v_inst_113_, lean_object* v_x_114_){
_start:
{
lean_object* v___x_115_; 
v___x_115_ = lean_obj_tag_nat(v_x_114_);
return v___x_115_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorIdx___impl___boxed(lean_object* v_00_u03c3_116_, lean_object* v_00_u03c1_117_, lean_object* v_pat_118_, lean_object* v_s_119_, lean_object* v_inst_120_, lean_object* v_x_121_){
_start:
{
lean_object* v_res_122_; 
v_res_122_ = l_String_Slice_SplitIterator_ctorIdx___impl(v_00_u03c3_116_, v_00_u03c1_117_, v_pat_118_, v_s_119_, v_inst_120_, v_x_121_);
lean_dec(v_x_121_);
lean_dec(v_inst_120_);
lean_dec_ref(v_s_119_);
lean_dec(v_pat_118_);
return v_res_122_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___redArg(lean_object* v_t_123_, lean_object* v_k_124_){
_start:
{
if (lean_obj_tag(v_t_123_) == 0)
{
lean_object* v_currPos_125_; lean_object* v_searcher_126_; lean_object* v___x_127_; 
v_currPos_125_ = lean_ctor_get(v_t_123_, 0);
lean_inc(v_currPos_125_);
v_searcher_126_ = lean_ctor_get(v_t_123_, 1);
lean_inc(v_searcher_126_);
lean_dec_ref_known(v_t_123_, 2);
v___x_127_ = lean_apply_2(v_k_124_, v_currPos_125_, v_searcher_126_);
return v___x_127_;
}
else
{
return v_k_124_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim(lean_object* v_00_u03c3_128_, lean_object* v_00_u03c1_129_, lean_object* v_pat_130_, lean_object* v_s_131_, lean_object* v_inst_132_, lean_object* v_motive_133_, lean_object* v_ctorIdx_134_, lean_object* v_t_135_, lean_object* v_h_136_, lean_object* v_k_137_){
_start:
{
lean_object* v___x_138_; 
v___x_138_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_135_, v_k_137_);
return v___x_138_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_139_, lean_object* v_00_u03c1_140_, lean_object* v_pat_141_, lean_object* v_s_142_, lean_object* v_inst_143_, lean_object* v_motive_144_, lean_object* v_ctorIdx_145_, lean_object* v_t_146_, lean_object* v_h_147_, lean_object* v_k_148_){
_start:
{
lean_object* v_res_149_; 
v_res_149_ = l_String_Slice_SplitIterator_ctorElim(v_00_u03c3_139_, v_00_u03c1_140_, v_pat_141_, v_s_142_, v_inst_143_, v_motive_144_, v_ctorIdx_145_, v_t_146_, v_h_147_, v_k_148_);
lean_dec(v_ctorIdx_145_);
lean_dec(v_inst_143_);
lean_dec_ref(v_s_142_);
lean_dec(v_pat_141_);
return v_res_149_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___redArg(lean_object* v_t_150_, lean_object* v_operating_151_){
_start:
{
lean_object* v___x_152_; 
v___x_152_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_150_, v_operating_151_);
return v___x_152_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim(lean_object* v_00_u03c3_153_, lean_object* v_00_u03c1_154_, lean_object* v_pat_155_, lean_object* v_s_156_, lean_object* v_inst_157_, lean_object* v_motive_158_, lean_object* v_t_159_, lean_object* v_h_160_, lean_object* v_operating_161_){
_start:
{
lean_object* v___x_162_; 
v___x_162_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_159_, v_operating_161_);
return v___x_162_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_163_, lean_object* v_00_u03c1_164_, lean_object* v_pat_165_, lean_object* v_s_166_, lean_object* v_inst_167_, lean_object* v_motive_168_, lean_object* v_t_169_, lean_object* v_h_170_, lean_object* v_operating_171_){
_start:
{
lean_object* v_res_172_; 
v_res_172_ = l_String_Slice_SplitIterator_operating_elim(v_00_u03c3_163_, v_00_u03c1_164_, v_pat_165_, v_s_166_, v_inst_167_, v_motive_168_, v_t_169_, v_h_170_, v_operating_171_);
lean_dec(v_inst_167_);
lean_dec_ref(v_s_166_);
lean_dec(v_pat_165_);
return v_res_172_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___redArg(lean_object* v_t_173_, lean_object* v_atEnd_174_){
_start:
{
lean_object* v___x_175_; 
v___x_175_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_173_, v_atEnd_174_);
return v___x_175_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim(lean_object* v_00_u03c3_176_, lean_object* v_00_u03c1_177_, lean_object* v_pat_178_, lean_object* v_s_179_, lean_object* v_inst_180_, lean_object* v_motive_181_, lean_object* v_t_182_, lean_object* v_h_183_, lean_object* v_atEnd_184_){
_start:
{
lean_object* v___x_185_; 
v___x_185_ = l_String_Slice_SplitIterator_ctorElim___redArg(v_t_182_, v_atEnd_184_);
return v___x_185_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_186_, lean_object* v_00_u03c1_187_, lean_object* v_pat_188_, lean_object* v_s_189_, lean_object* v_inst_190_, lean_object* v_motive_191_, lean_object* v_t_192_, lean_object* v_h_193_, lean_object* v_atEnd_194_){
_start:
{
lean_object* v_res_195_; 
v_res_195_ = l_String_Slice_SplitIterator_atEnd_elim(v_00_u03c3_186_, v_00_u03c1_187_, v_pat_188_, v_s_189_, v_inst_190_, v_motive_191_, v_t_192_, v_h_193_, v_atEnd_194_);
lean_dec(v_inst_190_);
lean_dec_ref(v_s_189_);
lean_dec(v_pat_188_);
return v_res_195_;
}
}
lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg(){
_start:
{
lean_object* v___x_197_; 
v___x_197_ = lean_box(1);
return v___x_197_;
}
}
LEAN_EXPORT void l_String_Slice_instInhabitedSplitIterator_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_198_;
v_res_198_ = l_String_Slice_instInhabitedSplitIterator_default___redArg();
stack->m_obj
 = v_res_198_;
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___redArg___boxed(lean_object* v___dummy_199_){
_start:
{
lean_object* v_res_200_; 
v_res_200_ = l_String_Slice_instInhabitedSplitIterator_default___redArg();
return v_res_200_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default(lean_object* v_00_u03c3_201_, lean_object* v_00_u03c1_202_, lean_object* v_pat_203_, lean_object* v_s_204_, lean_object* v_inst_205_){
_start:
{
lean_object* v___x_206_; 
v___x_206_ = lean_box(1);
return v___x_206_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator_default___boxed(lean_object* v_00_u03c3_207_, lean_object* v_00_u03c1_208_, lean_object* v_pat_209_, lean_object* v_s_210_, lean_object* v_inst_211_){
_start:
{
lean_object* v_res_212_; 
v_res_212_ = l_String_Slice_instInhabitedSplitIterator_default(v_00_u03c3_207_, v_00_u03c1_208_, v_pat_209_, v_s_210_, v_inst_211_);
lean_dec(v_inst_211_);
lean_dec_ref(v_s_210_);
lean_dec(v_pat_209_);
return v_res_212_;
}
}
lean_object* l_String_Slice_instInhabitedSplitIterator___redArg(){
_start:
{
lean_object* v___x_214_; 
v___x_214_ = lean_box(1);
return v___x_214_;
}
}
LEAN_EXPORT void l_String_Slice_instInhabitedSplitIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_215_;
v_res_215_ = l_String_Slice_instInhabitedSplitIterator___redArg();
stack->m_obj
 = v_res_215_;
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___redArg___boxed(lean_object* v___dummy_216_){
_start:
{
lean_object* v_res_217_; 
v_res_217_ = l_String_Slice_instInhabitedSplitIterator___redArg();
return v_res_217_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator(lean_object* v_a_218_, lean_object* v_a_219_, lean_object* v_a_220_, lean_object* v_a_221_, lean_object* v_a_222_){
_start:
{
lean_object* v___x_223_; 
v___x_223_ = lean_box(1);
return v___x_223_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitIterator___boxed(lean_object* v_a_224_, lean_object* v_a_225_, lean_object* v_a_226_, lean_object* v_a_227_, lean_object* v_a_228_){
_start:
{
lean_object* v_res_229_; 
v_res_229_ = l_String_Slice_instInhabitedSplitIterator(v_a_224_, v_a_225_, v_a_226_, v_a_227_, v_a_228_);
lean_dec(v_a_228_);
lean_dec_ref(v_a_227_);
lean_dec(v_a_226_);
return v_res_229_;
}
}
lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl(uint8_t v_x_230_){
_start:
{
lean_object* v___x_231_; lean_object* v___x_232_; 
v___x_231_ = lean_box(v_x_230_);
v___x_232_ = lean_obj_tag_nat(v___x_231_);
lean_dec(v___x_231_);
return v___x_232_;
}
}
LEAN_EXPORT void l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl_0interp(lean_interpreter_value* stack)
{
uint8_t v_x_230_ = stack[0].m_num;
lean_object* v_res_233_;
v_res_233_ = l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl(v_x_230_);
stack->m_obj
 = v_res_233_;
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl___boxed(lean_object* v_x_234_){
_start:
{
uint8_t v_x_4__boxed_235_; lean_object* v_res_236_; 
v_x_4__boxed_235_ = lean_unbox(v_x_234_);
v_res_236_ = l_String_Slice_SplitIterator_PlausibleStep_ctorIdx___impl(v_x_4__boxed_235_);
return v_res_236_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0(lean_object* v_inst_237_, lean_object* v_s_238_, lean_object* v_x_239_){
_start:
{
if (lean_obj_tag(v_x_239_) == 0)
{
lean_object* v_currPos_240_; lean_object* v_searcher_241_; lean_object* v___x_243_; uint8_t v_isShared_244_; uint8_t v_isSharedCheck_284_; 
v_currPos_240_ = lean_ctor_get(v_x_239_, 0);
v_searcher_241_ = lean_ctor_get(v_x_239_, 1);
v_isSharedCheck_284_ = !lean_is_exclusive(v_x_239_);
if (v_isSharedCheck_284_ == 0)
{
v___x_243_ = v_x_239_;
v_isShared_244_ = v_isSharedCheck_284_;
goto v_resetjp_242_;
}
else
{
lean_inc(v_searcher_241_);
lean_inc(v_currPos_240_);
lean_dec(v_x_239_);
v___x_243_ = lean_box(0);
v_isShared_244_ = v_isSharedCheck_284_;
goto v_resetjp_242_;
}
v_resetjp_242_:
{
lean_object* v___x_245_; 
lean_inc_ref(v_s_238_);
v___x_245_ = lean_apply_2(v_inst_237_, v_s_238_, v_searcher_241_);
switch(lean_obj_tag(v___x_245_))
{
case 0:
{
lean_object* v_out_246_; 
v_out_246_ = lean_ctor_get(v___x_245_, 1);
lean_inc(v_out_246_);
if (lean_obj_tag(v_out_246_) == 0)
{
lean_object* v_it_247_; lean_object* v___x_249_; 
lean_dec_ref_known(v_out_246_, 2);
lean_dec_ref(v_s_238_);
v_it_247_ = lean_ctor_get(v___x_245_, 0);
lean_inc(v_it_247_);
lean_dec_ref_known(v___x_245_, 2);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v_it_247_);
v___x_249_ = v___x_243_;
goto v_reusejp_248_;
}
else
{
lean_object* v_reuseFailAlloc_251_; 
v_reuseFailAlloc_251_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_251_, 0, v_currPos_240_);
lean_ctor_set(v_reuseFailAlloc_251_, 1, v_it_247_);
v___x_249_ = v_reuseFailAlloc_251_;
goto v_reusejp_248_;
}
v_reusejp_248_:
{
lean_object* v___x_250_; 
v___x_250_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_250_, 0, v___x_249_);
return v___x_250_;
}
}
else
{
lean_object* v_it_252_; lean_object* v___x_254_; uint8_t v_isShared_255_; uint8_t v_isSharedCheck_265_; 
v_it_252_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_265_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_265_ == 0)
{
lean_object* v_unused_266_; 
v_unused_266_ = lean_ctor_get(v___x_245_, 1);
lean_dec(v_unused_266_);
v___x_254_ = v___x_245_;
v_isShared_255_ = v_isSharedCheck_265_;
goto v_resetjp_253_;
}
else
{
lean_inc(v_it_252_);
lean_dec(v___x_245_);
v___x_254_ = lean_box(0);
v_isShared_255_ = v_isSharedCheck_265_;
goto v_resetjp_253_;
}
v_resetjp_253_:
{
lean_object* v_startPos_256_; lean_object* v_endPos_257_; lean_object* v_slice_258_; lean_object* v_nextIt_260_; 
v_startPos_256_ = lean_ctor_get(v_out_246_, 0);
lean_inc(v_startPos_256_);
v_endPos_257_ = lean_ctor_get(v_out_246_, 1);
lean_inc(v_endPos_257_);
lean_dec_ref_known(v_out_246_, 2);
v_slice_258_ = l_String_Slice_subslice_x21(v_s_238_, v_currPos_240_, v_startPos_256_);
lean_dec_ref(v_s_238_);
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v_it_252_);
lean_ctor_set(v___x_243_, 0, v_endPos_257_);
v_nextIt_260_ = v___x_243_;
goto v_reusejp_259_;
}
else
{
lean_object* v_reuseFailAlloc_264_; 
v_reuseFailAlloc_264_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_264_, 0, v_endPos_257_);
lean_ctor_set(v_reuseFailAlloc_264_, 1, v_it_252_);
v_nextIt_260_ = v_reuseFailAlloc_264_;
goto v_reusejp_259_;
}
v_reusejp_259_:
{
lean_object* v___x_262_; 
if (v_isShared_255_ == 0)
{
lean_ctor_set(v___x_254_, 1, v_slice_258_);
lean_ctor_set(v___x_254_, 0, v_nextIt_260_);
v___x_262_ = v___x_254_;
goto v_reusejp_261_;
}
else
{
lean_object* v_reuseFailAlloc_263_; 
v_reuseFailAlloc_263_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_263_, 0, v_nextIt_260_);
lean_ctor_set(v_reuseFailAlloc_263_, 1, v_slice_258_);
v___x_262_ = v_reuseFailAlloc_263_;
goto v_reusejp_261_;
}
v_reusejp_261_:
{
return v___x_262_;
}
}
}
}
}
case 1:
{
lean_object* v_it_267_; lean_object* v___x_269_; uint8_t v_isShared_270_; uint8_t v_isSharedCheck_277_; 
lean_dec_ref(v_s_238_);
v_it_267_ = lean_ctor_get(v___x_245_, 0);
v_isSharedCheck_277_ = !lean_is_exclusive(v___x_245_);
if (v_isSharedCheck_277_ == 0)
{
v___x_269_ = v___x_245_;
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
else
{
lean_inc(v_it_267_);
lean_dec(v___x_245_);
v___x_269_ = lean_box(0);
v_isShared_270_ = v_isSharedCheck_277_;
goto v_resetjp_268_;
}
v_resetjp_268_:
{
lean_object* v___x_272_; 
if (v_isShared_244_ == 0)
{
lean_ctor_set(v___x_243_, 1, v_it_267_);
v___x_272_ = v___x_243_;
goto v_reusejp_271_;
}
else
{
lean_object* v_reuseFailAlloc_276_; 
v_reuseFailAlloc_276_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_276_, 0, v_currPos_240_);
lean_ctor_set(v_reuseFailAlloc_276_, 1, v_it_267_);
v___x_272_ = v_reuseFailAlloc_276_;
goto v_reusejp_271_;
}
v_reusejp_271_:
{
lean_object* v___x_274_; 
if (v_isShared_270_ == 0)
{
lean_ctor_set(v___x_269_, 0, v___x_272_);
v___x_274_ = v___x_269_;
goto v_reusejp_273_;
}
else
{
lean_object* v_reuseFailAlloc_275_; 
v_reuseFailAlloc_275_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_275_, 0, v___x_272_);
v___x_274_ = v_reuseFailAlloc_275_;
goto v_reusejp_273_;
}
v_reusejp_273_:
{
return v___x_274_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_278_; lean_object* v_endExclusive_279_; lean_object* v___x_280_; lean_object* v_slice_281_; lean_object* v___x_282_; lean_object* v___x_283_; 
lean_del_object(v___x_243_);
v_startInclusive_278_ = lean_ctor_get(v_s_238_, 1);
lean_inc(v_startInclusive_278_);
v_endExclusive_279_ = lean_ctor_get(v_s_238_, 2);
lean_inc(v_endExclusive_279_);
lean_dec_ref(v_s_238_);
v___x_280_ = lean_nat_sub(v_endExclusive_279_, v_startInclusive_278_);
lean_dec(v_startInclusive_278_);
lean_dec(v_endExclusive_279_);
v_slice_281_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_281_, 0, v_currPos_240_);
lean_ctor_set(v_slice_281_, 1, v___x_280_);
v___x_282_ = lean_box(1);
v___x_283_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_283_, 0, v___x_282_);
lean_ctor_set(v___x_283_, 1, v_slice_281_);
return v___x_283_;
}
}
}
}
else
{
lean_object* v___x_285_; 
lean_dec_ref(v_s_238_);
lean_dec(v_inst_237_);
v___x_285_ = lean_box(2);
return v___x_285_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg(lean_object* v_inst_286_, lean_object* v_s_287_){
_start:
{
lean_object* v___f_288_; 
v___f_288_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0), 3, 2);
lean_closure_set(v___f_288_, 0, v_inst_286_);
lean_closure_set(v___f_288_, 1, v_s_287_);
return v___f_288_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice(lean_object* v_00_u03c1_289_, lean_object* v_00_u03c3_290_, lean_object* v_inst_291_, lean_object* v_pat_292_, lean_object* v_inst_293_, lean_object* v_s_294_){
_start:
{
lean_object* v___f_295_; 
v___f_295_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorIdSubslice___redArg___lam__0), 3, 2);
lean_closure_set(v___f_295_, 0, v_inst_291_);
lean_closure_set(v___f_295_, 1, v_s_294_);
return v___f_295_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorIdSubslice___boxed(lean_object* v_00_u03c1_296_, lean_object* v_00_u03c3_297_, lean_object* v_inst_298_, lean_object* v_pat_299_, lean_object* v_inst_300_, lean_object* v_s_301_){
_start:
{
lean_object* v_res_302_; 
v_res_302_ = l_String_Slice_SplitIterator_instIteratorIdSubslice(v_00_u03c1_296_, v_00_u03c3_297_, v_inst_298_, v_pat_299_, v_inst_300_, v_s_301_);
lean_dec(v_inst_300_);
lean_dec(v_pat_299_);
return v_res_302_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(lean_object* v_x_303_){
_start:
{
if (lean_obj_tag(v_x_303_) == 0)
{
lean_object* v_searcher_304_; lean_object* v___x_305_; 
v_searcher_304_ = lean_ctor_get(v_x_303_, 1);
lean_inc(v_searcher_304_);
v___x_305_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_305_, 0, v_searcher_304_);
return v___x_305_;
}
else
{
lean_object* v___x_306_; 
v___x_306_ = lean_box(0);
return v___x_306_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg___boxed(lean_object* v_x_307_){
_start:
{
lean_object* v_res_308_; 
v_res_308_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(v_x_307_);
lean_dec(v_x_307_);
return v_res_308_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption(lean_object* v_00_u03c1_309_, lean_object* v_00_u03c3_310_, lean_object* v_pat_311_, lean_object* v_inst_312_, lean_object* v_s_313_, lean_object* v_x_314_){
_start:
{
lean_object* v___x_315_; 
v___x_315_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___redArg(v_x_314_);
return v___x_315_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption___boxed(lean_object* v_00_u03c1_316_, lean_object* v_00_u03c3_317_, lean_object* v_pat_318_, lean_object* v_inst_319_, lean_object* v_s_320_, lean_object* v_x_321_){
_start:
{
lean_object* v_res_322_; 
v_res_322_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_toOption(v_00_u03c1_316_, v_00_u03c3_317_, v_pat_318_, v_inst_319_, v_s_320_, v_x_321_);
lean_dec(v_x_321_);
lean_dec_ref(v_s_320_);
lean_dec(v_inst_319_);
lean_dec(v_pat_318_);
return v_res_322_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___redArg(lean_object* v_x_323_, lean_object* v_h__1_324_, lean_object* v_h__2_325_){
_start:
{
if (lean_obj_tag(v_x_323_) == 0)
{
lean_object* v_currPos_326_; lean_object* v_searcher_327_; lean_object* v___x_328_; 
lean_dec(v_h__2_325_);
v_currPos_326_ = lean_ctor_get(v_x_323_, 0);
lean_inc(v_currPos_326_);
v_searcher_327_ = lean_ctor_get(v_x_323_, 1);
lean_inc(v_searcher_327_);
lean_dec_ref_known(v_x_323_, 2);
v___x_328_ = lean_apply_2(v_h__1_324_, v_currPos_326_, v_searcher_327_);
return v___x_328_;
}
else
{
lean_object* v___x_329_; lean_object* v___x_330_; 
lean_dec(v_h__1_324_);
v___x_329_ = lean_box(0);
v___x_330_ = lean_apply_1(v_h__2_325_, v___x_329_);
return v___x_330_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(lean_object* v_00_u03c1_331_, lean_object* v_00_u03c3_332_, lean_object* v_pat_333_, lean_object* v_inst_334_, lean_object* v_s_335_, lean_object* v_motive_336_, lean_object* v_x_337_, lean_object* v_h__1_338_, lean_object* v_h__2_339_){
_start:
{
if (lean_obj_tag(v_x_337_) == 0)
{
lean_object* v_currPos_340_; lean_object* v_searcher_341_; lean_object* v___x_342_; 
lean_dec(v_h__2_339_);
v_currPos_340_ = lean_ctor_get(v_x_337_, 0);
lean_inc(v_currPos_340_);
v_searcher_341_ = lean_ctor_get(v_x_337_, 1);
lean_inc(v_searcher_341_);
lean_dec_ref_known(v_x_337_, 2);
v___x_342_ = lean_apply_2(v_h__1_338_, v_currPos_340_, v_searcher_341_);
return v___x_342_;
}
else
{
lean_object* v___x_343_; lean_object* v___x_344_; 
lean_dec(v_h__1_338_);
v___x_343_ = lean_box(0);
v___x_344_ = lean_apply_1(v_h__2_339_, v___x_343_);
return v___x_344_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter___boxed(lean_object* v_00_u03c1_345_, lean_object* v_00_u03c3_346_, lean_object* v_pat_347_, lean_object* v_inst_348_, lean_object* v_s_349_, lean_object* v_motive_350_, lean_object* v_x_351_, lean_object* v_h__1_352_, lean_object* v_h__2_353_){
_start:
{
lean_object* v_res_354_; 
v_res_354_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__5_splitter(v_00_u03c1_345_, v_00_u03c3_346_, v_pat_347_, v_inst_348_, v_s_349_, v_motive_350_, v_x_351_, v_h__1_352_, v_h__2_353_);
lean_dec_ref(v_s_349_);
lean_dec(v_inst_348_);
lean_dec(v_pat_347_);
return v_res_354_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___redArg(lean_object* v_x_355_, lean_object* v_h__1_356_, lean_object* v_h__2_357_, lean_object* v_h__3_358_, lean_object* v_h__4_359_){
_start:
{
switch(lean_obj_tag(v_x_355_))
{
case 0:
{
lean_object* v_out_360_; 
lean_dec(v_h__4_359_);
lean_dec(v_h__3_358_);
v_out_360_ = lean_ctor_get(v_x_355_, 1);
lean_inc(v_out_360_);
if (lean_obj_tag(v_out_360_) == 0)
{
lean_object* v_it_361_; lean_object* v_startPos_362_; lean_object* v_endPos_363_; lean_object* v___x_364_; 
lean_dec(v_h__1_356_);
v_it_361_ = lean_ctor_get(v_x_355_, 0);
lean_inc(v_it_361_);
lean_dec_ref_known(v_x_355_, 2);
v_startPos_362_ = lean_ctor_get(v_out_360_, 0);
lean_inc(v_startPos_362_);
v_endPos_363_ = lean_ctor_get(v_out_360_, 1);
lean_inc(v_endPos_363_);
lean_dec_ref_known(v_out_360_, 2);
v___x_364_ = lean_apply_5(v_h__2_357_, v_it_361_, v_startPos_362_, v_endPos_363_, lean_box(0), lean_box(0));
return v___x_364_;
}
else
{
lean_object* v_it_365_; lean_object* v_startPos_366_; lean_object* v_endPos_367_; lean_object* v___x_368_; 
lean_dec(v_h__2_357_);
v_it_365_ = lean_ctor_get(v_x_355_, 0);
lean_inc(v_it_365_);
lean_dec_ref_known(v_x_355_, 2);
v_startPos_366_ = lean_ctor_get(v_out_360_, 0);
lean_inc(v_startPos_366_);
v_endPos_367_ = lean_ctor_get(v_out_360_, 1);
lean_inc(v_endPos_367_);
lean_dec_ref_known(v_out_360_, 2);
v___x_368_ = lean_apply_5(v_h__1_356_, v_it_365_, v_startPos_366_, v_endPos_367_, lean_box(0), lean_box(0));
return v___x_368_;
}
}
case 1:
{
lean_object* v_it_369_; lean_object* v___x_370_; 
lean_dec(v_h__4_359_);
lean_dec(v_h__2_357_);
lean_dec(v_h__1_356_);
v_it_369_ = lean_ctor_get(v_x_355_, 0);
lean_inc(v_it_369_);
lean_dec_ref_known(v_x_355_, 1);
v___x_370_ = lean_apply_3(v_h__3_358_, v_it_369_, lean_box(0), lean_box(0));
return v___x_370_;
}
default: 
{
lean_object* v___x_371_; 
lean_dec(v_h__3_358_);
lean_dec(v_h__2_357_);
lean_dec(v_h__1_356_);
v___x_371_ = lean_apply_2(v_h__4_359_, lean_box(0), lean_box(0));
return v___x_371_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(lean_object* v_00_u03c3_372_, lean_object* v_inst_373_, lean_object* v_s_374_, lean_object* v_searcher_375_, lean_object* v_motive_376_, lean_object* v_x_377_, lean_object* v_h__1_378_, lean_object* v_h__2_379_, lean_object* v_h__3_380_, lean_object* v_h__4_381_){
_start:
{
switch(lean_obj_tag(v_x_377_))
{
case 0:
{
lean_object* v_out_382_; 
lean_dec(v_h__4_381_);
lean_dec(v_h__3_380_);
v_out_382_ = lean_ctor_get(v_x_377_, 1);
lean_inc(v_out_382_);
if (lean_obj_tag(v_out_382_) == 0)
{
lean_object* v_it_383_; lean_object* v_startPos_384_; lean_object* v_endPos_385_; lean_object* v___x_386_; 
lean_dec(v_h__1_378_);
v_it_383_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_it_383_);
lean_dec_ref_known(v_x_377_, 2);
v_startPos_384_ = lean_ctor_get(v_out_382_, 0);
lean_inc(v_startPos_384_);
v_endPos_385_ = lean_ctor_get(v_out_382_, 1);
lean_inc(v_endPos_385_);
lean_dec_ref_known(v_out_382_, 2);
v___x_386_ = lean_apply_5(v_h__2_379_, v_it_383_, v_startPos_384_, v_endPos_385_, lean_box(0), lean_box(0));
return v___x_386_;
}
else
{
lean_object* v_it_387_; lean_object* v_startPos_388_; lean_object* v_endPos_389_; lean_object* v___x_390_; 
lean_dec(v_h__2_379_);
v_it_387_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_it_387_);
lean_dec_ref_known(v_x_377_, 2);
v_startPos_388_ = lean_ctor_get(v_out_382_, 0);
lean_inc(v_startPos_388_);
v_endPos_389_ = lean_ctor_get(v_out_382_, 1);
lean_inc(v_endPos_389_);
lean_dec_ref_known(v_out_382_, 2);
v___x_390_ = lean_apply_5(v_h__1_378_, v_it_387_, v_startPos_388_, v_endPos_389_, lean_box(0), lean_box(0));
return v___x_390_;
}
}
case 1:
{
lean_object* v_it_391_; lean_object* v___x_392_; 
lean_dec(v_h__4_381_);
lean_dec(v_h__2_379_);
lean_dec(v_h__1_378_);
v_it_391_ = lean_ctor_get(v_x_377_, 0);
lean_inc(v_it_391_);
lean_dec_ref_known(v_x_377_, 1);
v___x_392_ = lean_apply_3(v_h__3_380_, v_it_391_, lean_box(0), lean_box(0));
return v___x_392_;
}
default: 
{
lean_object* v___x_393_; 
lean_dec(v_h__3_380_);
lean_dec(v_h__2_379_);
lean_dec(v_h__1_378_);
v___x_393_ = lean_apply_2(v_h__4_381_, lean_box(0), lean_box(0));
return v___x_393_;
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter___boxed(lean_object* v_00_u03c3_394_, lean_object* v_inst_395_, lean_object* v_s_396_, lean_object* v_searcher_397_, lean_object* v_motive_398_, lean_object* v_x_399_, lean_object* v_h__1_400_, lean_object* v_h__2_401_, lean_object* v_h__3_402_, lean_object* v_h__4_403_){
_start:
{
lean_object* v_res_404_; 
v_res_404_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__3_splitter(v_00_u03c3_394_, v_inst_395_, v_s_396_, v_searcher_397_, v_motive_398_, v_x_399_, v_h__1_400_, v_h__2_401_, v_h__3_402_, v_h__4_403_);
lean_dec(v_searcher_397_);
lean_dec_ref(v_s_396_);
lean_dec(v_inst_395_);
return v_res_404_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___redArg(lean_object* v_x_405_, lean_object* v_x_406_, lean_object* v_h__1_407_, lean_object* v_h__2_408_, lean_object* v_h__3_409_, lean_object* v_h__4_410_, lean_object* v_h__5_411_, lean_object* v_h__6_412_, lean_object* v_h__7_413_, lean_object* v_h__8_414_){
_start:
{
if (lean_obj_tag(v_x_405_) == 0)
{
lean_dec(v_h__8_414_);
lean_dec(v_h__7_413_);
lean_dec(v_h__6_412_);
switch(lean_obj_tag(v_x_406_))
{
case 0:
{
lean_object* v_it_415_; 
lean_dec(v_h__5_411_);
lean_dec(v_h__4_410_);
lean_dec(v_h__3_409_);
v_it_415_ = lean_ctor_get(v_x_406_, 0);
if (lean_obj_tag(v_it_415_) == 0)
{
lean_object* v_currPos_416_; lean_object* v_searcher_417_; lean_object* v_out_418_; lean_object* v_currPos_419_; lean_object* v_searcher_420_; lean_object* v___x_421_; 
lean_inc_ref(v_it_415_);
lean_dec(v_h__2_408_);
v_currPos_416_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_currPos_416_);
v_searcher_417_ = lean_ctor_get(v_x_405_, 1);
lean_inc(v_searcher_417_);
lean_dec_ref_known(v_x_405_, 2);
v_out_418_ = lean_ctor_get(v_x_406_, 1);
lean_inc(v_out_418_);
lean_dec_ref_known(v_x_406_, 2);
v_currPos_419_ = lean_ctor_get(v_it_415_, 0);
lean_inc(v_currPos_419_);
v_searcher_420_ = lean_ctor_get(v_it_415_, 1);
lean_inc(v_searcher_420_);
lean_dec_ref_known(v_it_415_, 2);
v___x_421_ = lean_apply_5(v_h__1_407_, v_currPos_416_, v_searcher_417_, v_currPos_419_, v_searcher_420_, v_out_418_);
return v___x_421_;
}
else
{
lean_object* v_currPos_422_; lean_object* v_searcher_423_; lean_object* v_out_424_; lean_object* v___x_425_; 
lean_dec(v_h__1_407_);
v_currPos_422_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_currPos_422_);
v_searcher_423_ = lean_ctor_get(v_x_405_, 1);
lean_inc(v_searcher_423_);
lean_dec_ref_known(v_x_405_, 2);
v_out_424_ = lean_ctor_get(v_x_406_, 1);
lean_inc(v_out_424_);
lean_dec_ref_known(v_x_406_, 2);
v___x_425_ = lean_apply_3(v_h__2_408_, v_currPos_422_, v_searcher_423_, v_out_424_);
return v___x_425_;
}
}
case 1:
{
lean_object* v_it_426_; 
lean_dec(v_h__5_411_);
lean_dec(v_h__2_408_);
lean_dec(v_h__1_407_);
v_it_426_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_it_426_);
lean_dec_ref_known(v_x_406_, 1);
if (lean_obj_tag(v_it_426_) == 0)
{
lean_object* v_currPos_427_; lean_object* v_searcher_428_; lean_object* v_currPos_429_; lean_object* v_searcher_430_; lean_object* v___x_431_; 
lean_dec(v_h__4_410_);
v_currPos_427_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_currPos_427_);
v_searcher_428_ = lean_ctor_get(v_x_405_, 1);
lean_inc(v_searcher_428_);
lean_dec_ref_known(v_x_405_, 2);
v_currPos_429_ = lean_ctor_get(v_it_426_, 0);
lean_inc(v_currPos_429_);
v_searcher_430_ = lean_ctor_get(v_it_426_, 1);
lean_inc(v_searcher_430_);
lean_dec_ref_known(v_it_426_, 2);
v___x_431_ = lean_apply_4(v_h__3_409_, v_currPos_427_, v_searcher_428_, v_currPos_429_, v_searcher_430_);
return v___x_431_;
}
else
{
lean_object* v_currPos_432_; lean_object* v_searcher_433_; lean_object* v___x_434_; 
lean_dec(v_h__3_409_);
v_currPos_432_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_currPos_432_);
v_searcher_433_ = lean_ctor_get(v_x_405_, 1);
lean_inc(v_searcher_433_);
lean_dec_ref_known(v_x_405_, 2);
v___x_434_ = lean_apply_2(v_h__4_410_, v_currPos_432_, v_searcher_433_);
return v___x_434_;
}
}
default: 
{
lean_object* v_currPos_435_; lean_object* v_searcher_436_; lean_object* v___x_437_; 
lean_dec(v_h__4_410_);
lean_dec(v_h__3_409_);
lean_dec(v_h__2_408_);
lean_dec(v_h__1_407_);
v_currPos_435_ = lean_ctor_get(v_x_405_, 0);
lean_inc(v_currPos_435_);
v_searcher_436_ = lean_ctor_get(v_x_405_, 1);
lean_inc(v_searcher_436_);
lean_dec_ref_known(v_x_405_, 2);
v___x_437_ = lean_apply_2(v_h__5_411_, v_currPos_435_, v_searcher_436_);
return v___x_437_;
}
}
}
else
{
lean_dec(v_h__5_411_);
lean_dec(v_h__4_410_);
lean_dec(v_h__3_409_);
lean_dec(v_h__2_408_);
lean_dec(v_h__1_407_);
switch(lean_obj_tag(v_x_406_))
{
case 0:
{
lean_object* v_it_438_; lean_object* v_out_439_; lean_object* v___x_440_; 
lean_dec(v_h__8_414_);
lean_dec(v_h__7_413_);
v_it_438_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_it_438_);
v_out_439_ = lean_ctor_get(v_x_406_, 1);
lean_inc(v_out_439_);
lean_dec_ref_known(v_x_406_, 2);
v___x_440_ = lean_apply_2(v_h__6_412_, v_it_438_, v_out_439_);
return v___x_440_;
}
case 1:
{
lean_object* v_it_441_; lean_object* v___x_442_; 
lean_dec(v_h__8_414_);
lean_dec(v_h__6_412_);
v_it_441_ = lean_ctor_get(v_x_406_, 0);
lean_inc(v_it_441_);
lean_dec_ref_known(v_x_406_, 1);
v___x_442_ = lean_apply_1(v_h__7_413_, v_it_441_);
return v___x_442_;
}
default: 
{
lean_object* v___x_443_; lean_object* v___x_444_; 
lean_dec(v_h__7_413_);
lean_dec(v_h__6_412_);
v___x_443_ = lean_box(0);
v___x_444_ = lean_apply_1(v_h__8_414_, v___x_443_);
return v___x_444_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(lean_object* v_00_u03c1_445_, lean_object* v_00_u03c3_446_, lean_object* v_pat_447_, lean_object* v_inst_448_, lean_object* v_s_449_, lean_object* v_motive_450_, lean_object* v_x_451_, lean_object* v_x_452_, lean_object* v_h__1_453_, lean_object* v_h__2_454_, lean_object* v_h__3_455_, lean_object* v_h__4_456_, lean_object* v_h__5_457_, lean_object* v_h__6_458_, lean_object* v_h__7_459_, lean_object* v_h__8_460_){
_start:
{
if (lean_obj_tag(v_x_451_) == 0)
{
lean_dec(v_h__8_460_);
lean_dec(v_h__7_459_);
lean_dec(v_h__6_458_);
switch(lean_obj_tag(v_x_452_))
{
case 0:
{
lean_object* v_it_461_; 
lean_dec(v_h__5_457_);
lean_dec(v_h__4_456_);
lean_dec(v_h__3_455_);
v_it_461_ = lean_ctor_get(v_x_452_, 0);
if (lean_obj_tag(v_it_461_) == 0)
{
lean_object* v_currPos_462_; lean_object* v_searcher_463_; lean_object* v_out_464_; lean_object* v_currPos_465_; lean_object* v_searcher_466_; lean_object* v___x_467_; 
lean_inc_ref(v_it_461_);
lean_dec(v_h__2_454_);
v_currPos_462_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_currPos_462_);
v_searcher_463_ = lean_ctor_get(v_x_451_, 1);
lean_inc(v_searcher_463_);
lean_dec_ref_known(v_x_451_, 2);
v_out_464_ = lean_ctor_get(v_x_452_, 1);
lean_inc(v_out_464_);
lean_dec_ref_known(v_x_452_, 2);
v_currPos_465_ = lean_ctor_get(v_it_461_, 0);
lean_inc(v_currPos_465_);
v_searcher_466_ = lean_ctor_get(v_it_461_, 1);
lean_inc(v_searcher_466_);
lean_dec_ref_known(v_it_461_, 2);
v___x_467_ = lean_apply_5(v_h__1_453_, v_currPos_462_, v_searcher_463_, v_currPos_465_, v_searcher_466_, v_out_464_);
return v___x_467_;
}
else
{
lean_object* v_currPos_468_; lean_object* v_searcher_469_; lean_object* v_out_470_; lean_object* v___x_471_; 
lean_dec(v_h__1_453_);
v_currPos_468_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_currPos_468_);
v_searcher_469_ = lean_ctor_get(v_x_451_, 1);
lean_inc(v_searcher_469_);
lean_dec_ref_known(v_x_451_, 2);
v_out_470_ = lean_ctor_get(v_x_452_, 1);
lean_inc(v_out_470_);
lean_dec_ref_known(v_x_452_, 2);
v___x_471_ = lean_apply_3(v_h__2_454_, v_currPos_468_, v_searcher_469_, v_out_470_);
return v___x_471_;
}
}
case 1:
{
lean_object* v_it_472_; 
lean_dec(v_h__5_457_);
lean_dec(v_h__2_454_);
lean_dec(v_h__1_453_);
v_it_472_ = lean_ctor_get(v_x_452_, 0);
lean_inc(v_it_472_);
lean_dec_ref_known(v_x_452_, 1);
if (lean_obj_tag(v_it_472_) == 0)
{
lean_object* v_currPos_473_; lean_object* v_searcher_474_; lean_object* v_currPos_475_; lean_object* v_searcher_476_; lean_object* v___x_477_; 
lean_dec(v_h__4_456_);
v_currPos_473_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_currPos_473_);
v_searcher_474_ = lean_ctor_get(v_x_451_, 1);
lean_inc(v_searcher_474_);
lean_dec_ref_known(v_x_451_, 2);
v_currPos_475_ = lean_ctor_get(v_it_472_, 0);
lean_inc(v_currPos_475_);
v_searcher_476_ = lean_ctor_get(v_it_472_, 1);
lean_inc(v_searcher_476_);
lean_dec_ref_known(v_it_472_, 2);
v___x_477_ = lean_apply_4(v_h__3_455_, v_currPos_473_, v_searcher_474_, v_currPos_475_, v_searcher_476_);
return v___x_477_;
}
else
{
lean_object* v_currPos_478_; lean_object* v_searcher_479_; lean_object* v___x_480_; 
lean_dec(v_h__3_455_);
v_currPos_478_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_currPos_478_);
v_searcher_479_ = lean_ctor_get(v_x_451_, 1);
lean_inc(v_searcher_479_);
lean_dec_ref_known(v_x_451_, 2);
v___x_480_ = lean_apply_2(v_h__4_456_, v_currPos_478_, v_searcher_479_);
return v___x_480_;
}
}
default: 
{
lean_object* v_currPos_481_; lean_object* v_searcher_482_; lean_object* v___x_483_; 
lean_dec(v_h__4_456_);
lean_dec(v_h__3_455_);
lean_dec(v_h__2_454_);
lean_dec(v_h__1_453_);
v_currPos_481_ = lean_ctor_get(v_x_451_, 0);
lean_inc(v_currPos_481_);
v_searcher_482_ = lean_ctor_get(v_x_451_, 1);
lean_inc(v_searcher_482_);
lean_dec_ref_known(v_x_451_, 2);
v___x_483_ = lean_apply_2(v_h__5_457_, v_currPos_481_, v_searcher_482_);
return v___x_483_;
}
}
}
else
{
lean_dec(v_h__5_457_);
lean_dec(v_h__4_456_);
lean_dec(v_h__3_455_);
lean_dec(v_h__2_454_);
lean_dec(v_h__1_453_);
switch(lean_obj_tag(v_x_452_))
{
case 0:
{
lean_object* v_it_484_; lean_object* v_out_485_; lean_object* v___x_486_; 
lean_dec(v_h__8_460_);
lean_dec(v_h__7_459_);
v_it_484_ = lean_ctor_get(v_x_452_, 0);
lean_inc(v_it_484_);
v_out_485_ = lean_ctor_get(v_x_452_, 1);
lean_inc(v_out_485_);
lean_dec_ref_known(v_x_452_, 2);
v___x_486_ = lean_apply_2(v_h__6_458_, v_it_484_, v_out_485_);
return v___x_486_;
}
case 1:
{
lean_object* v_it_487_; lean_object* v___x_488_; 
lean_dec(v_h__8_460_);
lean_dec(v_h__6_458_);
v_it_487_ = lean_ctor_get(v_x_452_, 0);
lean_inc(v_it_487_);
lean_dec_ref_known(v_x_452_, 1);
v___x_488_ = lean_apply_1(v_h__7_459_, v_it_487_);
return v___x_488_;
}
default: 
{
lean_object* v___x_489_; lean_object* v___x_490_; 
lean_dec(v_h__7_459_);
lean_dec(v_h__6_458_);
v___x_489_ = lean_box(0);
v___x_490_ = lean_apply_1(v_h__8_460_, v___x_489_);
return v___x_490_;
}
}
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter___boxed(lean_object* v_00_u03c1_491_, lean_object* v_00_u03c3_492_, lean_object* v_pat_493_, lean_object* v_inst_494_, lean_object* v_s_495_, lean_object* v_motive_496_, lean_object* v_x_497_, lean_object* v_x_498_, lean_object* v_h__1_499_, lean_object* v_h__2_500_, lean_object* v_h__3_501_, lean_object* v_h__4_502_, lean_object* v_h__5_503_, lean_object* v_h__6_504_, lean_object* v_h__7_505_, lean_object* v_h__8_506_){
_start:
{
lean_object* v_res_507_; 
v_res_507_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_instIteratorIdSubslice_match__1_splitter(v_00_u03c1_491_, v_00_u03c3_492_, v_pat_493_, v_inst_494_, v_s_495_, v_motive_496_, v_x_497_, v_x_498_, v_h__1_499_, v_h__2_500_, v_h__3_501_, v_h__4_502_, v_h__5_503_, v_h__6_504_, v_h__7_505_, v_h__8_506_);
lean_dec_ref(v_s_495_);
lean_dec(v_inst_494_);
lean_dec(v_pat_493_);
return v_res_507_;
}
}
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_509_; 
v___x_509_ = lean_box(0);
return v___x_509_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_510_;
v_res_510_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg();
stack->m_obj
 = v_res_510_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_511_){
_start:
{
lean_object* v_res_512_; 
v_res_512_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___redArg();
return v_res_512_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(lean_object* v_00_u03c1_513_, lean_object* v_00_u03c3_514_, lean_object* v_inst_515_, lean_object* v_pat_516_, lean_object* v_inst_517_, lean_object* v_s_518_, lean_object* v_inst_519_){
_start:
{
lean_object* v___x_520_; 
v___x_520_ = lean_box(0);
return v___x_520_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_521_, lean_object* v_00_u03c3_522_, lean_object* v_inst_523_, lean_object* v_pat_524_, lean_object* v_inst_525_, lean_object* v_s_526_, lean_object* v_inst_527_){
_start:
{
lean_object* v_res_528_; 
v_res_528_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitIterator_finitenessRelation(v_00_u03c1_521_, v_00_u03c3_522_, v_inst_523_, v_pat_524_, v_inst_525_, v_s_526_, v_inst_527_);
lean_dec_ref(v_s_526_);
lean_dec(v_inst_525_);
lean_dec(v_pat_524_);
lean_dec(v_inst_523_);
return v_res_528_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0(lean_object* v_toPure_529_, lean_object* v_recur_530_, lean_object* v_it_531_, lean_object* v_____do__lift_532_){
_start:
{
if (lean_obj_tag(v_____do__lift_532_) == 0)
{
lean_object* v_a_533_; lean_object* v___x_534_; 
lean_dec(v_it_531_);
lean_dec(v_recur_530_);
v_a_533_ = lean_ctor_get(v_____do__lift_532_, 0);
lean_inc(v_a_533_);
lean_dec_ref_known(v_____do__lift_532_, 1);
v___x_534_ = lean_apply_2(v_toPure_529_, lean_box(0), v_a_533_);
return v___x_534_;
}
else
{
lean_object* v_a_535_; lean_object* v___x_536_; 
lean_dec(v_toPure_529_);
v_a_535_ = lean_ctor_get(v_____do__lift_532_, 0);
lean_inc(v_a_535_);
lean_dec_ref_known(v_____do__lift_532_, 1);
v___x_536_ = lean_apply_4(v_recur_530_, v_it_531_, v_a_535_, lean_box(0), lean_box(0));
return v___x_536_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1(lean_object* v_toPure_537_, lean_object* v_recur_538_, lean_object* v___y_539_, lean_object* v_acc_540_, lean_object* v_toBind_541_, lean_object* v_s_542_){
_start:
{
switch(lean_obj_tag(v_s_542_))
{
case 0:
{
lean_object* v_it_543_; lean_object* v_out_544_; lean_object* v___f_545_; lean_object* v___x_546_; lean_object* v___x_547_; 
v_it_543_ = lean_ctor_get(v_s_542_, 0);
lean_inc(v_it_543_);
v_out_544_ = lean_ctor_get(v_s_542_, 1);
lean_inc(v_out_544_);
lean_dec_ref_known(v_s_542_, 2);
v___f_545_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_545_, 0, v_toPure_537_);
lean_closure_set(v___f_545_, 1, v_recur_538_);
lean_closure_set(v___f_545_, 2, v_it_543_);
v___x_546_ = lean_apply_3(v___y_539_, v_out_544_, lean_box(0), v_acc_540_);
v___x_547_ = lean_apply_4(v_toBind_541_, lean_box(0), lean_box(0), v___x_546_, v___f_545_);
return v___x_547_;
}
case 1:
{
lean_object* v_it_548_; lean_object* v___x_549_; 
lean_dec(v_toBind_541_);
lean_dec(v___y_539_);
lean_dec(v_toPure_537_);
v_it_548_ = lean_ctor_get(v_s_542_, 0);
lean_inc(v_it_548_);
lean_dec_ref_known(v_s_542_, 1);
v___x_549_ = lean_apply_4(v_recur_538_, v_it_548_, v_acc_540_, lean_box(0), lean_box(0));
return v___x_549_;
}
default: 
{
lean_object* v___x_550_; 
lean_dec(v_toBind_541_);
lean_dec(v___y_539_);
lean_dec(v_recur_538_);
v___x_550_ = lean_apply_2(v_toPure_537_, lean_box(0), v_acc_540_);
return v___x_550_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2(lean_object* v_toPure_551_, lean_object* v___y_552_, lean_object* v_toBind_553_, lean_object* v_inst_554_, lean_object* v_s_555_, lean_object* v_lift_556_, lean_object* v_it_557_, lean_object* v_acc_558_, lean_object* v_hP_559_, lean_object* v_recur_560_){
_start:
{
lean_object* v___f_561_; 
v___f_561_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_561_, 0, v_toPure_551_);
lean_closure_set(v___f_561_, 1, v_recur_560_);
lean_closure_set(v___f_561_, 2, v___y_552_);
lean_closure_set(v___f_561_, 3, v_acc_558_);
lean_closure_set(v___f_561_, 4, v_toBind_553_);
if (lean_obj_tag(v_it_557_) == 0)
{
lean_object* v_currPos_562_; lean_object* v_searcher_563_; lean_object* v___x_565_; uint8_t v_isShared_566_; uint8_t v_isSharedCheck_610_; 
v_currPos_562_ = lean_ctor_get(v_it_557_, 0);
v_searcher_563_ = lean_ctor_get(v_it_557_, 1);
v_isSharedCheck_610_ = !lean_is_exclusive(v_it_557_);
if (v_isSharedCheck_610_ == 0)
{
v___x_565_ = v_it_557_;
v_isShared_566_ = v_isSharedCheck_610_;
goto v_resetjp_564_;
}
else
{
lean_inc(v_searcher_563_);
lean_inc(v_currPos_562_);
lean_dec(v_it_557_);
v___x_565_ = lean_box(0);
v_isShared_566_ = v_isSharedCheck_610_;
goto v_resetjp_564_;
}
v_resetjp_564_:
{
lean_object* v___x_567_; 
lean_inc_ref(v_s_555_);
v___x_567_ = lean_apply_2(v_inst_554_, v_s_555_, v_searcher_563_);
switch(lean_obj_tag(v___x_567_))
{
case 0:
{
lean_object* v_out_568_; 
v_out_568_ = lean_ctor_get(v___x_567_, 1);
lean_inc(v_out_568_);
if (lean_obj_tag(v_out_568_) == 0)
{
lean_object* v_it_569_; lean_object* v___x_571_; 
lean_dec_ref_known(v_out_568_, 2);
lean_dec_ref(v_s_555_);
v_it_569_ = lean_ctor_get(v___x_567_, 0);
lean_inc(v_it_569_);
lean_dec_ref_known(v___x_567_, 2);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_it_569_);
v___x_571_ = v___x_565_;
goto v_reusejp_570_;
}
else
{
lean_object* v_reuseFailAlloc_574_; 
v_reuseFailAlloc_574_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_574_, 0, v_currPos_562_);
lean_ctor_set(v_reuseFailAlloc_574_, 1, v_it_569_);
v___x_571_ = v_reuseFailAlloc_574_;
goto v_reusejp_570_;
}
v_reusejp_570_:
{
lean_object* v___x_572_; lean_object* v___x_573_; 
v___x_572_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_572_, 0, v___x_571_);
v___x_573_ = lean_apply_4(v_lift_556_, lean_box(0), lean_box(0), v___f_561_, v___x_572_);
return v___x_573_;
}
}
else
{
lean_object* v_it_575_; lean_object* v___x_577_; uint8_t v_isShared_578_; uint8_t v_isSharedCheck_589_; 
v_it_575_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_589_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_589_ == 0)
{
lean_object* v_unused_590_; 
v_unused_590_ = lean_ctor_get(v___x_567_, 1);
lean_dec(v_unused_590_);
v___x_577_ = v___x_567_;
v_isShared_578_ = v_isSharedCheck_589_;
goto v_resetjp_576_;
}
else
{
lean_inc(v_it_575_);
lean_dec(v___x_567_);
v___x_577_ = lean_box(0);
v_isShared_578_ = v_isSharedCheck_589_;
goto v_resetjp_576_;
}
v_resetjp_576_:
{
lean_object* v_startPos_579_; lean_object* v_endPos_580_; lean_object* v_slice_581_; lean_object* v_nextIt_583_; 
v_startPos_579_ = lean_ctor_get(v_out_568_, 0);
lean_inc(v_startPos_579_);
v_endPos_580_ = lean_ctor_get(v_out_568_, 1);
lean_inc(v_endPos_580_);
lean_dec_ref_known(v_out_568_, 2);
v_slice_581_ = l_String_Slice_subslice_x21(v_s_555_, v_currPos_562_, v_startPos_579_);
lean_dec_ref(v_s_555_);
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_it_575_);
lean_ctor_set(v___x_565_, 0, v_endPos_580_);
v_nextIt_583_ = v___x_565_;
goto v_reusejp_582_;
}
else
{
lean_object* v_reuseFailAlloc_588_; 
v_reuseFailAlloc_588_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_588_, 0, v_endPos_580_);
lean_ctor_set(v_reuseFailAlloc_588_, 1, v_it_575_);
v_nextIt_583_ = v_reuseFailAlloc_588_;
goto v_reusejp_582_;
}
v_reusejp_582_:
{
lean_object* v___x_585_; 
if (v_isShared_578_ == 0)
{
lean_ctor_set(v___x_577_, 1, v_slice_581_);
lean_ctor_set(v___x_577_, 0, v_nextIt_583_);
v___x_585_ = v___x_577_;
goto v_reusejp_584_;
}
else
{
lean_object* v_reuseFailAlloc_587_; 
v_reuseFailAlloc_587_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_587_, 0, v_nextIt_583_);
lean_ctor_set(v_reuseFailAlloc_587_, 1, v_slice_581_);
v___x_585_ = v_reuseFailAlloc_587_;
goto v_reusejp_584_;
}
v_reusejp_584_:
{
lean_object* v___x_586_; 
v___x_586_ = lean_apply_4(v_lift_556_, lean_box(0), lean_box(0), v___f_561_, v___x_585_);
return v___x_586_;
}
}
}
}
}
case 1:
{
lean_object* v_it_591_; lean_object* v___x_593_; uint8_t v_isShared_594_; uint8_t v_isSharedCheck_602_; 
lean_dec_ref(v_s_555_);
v_it_591_ = lean_ctor_get(v___x_567_, 0);
v_isSharedCheck_602_ = !lean_is_exclusive(v___x_567_);
if (v_isSharedCheck_602_ == 0)
{
v___x_593_ = v___x_567_;
v_isShared_594_ = v_isSharedCheck_602_;
goto v_resetjp_592_;
}
else
{
lean_inc(v_it_591_);
lean_dec(v___x_567_);
v___x_593_ = lean_box(0);
v_isShared_594_ = v_isSharedCheck_602_;
goto v_resetjp_592_;
}
v_resetjp_592_:
{
lean_object* v___x_596_; 
if (v_isShared_566_ == 0)
{
lean_ctor_set(v___x_565_, 1, v_it_591_);
v___x_596_ = v___x_565_;
goto v_reusejp_595_;
}
else
{
lean_object* v_reuseFailAlloc_601_; 
v_reuseFailAlloc_601_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_601_, 0, v_currPos_562_);
lean_ctor_set(v_reuseFailAlloc_601_, 1, v_it_591_);
v___x_596_ = v_reuseFailAlloc_601_;
goto v_reusejp_595_;
}
v_reusejp_595_:
{
lean_object* v___x_598_; 
if (v_isShared_594_ == 0)
{
lean_ctor_set(v___x_593_, 0, v___x_596_);
v___x_598_ = v___x_593_;
goto v_reusejp_597_;
}
else
{
lean_object* v_reuseFailAlloc_600_; 
v_reuseFailAlloc_600_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_600_, 0, v___x_596_);
v___x_598_ = v_reuseFailAlloc_600_;
goto v_reusejp_597_;
}
v_reusejp_597_:
{
lean_object* v___x_599_; 
v___x_599_ = lean_apply_4(v_lift_556_, lean_box(0), lean_box(0), v___f_561_, v___x_598_);
return v___x_599_;
}
}
}
}
default: 
{
lean_object* v_startInclusive_603_; lean_object* v_endExclusive_604_; lean_object* v___x_605_; lean_object* v_slice_606_; lean_object* v___x_607_; lean_object* v___x_608_; lean_object* v___x_609_; 
lean_del_object(v___x_565_);
v_startInclusive_603_ = lean_ctor_get(v_s_555_, 1);
lean_inc(v_startInclusive_603_);
v_endExclusive_604_ = lean_ctor_get(v_s_555_, 2);
lean_inc(v_endExclusive_604_);
lean_dec_ref(v_s_555_);
v___x_605_ = lean_nat_sub(v_endExclusive_604_, v_startInclusive_603_);
lean_dec(v_startInclusive_603_);
lean_dec(v_endExclusive_604_);
v_slice_606_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_slice_606_, 0, v_currPos_562_);
lean_ctor_set(v_slice_606_, 1, v___x_605_);
v___x_607_ = lean_box(1);
v___x_608_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_608_, 0, v___x_607_);
lean_ctor_set(v___x_608_, 1, v_slice_606_);
v___x_609_ = lean_apply_4(v_lift_556_, lean_box(0), lean_box(0), v___f_561_, v___x_608_);
return v___x_609_;
}
}
}
}
else
{
lean_object* v___x_611_; lean_object* v___x_612_; 
lean_dec_ref(v_s_555_);
lean_dec(v_inst_554_);
v___x_611_ = lean_box(2);
v___x_612_ = lean_apply_4(v_lift_556_, lean_box(0), lean_box(0), v___f_561_, v___x_611_);
return v___x_612_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3(lean_object* v_inst_613_, lean_object* v_inst_614_, lean_object* v_s_615_, lean_object* v_lift_616_, lean_object* v_00_u03b3_617_, lean_object* v_Pl_618_, lean_object* v_it_619_, lean_object* v_init_620_, lean_object* v___y_621_){
_start:
{
lean_object* v_toApplicative_622_; lean_object* v_toBind_623_; lean_object* v_toPure_624_; lean_object* v___f_625_; lean_object* v___x_626_; 
v_toApplicative_622_ = lean_ctor_get(v_inst_613_, 0);
lean_inc_ref(v_toApplicative_622_);
v_toBind_623_ = lean_ctor_get(v_inst_613_, 1);
lean_inc(v_toBind_623_);
lean_dec_ref(v_inst_613_);
v_toPure_624_ = lean_ctor_get(v_toApplicative_622_, 1);
lean_inc(v_toPure_624_);
lean_dec_ref(v_toApplicative_622_);
v___f_625_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_625_, 0, v_toPure_624_);
lean_closure_set(v___f_625_, 1, v___y_621_);
lean_closure_set(v___f_625_, 2, v_toBind_623_);
lean_closure_set(v___f_625_, 3, v_inst_614_);
lean_closure_set(v___f_625_, 4, v_s_615_);
lean_closure_set(v___f_625_, 5, v_lift_616_);
v___x_626_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_625_, v_it_619_, v_init_620_, lean_box(0));
return v___x_626_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg(lean_object* v_inst_627_, lean_object* v_s_628_, lean_object* v_inst_629_){
_start:
{
lean_object* v___f_630_; 
v___f_630_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_630_, 0, v_inst_629_);
lean_closure_set(v___f_630_, 1, v_inst_627_);
lean_closure_set(v___f_630_, 2, v_s_628_);
return v___f_630_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(lean_object* v_00_u03c1_631_, lean_object* v_00_u03c3_632_, lean_object* v_inst_633_, lean_object* v_pat_634_, lean_object* v_inst_635_, lean_object* v_n_636_, lean_object* v_s_637_, lean_object* v_inst_638_){
_start:
{
lean_object* v___f_639_; 
v___f_639_ = lean_alloc_closure((void*)(l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_639_, 0, v_inst_638_);
lean_closure_set(v___f_639_, 1, v_inst_633_);
lean_closure_set(v___f_639_, 2, v_s_637_);
return v___f_639_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad___boxed(lean_object* v_00_u03c1_640_, lean_object* v_00_u03c3_641_, lean_object* v_inst_642_, lean_object* v_pat_643_, lean_object* v_inst_644_, lean_object* v_n_645_, lean_object* v_s_646_, lean_object* v_inst_647_){
_start:
{
lean_object* v_res_648_; 
v_res_648_ = l_String_Slice_SplitIterator_instIteratorLoopIdSubsliceOfMonad(v_00_u03c1_640_, v_00_u03c3_641_, v_inst_642_, v_pat_643_, v_inst_644_, v_n_645_, v_s_646_, v_inst_647_);
lean_dec(v_inst_644_);
lean_dec(v_pat_643_);
return v_res_648_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___redArg(lean_object* v_s_649_, lean_object* v_inst_650_){
_start:
{
lean_object* v___x_651_; lean_object* v___x_652_; lean_object* v___x_653_; 
v___x_651_ = lean_unsigned_to_nat(0u);
v___x_652_ = lean_apply_1(v_inst_650_, v_s_649_);
v___x_653_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_653_, 0, v___x_651_);
lean_ctor_set(v___x_653_, 1, v___x_652_);
return v___x_653_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice(lean_object* v_00_u03c1_654_, lean_object* v_00_u03c3_655_, lean_object* v_s_656_, lean_object* v_pat_657_, lean_object* v_inst_658_){
_start:
{
lean_object* v___x_659_; 
v___x_659_ = l_String_Slice_splitToSubslice___redArg(v_s_656_, v_inst_658_);
return v___x_659_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitToSubslice___boxed(lean_object* v_00_u03c1_660_, lean_object* v_00_u03c3_661_, lean_object* v_s_662_, lean_object* v_pat_663_, lean_object* v_inst_664_){
_start:
{
lean_object* v_res_665_; 
v_res_665_ = l_String_Slice_splitToSubslice(v_00_u03c1_660_, v_00_u03c3_661_, v_s_662_, v_pat_663_, v_inst_664_);
lean_dec(v_pat_663_);
return v_res_665_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___redArg(lean_object* v_s_666_, lean_object* v_inst_667_){
_start:
{
lean_object* v___x_668_; 
v___x_668_ = l_String_Slice_splitToSubslice___redArg(v_s_666_, v_inst_667_);
return v___x_668_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split(lean_object* v_00_u03c1_669_, lean_object* v_00_u03c3_670_, lean_object* v_inst_671_, lean_object* v_s_672_, lean_object* v_pat_673_, lean_object* v_inst_674_){
_start:
{
lean_object* v___x_675_; 
v___x_675_ = l_String_Slice_splitToSubslice___redArg(v_s_672_, v_inst_674_);
return v___x_675_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_split___boxed(lean_object* v_00_u03c1_676_, lean_object* v_00_u03c3_677_, lean_object* v_inst_678_, lean_object* v_s_679_, lean_object* v_pat_680_, lean_object* v_inst_681_){
_start:
{
lean_object* v_res_682_; 
v_res_682_ = l_String_Slice_split(v_00_u03c1_676_, v_00_u03c3_677_, v_inst_678_, v_s_679_, v_pat_680_, v_inst_681_);
lean_dec(v_pat_680_);
lean_dec(v_inst_678_);
return v_res_682_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg(lean_object* v_x_683_){
_start:
{
lean_object* v___x_684_; 
v___x_684_ = lean_obj_tag_nat(v_x_683_);
return v___x_684_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg___boxed(lean_object* v_x_685_){
_start:
{
lean_object* v_res_686_; 
v_res_686_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___redArg(v_x_685_);
lean_dec(v_x_685_);
return v_res_686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl(lean_object* v_00_u03c3_687_, lean_object* v_00_u03c1_688_, lean_object* v_pat_689_, lean_object* v_s_690_, lean_object* v_inst_691_, lean_object* v_x_692_){
_start:
{
lean_object* v___x_693_; 
v___x_693_ = lean_obj_tag_nat(v_x_692_);
return v___x_693_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorIdx___impl___boxed(lean_object* v_00_u03c3_694_, lean_object* v_00_u03c1_695_, lean_object* v_pat_696_, lean_object* v_s_697_, lean_object* v_inst_698_, lean_object* v_x_699_){
_start:
{
lean_object* v_res_700_; 
v_res_700_ = l_String_Slice_SplitInclusiveIterator_ctorIdx___impl(v_00_u03c3_694_, v_00_u03c1_695_, v_pat_696_, v_s_697_, v_inst_698_, v_x_699_);
lean_dec(v_x_699_);
lean_dec(v_inst_698_);
lean_dec_ref(v_s_697_);
lean_dec(v_pat_696_);
return v_res_700_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(lean_object* v_t_701_, lean_object* v_k_702_){
_start:
{
if (lean_obj_tag(v_t_701_) == 0)
{
lean_object* v_currPos_703_; lean_object* v_searcher_704_; lean_object* v___x_705_; 
v_currPos_703_ = lean_ctor_get(v_t_701_, 0);
lean_inc(v_currPos_703_);
v_searcher_704_ = lean_ctor_get(v_t_701_, 1);
lean_inc(v_searcher_704_);
lean_dec_ref_known(v_t_701_, 2);
v___x_705_ = lean_apply_2(v_k_702_, v_currPos_703_, v_searcher_704_);
return v___x_705_;
}
else
{
return v_k_702_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim(lean_object* v_00_u03c3_706_, lean_object* v_00_u03c1_707_, lean_object* v_pat_708_, lean_object* v_s_709_, lean_object* v_inst_710_, lean_object* v_motive_711_, lean_object* v_ctorIdx_712_, lean_object* v_t_713_, lean_object* v_h_714_, lean_object* v_k_715_){
_start:
{
lean_object* v___x_716_; 
v___x_716_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_713_, v_k_715_);
return v___x_716_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_ctorElim___boxed(lean_object* v_00_u03c3_717_, lean_object* v_00_u03c1_718_, lean_object* v_pat_719_, lean_object* v_s_720_, lean_object* v_inst_721_, lean_object* v_motive_722_, lean_object* v_ctorIdx_723_, lean_object* v_t_724_, lean_object* v_h_725_, lean_object* v_k_726_){
_start:
{
lean_object* v_res_727_; 
v_res_727_ = l_String_Slice_SplitInclusiveIterator_ctorElim(v_00_u03c3_717_, v_00_u03c1_718_, v_pat_719_, v_s_720_, v_inst_721_, v_motive_722_, v_ctorIdx_723_, v_t_724_, v_h_725_, v_k_726_);
lean_dec(v_ctorIdx_723_);
lean_dec(v_inst_721_);
lean_dec_ref(v_s_720_);
lean_dec(v_pat_719_);
return v_res_727_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___redArg(lean_object* v_t_728_, lean_object* v_operating_729_){
_start:
{
lean_object* v___x_730_; 
v___x_730_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_728_, v_operating_729_);
return v___x_730_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim(lean_object* v_00_u03c3_731_, lean_object* v_00_u03c1_732_, lean_object* v_pat_733_, lean_object* v_s_734_, lean_object* v_inst_735_, lean_object* v_motive_736_, lean_object* v_t_737_, lean_object* v_h_738_, lean_object* v_operating_739_){
_start:
{
lean_object* v___x_740_; 
v___x_740_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_737_, v_operating_739_);
return v___x_740_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_operating_elim___boxed(lean_object* v_00_u03c3_741_, lean_object* v_00_u03c1_742_, lean_object* v_pat_743_, lean_object* v_s_744_, lean_object* v_inst_745_, lean_object* v_motive_746_, lean_object* v_t_747_, lean_object* v_h_748_, lean_object* v_operating_749_){
_start:
{
lean_object* v_res_750_; 
v_res_750_ = l_String_Slice_SplitInclusiveIterator_operating_elim(v_00_u03c3_741_, v_00_u03c1_742_, v_pat_743_, v_s_744_, v_inst_745_, v_motive_746_, v_t_747_, v_h_748_, v_operating_749_);
lean_dec(v_inst_745_);
lean_dec_ref(v_s_744_);
lean_dec(v_pat_743_);
return v_res_750_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___redArg(lean_object* v_t_751_, lean_object* v_atEnd_752_){
_start:
{
lean_object* v___x_753_; 
v___x_753_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_751_, v_atEnd_752_);
return v___x_753_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim(lean_object* v_00_u03c3_754_, lean_object* v_00_u03c1_755_, lean_object* v_pat_756_, lean_object* v_s_757_, lean_object* v_inst_758_, lean_object* v_motive_759_, lean_object* v_t_760_, lean_object* v_h_761_, lean_object* v_atEnd_762_){
_start:
{
lean_object* v___x_763_; 
v___x_763_ = l_String_Slice_SplitInclusiveIterator_ctorElim___redArg(v_t_760_, v_atEnd_762_);
return v___x_763_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_764_, lean_object* v_00_u03c1_765_, lean_object* v_pat_766_, lean_object* v_s_767_, lean_object* v_inst_768_, lean_object* v_motive_769_, lean_object* v_t_770_, lean_object* v_h_771_, lean_object* v_atEnd_772_){
_start:
{
lean_object* v_res_773_; 
v_res_773_ = l_String_Slice_SplitInclusiveIterator_atEnd_elim(v_00_u03c3_764_, v_00_u03c1_765_, v_pat_766_, v_s_767_, v_inst_768_, v_motive_769_, v_t_770_, v_h_771_, v_atEnd_772_);
lean_dec(v_inst_768_);
lean_dec_ref(v_s_767_);
lean_dec(v_pat_766_);
return v_res_773_;
}
}
lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg(){
_start:
{
lean_object* v___x_775_; 
v___x_775_ = lean_box(1);
return v___x_775_;
}
}
LEAN_EXPORT void l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_776_;
v_res_776_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg();
stack->m_obj
 = v_res_776_;
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg___boxed(lean_object* v___dummy_777_){
_start:
{
lean_object* v_res_778_; 
v_res_778_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default___redArg();
return v_res_778_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default(lean_object* v_00_u03c3_779_, lean_object* v_00_u03c1_780_, lean_object* v_pat_781_, lean_object* v_s_782_, lean_object* v_inst_783_){
_start:
{
lean_object* v___x_784_; 
v___x_784_ = lean_box(1);
return v___x_784_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator_default___boxed(lean_object* v_00_u03c3_785_, lean_object* v_00_u03c1_786_, lean_object* v_pat_787_, lean_object* v_s_788_, lean_object* v_inst_789_){
_start:
{
lean_object* v_res_790_; 
v_res_790_ = l_String_Slice_instInhabitedSplitInclusiveIterator_default(v_00_u03c3_785_, v_00_u03c1_786_, v_pat_787_, v_s_788_, v_inst_789_);
lean_dec(v_inst_789_);
lean_dec_ref(v_s_788_);
lean_dec(v_pat_787_);
return v_res_790_;
}
}
lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg(){
_start:
{
lean_object* v___x_792_; 
v___x_792_ = lean_box(1);
return v___x_792_;
}
}
LEAN_EXPORT void l_String_Slice_instInhabitedSplitInclusiveIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_793_;
v_res_793_ = l_String_Slice_instInhabitedSplitInclusiveIterator___redArg();
stack->m_obj
 = v_res_793_;
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___redArg___boxed(lean_object* v___dummy_794_){
_start:
{
lean_object* v_res_795_; 
v_res_795_ = l_String_Slice_instInhabitedSplitInclusiveIterator___redArg();
return v_res_795_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator(lean_object* v_a_796_, lean_object* v_a_797_, lean_object* v_a_798_, lean_object* v_a_799_, lean_object* v_a_800_){
_start:
{
lean_object* v___x_801_; 
v___x_801_ = lean_box(1);
return v___x_801_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedSplitInclusiveIterator___boxed(lean_object* v_a_802_, lean_object* v_a_803_, lean_object* v_a_804_, lean_object* v_a_805_, lean_object* v_a_806_){
_start:
{
lean_object* v_res_807_; 
v_res_807_ = l_String_Slice_instInhabitedSplitInclusiveIterator(v_a_802_, v_a_803_, v_a_804_, v_a_805_, v_a_806_);
lean_dec(v_a_806_);
lean_dec_ref(v_a_805_);
lean_dec(v_a_804_);
return v_res_807_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorId___redArg___lam__0(lean_object* v_inst_808_, lean_object* v_s_809_, lean_object* v_x_810_){
_start:
{
if (lean_obj_tag(v_x_810_) == 0)
{
lean_object* v_currPos_811_; lean_object* v_searcher_812_; lean_object* v___x_814_; uint8_t v_isShared_815_; uint8_t v_isSharedCheck_864_; 
v_currPos_811_ = lean_ctor_get(v_x_810_, 0);
v_searcher_812_ = lean_ctor_get(v_x_810_, 1);
v_isSharedCheck_864_ = !lean_is_exclusive(v_x_810_);
if (v_isSharedCheck_864_ == 0)
{
v___x_814_ = v_x_810_;
v_isShared_815_ = v_isSharedCheck_864_;
goto v_resetjp_813_;
}
else
{
lean_inc(v_searcher_812_);
lean_inc(v_currPos_811_);
lean_dec(v_x_810_);
v___x_814_ = lean_box(0);
v_isShared_815_ = v_isSharedCheck_864_;
goto v_resetjp_813_;
}
v_resetjp_813_:
{
lean_object* v___x_816_; 
lean_inc_ref(v_s_809_);
v___x_816_ = lean_apply_2(v_inst_808_, v_s_809_, v_searcher_812_);
switch(lean_obj_tag(v___x_816_))
{
case 0:
{
lean_object* v_out_817_; 
v_out_817_ = lean_ctor_get(v___x_816_, 1);
lean_inc(v_out_817_);
if (lean_obj_tag(v_out_817_) == 0)
{
lean_object* v_it_818_; lean_object* v___x_820_; 
lean_dec_ref_known(v_out_817_, 2);
lean_dec_ref(v_s_809_);
v_it_818_ = lean_ctor_get(v___x_816_, 0);
lean_inc(v_it_818_);
lean_dec_ref_known(v___x_816_, 2);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v_it_818_);
v___x_820_ = v___x_814_;
goto v_reusejp_819_;
}
else
{
lean_object* v_reuseFailAlloc_822_; 
v_reuseFailAlloc_822_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_822_, 0, v_currPos_811_);
lean_ctor_set(v_reuseFailAlloc_822_, 1, v_it_818_);
v___x_820_ = v_reuseFailAlloc_822_;
goto v_reusejp_819_;
}
v_reusejp_819_:
{
lean_object* v___x_821_; 
v___x_821_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_821_, 0, v___x_820_);
return v___x_821_;
}
}
else
{
lean_object* v_it_823_; lean_object* v___x_825_; uint8_t v_isShared_826_; uint8_t v_isSharedCheck_835_; 
v_it_823_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_835_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_835_ == 0)
{
lean_object* v_unused_836_; 
v_unused_836_ = lean_ctor_get(v___x_816_, 1);
lean_dec(v_unused_836_);
v___x_825_ = v___x_816_;
v_isShared_826_ = v_isSharedCheck_835_;
goto v_resetjp_824_;
}
else
{
lean_inc(v_it_823_);
lean_dec(v___x_816_);
v___x_825_ = lean_box(0);
v_isShared_826_ = v_isSharedCheck_835_;
goto v_resetjp_824_;
}
v_resetjp_824_:
{
lean_object* v_endPos_827_; lean_object* v_slice_828_; lean_object* v_nextIt_830_; 
v_endPos_827_ = lean_ctor_get(v_out_817_, 1);
lean_inc(v_endPos_827_);
lean_dec_ref_known(v_out_817_, 2);
v_slice_828_ = l_String_Slice_slice_x21(v_s_809_, v_currPos_811_, v_endPos_827_);
lean_dec(v_currPos_811_);
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v_it_823_);
lean_ctor_set(v___x_814_, 0, v_endPos_827_);
v_nextIt_830_ = v___x_814_;
goto v_reusejp_829_;
}
else
{
lean_object* v_reuseFailAlloc_834_; 
v_reuseFailAlloc_834_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_834_, 0, v_endPos_827_);
lean_ctor_set(v_reuseFailAlloc_834_, 1, v_it_823_);
v_nextIt_830_ = v_reuseFailAlloc_834_;
goto v_reusejp_829_;
}
v_reusejp_829_:
{
lean_object* v___x_832_; 
if (v_isShared_826_ == 0)
{
lean_ctor_set(v___x_825_, 1, v_slice_828_);
lean_ctor_set(v___x_825_, 0, v_nextIt_830_);
v___x_832_ = v___x_825_;
goto v_reusejp_831_;
}
else
{
lean_object* v_reuseFailAlloc_833_; 
v_reuseFailAlloc_833_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_833_, 0, v_nextIt_830_);
lean_ctor_set(v_reuseFailAlloc_833_, 1, v_slice_828_);
v___x_832_ = v_reuseFailAlloc_833_;
goto v_reusejp_831_;
}
v_reusejp_831_:
{
return v___x_832_;
}
}
}
}
}
case 1:
{
lean_object* v_it_837_; lean_object* v___x_839_; uint8_t v_isShared_840_; uint8_t v_isSharedCheck_847_; 
lean_dec_ref(v_s_809_);
v_it_837_ = lean_ctor_get(v___x_816_, 0);
v_isSharedCheck_847_ = !lean_is_exclusive(v___x_816_);
if (v_isSharedCheck_847_ == 0)
{
v___x_839_ = v___x_816_;
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
else
{
lean_inc(v_it_837_);
lean_dec(v___x_816_);
v___x_839_ = lean_box(0);
v_isShared_840_ = v_isSharedCheck_847_;
goto v_resetjp_838_;
}
v_resetjp_838_:
{
lean_object* v___x_842_; 
if (v_isShared_815_ == 0)
{
lean_ctor_set(v___x_814_, 1, v_it_837_);
v___x_842_ = v___x_814_;
goto v_reusejp_841_;
}
else
{
lean_object* v_reuseFailAlloc_846_; 
v_reuseFailAlloc_846_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_846_, 0, v_currPos_811_);
lean_ctor_set(v_reuseFailAlloc_846_, 1, v_it_837_);
v___x_842_ = v_reuseFailAlloc_846_;
goto v_reusejp_841_;
}
v_reusejp_841_:
{
lean_object* v___x_844_; 
if (v_isShared_840_ == 0)
{
lean_ctor_set(v___x_839_, 0, v___x_842_);
v___x_844_ = v___x_839_;
goto v_reusejp_843_;
}
else
{
lean_object* v_reuseFailAlloc_845_; 
v_reuseFailAlloc_845_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_845_, 0, v___x_842_);
v___x_844_ = v_reuseFailAlloc_845_;
goto v_reusejp_843_;
}
v_reusejp_843_:
{
return v___x_844_;
}
}
}
}
default: 
{
lean_object* v_str_848_; lean_object* v_startInclusive_849_; lean_object* v_endExclusive_850_; lean_object* v___x_852_; uint8_t v_isShared_853_; uint8_t v_isSharedCheck_863_; 
lean_del_object(v___x_814_);
v_str_848_ = lean_ctor_get(v_s_809_, 0);
v_startInclusive_849_ = lean_ctor_get(v_s_809_, 1);
v_endExclusive_850_ = lean_ctor_get(v_s_809_, 2);
v_isSharedCheck_863_ = !lean_is_exclusive(v_s_809_);
if (v_isSharedCheck_863_ == 0)
{
v___x_852_ = v_s_809_;
v_isShared_853_ = v_isSharedCheck_863_;
goto v_resetjp_851_;
}
else
{
lean_inc(v_endExclusive_850_);
lean_inc(v_startInclusive_849_);
lean_inc(v_str_848_);
lean_dec(v_s_809_);
v___x_852_ = lean_box(0);
v_isShared_853_ = v_isSharedCheck_863_;
goto v_resetjp_851_;
}
v_resetjp_851_:
{
lean_object* v___x_854_; uint8_t v_decide_855_; 
v___x_854_ = lean_nat_sub(v_endExclusive_850_, v_startInclusive_849_);
v_decide_855_ = lean_nat_dec_eq(v_currPos_811_, v___x_854_);
lean_dec(v___x_854_);
if (v_decide_855_ == 0)
{
lean_object* v___x_856_; lean_object* v_slice_858_; 
v___x_856_ = lean_nat_add(v_startInclusive_849_, v_currPos_811_);
lean_dec(v_currPos_811_);
lean_dec(v_startInclusive_849_);
if (v_isShared_853_ == 0)
{
lean_ctor_set(v___x_852_, 1, v___x_856_);
v_slice_858_ = v___x_852_;
goto v_reusejp_857_;
}
else
{
lean_object* v_reuseFailAlloc_861_; 
v_reuseFailAlloc_861_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_861_, 0, v_str_848_);
lean_ctor_set(v_reuseFailAlloc_861_, 1, v___x_856_);
lean_ctor_set(v_reuseFailAlloc_861_, 2, v_endExclusive_850_);
v_slice_858_ = v_reuseFailAlloc_861_;
goto v_reusejp_857_;
}
v_reusejp_857_:
{
lean_object* v___x_859_; lean_object* v___x_860_; 
v___x_859_ = lean_box(1);
v___x_860_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_860_, 0, v___x_859_);
lean_ctor_set(v___x_860_, 1, v_slice_858_);
return v___x_860_;
}
}
else
{
lean_object* v___x_862_; 
lean_del_object(v___x_852_);
lean_dec(v_endExclusive_850_);
lean_dec(v_startInclusive_849_);
lean_dec_ref(v_str_848_);
lean_dec(v_currPos_811_);
v___x_862_ = lean_box(2);
return v___x_862_;
}
}
}
}
}
}
else
{
lean_object* v___x_865_; 
lean_dec_ref(v_s_809_);
lean_dec(v_inst_808_);
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
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_1039_; 
v___x_1039_ = lean_box(0);
return v___x_1039_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1040_;
v_res_1040_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg();
stack->m_obj
 = v_res_1040_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_1041_){
_start:
{
lean_object* v_res_1042_; 
v_res_1042_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___redArg();
return v_res_1042_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(lean_object* v_00_u03c1_1043_, lean_object* v_00_u03c3_1044_, lean_object* v_inst_1045_, lean_object* v_pat_1046_, lean_object* v_inst_1047_, lean_object* v_s_1048_, lean_object* v_inst_1049_){
_start:
{
lean_object* v___x_1050_; 
v___x_1050_ = lean_box(0);
return v___x_1050_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_1051_, lean_object* v_00_u03c3_1052_, lean_object* v_inst_1053_, lean_object* v_pat_1054_, lean_object* v_inst_1055_, lean_object* v_s_1056_, lean_object* v_inst_1057_){
_start:
{
lean_object* v_res_1058_; 
v_res_1058_ = l___private_Init_Data_String_Slice_0__String_Slice_SplitInclusiveIterator_finitenessRelation(v_00_u03c1_1051_, v_00_u03c3_1052_, v_inst_1053_, v_pat_1054_, v_inst_1055_, v_s_1056_, v_inst_1057_);
lean_dec_ref(v_s_1056_);
lean_dec(v_inst_1055_);
lean_dec(v_pat_1054_);
lean_dec(v_inst_1053_);
return v_res_1058_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0(lean_object* v_toPure_1059_, lean_object* v_recur_1060_, lean_object* v_it_1061_, lean_object* v_____do__lift_1062_){
_start:
{
if (lean_obj_tag(v_____do__lift_1062_) == 0)
{
lean_object* v_a_1063_; lean_object* v___x_1064_; 
lean_dec(v_it_1061_);
lean_dec(v_recur_1060_);
v_a_1063_ = lean_ctor_get(v_____do__lift_1062_, 0);
lean_inc(v_a_1063_);
lean_dec_ref_known(v_____do__lift_1062_, 1);
v___x_1064_ = lean_apply_2(v_toPure_1059_, lean_box(0), v_a_1063_);
return v___x_1064_;
}
else
{
lean_object* v_a_1065_; lean_object* v___x_1066_; 
lean_dec(v_toPure_1059_);
v_a_1065_ = lean_ctor_get(v_____do__lift_1062_, 0);
lean_inc(v_a_1065_);
lean_dec_ref_known(v_____do__lift_1062_, 1);
v___x_1066_ = lean_apply_4(v_recur_1060_, v_it_1061_, v_a_1065_, lean_box(0), lean_box(0));
return v___x_1066_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1(lean_object* v_toPure_1067_, lean_object* v_recur_1068_, lean_object* v___y_1069_, lean_object* v_acc_1070_, lean_object* v_toBind_1071_, lean_object* v_s_1072_){
_start:
{
switch(lean_obj_tag(v_s_1072_))
{
case 0:
{
lean_object* v_it_1073_; lean_object* v_out_1074_; lean_object* v___f_1075_; lean_object* v___x_1076_; lean_object* v___x_1077_; 
v_it_1073_ = lean_ctor_get(v_s_1072_, 0);
lean_inc(v_it_1073_);
v_out_1074_ = lean_ctor_get(v_s_1072_, 1);
lean_inc(v_out_1074_);
lean_dec_ref_known(v_s_1072_, 2);
v___f_1075_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_1075_, 0, v_toPure_1067_);
lean_closure_set(v___f_1075_, 1, v_recur_1068_);
lean_closure_set(v___f_1075_, 2, v_it_1073_);
v___x_1076_ = lean_apply_3(v___y_1069_, v_out_1074_, lean_box(0), v_acc_1070_);
v___x_1077_ = lean_apply_4(v_toBind_1071_, lean_box(0), lean_box(0), v___x_1076_, v___f_1075_);
return v___x_1077_;
}
case 1:
{
lean_object* v_it_1078_; lean_object* v___x_1079_; 
lean_dec(v_toBind_1071_);
lean_dec(v___y_1069_);
lean_dec(v_toPure_1067_);
v_it_1078_ = lean_ctor_get(v_s_1072_, 0);
lean_inc(v_it_1078_);
lean_dec_ref_known(v_s_1072_, 1);
v___x_1079_ = lean_apply_4(v_recur_1068_, v_it_1078_, v_acc_1070_, lean_box(0), lean_box(0));
return v___x_1079_;
}
default: 
{
lean_object* v___x_1080_; 
lean_dec(v_toBind_1071_);
lean_dec(v___y_1069_);
lean_dec(v_recur_1068_);
v___x_1080_ = lean_apply_2(v_toPure_1067_, lean_box(0), v_acc_1070_);
return v___x_1080_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2(lean_object* v_toPure_1081_, lean_object* v___y_1082_, lean_object* v_toBind_1083_, lean_object* v_inst_1084_, lean_object* v_s_1085_, lean_object* v_lift_1086_, lean_object* v_it_1087_, lean_object* v_acc_1088_, lean_object* v_hP_1089_, lean_object* v_recur_1090_){
_start:
{
lean_object* v___f_1091_; 
v___f_1091_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_1091_, 0, v_toPure_1081_);
lean_closure_set(v___f_1091_, 1, v_recur_1090_);
lean_closure_set(v___f_1091_, 2, v___y_1082_);
lean_closure_set(v___f_1091_, 3, v_acc_1088_);
lean_closure_set(v___f_1091_, 4, v_toBind_1083_);
if (lean_obj_tag(v_it_1087_) == 0)
{
lean_object* v_currPos_1092_; lean_object* v_searcher_1093_; lean_object* v___x_1095_; uint8_t v_isShared_1096_; uint8_t v_isSharedCheck_1150_; 
v_currPos_1092_ = lean_ctor_get(v_it_1087_, 0);
v_searcher_1093_ = lean_ctor_get(v_it_1087_, 1);
v_isSharedCheck_1150_ = !lean_is_exclusive(v_it_1087_);
if (v_isSharedCheck_1150_ == 0)
{
v___x_1095_ = v_it_1087_;
v_isShared_1096_ = v_isSharedCheck_1150_;
goto v_resetjp_1094_;
}
else
{
lean_inc(v_searcher_1093_);
lean_inc(v_currPos_1092_);
lean_dec(v_it_1087_);
v___x_1095_ = lean_box(0);
v_isShared_1096_ = v_isSharedCheck_1150_;
goto v_resetjp_1094_;
}
v_resetjp_1094_:
{
lean_object* v___x_1097_; 
lean_inc_ref(v_s_1085_);
v___x_1097_ = lean_apply_2(v_inst_1084_, v_s_1085_, v_searcher_1093_);
switch(lean_obj_tag(v___x_1097_))
{
case 0:
{
lean_object* v_out_1098_; 
v_out_1098_ = lean_ctor_get(v___x_1097_, 1);
lean_inc(v_out_1098_);
if (lean_obj_tag(v_out_1098_) == 0)
{
lean_object* v_it_1099_; lean_object* v___x_1101_; 
lean_dec_ref_known(v_out_1098_, 2);
lean_dec_ref(v_s_1085_);
v_it_1099_ = lean_ctor_get(v___x_1097_, 0);
lean_inc(v_it_1099_);
lean_dec_ref_known(v___x_1097_, 2);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v_it_1099_);
v___x_1101_ = v___x_1095_;
goto v_reusejp_1100_;
}
else
{
lean_object* v_reuseFailAlloc_1104_; 
v_reuseFailAlloc_1104_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1104_, 0, v_currPos_1092_);
lean_ctor_set(v_reuseFailAlloc_1104_, 1, v_it_1099_);
v___x_1101_ = v_reuseFailAlloc_1104_;
goto v_reusejp_1100_;
}
v_reusejp_1100_:
{
lean_object* v___x_1102_; lean_object* v___x_1103_; 
v___x_1102_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1102_, 0, v___x_1101_);
v___x_1103_ = lean_apply_4(v_lift_1086_, lean_box(0), lean_box(0), v___f_1091_, v___x_1102_);
return v___x_1103_;
}
}
else
{
lean_object* v_it_1105_; lean_object* v___x_1107_; uint8_t v_isShared_1108_; uint8_t v_isSharedCheck_1118_; 
v_it_1105_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1118_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1118_ == 0)
{
lean_object* v_unused_1119_; 
v_unused_1119_ = lean_ctor_get(v___x_1097_, 1);
lean_dec(v_unused_1119_);
v___x_1107_ = v___x_1097_;
v_isShared_1108_ = v_isSharedCheck_1118_;
goto v_resetjp_1106_;
}
else
{
lean_inc(v_it_1105_);
lean_dec(v___x_1097_);
v___x_1107_ = lean_box(0);
v_isShared_1108_ = v_isSharedCheck_1118_;
goto v_resetjp_1106_;
}
v_resetjp_1106_:
{
lean_object* v_endPos_1109_; lean_object* v_slice_1110_; lean_object* v_nextIt_1112_; 
v_endPos_1109_ = lean_ctor_get(v_out_1098_, 1);
lean_inc(v_endPos_1109_);
lean_dec_ref_known(v_out_1098_, 2);
v_slice_1110_ = l_String_Slice_slice_x21(v_s_1085_, v_currPos_1092_, v_endPos_1109_);
lean_dec(v_currPos_1092_);
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v_it_1105_);
lean_ctor_set(v___x_1095_, 0, v_endPos_1109_);
v_nextIt_1112_ = v___x_1095_;
goto v_reusejp_1111_;
}
else
{
lean_object* v_reuseFailAlloc_1117_; 
v_reuseFailAlloc_1117_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1117_, 0, v_endPos_1109_);
lean_ctor_set(v_reuseFailAlloc_1117_, 1, v_it_1105_);
v_nextIt_1112_ = v_reuseFailAlloc_1117_;
goto v_reusejp_1111_;
}
v_reusejp_1111_:
{
lean_object* v___x_1114_; 
if (v_isShared_1108_ == 0)
{
lean_ctor_set(v___x_1107_, 1, v_slice_1110_);
lean_ctor_set(v___x_1107_, 0, v_nextIt_1112_);
v___x_1114_ = v___x_1107_;
goto v_reusejp_1113_;
}
else
{
lean_object* v_reuseFailAlloc_1116_; 
v_reuseFailAlloc_1116_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1116_, 0, v_nextIt_1112_);
lean_ctor_set(v_reuseFailAlloc_1116_, 1, v_slice_1110_);
v___x_1114_ = v_reuseFailAlloc_1116_;
goto v_reusejp_1113_;
}
v_reusejp_1113_:
{
lean_object* v___x_1115_; 
v___x_1115_ = lean_apply_4(v_lift_1086_, lean_box(0), lean_box(0), v___f_1091_, v___x_1114_);
return v___x_1115_;
}
}
}
}
}
case 1:
{
lean_object* v_it_1120_; lean_object* v___x_1122_; uint8_t v_isShared_1123_; uint8_t v_isSharedCheck_1131_; 
lean_dec_ref(v_s_1085_);
v_it_1120_ = lean_ctor_get(v___x_1097_, 0);
v_isSharedCheck_1131_ = !lean_is_exclusive(v___x_1097_);
if (v_isSharedCheck_1131_ == 0)
{
v___x_1122_ = v___x_1097_;
v_isShared_1123_ = v_isSharedCheck_1131_;
goto v_resetjp_1121_;
}
else
{
lean_inc(v_it_1120_);
lean_dec(v___x_1097_);
v___x_1122_ = lean_box(0);
v_isShared_1123_ = v_isSharedCheck_1131_;
goto v_resetjp_1121_;
}
v_resetjp_1121_:
{
lean_object* v___x_1125_; 
if (v_isShared_1096_ == 0)
{
lean_ctor_set(v___x_1095_, 1, v_it_1120_);
v___x_1125_ = v___x_1095_;
goto v_reusejp_1124_;
}
else
{
lean_object* v_reuseFailAlloc_1130_; 
v_reuseFailAlloc_1130_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_1130_, 0, v_currPos_1092_);
lean_ctor_set(v_reuseFailAlloc_1130_, 1, v_it_1120_);
v___x_1125_ = v_reuseFailAlloc_1130_;
goto v_reusejp_1124_;
}
v_reusejp_1124_:
{
lean_object* v___x_1127_; 
if (v_isShared_1123_ == 0)
{
lean_ctor_set(v___x_1122_, 0, v___x_1125_);
v___x_1127_ = v___x_1122_;
goto v_reusejp_1126_;
}
else
{
lean_object* v_reuseFailAlloc_1129_; 
v_reuseFailAlloc_1129_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1129_, 0, v___x_1125_);
v___x_1127_ = v_reuseFailAlloc_1129_;
goto v_reusejp_1126_;
}
v_reusejp_1126_:
{
lean_object* v___x_1128_; 
v___x_1128_ = lean_apply_4(v_lift_1086_, lean_box(0), lean_box(0), v___f_1091_, v___x_1127_);
return v___x_1128_;
}
}
}
}
default: 
{
lean_object* v_str_1132_; lean_object* v_startInclusive_1133_; lean_object* v_endExclusive_1134_; lean_object* v___x_1136_; uint8_t v_isShared_1137_; uint8_t v_isSharedCheck_1149_; 
lean_del_object(v___x_1095_);
v_str_1132_ = lean_ctor_get(v_s_1085_, 0);
v_startInclusive_1133_ = lean_ctor_get(v_s_1085_, 1);
v_endExclusive_1134_ = lean_ctor_get(v_s_1085_, 2);
v_isSharedCheck_1149_ = !lean_is_exclusive(v_s_1085_);
if (v_isSharedCheck_1149_ == 0)
{
v___x_1136_ = v_s_1085_;
v_isShared_1137_ = v_isSharedCheck_1149_;
goto v_resetjp_1135_;
}
else
{
lean_inc(v_endExclusive_1134_);
lean_inc(v_startInclusive_1133_);
lean_inc(v_str_1132_);
lean_dec(v_s_1085_);
v___x_1136_ = lean_box(0);
v_isShared_1137_ = v_isSharedCheck_1149_;
goto v_resetjp_1135_;
}
v_resetjp_1135_:
{
lean_object* v___x_1138_; uint8_t v_decide_1139_; 
v___x_1138_ = lean_nat_sub(v_endExclusive_1134_, v_startInclusive_1133_);
v_decide_1139_ = lean_nat_dec_eq(v_currPos_1092_, v___x_1138_);
lean_dec(v___x_1138_);
if (v_decide_1139_ == 0)
{
lean_object* v___x_1140_; lean_object* v_slice_1142_; 
v___x_1140_ = lean_nat_add(v_startInclusive_1133_, v_currPos_1092_);
lean_dec(v_currPos_1092_);
lean_dec(v_startInclusive_1133_);
if (v_isShared_1137_ == 0)
{
lean_ctor_set(v___x_1136_, 1, v___x_1140_);
v_slice_1142_ = v___x_1136_;
goto v_reusejp_1141_;
}
else
{
lean_object* v_reuseFailAlloc_1146_; 
v_reuseFailAlloc_1146_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1146_, 0, v_str_1132_);
lean_ctor_set(v_reuseFailAlloc_1146_, 1, v___x_1140_);
lean_ctor_set(v_reuseFailAlloc_1146_, 2, v_endExclusive_1134_);
v_slice_1142_ = v_reuseFailAlloc_1146_;
goto v_reusejp_1141_;
}
v_reusejp_1141_:
{
lean_object* v___x_1143_; lean_object* v___x_1144_; lean_object* v___x_1145_; 
v___x_1143_ = lean_box(1);
v___x_1144_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1144_, 0, v___x_1143_);
lean_ctor_set(v___x_1144_, 1, v_slice_1142_);
v___x_1145_ = lean_apply_4(v_lift_1086_, lean_box(0), lean_box(0), v___f_1091_, v___x_1144_);
return v___x_1145_;
}
}
else
{
lean_object* v___x_1147_; lean_object* v___x_1148_; 
lean_del_object(v___x_1136_);
lean_dec(v_endExclusive_1134_);
lean_dec(v_startInclusive_1133_);
lean_dec_ref(v_str_1132_);
lean_dec(v_currPos_1092_);
v___x_1147_ = lean_box(2);
v___x_1148_ = lean_apply_4(v_lift_1086_, lean_box(0), lean_box(0), v___f_1091_, v___x_1147_);
return v___x_1148_;
}
}
}
}
}
}
else
{
lean_object* v___x_1151_; lean_object* v___x_1152_; 
lean_dec_ref(v_s_1085_);
lean_dec(v_inst_1084_);
v___x_1151_ = lean_box(2);
v___x_1152_ = lean_apply_4(v_lift_1086_, lean_box(0), lean_box(0), v___f_1091_, v___x_1151_);
return v___x_1152_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3(lean_object* v_inst_1153_, lean_object* v_inst_1154_, lean_object* v_s_1155_, lean_object* v_lift_1156_, lean_object* v_00_u03b3_1157_, lean_object* v_Pl_1158_, lean_object* v_it_1159_, lean_object* v_init_1160_, lean_object* v___y_1161_){
_start:
{
lean_object* v_toApplicative_1162_; lean_object* v_toBind_1163_; lean_object* v_toPure_1164_; lean_object* v___f_1165_; lean_object* v___x_1166_; 
v_toApplicative_1162_ = lean_ctor_get(v_inst_1153_, 0);
lean_inc_ref(v_toApplicative_1162_);
v_toBind_1163_ = lean_ctor_get(v_inst_1153_, 1);
lean_inc(v_toBind_1163_);
lean_dec_ref(v_inst_1153_);
v_toPure_1164_ = lean_ctor_get(v_toApplicative_1162_, 1);
lean_inc(v_toPure_1164_);
lean_dec_ref(v_toApplicative_1162_);
v___f_1165_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__2), 10, 6);
lean_closure_set(v___f_1165_, 0, v_toPure_1164_);
lean_closure_set(v___f_1165_, 1, v___y_1161_);
lean_closure_set(v___f_1165_, 2, v_toBind_1163_);
lean_closure_set(v___f_1165_, 3, v_inst_1154_);
lean_closure_set(v___f_1165_, 4, v_s_1155_);
lean_closure_set(v___f_1165_, 5, v_lift_1156_);
v___x_1166_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_1165_, v_it_1159_, v_init_1160_, lean_box(0));
return v___x_1166_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg(lean_object* v_inst_1167_, lean_object* v_inst_1168_, lean_object* v_s_1169_){
_start:
{
lean_object* v___f_1170_; 
v___f_1170_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1170_, 0, v_inst_1168_);
lean_closure_set(v___f_1170_, 1, v_inst_1167_);
lean_closure_set(v___f_1170_, 2, v_s_1169_);
return v___f_1170_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(lean_object* v_00_u03c1_1171_, lean_object* v_00_u03c3_1172_, lean_object* v_inst_1173_, lean_object* v_pat_1174_, lean_object* v_inst_1175_, lean_object* v_n_1176_, lean_object* v_inst_1177_, lean_object* v_s_1178_){
_start:
{
lean_object* v___f_1179_; 
v___f_1179_ = lean_alloc_closure((void*)(l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___redArg___lam__3), 9, 3);
lean_closure_set(v___f_1179_, 0, v_inst_1177_);
lean_closure_set(v___f_1179_, 1, v_inst_1173_);
lean_closure_set(v___f_1179_, 2, v_s_1178_);
return v___f_1179_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad___boxed(lean_object* v_00_u03c1_1180_, lean_object* v_00_u03c3_1181_, lean_object* v_inst_1182_, lean_object* v_pat_1183_, lean_object* v_inst_1184_, lean_object* v_n_1185_, lean_object* v_inst_1186_, lean_object* v_s_1187_){
_start:
{
lean_object* v_res_1188_; 
v_res_1188_ = l_String_Slice_SplitInclusiveIterator_instIteratorLoopIdOfMonad(v_00_u03c1_1180_, v_00_u03c3_1181_, v_inst_1182_, v_pat_1183_, v_inst_1184_, v_n_1185_, v_inst_1186_, v_s_1187_);
lean_dec(v_inst_1184_);
lean_dec(v_pat_1183_);
return v_res_1188_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___redArg(lean_object* v_s_1189_, lean_object* v_inst_1190_){
_start:
{
lean_object* v___x_1191_; lean_object* v___x_1192_; lean_object* v___x_1193_; 
v___x_1191_ = lean_unsigned_to_nat(0u);
v___x_1192_ = lean_apply_1(v_inst_1190_, v_s_1189_);
v___x_1193_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_1193_, 0, v___x_1191_);
lean_ctor_set(v___x_1193_, 1, v___x_1192_);
return v___x_1193_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive(lean_object* v_00_u03c1_1194_, lean_object* v_00_u03c3_1195_, lean_object* v_s_1196_, lean_object* v_pat_1197_, lean_object* v_inst_1198_){
_start:
{
lean_object* v___x_1199_; 
v___x_1199_ = l_String_Slice_splitInclusive___redArg(v_s_1196_, v_inst_1198_);
return v___x_1199_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___boxed(lean_object* v_00_u03c1_1200_, lean_object* v_00_u03c3_1201_, lean_object* v_s_1202_, lean_object* v_pat_1203_, lean_object* v_inst_1204_){
_start:
{
lean_object* v_res_1205_; 
v_res_1205_ = l_String_Slice_splitInclusive(v_00_u03c1_1200_, v_00_u03c3_1201_, v_s_1202_, v_pat_1203_, v_inst_1204_);
lean_dec(v_pat_1203_);
return v_res_1205_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___redArg(lean_object* v_s_1206_, lean_object* v_inst_1207_){
_start:
{
lean_object* v_skipPrefix_x3f_1208_; lean_object* v___x_1209_; 
v_skipPrefix_x3f_1208_ = lean_ctor_get(v_inst_1207_, 0);
lean_inc_ref(v_skipPrefix_x3f_1208_);
lean_dec_ref(v_inst_1207_);
v___x_1209_ = lean_apply_1(v_skipPrefix_x3f_1208_, v_s_1206_);
return v___x_1209_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f(lean_object* v_00_u03c1_1210_, lean_object* v_s_1211_, lean_object* v_pat_1212_, lean_object* v_inst_1213_){
_start:
{
lean_object* v_skipPrefix_x3f_1214_; lean_object* v___x_1215_; 
v_skipPrefix_x3f_1214_ = lean_ctor_get(v_inst_1213_, 0);
lean_inc_ref(v_skipPrefix_x3f_1214_);
lean_dec_ref(v_inst_1213_);
v___x_1215_ = lean_apply_1(v_skipPrefix_x3f_1214_, v_s_1211_);
return v___x_1215_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefix_x3f___boxed(lean_object* v_00_u03c1_1216_, lean_object* v_s_1217_, lean_object* v_pat_1218_, lean_object* v_inst_1219_){
_start:
{
lean_object* v_res_1220_; 
v_res_1220_ = l_String_Slice_skipPrefix_x3f(v_00_u03c1_1216_, v_s_1217_, v_pat_1218_, v_inst_1219_);
lean_dec(v_pat_1218_);
return v_res_1220_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg(lean_object* v_s_1221_, lean_object* v_pos_1222_, lean_object* v_inst_1223_){
_start:
{
lean_object* v_str_1224_; lean_object* v_startInclusive_1225_; lean_object* v_endExclusive_1226_; lean_object* v___x_1228_; uint8_t v_isShared_1229_; uint8_t v_isSharedCheck_1245_; 
v_str_1224_ = lean_ctor_get(v_s_1221_, 0);
v_startInclusive_1225_ = lean_ctor_get(v_s_1221_, 1);
v_endExclusive_1226_ = lean_ctor_get(v_s_1221_, 2);
v_isSharedCheck_1245_ = !lean_is_exclusive(v_s_1221_);
if (v_isSharedCheck_1245_ == 0)
{
v___x_1228_ = v_s_1221_;
v_isShared_1229_ = v_isSharedCheck_1245_;
goto v_resetjp_1227_;
}
else
{
lean_inc(v_endExclusive_1226_);
lean_inc(v_startInclusive_1225_);
lean_inc(v_str_1224_);
lean_dec(v_s_1221_);
v___x_1228_ = lean_box(0);
v_isShared_1229_ = v_isSharedCheck_1245_;
goto v_resetjp_1227_;
}
v_resetjp_1227_:
{
lean_object* v_skipPrefix_x3f_1230_; lean_object* v___x_1231_; lean_object* v___x_1233_; 
v_skipPrefix_x3f_1230_ = lean_ctor_get(v_inst_1223_, 0);
lean_inc_ref(v_skipPrefix_x3f_1230_);
lean_dec_ref(v_inst_1223_);
v___x_1231_ = lean_nat_add(v_startInclusive_1225_, v_pos_1222_);
lean_dec(v_startInclusive_1225_);
if (v_isShared_1229_ == 0)
{
lean_ctor_set(v___x_1228_, 1, v___x_1231_);
v___x_1233_ = v___x_1228_;
goto v_reusejp_1232_;
}
else
{
lean_object* v_reuseFailAlloc_1244_; 
v_reuseFailAlloc_1244_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1244_, 0, v_str_1224_);
lean_ctor_set(v_reuseFailAlloc_1244_, 1, v___x_1231_);
lean_ctor_set(v_reuseFailAlloc_1244_, 2, v_endExclusive_1226_);
v___x_1233_ = v_reuseFailAlloc_1244_;
goto v_reusejp_1232_;
}
v_reusejp_1232_:
{
lean_object* v___x_1234_; 
v___x_1234_ = lean_apply_1(v_skipPrefix_x3f_1230_, v___x_1233_);
if (lean_obj_tag(v___x_1234_) == 0)
{
return v___x_1234_;
}
else
{
lean_object* v_val_1235_; lean_object* v___x_1237_; uint8_t v_isShared_1238_; uint8_t v_isSharedCheck_1243_; 
v_val_1235_ = lean_ctor_get(v___x_1234_, 0);
v_isSharedCheck_1243_ = !lean_is_exclusive(v___x_1234_);
if (v_isSharedCheck_1243_ == 0)
{
v___x_1237_ = v___x_1234_;
v_isShared_1238_ = v_isSharedCheck_1243_;
goto v_resetjp_1236_;
}
else
{
lean_inc(v_val_1235_);
lean_dec(v___x_1234_);
v___x_1237_ = lean_box(0);
v_isShared_1238_ = v_isSharedCheck_1243_;
goto v_resetjp_1236_;
}
v_resetjp_1236_:
{
lean_object* v___x_1239_; lean_object* v___x_1241_; 
v___x_1239_ = lean_nat_add(v_pos_1222_, v_val_1235_);
lean_dec(v_val_1235_);
if (v_isShared_1238_ == 0)
{
lean_ctor_set(v___x_1237_, 0, v___x_1239_);
v___x_1241_ = v___x_1237_;
goto v_reusejp_1240_;
}
else
{
lean_object* v_reuseFailAlloc_1242_; 
v_reuseFailAlloc_1242_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1242_, 0, v___x_1239_);
v___x_1241_ = v_reuseFailAlloc_1242_;
goto v_reusejp_1240_;
}
v_reusejp_1240_:
{
return v___x_1241_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___redArg___boxed(lean_object* v_s_1246_, lean_object* v_pos_1247_, lean_object* v_inst_1248_){
_start:
{
lean_object* v_res_1249_; 
v_res_1249_ = l_String_Slice_Pos_skip_x3f___redArg(v_s_1246_, v_pos_1247_, v_inst_1248_);
lean_dec(v_pos_1247_);
return v_res_1249_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f(lean_object* v_00_u03c1_1250_, lean_object* v_s_1251_, lean_object* v_pos_1252_, lean_object* v_pat_1253_, lean_object* v_inst_1254_){
_start:
{
lean_object* v_str_1255_; lean_object* v_startInclusive_1256_; lean_object* v_endExclusive_1257_; lean_object* v___x_1259_; uint8_t v_isShared_1260_; uint8_t v_isSharedCheck_1276_; 
v_str_1255_ = lean_ctor_get(v_s_1251_, 0);
v_startInclusive_1256_ = lean_ctor_get(v_s_1251_, 1);
v_endExclusive_1257_ = lean_ctor_get(v_s_1251_, 2);
v_isSharedCheck_1276_ = !lean_is_exclusive(v_s_1251_);
if (v_isSharedCheck_1276_ == 0)
{
v___x_1259_ = v_s_1251_;
v_isShared_1260_ = v_isSharedCheck_1276_;
goto v_resetjp_1258_;
}
else
{
lean_inc(v_endExclusive_1257_);
lean_inc(v_startInclusive_1256_);
lean_inc(v_str_1255_);
lean_dec(v_s_1251_);
v___x_1259_ = lean_box(0);
v_isShared_1260_ = v_isSharedCheck_1276_;
goto v_resetjp_1258_;
}
v_resetjp_1258_:
{
lean_object* v_skipPrefix_x3f_1261_; lean_object* v___x_1262_; lean_object* v___x_1264_; 
v_skipPrefix_x3f_1261_ = lean_ctor_get(v_inst_1254_, 0);
lean_inc_ref(v_skipPrefix_x3f_1261_);
lean_dec_ref(v_inst_1254_);
v___x_1262_ = lean_nat_add(v_startInclusive_1256_, v_pos_1252_);
lean_dec(v_startInclusive_1256_);
if (v_isShared_1260_ == 0)
{
lean_ctor_set(v___x_1259_, 1, v___x_1262_);
v___x_1264_ = v___x_1259_;
goto v_reusejp_1263_;
}
else
{
lean_object* v_reuseFailAlloc_1275_; 
v_reuseFailAlloc_1275_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1275_, 0, v_str_1255_);
lean_ctor_set(v_reuseFailAlloc_1275_, 1, v___x_1262_);
lean_ctor_set(v_reuseFailAlloc_1275_, 2, v_endExclusive_1257_);
v___x_1264_ = v_reuseFailAlloc_1275_;
goto v_reusejp_1263_;
}
v_reusejp_1263_:
{
lean_object* v___x_1265_; 
v___x_1265_ = lean_apply_1(v_skipPrefix_x3f_1261_, v___x_1264_);
if (lean_obj_tag(v___x_1265_) == 0)
{
return v___x_1265_;
}
else
{
lean_object* v_val_1266_; lean_object* v___x_1268_; uint8_t v_isShared_1269_; uint8_t v_isSharedCheck_1274_; 
v_val_1266_ = lean_ctor_get(v___x_1265_, 0);
v_isSharedCheck_1274_ = !lean_is_exclusive(v___x_1265_);
if (v_isSharedCheck_1274_ == 0)
{
v___x_1268_ = v___x_1265_;
v_isShared_1269_ = v_isSharedCheck_1274_;
goto v_resetjp_1267_;
}
else
{
lean_inc(v_val_1266_);
lean_dec(v___x_1265_);
v___x_1268_ = lean_box(0);
v_isShared_1269_ = v_isSharedCheck_1274_;
goto v_resetjp_1267_;
}
v_resetjp_1267_:
{
lean_object* v___x_1270_; lean_object* v___x_1272_; 
v___x_1270_ = lean_nat_add(v_pos_1252_, v_val_1266_);
lean_dec(v_val_1266_);
if (v_isShared_1269_ == 0)
{
lean_ctor_set(v___x_1268_, 0, v___x_1270_);
v___x_1272_ = v___x_1268_;
goto v_reusejp_1271_;
}
else
{
lean_object* v_reuseFailAlloc_1273_; 
v_reuseFailAlloc_1273_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1273_, 0, v___x_1270_);
v___x_1272_ = v_reuseFailAlloc_1273_;
goto v_reusejp_1271_;
}
v_reusejp_1271_:
{
return v___x_1272_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skip_x3f___boxed(lean_object* v_00_u03c1_1277_, lean_object* v_s_1278_, lean_object* v_pos_1279_, lean_object* v_pat_1280_, lean_object* v_inst_1281_){
_start:
{
lean_object* v_res_1282_; 
v_res_1282_ = l_String_Slice_Pos_skip_x3f(v_00_u03c1_1277_, v_s_1278_, v_pos_1279_, v_pat_1280_, v_inst_1281_);
lean_dec(v_pat_1280_);
lean_dec(v_pos_1279_);
return v_res_1282_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___redArg(lean_object* v_s_1283_, lean_object* v_inst_1284_){
_start:
{
lean_object* v_skipPrefix_x3f_1285_; lean_object* v___x_1286_; 
v_skipPrefix_x3f_1285_ = lean_ctor_get(v_inst_1284_, 0);
lean_inc_ref(v_skipPrefix_x3f_1285_);
lean_dec_ref(v_inst_1284_);
lean_inc_ref(v_s_1283_);
v___x_1286_ = lean_apply_1(v_skipPrefix_x3f_1285_, v_s_1283_);
if (lean_obj_tag(v___x_1286_) == 0)
{
lean_object* v___x_1287_; 
lean_dec_ref(v_s_1283_);
v___x_1287_ = lean_box(0);
return v___x_1287_;
}
else
{
lean_object* v_val_1288_; lean_object* v___x_1290_; uint8_t v_isShared_1291_; uint8_t v_isSharedCheck_1306_; 
v_val_1288_ = lean_ctor_get(v___x_1286_, 0);
v_isSharedCheck_1306_ = !lean_is_exclusive(v___x_1286_);
if (v_isSharedCheck_1306_ == 0)
{
v___x_1290_ = v___x_1286_;
v_isShared_1291_ = v_isSharedCheck_1306_;
goto v_resetjp_1289_;
}
else
{
lean_inc(v_val_1288_);
lean_dec(v___x_1286_);
v___x_1290_ = lean_box(0);
v_isShared_1291_ = v_isSharedCheck_1306_;
goto v_resetjp_1289_;
}
v_resetjp_1289_:
{
lean_object* v_str_1292_; lean_object* v_startInclusive_1293_; lean_object* v_endExclusive_1294_; lean_object* v___x_1296_; uint8_t v_isShared_1297_; uint8_t v_isSharedCheck_1305_; 
v_str_1292_ = lean_ctor_get(v_s_1283_, 0);
v_startInclusive_1293_ = lean_ctor_get(v_s_1283_, 1);
v_endExclusive_1294_ = lean_ctor_get(v_s_1283_, 2);
v_isSharedCheck_1305_ = !lean_is_exclusive(v_s_1283_);
if (v_isSharedCheck_1305_ == 0)
{
v___x_1296_ = v_s_1283_;
v_isShared_1297_ = v_isSharedCheck_1305_;
goto v_resetjp_1295_;
}
else
{
lean_inc(v_endExclusive_1294_);
lean_inc(v_startInclusive_1293_);
lean_inc(v_str_1292_);
lean_dec(v_s_1283_);
v___x_1296_ = lean_box(0);
v_isShared_1297_ = v_isSharedCheck_1305_;
goto v_resetjp_1295_;
}
v_resetjp_1295_:
{
lean_object* v___x_1298_; lean_object* v___x_1300_; 
v___x_1298_ = lean_nat_add(v_startInclusive_1293_, v_val_1288_);
lean_dec(v_val_1288_);
lean_dec(v_startInclusive_1293_);
if (v_isShared_1297_ == 0)
{
lean_ctor_set(v___x_1296_, 1, v___x_1298_);
v___x_1300_ = v___x_1296_;
goto v_reusejp_1299_;
}
else
{
lean_object* v_reuseFailAlloc_1304_; 
v_reuseFailAlloc_1304_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1304_, 0, v_str_1292_);
lean_ctor_set(v_reuseFailAlloc_1304_, 1, v___x_1298_);
lean_ctor_set(v_reuseFailAlloc_1304_, 2, v_endExclusive_1294_);
v___x_1300_ = v_reuseFailAlloc_1304_;
goto v_reusejp_1299_;
}
v_reusejp_1299_:
{
lean_object* v___x_1302_; 
if (v_isShared_1291_ == 0)
{
lean_ctor_set(v___x_1290_, 0, v___x_1300_);
v___x_1302_ = v___x_1290_;
goto v_reusejp_1301_;
}
else
{
lean_object* v_reuseFailAlloc_1303_; 
v_reuseFailAlloc_1303_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_1303_, 0, v___x_1300_);
v___x_1302_ = v_reuseFailAlloc_1303_;
goto v_reusejp_1301_;
}
v_reusejp_1301_:
{
return v___x_1302_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f(lean_object* v_00_u03c1_1307_, lean_object* v_s_1308_, lean_object* v_pat_1309_, lean_object* v_inst_1310_){
_start:
{
lean_object* v_skipPrefix_x3f_1311_; lean_object* v___x_1312_; 
v_skipPrefix_x3f_1311_ = lean_ctor_get(v_inst_1310_, 0);
lean_inc_ref(v_skipPrefix_x3f_1311_);
lean_dec_ref(v_inst_1310_);
lean_inc_ref(v_s_1308_);
v___x_1312_ = lean_apply_1(v_skipPrefix_x3f_1311_, v_s_1308_);
if (lean_obj_tag(v___x_1312_) == 0)
{
lean_object* v___x_1313_; 
lean_dec_ref(v_s_1308_);
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
v_str_1318_ = lean_ctor_get(v_s_1308_, 0);
v_startInclusive_1319_ = lean_ctor_get(v_s_1308_, 1);
v_endExclusive_1320_ = lean_ctor_get(v_s_1308_, 2);
v_isSharedCheck_1331_ = !lean_is_exclusive(v_s_1308_);
if (v_isSharedCheck_1331_ == 0)
{
v___x_1322_ = v_s_1308_;
v_isShared_1323_ = v_isSharedCheck_1331_;
goto v_resetjp_1321_;
}
else
{
lean_inc(v_endExclusive_1320_);
lean_inc(v_startInclusive_1319_);
lean_inc(v_str_1318_);
lean_dec(v_s_1308_);
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
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix_x3f___boxed(lean_object* v_00_u03c1_1333_, lean_object* v_s_1334_, lean_object* v_pat_1335_, lean_object* v_inst_1336_){
_start:
{
lean_object* v_res_1337_; 
v_res_1337_ = l_String_Slice_dropPrefix_x3f(v_00_u03c1_1333_, v_s_1334_, v_pat_1335_, v_inst_1336_);
lean_dec(v_pat_1335_);
return v_res_1337_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___redArg(lean_object* v_s_1338_, lean_object* v_inst_1339_){
_start:
{
lean_object* v_skipPrefix_x3f_1340_; lean_object* v___x_1341_; 
v_skipPrefix_x3f_1340_ = lean_ctor_get(v_inst_1339_, 0);
lean_inc_ref(v_skipPrefix_x3f_1340_);
lean_dec_ref(v_inst_1339_);
lean_inc_ref(v_s_1338_);
v___x_1341_ = lean_apply_1(v_skipPrefix_x3f_1340_, v_s_1338_);
if (lean_obj_tag(v___x_1341_) == 0)
{
return v_s_1338_;
}
else
{
lean_object* v_val_1342_; lean_object* v_str_1343_; lean_object* v_startInclusive_1344_; lean_object* v_endExclusive_1345_; lean_object* v___x_1347_; uint8_t v_isShared_1348_; uint8_t v_isSharedCheck_1353_; 
v_val_1342_ = lean_ctor_get(v___x_1341_, 0);
lean_inc(v_val_1342_);
lean_dec_ref_known(v___x_1341_, 1);
v_str_1343_ = lean_ctor_get(v_s_1338_, 0);
v_startInclusive_1344_ = lean_ctor_get(v_s_1338_, 1);
v_endExclusive_1345_ = lean_ctor_get(v_s_1338_, 2);
v_isSharedCheck_1353_ = !lean_is_exclusive(v_s_1338_);
if (v_isSharedCheck_1353_ == 0)
{
v___x_1347_ = v_s_1338_;
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
else
{
lean_inc(v_endExclusive_1345_);
lean_inc(v_startInclusive_1344_);
lean_inc(v_str_1343_);
lean_dec(v_s_1338_);
v___x_1347_ = lean_box(0);
v_isShared_1348_ = v_isSharedCheck_1353_;
goto v_resetjp_1346_;
}
v_resetjp_1346_:
{
lean_object* v___x_1349_; lean_object* v___x_1351_; 
v___x_1349_ = lean_nat_add(v_startInclusive_1344_, v_val_1342_);
lean_dec(v_val_1342_);
lean_dec(v_startInclusive_1344_);
if (v_isShared_1348_ == 0)
{
lean_ctor_set(v___x_1347_, 1, v___x_1349_);
v___x_1351_ = v___x_1347_;
goto v_reusejp_1350_;
}
else
{
lean_object* v_reuseFailAlloc_1352_; 
v_reuseFailAlloc_1352_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1352_, 0, v_str_1343_);
lean_ctor_set(v_reuseFailAlloc_1352_, 1, v___x_1349_);
lean_ctor_set(v_reuseFailAlloc_1352_, 2, v_endExclusive_1345_);
v___x_1351_ = v_reuseFailAlloc_1352_;
goto v_reusejp_1350_;
}
v_reusejp_1350_:
{
return v___x_1351_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix(lean_object* v_00_u03c1_1354_, lean_object* v_s_1355_, lean_object* v_pat_1356_, lean_object* v_inst_1357_){
_start:
{
lean_object* v___x_1358_; 
v___x_1358_ = l_String_Slice_dropPrefix___redArg(v_s_1355_, v_inst_1357_);
return v___x_1358_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropPrefix___boxed(lean_object* v_00_u03c1_1359_, lean_object* v_s_1360_, lean_object* v_pat_1361_, lean_object* v_inst_1362_){
_start:
{
lean_object* v_res_1363_; 
v_res_1363_ = l_String_Slice_dropPrefix(v_00_u03c1_1359_, v_s_1360_, v_pat_1361_, v_inst_1362_);
lean_dec(v_pat_1361_);
return v_res_1363_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__0(lean_object* v_x_1364_, lean_object* v_x_1365_, lean_object* v_f_1366_, lean_object* v_c_1367_){
_start:
{
lean_object* v___x_1368_; 
v___x_1368_ = lean_apply_1(v_f_1366_, v_c_1367_);
return v___x_1368_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1(lean_object* v_s_1369_, lean_object* v_inst_1370_, lean_object* v_replacement_1371_, lean_object* v_x1_1372_, lean_object* v_x2_1373_, lean_object* v_x3_1374_){
_start:
{
if (lean_obj_tag(v_x1_1372_) == 0)
{
lean_object* v_startPos_1375_; lean_object* v_endPos_1376_; lean_object* v___x_1377_; lean_object* v_str_1378_; lean_object* v_startInclusive_1379_; lean_object* v_endExclusive_1380_; lean_object* v___x_1381_; lean_object* v___x_1382_; lean_object* v___x_1383_; 
lean_dec(v_replacement_1371_);
lean_dec_ref(v_inst_1370_);
v_startPos_1375_ = lean_ctor_get(v_x1_1372_, 0);
v_endPos_1376_ = lean_ctor_get(v_x1_1372_, 1);
v___x_1377_ = l_String_Slice_slice_x21(v_s_1369_, v_startPos_1375_, v_endPos_1376_);
v_str_1378_ = lean_ctor_get(v___x_1377_, 0);
lean_inc_ref(v_str_1378_);
v_startInclusive_1379_ = lean_ctor_get(v___x_1377_, 1);
lean_inc(v_startInclusive_1379_);
v_endExclusive_1380_ = lean_ctor_get(v___x_1377_, 2);
lean_inc(v_endExclusive_1380_);
lean_dec_ref(v___x_1377_);
v___x_1381_ = lean_string_utf8_extract_fast(v_str_1378_, v_startInclusive_1379_, v_endExclusive_1380_);
lean_dec(v_endExclusive_1380_);
lean_dec(v_startInclusive_1379_);
lean_dec_ref(v_str_1378_);
v___x_1382_ = lean_string_append(v_x3_1374_, v___x_1381_);
lean_dec_ref(v___x_1381_);
v___x_1383_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1383_, 0, v___x_1382_);
return v___x_1383_;
}
else
{
lean_object* v___x_1384_; lean_object* v_str_1385_; lean_object* v_startInclusive_1386_; lean_object* v_endExclusive_1387_; lean_object* v___x_1388_; lean_object* v___x_1389_; lean_object* v___x_1390_; 
lean_dec_ref(v_s_1369_);
v___x_1384_ = lean_apply_1(v_inst_1370_, v_replacement_1371_);
v_str_1385_ = lean_ctor_get(v___x_1384_, 0);
lean_inc_ref(v_str_1385_);
v_startInclusive_1386_ = lean_ctor_get(v___x_1384_, 1);
lean_inc(v_startInclusive_1386_);
v_endExclusive_1387_ = lean_ctor_get(v___x_1384_, 2);
lean_inc(v_endExclusive_1387_);
lean_dec_ref(v___x_1384_);
v___x_1388_ = lean_string_utf8_extract_fast(v_str_1385_, v_startInclusive_1386_, v_endExclusive_1387_);
lean_dec(v_endExclusive_1387_);
lean_dec(v_startInclusive_1386_);
lean_dec_ref(v_str_1385_);
v___x_1389_ = lean_string_append(v_x3_1374_, v___x_1388_);
lean_dec_ref(v___x_1388_);
v___x_1390_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1390_, 0, v___x_1389_);
return v___x_1390_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg___lam__1___boxed(lean_object* v_s_1391_, lean_object* v_inst_1392_, lean_object* v_replacement_1393_, lean_object* v_x1_1394_, lean_object* v_x2_1395_, lean_object* v_x3_1396_){
_start:
{
lean_object* v_res_1397_; 
v_res_1397_ = l_String_Slice_replace___redArg___lam__1(v_s_1391_, v_inst_1392_, v_replacement_1393_, v_x1_1394_, v_x2_1395_, v_x3_1396_);
lean_dec_ref(v_x1_1394_);
return v_res_1397_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___redArg(lean_object* v_inst_1400_, lean_object* v_inst_1401_, lean_object* v_s_1402_, lean_object* v_inst_1403_, lean_object* v_replacement_1404_){
_start:
{
lean_object* v___f_1405_; lean_object* v___f_1406_; lean_object* v___x_1407_; lean_object* v___x_1408_; lean_object* v___x_1409_; 
v___f_1405_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1402_, 2);
v___f_1406_ = lean_alloc_closure((void*)(l_String_Slice_replace___redArg___lam__1___boxed), 6, 3);
lean_closure_set(v___f_1406_, 0, v_s_1402_);
lean_closure_set(v___f_1406_, 1, v_inst_1401_);
lean_closure_set(v___f_1406_, 2, v_replacement_1404_);
v___x_1407_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
v___x_1408_ = lean_apply_1(v_inst_1403_, v_s_1402_);
v___x_1409_ = lean_apply_7(v_inst_1400_, v_s_1402_, v___f_1405_, lean_box(0), lean_box(0), v___x_1408_, v___x_1407_, v___f_1406_);
return v___x_1409_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace(lean_object* v_00_u03c1_1410_, lean_object* v_00_u03c3_1411_, lean_object* v_inst_1412_, lean_object* v_inst_1413_, lean_object* v_00_u03b1_1414_, lean_object* v_inst_1415_, lean_object* v_s_1416_, lean_object* v_pattern_1417_, lean_object* v_inst_1418_, lean_object* v_replacement_1419_){
_start:
{
lean_object* v___x_1420_; 
v___x_1420_ = l_String_Slice_replace___redArg(v_inst_1413_, v_inst_1415_, v_s_1416_, v_inst_1418_, v_replacement_1419_);
return v___x_1420_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_replace___boxed(lean_object* v_00_u03c1_1421_, lean_object* v_00_u03c3_1422_, lean_object* v_inst_1423_, lean_object* v_inst_1424_, lean_object* v_00_u03b1_1425_, lean_object* v_inst_1426_, lean_object* v_s_1427_, lean_object* v_pattern_1428_, lean_object* v_inst_1429_, lean_object* v_replacement_1430_){
_start:
{
lean_object* v_res_1431_; 
v_res_1431_ = l_String_Slice_replace(v_00_u03c1_1421_, v_00_u03c3_1422_, v_inst_1423_, v_inst_1424_, v_00_u03b1_1425_, v_inst_1426_, v_s_1427_, v_pattern_1428_, v_inst_1429_, v_replacement_1430_);
lean_dec(v_pattern_1428_);
lean_dec(v_inst_1423_);
return v_res_1431_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_drop(lean_object* v_s_1432_, lean_object* v_n_1433_){
_start:
{
lean_object* v_str_1434_; lean_object* v_startInclusive_1435_; lean_object* v_endExclusive_1436_; lean_object* v___x_1437_; lean_object* v___x_1438_; lean_object* v___x_1440_; uint8_t v_isShared_1441_; uint8_t v_isSharedCheck_1446_; 
v_str_1434_ = lean_ctor_get(v_s_1432_, 0);
lean_inc_ref(v_str_1434_);
v_startInclusive_1435_ = lean_ctor_get(v_s_1432_, 1);
lean_inc(v_startInclusive_1435_);
v_endExclusive_1436_ = lean_ctor_get(v_s_1432_, 2);
lean_inc(v_endExclusive_1436_);
v___x_1437_ = lean_unsigned_to_nat(0u);
v___x_1438_ = l_String_Slice_Pos_nextn(v_s_1432_, v___x_1437_, v_n_1433_);
v_isSharedCheck_1446_ = !lean_is_exclusive(v_s_1432_);
if (v_isSharedCheck_1446_ == 0)
{
lean_object* v_unused_1447_; lean_object* v_unused_1448_; lean_object* v_unused_1449_; 
v_unused_1447_ = lean_ctor_get(v_s_1432_, 2);
lean_dec(v_unused_1447_);
v_unused_1448_ = lean_ctor_get(v_s_1432_, 1);
lean_dec(v_unused_1448_);
v_unused_1449_ = lean_ctor_get(v_s_1432_, 0);
lean_dec(v_unused_1449_);
v___x_1440_ = v_s_1432_;
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
else
{
lean_dec(v_s_1432_);
v___x_1440_ = lean_box(0);
v_isShared_1441_ = v_isSharedCheck_1446_;
goto v_resetjp_1439_;
}
v_resetjp_1439_:
{
lean_object* v___x_1442_; lean_object* v___x_1444_; 
v___x_1442_ = lean_nat_add(v_startInclusive_1435_, v___x_1438_);
lean_dec(v___x_1438_);
lean_dec(v_startInclusive_1435_);
if (v_isShared_1441_ == 0)
{
lean_ctor_set(v___x_1440_, 1, v___x_1442_);
v___x_1444_ = v___x_1440_;
goto v_reusejp_1443_;
}
else
{
lean_object* v_reuseFailAlloc_1445_; 
v_reuseFailAlloc_1445_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1445_, 0, v_str_1434_);
lean_ctor_set(v_reuseFailAlloc_1445_, 1, v___x_1442_);
lean_ctor_set(v_reuseFailAlloc_1445_, 2, v_endExclusive_1436_);
v___x_1444_ = v_reuseFailAlloc_1445_;
goto v_reusejp_1443_;
}
v_reusejp_1443_:
{
return v___x_1444_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg(lean_object* v_s_1450_, lean_object* v_pos_1451_, lean_object* v_inst_1452_){
_start:
{
lean_object* v_str_1453_; lean_object* v_startInclusive_1454_; lean_object* v_endExclusive_1455_; lean_object* v_skipPrefix_x3f_1456_; lean_object* v___x_1457_; lean_object* v___x_1458_; lean_object* v___x_1459_; 
v_str_1453_ = lean_ctor_get(v_s_1450_, 0);
v_startInclusive_1454_ = lean_ctor_get(v_s_1450_, 1);
v_endExclusive_1455_ = lean_ctor_get(v_s_1450_, 2);
v_skipPrefix_x3f_1456_ = lean_ctor_get(v_inst_1452_, 0);
v___x_1457_ = lean_nat_add(v_startInclusive_1454_, v_pos_1451_);
lean_inc(v_endExclusive_1455_);
lean_inc_ref(v_str_1453_);
v___x_1458_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_1458_, 0, v_str_1453_);
lean_ctor_set(v___x_1458_, 1, v___x_1457_);
lean_ctor_set(v___x_1458_, 2, v_endExclusive_1455_);
lean_inc_ref(v_skipPrefix_x3f_1456_);
v___x_1459_ = lean_apply_1(v_skipPrefix_x3f_1456_, v___x_1458_);
if (lean_obj_tag(v___x_1459_) == 0)
{
lean_dec_ref(v_inst_1452_);
return v_pos_1451_;
}
else
{
lean_object* v_val_1460_; lean_object* v___x_1461_; lean_object* v___x_1462_; lean_object* v___x_1463_; uint8_t v___x_1464_; 
v_val_1460_ = lean_ctor_get(v___x_1459_, 0);
lean_inc(v_val_1460_);
lean_dec_ref_known(v___x_1459_, 1);
v___x_1461_ = lean_nat_add(v_pos_1451_, v_val_1460_);
lean_dec(v_val_1460_);
v___x_1462_ = lean_unsigned_to_nat(1u);
v___x_1463_ = lean_nat_add(v_pos_1451_, v___x_1462_);
v___x_1464_ = lean_nat_dec_le(v___x_1463_, v___x_1461_);
lean_dec(v___x_1463_);
if (v___x_1464_ == 0)
{
lean_dec(v___x_1461_);
lean_dec_ref(v_inst_1452_);
return v_pos_1451_;
}
else
{
lean_dec(v_pos_1451_);
v_pos_1451_ = v___x_1461_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___redArg___boxed(lean_object* v_s_1466_, lean_object* v_pos_1467_, lean_object* v_inst_1468_){
_start:
{
lean_object* v_res_1469_; 
v_res_1469_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1466_, v_pos_1467_, v_inst_1468_);
lean_dec_ref(v_s_1466_);
return v_res_1469_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile(lean_object* v_00_u03c1_1470_, lean_object* v_s_1471_, lean_object* v_pos_1472_, lean_object* v_pat_1473_, lean_object* v_inst_1474_){
_start:
{
lean_object* v___x_1475_; 
v___x_1475_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1471_, v_pos_1472_, v_inst_1474_);
return v___x_1475_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___boxed(lean_object* v_00_u03c1_1476_, lean_object* v_s_1477_, lean_object* v_pos_1478_, lean_object* v_pat_1479_, lean_object* v_inst_1480_){
_start:
{
lean_object* v_res_1481_; 
v_res_1481_ = l_String_Slice_Pos_skipWhile(v_00_u03c1_1476_, v_s_1477_, v_pos_1478_, v_pat_1479_, v_inst_1480_);
lean_dec(v_pat_1479_);
lean_dec_ref(v_s_1477_);
return v_res_1481_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___redArg(lean_object* v_x_1482_, lean_object* v_h__1_1483_, lean_object* v_h__2_1484_){
_start:
{
if (lean_obj_tag(v_x_1482_) == 0)
{
lean_object* v___x_1485_; lean_object* v___x_1486_; 
lean_dec(v_h__1_1483_);
v___x_1485_ = lean_box(0);
v___x_1486_ = lean_apply_1(v_h__2_1484_, v___x_1485_);
return v___x_1486_;
}
else
{
lean_object* v_val_1487_; lean_object* v___x_1488_; 
lean_dec(v_h__2_1484_);
v_val_1487_ = lean_ctor_get(v_x_1482_, 0);
lean_inc(v_val_1487_);
lean_dec_ref_known(v_x_1482_, 1);
v___x_1488_ = lean_apply_1(v_h__1_1483_, v_val_1487_);
return v___x_1488_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(lean_object* v_s_1489_, lean_object* v_motive_1490_, lean_object* v_x_1491_, lean_object* v_h__1_1492_, lean_object* v_h__2_1493_){
_start:
{
if (lean_obj_tag(v_x_1491_) == 0)
{
lean_object* v___x_1494_; lean_object* v___x_1495_; 
lean_dec(v_h__1_1492_);
v___x_1494_ = lean_box(0);
v___x_1495_ = lean_apply_1(v_h__2_1493_, v___x_1494_);
return v___x_1495_;
}
else
{
lean_object* v_val_1496_; lean_object* v___x_1497_; 
lean_dec(v_h__2_1493_);
v_val_1496_ = lean_ctor_get(v_x_1491_, 0);
lean_inc(v_val_1496_);
lean_dec_ref_known(v_x_1491_, 1);
v___x_1497_ = lean_apply_1(v_h__1_1492_, v_val_1496_);
return v___x_1497_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter___boxed(lean_object* v_s_1498_, lean_object* v_motive_1499_, lean_object* v_x_1500_, lean_object* v_h__1_1501_, lean_object* v_h__2_1502_){
_start:
{
lean_object* v_res_1503_; 
v_res_1503_ = l___private_Init_Data_String_Slice_0__String_Slice_Pos_skipWhile_match__1_splitter(v_s_1498_, v_motive_1499_, v_x_1500_, v_h__1_1501_, v_h__2_1502_);
lean_dec_ref(v_s_1498_);
return v_res_1503_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg(lean_object* v_s_1504_, lean_object* v_inst_1505_){
_start:
{
lean_object* v___x_1506_; lean_object* v___x_1507_; 
v___x_1506_ = lean_unsigned_to_nat(0u);
v___x_1507_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1504_, v___x_1506_, v_inst_1505_);
return v___x_1507_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___redArg___boxed(lean_object* v_s_1508_, lean_object* v_inst_1509_){
_start:
{
lean_object* v_res_1510_; 
v_res_1510_ = l_String_Slice_skipPrefixWhile___redArg(v_s_1508_, v_inst_1509_);
lean_dec_ref(v_s_1508_);
return v_res_1510_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile(lean_object* v_00_u03c1_1511_, lean_object* v_s_1512_, lean_object* v_pat_1513_, lean_object* v_inst_1514_){
_start:
{
lean_object* v___x_1515_; lean_object* v___x_1516_; 
v___x_1515_ = lean_unsigned_to_nat(0u);
v___x_1516_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1512_, v___x_1515_, v_inst_1514_);
return v___x_1516_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipPrefixWhile___boxed(lean_object* v_00_u03c1_1517_, lean_object* v_s_1518_, lean_object* v_pat_1519_, lean_object* v_inst_1520_){
_start:
{
lean_object* v_res_1521_; 
v_res_1521_ = l_String_Slice_skipPrefixWhile(v_00_u03c1_1517_, v_s_1518_, v_pat_1519_, v_inst_1520_);
lean_dec(v_pat_1519_);
lean_dec_ref(v_s_1518_);
return v_res_1521_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___redArg(lean_object* v_s_1522_, lean_object* v_inst_1523_){
_start:
{
lean_object* v_str_1524_; lean_object* v_startInclusive_1525_; lean_object* v_endExclusive_1526_; lean_object* v___x_1527_; lean_object* v___x_1528_; lean_object* v___x_1530_; uint8_t v_isShared_1531_; uint8_t v_isSharedCheck_1536_; 
v_str_1524_ = lean_ctor_get(v_s_1522_, 0);
lean_inc_ref(v_str_1524_);
v_startInclusive_1525_ = lean_ctor_get(v_s_1522_, 1);
lean_inc(v_startInclusive_1525_);
v_endExclusive_1526_ = lean_ctor_get(v_s_1522_, 2);
lean_inc(v_endExclusive_1526_);
v___x_1527_ = lean_unsigned_to_nat(0u);
v___x_1528_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1522_, v___x_1527_, v_inst_1523_);
v_isSharedCheck_1536_ = !lean_is_exclusive(v_s_1522_);
if (v_isSharedCheck_1536_ == 0)
{
lean_object* v_unused_1537_; lean_object* v_unused_1538_; lean_object* v_unused_1539_; 
v_unused_1537_ = lean_ctor_get(v_s_1522_, 2);
lean_dec(v_unused_1537_);
v_unused_1538_ = lean_ctor_get(v_s_1522_, 1);
lean_dec(v_unused_1538_);
v_unused_1539_ = lean_ctor_get(v_s_1522_, 0);
lean_dec(v_unused_1539_);
v___x_1530_ = v_s_1522_;
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
else
{
lean_dec(v_s_1522_);
v___x_1530_ = lean_box(0);
v_isShared_1531_ = v_isSharedCheck_1536_;
goto v_resetjp_1529_;
}
v_resetjp_1529_:
{
lean_object* v___x_1532_; lean_object* v___x_1534_; 
v___x_1532_ = lean_nat_add(v_startInclusive_1525_, v___x_1528_);
lean_dec(v___x_1528_);
lean_dec(v_startInclusive_1525_);
if (v_isShared_1531_ == 0)
{
lean_ctor_set(v___x_1530_, 1, v___x_1532_);
v___x_1534_ = v___x_1530_;
goto v_reusejp_1533_;
}
else
{
lean_object* v_reuseFailAlloc_1535_; 
v_reuseFailAlloc_1535_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1535_, 0, v_str_1524_);
lean_ctor_set(v_reuseFailAlloc_1535_, 1, v___x_1532_);
lean_ctor_set(v_reuseFailAlloc_1535_, 2, v_endExclusive_1526_);
v___x_1534_ = v_reuseFailAlloc_1535_;
goto v_reusejp_1533_;
}
v_reusejp_1533_:
{
return v___x_1534_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropWhile(lean_object* v_00_u03c1_1540_, lean_object* v_s_1541_, lean_object* v_pat_1542_, lean_object* v_inst_1543_){
_start:
{
lean_object* v_str_1544_; lean_object* v_startInclusive_1545_; lean_object* v_endExclusive_1546_; lean_object* v___x_1547_; lean_object* v___x_1548_; lean_object* v___x_1550_; uint8_t v_isShared_1551_; uint8_t v_isSharedCheck_1556_; 
v_str_1544_ = lean_ctor_get(v_s_1541_, 0);
lean_inc_ref(v_str_1544_);
v_startInclusive_1545_ = lean_ctor_get(v_s_1541_, 1);
lean_inc(v_startInclusive_1545_);
v_endExclusive_1546_ = lean_ctor_get(v_s_1541_, 2);
lean_inc(v_endExclusive_1546_);
v___x_1547_ = lean_unsigned_to_nat(0u);
v___x_1548_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1541_, v___x_1547_, v_inst_1543_);
v_isSharedCheck_1556_ = !lean_is_exclusive(v_s_1541_);
if (v_isSharedCheck_1556_ == 0)
{
lean_object* v_unused_1557_; lean_object* v_unused_1558_; lean_object* v_unused_1559_; 
v_unused_1557_ = lean_ctor_get(v_s_1541_, 2);
lean_dec(v_unused_1557_);
v_unused_1558_ = lean_ctor_get(v_s_1541_, 1);
lean_dec(v_unused_1558_);
v_unused_1559_ = lean_ctor_get(v_s_1541_, 0);
lean_dec(v_unused_1559_);
v___x_1550_ = v_s_1541_;
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
else
{
lean_dec(v_s_1541_);
v___x_1550_ = lean_box(0);
v_isShared_1551_ = v_isSharedCheck_1556_;
goto v_resetjp_1549_;
}
v_resetjp_1549_:
{
lean_object* v___x_1552_; lean_object* v___x_1554_; 
v___x_1552_ = lean_nat_add(v_startInclusive_1545_, v___x_1548_);
lean_dec(v___x_1548_);
lean_dec(v_startInclusive_1545_);
if (v_isShared_1551_ == 0)
{
lean_ctor_set(v___x_1550_, 1, v___x_1552_);
v___x_1554_ = v___x_1550_;
goto v_reusejp_1553_;
}
else
{
lean_object* v_reuseFailAlloc_1555_; 
v_reuseFailAlloc_1555_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1555_, 0, v_str_1544_);
lean_ctor_set(v_reuseFailAlloc_1555_, 1, v___x_1552_);
lean_ctor_set(v_reuseFailAlloc_1555_, 2, v_endExclusive_1546_);
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
LEAN_EXPORT lean_object* l_String_Slice_dropWhile___boxed(lean_object* v_00_u03c1_1560_, lean_object* v_s_1561_, lean_object* v_pat_1562_, lean_object* v_inst_1563_){
_start:
{
lean_object* v_res_1564_; 
v_res_1564_ = l_String_Slice_dropWhile(v_00_u03c1_1560_, v_s_1561_, v_pat_1562_, v_inst_1563_);
lean_dec(v_pat_1562_);
return v_res_1564_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiStart___closed__1(void){
_start:
{
lean_object* v___x_1566_; lean_object* v___x_1567_; 
v___x_1566_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_1567_ = l_String_Slice_Pattern_CharPred_instForwardPatternForallCharBool(v___x_1566_);
return v___x_1567_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiStart(lean_object* v_s_1568_){
_start:
{
lean_object* v___x_1569_; lean_object* v_str_1570_; lean_object* v_startInclusive_1571_; lean_object* v_endExclusive_1572_; lean_object* v___x_1573_; lean_object* v___x_1574_; lean_object* v___x_1576_; uint8_t v_isShared_1577_; uint8_t v_isSharedCheck_1582_; 
v___x_1569_ = lean_obj_once(&l_String_Slice_trimAsciiStart___closed__1, &l_String_Slice_trimAsciiStart___closed__1_once, _init_l_String_Slice_trimAsciiStart___closed__1);
v_str_1570_ = lean_ctor_get(v_s_1568_, 0);
lean_inc_ref(v_str_1570_);
v_startInclusive_1571_ = lean_ctor_get(v_s_1568_, 1);
lean_inc(v_startInclusive_1571_);
v_endExclusive_1572_ = lean_ctor_get(v_s_1568_, 2);
lean_inc(v_endExclusive_1572_);
v___x_1573_ = lean_unsigned_to_nat(0u);
v___x_1574_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1568_, v___x_1573_, v___x_1569_);
v_isSharedCheck_1582_ = !lean_is_exclusive(v_s_1568_);
if (v_isSharedCheck_1582_ == 0)
{
lean_object* v_unused_1583_; lean_object* v_unused_1584_; lean_object* v_unused_1585_; 
v_unused_1583_ = lean_ctor_get(v_s_1568_, 2);
lean_dec(v_unused_1583_);
v_unused_1584_ = lean_ctor_get(v_s_1568_, 1);
lean_dec(v_unused_1584_);
v_unused_1585_ = lean_ctor_get(v_s_1568_, 0);
lean_dec(v_unused_1585_);
v___x_1576_ = v_s_1568_;
v_isShared_1577_ = v_isSharedCheck_1582_;
goto v_resetjp_1575_;
}
else
{
lean_dec(v_s_1568_);
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
LEAN_EXPORT lean_object* l_String_Slice_take(lean_object* v_s_1586_, lean_object* v_n_1587_){
_start:
{
lean_object* v_str_1588_; lean_object* v_startInclusive_1589_; lean_object* v___x_1590_; lean_object* v___x_1591_; lean_object* v___x_1593_; uint8_t v_isShared_1594_; uint8_t v_isSharedCheck_1599_; 
v_str_1588_ = lean_ctor_get(v_s_1586_, 0);
lean_inc_ref(v_str_1588_);
v_startInclusive_1589_ = lean_ctor_get(v_s_1586_, 1);
lean_inc(v_startInclusive_1589_);
v___x_1590_ = lean_unsigned_to_nat(0u);
v___x_1591_ = l_String_Slice_Pos_nextn(v_s_1586_, v___x_1590_, v_n_1587_);
v_isSharedCheck_1599_ = !lean_is_exclusive(v_s_1586_);
if (v_isSharedCheck_1599_ == 0)
{
lean_object* v_unused_1600_; lean_object* v_unused_1601_; lean_object* v_unused_1602_; 
v_unused_1600_ = lean_ctor_get(v_s_1586_, 2);
lean_dec(v_unused_1600_);
v_unused_1601_ = lean_ctor_get(v_s_1586_, 1);
lean_dec(v_unused_1601_);
v_unused_1602_ = lean_ctor_get(v_s_1586_, 0);
lean_dec(v_unused_1602_);
v___x_1593_ = v_s_1586_;
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
else
{
lean_dec(v_s_1586_);
v___x_1593_ = lean_box(0);
v_isShared_1594_ = v_isSharedCheck_1599_;
goto v_resetjp_1592_;
}
v_resetjp_1592_:
{
lean_object* v___x_1595_; lean_object* v___x_1597_; 
v___x_1595_ = lean_nat_add(v_startInclusive_1589_, v___x_1591_);
lean_dec(v___x_1591_);
if (v_isShared_1594_ == 0)
{
lean_ctor_set(v___x_1593_, 2, v___x_1595_);
v___x_1597_ = v___x_1593_;
goto v_reusejp_1596_;
}
else
{
lean_object* v_reuseFailAlloc_1598_; 
v_reuseFailAlloc_1598_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1598_, 0, v_str_1588_);
lean_ctor_set(v_reuseFailAlloc_1598_, 1, v_startInclusive_1589_);
lean_ctor_set(v_reuseFailAlloc_1598_, 2, v___x_1595_);
v___x_1597_ = v_reuseFailAlloc_1598_;
goto v_reusejp_1596_;
}
v_reusejp_1596_:
{
return v___x_1597_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___redArg(lean_object* v_s_1603_, lean_object* v_inst_1604_){
_start:
{
lean_object* v_str_1605_; lean_object* v_startInclusive_1606_; lean_object* v___x_1607_; lean_object* v___x_1608_; lean_object* v___x_1610_; uint8_t v_isShared_1611_; uint8_t v_isSharedCheck_1616_; 
v_str_1605_ = lean_ctor_get(v_s_1603_, 0);
lean_inc_ref(v_str_1605_);
v_startInclusive_1606_ = lean_ctor_get(v_s_1603_, 1);
lean_inc(v_startInclusive_1606_);
v___x_1607_ = lean_unsigned_to_nat(0u);
v___x_1608_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1603_, v___x_1607_, v_inst_1604_);
v_isSharedCheck_1616_ = !lean_is_exclusive(v_s_1603_);
if (v_isSharedCheck_1616_ == 0)
{
lean_object* v_unused_1617_; lean_object* v_unused_1618_; lean_object* v_unused_1619_; 
v_unused_1617_ = lean_ctor_get(v_s_1603_, 2);
lean_dec(v_unused_1617_);
v_unused_1618_ = lean_ctor_get(v_s_1603_, 1);
lean_dec(v_unused_1618_);
v_unused_1619_ = lean_ctor_get(v_s_1603_, 0);
lean_dec(v_unused_1619_);
v___x_1610_ = v_s_1603_;
v_isShared_1611_ = v_isSharedCheck_1616_;
goto v_resetjp_1609_;
}
else
{
lean_dec(v_s_1603_);
v___x_1610_ = lean_box(0);
v_isShared_1611_ = v_isSharedCheck_1616_;
goto v_resetjp_1609_;
}
v_resetjp_1609_:
{
lean_object* v___x_1612_; lean_object* v___x_1614_; 
v___x_1612_ = lean_nat_add(v_startInclusive_1606_, v___x_1608_);
lean_dec(v___x_1608_);
if (v_isShared_1611_ == 0)
{
lean_ctor_set(v___x_1610_, 2, v___x_1612_);
v___x_1614_ = v___x_1610_;
goto v_reusejp_1613_;
}
else
{
lean_object* v_reuseFailAlloc_1615_; 
v_reuseFailAlloc_1615_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1615_, 0, v_str_1605_);
lean_ctor_set(v_reuseFailAlloc_1615_, 1, v_startInclusive_1606_);
lean_ctor_set(v_reuseFailAlloc_1615_, 2, v___x_1612_);
v___x_1614_ = v_reuseFailAlloc_1615_;
goto v_reusejp_1613_;
}
v_reusejp_1613_:
{
return v___x_1614_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeWhile(lean_object* v_00_u03c1_1620_, lean_object* v_s_1621_, lean_object* v_pat_1622_, lean_object* v_inst_1623_){
_start:
{
lean_object* v_str_1624_; lean_object* v_startInclusive_1625_; lean_object* v___x_1626_; lean_object* v___x_1627_; lean_object* v___x_1629_; uint8_t v_isShared_1630_; uint8_t v_isSharedCheck_1635_; 
v_str_1624_ = lean_ctor_get(v_s_1621_, 0);
lean_inc_ref(v_str_1624_);
v_startInclusive_1625_ = lean_ctor_get(v_s_1621_, 1);
lean_inc(v_startInclusive_1625_);
v___x_1626_ = lean_unsigned_to_nat(0u);
v___x_1627_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1621_, v___x_1626_, v_inst_1623_);
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
v___x_1631_ = lean_nat_add(v_startInclusive_1625_, v___x_1627_);
lean_dec(v___x_1627_);
if (v_isShared_1630_ == 0)
{
lean_ctor_set(v___x_1629_, 2, v___x_1631_);
v___x_1633_ = v___x_1629_;
goto v_reusejp_1632_;
}
else
{
lean_object* v_reuseFailAlloc_1634_; 
v_reuseFailAlloc_1634_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_1634_, 0, v_str_1624_);
lean_ctor_set(v_reuseFailAlloc_1634_, 1, v_startInclusive_1625_);
lean_ctor_set(v_reuseFailAlloc_1634_, 2, v___x_1631_);
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
LEAN_EXPORT lean_object* l_String_Slice_takeWhile___boxed(lean_object* v_00_u03c1_1639_, lean_object* v_s_1640_, lean_object* v_pat_1641_, lean_object* v_inst_1642_){
_start:
{
lean_object* v_res_1643_; 
v_res_1643_ = l_String_Slice_takeWhile(v_00_u03c1_1639_, v_s_1640_, v_pat_1641_, v_inst_1642_);
lean_dec(v_pat_1641_);
return v_res_1643_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1(lean_object* v___x_1644_, lean_object* v_x1_1645_, lean_object* v_x2_1646_, lean_object* v_x3_1647_){
_start:
{
if (lean_obj_tag(v_x1_1645_) == 0)
{
lean_object* v___x_1648_; 
v___x_1648_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1648_, 0, v___x_1644_);
return v___x_1648_;
}
else
{
lean_object* v_startPos_1649_; lean_object* v___x_1650_; lean_object* v___x_1651_; 
lean_dec(v___x_1644_);
v_startPos_1649_ = lean_ctor_get(v_x1_1645_, 0);
lean_inc(v_startPos_1649_);
v___x_1650_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1650_, 0, v_startPos_1649_);
v___x_1651_ = lean_alloc_ctor(0, 1, 0);
lean_ctor_set(v___x_1651_, 0, v___x_1650_);
return v___x_1651_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg___lam__1___boxed(lean_object* v___x_1652_, lean_object* v_x1_1653_, lean_object* v_x2_1654_, lean_object* v_x3_1655_){
_start:
{
lean_object* v_res_1656_; 
v_res_1656_ = l_String_Slice_find_x3f___redArg___lam__1(v___x_1652_, v_x1_1653_, v_x2_1654_, v_x3_1655_);
lean_dec(v_x3_1655_);
lean_dec_ref(v_x1_1653_);
return v_res_1656_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___redArg(lean_object* v_inst_1659_, lean_object* v_s_1660_, lean_object* v_inst_1661_){
_start:
{
lean_object* v___f_1662_; lean_object* v_searcher_1663_; lean_object* v___x_1664_; lean_object* v___f_1665_; lean_object* v___x_1666_; 
v___f_1662_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1660_);
v_searcher_1663_ = lean_apply_1(v_inst_1661_, v_s_1660_);
v___x_1664_ = lean_box(0);
v___f_1665_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1666_ = lean_apply_7(v_inst_1659_, v_s_1660_, v___f_1662_, lean_box(0), lean_box(0), v_searcher_1663_, v___x_1664_, v___f_1665_);
return v___x_1666_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f(lean_object* v_00_u03c1_1667_, lean_object* v_00_u03c3_1668_, lean_object* v_inst_1669_, lean_object* v_inst_1670_, lean_object* v_s_1671_, lean_object* v_pat_1672_, lean_object* v_inst_1673_){
_start:
{
lean_object* v___f_1674_; lean_object* v_searcher_1675_; lean_object* v___x_1676_; lean_object* v___f_1677_; lean_object* v___x_1678_; 
v___f_1674_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1671_);
v_searcher_1675_ = lean_apply_1(v_inst_1673_, v_s_1671_);
v___x_1676_ = lean_box(0);
v___f_1677_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1678_ = lean_apply_7(v_inst_1670_, v_s_1671_, v___f_1674_, lean_box(0), lean_box(0), v_searcher_1675_, v___x_1676_, v___f_1677_);
return v___x_1678_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find_x3f___boxed(lean_object* v_00_u03c1_1679_, lean_object* v_00_u03c3_1680_, lean_object* v_inst_1681_, lean_object* v_inst_1682_, lean_object* v_s_1683_, lean_object* v_pat_1684_, lean_object* v_inst_1685_){
_start:
{
lean_object* v_res_1686_; 
v_res_1686_ = l_String_Slice_find_x3f(v_00_u03c1_1679_, v_00_u03c3_1680_, v_inst_1681_, v_inst_1682_, v_s_1683_, v_pat_1684_, v_inst_1685_);
lean_dec(v_pat_1684_);
lean_dec(v_inst_1681_);
return v_res_1686_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___redArg(lean_object* v_inst_1687_, lean_object* v_s_1688_, lean_object* v_inst_1689_){
_start:
{
lean_object* v___f_1690_; lean_object* v_searcher_1691_; lean_object* v___x_1692_; lean_object* v___f_1693_; lean_object* v___x_1694_; 
v___f_1690_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1688_, 2);
v_searcher_1691_ = lean_apply_1(v_inst_1689_, v_s_1688_);
v___x_1692_ = lean_box(0);
v___f_1693_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1694_ = lean_apply_7(v_inst_1687_, v_s_1688_, v___f_1690_, lean_box(0), lean_box(0), v_searcher_1691_, v___x_1692_, v___f_1693_);
if (lean_obj_tag(v___x_1694_) == 0)
{
lean_object* v_startInclusive_1695_; lean_object* v_endExclusive_1696_; lean_object* v___x_1697_; 
v_startInclusive_1695_ = lean_ctor_get(v_s_1688_, 1);
lean_inc(v_startInclusive_1695_);
v_endExclusive_1696_ = lean_ctor_get(v_s_1688_, 2);
lean_inc(v_endExclusive_1696_);
lean_dec_ref(v_s_1688_);
v___x_1697_ = lean_nat_sub(v_endExclusive_1696_, v_startInclusive_1695_);
lean_dec(v_startInclusive_1695_);
lean_dec(v_endExclusive_1696_);
return v___x_1697_;
}
else
{
lean_object* v_val_1698_; 
lean_dec_ref(v_s_1688_);
v_val_1698_ = lean_ctor_get(v___x_1694_, 0);
lean_inc(v_val_1698_);
lean_dec_ref_known(v___x_1694_, 1);
return v_val_1698_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find(lean_object* v_00_u03c1_1699_, lean_object* v_00_u03c3_1700_, lean_object* v_inst_1701_, lean_object* v_inst_1702_, lean_object* v_s_1703_, lean_object* v_pat_1704_, lean_object* v_inst_1705_){
_start:
{
lean_object* v___f_1706_; lean_object* v_searcher_1707_; lean_object* v___x_1708_; lean_object* v___f_1709_; lean_object* v___x_1710_; 
v___f_1706_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref_n(v_s_1703_, 2);
v_searcher_1707_ = lean_apply_1(v_inst_1705_, v_s_1703_);
v___x_1708_ = lean_box(0);
v___f_1709_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_1710_ = lean_apply_7(v_inst_1702_, v_s_1703_, v___f_1706_, lean_box(0), lean_box(0), v_searcher_1707_, v___x_1708_, v___f_1709_);
if (lean_obj_tag(v___x_1710_) == 0)
{
lean_object* v_startInclusive_1711_; lean_object* v_endExclusive_1712_; lean_object* v___x_1713_; 
v_startInclusive_1711_ = lean_ctor_get(v_s_1703_, 1);
lean_inc(v_startInclusive_1711_);
v_endExclusive_1712_ = lean_ctor_get(v_s_1703_, 2);
lean_inc(v_endExclusive_1712_);
lean_dec_ref(v_s_1703_);
v___x_1713_ = lean_nat_sub(v_endExclusive_1712_, v_startInclusive_1711_);
lean_dec(v_startInclusive_1711_);
lean_dec(v_endExclusive_1712_);
return v___x_1713_;
}
else
{
lean_object* v_val_1714_; 
lean_dec_ref(v_s_1703_);
v_val_1714_ = lean_ctor_get(v___x_1710_, 0);
lean_inc(v_val_1714_);
lean_dec_ref_known(v___x_1710_, 1);
return v_val_1714_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_find___boxed(lean_object* v_00_u03c1_1715_, lean_object* v_00_u03c3_1716_, lean_object* v_inst_1717_, lean_object* v_inst_1718_, lean_object* v_s_1719_, lean_object* v_pat_1720_, lean_object* v_inst_1721_){
_start:
{
lean_object* v_res_1722_; 
v_res_1722_ = l_String_Slice_find(v_00_u03c1_1715_, v_00_u03c3_1716_, v_inst_1717_, v_inst_1718_, v_s_1719_, v_pat_1720_, v_inst_1721_);
lean_dec(v_pat_1720_);
lean_dec(v_inst_1717_);
return v_res_1722_;
}
}
lean_object* l_String_Slice_contains___redArg___lam__1(uint8_t v___x_1726_, lean_object* v_x1_1727_, lean_object* v_x2_1728_, uint8_t v_x3_1729_){
_start:
{
if (lean_obj_tag(v_x1_1727_) == 1)
{
lean_object* v___x_1730_; 
v___x_1730_ = ((lean_object*)(l_String_Slice_contains___redArg___lam__1___closed__0));
return v___x_1730_;
}
else
{
lean_object* v___x_1731_; lean_object* v___x_1732_; 
v___x_1731_ = lean_box(v___x_1726_);
v___x_1732_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1732_, 0, v___x_1731_);
return v___x_1732_;
}
}
}
LEAN_EXPORT void l_String_Slice_contains___redArg___lam__1_0interp(lean_interpreter_value* stack)
{
uint8_t v___x_1726_ = stack[0].m_num;
lean_object* v_x1_1727_ = stack[1].m_obj;
uint8_t v_x3_1729_ = stack[3].m_num;
lean_object* v_res_1733_;
v_res_1733_ = l_String_Slice_contains___redArg___lam__1(v___x_1726_, v_x1_1727_, lean_box(0), v_x3_1729_);
stack->m_obj
 = v_res_1733_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___lam__1___boxed(lean_object* v___x_1734_, lean_object* v_x1_1735_, lean_object* v_x2_1736_, lean_object* v_x3_1737_){
_start:
{
uint8_t v___x_82__boxed_1738_; uint8_t v_x3_85__boxed_1739_; lean_object* v_res_1740_; 
v___x_82__boxed_1738_ = lean_unbox(v___x_1734_);
v_x3_85__boxed_1739_ = lean_unbox(v_x3_1737_);
v_res_1740_ = l_String_Slice_contains___redArg___lam__1(v___x_82__boxed_1738_, v_x1_1735_, v_x2_1736_, v_x3_85__boxed_1739_);
lean_dec_ref(v_x1_1735_);
return v_res_1740_;
}
}
uint8_t l_String_Slice_contains___redArg(lean_object* v_inst_1744_, lean_object* v_s_1745_, lean_object* v_inst_1746_){
_start:
{
lean_object* v___f_1747_; lean_object* v_searcher_1748_; uint8_t v___x_1749_; lean_object* v___f_1750_; lean_object* v___x_1751_; lean_object* v___x_1752_; uint8_t v___x_1753_; 
v___f_1747_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_1745_);
v_searcher_1748_ = lean_apply_1(v_inst_1746_, v_s_1745_);
v___x_1749_ = 0;
v___f_1750_ = ((lean_object*)(l_String_Slice_contains___redArg___closed__0));
v___x_1751_ = lean_box(v___x_1749_);
v___x_1752_ = lean_apply_7(v_inst_1744_, v_s_1745_, v___f_1747_, lean_box(0), lean_box(0), v_searcher_1748_, v___x_1751_, v___f_1750_);
v___x_1753_ = lean_unbox(v___x_1752_);
return v___x_1753_;
}
}
LEAN_EXPORT void l_String_Slice_contains___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1744_ = stack[0].m_obj;
lean_object* v_s_1745_ = stack[1].m_obj;
lean_object* v_inst_1746_ = stack[2].m_obj;
uint8_t v_res_1754_;
v_res_1754_ = l_String_Slice_contains___redArg(v_inst_1744_, v_s_1745_, v_inst_1746_);
stack->m_num = v_res_1754_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___redArg___boxed(lean_object* v_inst_1755_, lean_object* v_s_1756_, lean_object* v_inst_1757_){
_start:
{
uint8_t v_res_1758_; lean_object* v_r_1759_; 
v_res_1758_ = l_String_Slice_contains___redArg(v_inst_1755_, v_s_1756_, v_inst_1757_);
v_r_1759_ = lean_box(v_res_1758_);
return v_r_1759_;
}
}
uint8_t l_String_Slice_contains(lean_object* v_00_u03c1_1760_, lean_object* v_00_u03c3_1761_, lean_object* v_inst_1762_, lean_object* v_inst_1763_, lean_object* v_s_1764_, lean_object* v_pat_1765_, lean_object* v_inst_1766_){
_start:
{
uint8_t v___x_1767_; 
v___x_1767_ = l_String_Slice_contains___redArg(v_inst_1763_, v_s_1764_, v_inst_1766_);
return v___x_1767_;
}
}
LEAN_EXPORT void l_String_Slice_contains_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1762_ = stack[2].m_obj;
lean_object* v_inst_1763_ = stack[3].m_obj;
lean_object* v_s_1764_ = stack[4].m_obj;
lean_object* v_pat_1765_ = stack[5].m_obj;
lean_object* v_inst_1766_ = stack[6].m_obj;
uint8_t v_res_1768_;
v_res_1768_ = l_String_Slice_contains(lean_box(0), lean_box(0), v_inst_1762_, v_inst_1763_, v_s_1764_, v_pat_1765_, v_inst_1766_);
stack->m_num = v_res_1768_;
}
LEAN_EXPORT lean_object* l_String_Slice_contains___boxed(lean_object* v_00_u03c1_1769_, lean_object* v_00_u03c3_1770_, lean_object* v_inst_1771_, lean_object* v_inst_1772_, lean_object* v_s_1773_, lean_object* v_pat_1774_, lean_object* v_inst_1775_){
_start:
{
uint8_t v_res_1776_; lean_object* v_r_1777_; 
v_res_1776_ = l_String_Slice_contains(v_00_u03c1_1769_, v_00_u03c3_1770_, v_inst_1771_, v_inst_1772_, v_s_1773_, v_pat_1774_, v_inst_1775_);
lean_dec(v_pat_1774_);
lean_dec(v_inst_1771_);
v_r_1777_ = lean_box(v_res_1776_);
return v_r_1777_;
}
}
uint8_t l_String_Slice_any___redArg(lean_object* v_inst_1778_, lean_object* v_s_1779_, lean_object* v_inst_1780_){
_start:
{
uint8_t v___x_1781_; 
v___x_1781_ = l_String_Slice_contains___redArg(v_inst_1778_, v_s_1779_, v_inst_1780_);
return v___x_1781_;
}
}
LEAN_EXPORT void l_String_Slice_any___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1778_ = stack[0].m_obj;
lean_object* v_s_1779_ = stack[1].m_obj;
lean_object* v_inst_1780_ = stack[2].m_obj;
uint8_t v_res_1782_;
v_res_1782_ = l_String_Slice_any___redArg(v_inst_1778_, v_s_1779_, v_inst_1780_);
stack->m_num = v_res_1782_;
}
LEAN_EXPORT lean_object* l_String_Slice_any___redArg___boxed(lean_object* v_inst_1783_, lean_object* v_s_1784_, lean_object* v_inst_1785_){
_start:
{
uint8_t v_res_1786_; lean_object* v_r_1787_; 
v_res_1786_ = l_String_Slice_any___redArg(v_inst_1783_, v_s_1784_, v_inst_1785_);
v_r_1787_ = lean_box(v_res_1786_);
return v_r_1787_;
}
}
uint8_t l_String_Slice_any(lean_object* v_00_u03c1_1788_, lean_object* v_00_u03c3_1789_, lean_object* v_inst_1790_, lean_object* v_inst_1791_, lean_object* v_s_1792_, lean_object* v_pat_1793_, lean_object* v_inst_1794_){
_start:
{
uint8_t v___x_1795_; 
v___x_1795_ = l_String_Slice_contains___redArg(v_inst_1791_, v_s_1792_, v_inst_1794_);
return v___x_1795_;
}
}
LEAN_EXPORT void l_String_Slice_any_0interp(lean_interpreter_value* stack)
{
lean_object* v_inst_1790_ = stack[2].m_obj;
lean_object* v_inst_1791_ = stack[3].m_obj;
lean_object* v_s_1792_ = stack[4].m_obj;
lean_object* v_pat_1793_ = stack[5].m_obj;
lean_object* v_inst_1794_ = stack[6].m_obj;
uint8_t v_res_1796_;
v_res_1796_ = l_String_Slice_any(lean_box(0), lean_box(0), v_inst_1790_, v_inst_1791_, v_s_1792_, v_pat_1793_, v_inst_1794_);
stack->m_num = v_res_1796_;
}
LEAN_EXPORT lean_object* l_String_Slice_any___boxed(lean_object* v_00_u03c1_1797_, lean_object* v_00_u03c3_1798_, lean_object* v_inst_1799_, lean_object* v_inst_1800_, lean_object* v_s_1801_, lean_object* v_pat_1802_, lean_object* v_inst_1803_){
_start:
{
uint8_t v_res_1804_; lean_object* v_r_1805_; 
v_res_1804_ = l_String_Slice_any(v_00_u03c1_1797_, v_00_u03c3_1798_, v_inst_1799_, v_inst_1800_, v_s_1801_, v_pat_1802_, v_inst_1803_);
lean_dec(v_pat_1802_);
lean_dec(v_inst_1799_);
v_r_1805_ = lean_box(v_res_1804_);
return v_r_1805_;
}
}
uint8_t l_String_Slice_all___redArg(lean_object* v_s_1806_, lean_object* v_inst_1807_){
_start:
{
lean_object* v_startInclusive_1808_; lean_object* v_endExclusive_1809_; lean_object* v___x_1810_; lean_object* v___x_1811_; lean_object* v___x_1812_; uint8_t v_decide_1813_; 
v_startInclusive_1808_ = lean_ctor_get(v_s_1806_, 1);
v_endExclusive_1809_ = lean_ctor_get(v_s_1806_, 2);
v___x_1810_ = lean_unsigned_to_nat(0u);
v___x_1811_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1806_, v___x_1810_, v_inst_1807_);
v___x_1812_ = lean_nat_sub(v_endExclusive_1809_, v_startInclusive_1808_);
v_decide_1813_ = lean_nat_dec_eq(v___x_1811_, v___x_1812_);
lean_dec(v___x_1812_);
lean_dec(v___x_1811_);
return v_decide_1813_;
}
}
LEAN_EXPORT void l_String_Slice_all___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1806_ = stack[0].m_obj;
lean_object* v_inst_1807_ = stack[1].m_obj;
uint8_t v_res_1814_;
v_res_1814_ = l_String_Slice_all___redArg(v_s_1806_, v_inst_1807_);
stack->m_num = v_res_1814_;
}
LEAN_EXPORT lean_object* l_String_Slice_all___redArg___boxed(lean_object* v_s_1815_, lean_object* v_inst_1816_){
_start:
{
uint8_t v_res_1817_; lean_object* v_r_1818_; 
v_res_1817_ = l_String_Slice_all___redArg(v_s_1815_, v_inst_1816_);
lean_dec_ref(v_s_1815_);
v_r_1818_ = lean_box(v_res_1817_);
return v_r_1818_;
}
}
uint8_t l_String_Slice_all(lean_object* v_00_u03c1_1819_, lean_object* v_s_1820_, lean_object* v_pat_1821_, lean_object* v_inst_1822_){
_start:
{
lean_object* v_startInclusive_1823_; lean_object* v_endExclusive_1824_; lean_object* v___x_1825_; lean_object* v___x_1826_; lean_object* v___x_1827_; uint8_t v_decide_1828_; 
v_startInclusive_1823_ = lean_ctor_get(v_s_1820_, 1);
v_endExclusive_1824_ = lean_ctor_get(v_s_1820_, 2);
v___x_1825_ = lean_unsigned_to_nat(0u);
v___x_1826_ = l_String_Slice_Pos_skipWhile___redArg(v_s_1820_, v___x_1825_, v_inst_1822_);
v___x_1827_ = lean_nat_sub(v_endExclusive_1824_, v_startInclusive_1823_);
v_decide_1828_ = lean_nat_dec_eq(v___x_1826_, v___x_1827_);
lean_dec(v___x_1827_);
lean_dec(v___x_1826_);
return v_decide_1828_;
}
}
LEAN_EXPORT void l_String_Slice_all_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1820_ = stack[1].m_obj;
lean_object* v_pat_1821_ = stack[2].m_obj;
lean_object* v_inst_1822_ = stack[3].m_obj;
uint8_t v_res_1829_;
v_res_1829_ = l_String_Slice_all(lean_box(0), v_s_1820_, v_pat_1821_, v_inst_1822_);
stack->m_num = v_res_1829_;
}
LEAN_EXPORT lean_object* l_String_Slice_all___boxed(lean_object* v_00_u03c1_1830_, lean_object* v_s_1831_, lean_object* v_pat_1832_, lean_object* v_inst_1833_){
_start:
{
uint8_t v_res_1834_; lean_object* v_r_1835_; 
v_res_1834_ = l_String_Slice_all(v_00_u03c1_1830_, v_s_1831_, v_pat_1832_, v_inst_1833_);
lean_dec(v_pat_1832_);
lean_dec_ref(v_s_1831_);
v_r_1835_ = lean_box(v_res_1834_);
return v_r_1835_;
}
}
uint8_t l_String_Slice_endsWith___redArg(lean_object* v_s_1836_, lean_object* v_inst_1837_){
_start:
{
lean_object* v_endsWith_1838_; lean_object* v___x_1839_; uint8_t v___x_1840_; 
v_endsWith_1838_ = lean_ctor_get(v_inst_1837_, 2);
lean_inc_ref(v_endsWith_1838_);
lean_dec_ref(v_inst_1837_);
v___x_1839_ = lean_apply_1(v_endsWith_1838_, v_s_1836_);
v___x_1840_ = lean_unbox(v___x_1839_);
return v___x_1840_;
}
}
LEAN_EXPORT void l_String_Slice_endsWith___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1836_ = stack[0].m_obj;
lean_object* v_inst_1837_ = stack[1].m_obj;
uint8_t v_res_1841_;
v_res_1841_ = l_String_Slice_endsWith___redArg(v_s_1836_, v_inst_1837_);
stack->m_num = v_res_1841_;
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___redArg___boxed(lean_object* v_s_1842_, lean_object* v_inst_1843_){
_start:
{
uint8_t v_res_1844_; lean_object* v_r_1845_; 
v_res_1844_ = l_String_Slice_endsWith___redArg(v_s_1842_, v_inst_1843_);
v_r_1845_ = lean_box(v_res_1844_);
return v_r_1845_;
}
}
uint8_t l_String_Slice_endsWith(lean_object* v_00_u03c1_1846_, lean_object* v_s_1847_, lean_object* v_pat_1848_, lean_object* v_inst_1849_){
_start:
{
lean_object* v_endsWith_1850_; lean_object* v___x_1851_; uint8_t v___x_1852_; 
v_endsWith_1850_ = lean_ctor_get(v_inst_1849_, 2);
lean_inc_ref(v_endsWith_1850_);
lean_dec_ref(v_inst_1849_);
v___x_1851_ = lean_apply_1(v_endsWith_1850_, v_s_1847_);
v___x_1852_ = lean_unbox(v___x_1851_);
return v___x_1852_;
}
}
LEAN_EXPORT void l_String_Slice_endsWith_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_1847_ = stack[1].m_obj;
lean_object* v_pat_1848_ = stack[2].m_obj;
lean_object* v_inst_1849_ = stack[3].m_obj;
uint8_t v_res_1853_;
v_res_1853_ = l_String_Slice_endsWith(lean_box(0), v_s_1847_, v_pat_1848_, v_inst_1849_);
stack->m_num = v_res_1853_;
}
LEAN_EXPORT lean_object* l_String_Slice_endsWith___boxed(lean_object* v_00_u03c1_1854_, lean_object* v_s_1855_, lean_object* v_pat_1856_, lean_object* v_inst_1857_){
_start:
{
uint8_t v_res_1858_; lean_object* v_r_1859_; 
v_res_1858_ = l_String_Slice_endsWith(v_00_u03c1_1854_, v_s_1855_, v_pat_1856_, v_inst_1857_);
lean_dec(v_pat_1856_);
v_r_1859_ = lean_box(v_res_1858_);
return v_r_1859_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg(lean_object* v_x_1860_){
_start:
{
lean_object* v___x_1861_; 
v___x_1861_ = lean_obj_tag_nat(v_x_1860_);
return v___x_1861_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg___boxed(lean_object* v_x_1862_){
_start:
{
lean_object* v_res_1863_; 
v_res_1863_ = l_String_Slice_RevSplitIterator_ctorIdx___impl___redArg(v_x_1862_);
lean_dec(v_x_1862_);
return v_res_1863_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl(lean_object* v_00_u03c3_1864_, lean_object* v_00_u03c1_1865_, lean_object* v_pat_1866_, lean_object* v_s_1867_, lean_object* v_inst_1868_, lean_object* v_x_1869_){
_start:
{
lean_object* v___x_1870_; 
v___x_1870_ = lean_obj_tag_nat(v_x_1869_);
return v___x_1870_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorIdx___impl___boxed(lean_object* v_00_u03c3_1871_, lean_object* v_00_u03c1_1872_, lean_object* v_pat_1873_, lean_object* v_s_1874_, lean_object* v_inst_1875_, lean_object* v_x_1876_){
_start:
{
lean_object* v_res_1877_; 
v_res_1877_ = l_String_Slice_RevSplitIterator_ctorIdx___impl(v_00_u03c3_1871_, v_00_u03c1_1872_, v_pat_1873_, v_s_1874_, v_inst_1875_, v_x_1876_);
lean_dec(v_x_1876_);
lean_dec(v_inst_1875_);
lean_dec_ref(v_s_1874_);
lean_dec(v_pat_1873_);
return v_res_1877_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___redArg(lean_object* v_t_1878_, lean_object* v_k_1879_){
_start:
{
if (lean_obj_tag(v_t_1878_) == 0)
{
lean_object* v_currPos_1880_; lean_object* v_searcher_1881_; lean_object* v___x_1882_; 
v_currPos_1880_ = lean_ctor_get(v_t_1878_, 0);
lean_inc(v_currPos_1880_);
v_searcher_1881_ = lean_ctor_get(v_t_1878_, 1);
lean_inc(v_searcher_1881_);
lean_dec_ref_known(v_t_1878_, 2);
v___x_1882_ = lean_apply_2(v_k_1879_, v_currPos_1880_, v_searcher_1881_);
return v___x_1882_;
}
else
{
return v_k_1879_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim(lean_object* v_00_u03c3_1883_, lean_object* v_00_u03c1_1884_, lean_object* v_pat_1885_, lean_object* v_s_1886_, lean_object* v_inst_1887_, lean_object* v_motive_1888_, lean_object* v_ctorIdx_1889_, lean_object* v_t_1890_, lean_object* v_h_1891_, lean_object* v_k_1892_){
_start:
{
lean_object* v___x_1893_; 
v___x_1893_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1890_, v_k_1892_);
return v___x_1893_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_ctorElim___boxed(lean_object* v_00_u03c3_1894_, lean_object* v_00_u03c1_1895_, lean_object* v_pat_1896_, lean_object* v_s_1897_, lean_object* v_inst_1898_, lean_object* v_motive_1899_, lean_object* v_ctorIdx_1900_, lean_object* v_t_1901_, lean_object* v_h_1902_, lean_object* v_k_1903_){
_start:
{
lean_object* v_res_1904_; 
v_res_1904_ = l_String_Slice_RevSplitIterator_ctorElim(v_00_u03c3_1894_, v_00_u03c1_1895_, v_pat_1896_, v_s_1897_, v_inst_1898_, v_motive_1899_, v_ctorIdx_1900_, v_t_1901_, v_h_1902_, v_k_1903_);
lean_dec(v_ctorIdx_1900_);
lean_dec(v_inst_1898_);
lean_dec_ref(v_s_1897_);
lean_dec(v_pat_1896_);
return v_res_1904_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___redArg(lean_object* v_t_1905_, lean_object* v_operating_1906_){
_start:
{
lean_object* v___x_1907_; 
v___x_1907_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1905_, v_operating_1906_);
return v___x_1907_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim(lean_object* v_00_u03c3_1908_, lean_object* v_00_u03c1_1909_, lean_object* v_pat_1910_, lean_object* v_s_1911_, lean_object* v_inst_1912_, lean_object* v_motive_1913_, lean_object* v_t_1914_, lean_object* v_h_1915_, lean_object* v_operating_1916_){
_start:
{
lean_object* v___x_1917_; 
v___x_1917_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1914_, v_operating_1916_);
return v___x_1917_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_operating_elim___boxed(lean_object* v_00_u03c3_1918_, lean_object* v_00_u03c1_1919_, lean_object* v_pat_1920_, lean_object* v_s_1921_, lean_object* v_inst_1922_, lean_object* v_motive_1923_, lean_object* v_t_1924_, lean_object* v_h_1925_, lean_object* v_operating_1926_){
_start:
{
lean_object* v_res_1927_; 
v_res_1927_ = l_String_Slice_RevSplitIterator_operating_elim(v_00_u03c3_1918_, v_00_u03c1_1919_, v_pat_1920_, v_s_1921_, v_inst_1922_, v_motive_1923_, v_t_1924_, v_h_1925_, v_operating_1926_);
lean_dec(v_inst_1922_);
lean_dec_ref(v_s_1921_);
lean_dec(v_pat_1920_);
return v_res_1927_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___redArg(lean_object* v_t_1928_, lean_object* v_atEnd_1929_){
_start:
{
lean_object* v___x_1930_; 
v___x_1930_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1928_, v_atEnd_1929_);
return v___x_1930_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim(lean_object* v_00_u03c3_1931_, lean_object* v_00_u03c1_1932_, lean_object* v_pat_1933_, lean_object* v_s_1934_, lean_object* v_inst_1935_, lean_object* v_motive_1936_, lean_object* v_t_1937_, lean_object* v_h_1938_, lean_object* v_atEnd_1939_){
_start:
{
lean_object* v___x_1940_; 
v___x_1940_ = l_String_Slice_RevSplitIterator_ctorElim___redArg(v_t_1937_, v_atEnd_1939_);
return v___x_1940_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_atEnd_elim___boxed(lean_object* v_00_u03c3_1941_, lean_object* v_00_u03c1_1942_, lean_object* v_pat_1943_, lean_object* v_s_1944_, lean_object* v_inst_1945_, lean_object* v_motive_1946_, lean_object* v_t_1947_, lean_object* v_h_1948_, lean_object* v_atEnd_1949_){
_start:
{
lean_object* v_res_1950_; 
v_res_1950_ = l_String_Slice_RevSplitIterator_atEnd_elim(v_00_u03c3_1941_, v_00_u03c1_1942_, v_pat_1943_, v_s_1944_, v_inst_1945_, v_motive_1946_, v_t_1947_, v_h_1948_, v_atEnd_1949_);
lean_dec(v_inst_1945_);
lean_dec_ref(v_s_1944_);
lean_dec(v_pat_1943_);
return v_res_1950_;
}
}
lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg(){
_start:
{
lean_object* v___x_1952_; 
v___x_1952_ = lean_box(1);
return v___x_1952_;
}
}
LEAN_EXPORT void l_String_Slice_instInhabitedRevSplitIterator_default___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1953_;
v_res_1953_ = l_String_Slice_instInhabitedRevSplitIterator_default___redArg();
stack->m_obj
 = v_res_1953_;
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___redArg___boxed(lean_object* v___dummy_1954_){
_start:
{
lean_object* v_res_1955_; 
v_res_1955_ = l_String_Slice_instInhabitedRevSplitIterator_default___redArg();
return v_res_1955_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default(lean_object* v_00_u03c3_1956_, lean_object* v_00_u03c1_1957_, lean_object* v_pat_1958_, lean_object* v_s_1959_, lean_object* v_inst_1960_){
_start:
{
lean_object* v___x_1961_; 
v___x_1961_ = lean_box(1);
return v___x_1961_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator_default___boxed(lean_object* v_00_u03c3_1962_, lean_object* v_00_u03c1_1963_, lean_object* v_pat_1964_, lean_object* v_s_1965_, lean_object* v_inst_1966_){
_start:
{
lean_object* v_res_1967_; 
v_res_1967_ = l_String_Slice_instInhabitedRevSplitIterator_default(v_00_u03c3_1962_, v_00_u03c1_1963_, v_pat_1964_, v_s_1965_, v_inst_1966_);
lean_dec(v_inst_1966_);
lean_dec_ref(v_s_1965_);
lean_dec(v_pat_1964_);
return v_res_1967_;
}
}
lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg(){
_start:
{
lean_object* v___x_1969_; 
v___x_1969_ = lean_box(1);
return v___x_1969_;
}
}
LEAN_EXPORT void l_String_Slice_instInhabitedRevSplitIterator___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_1970_;
v_res_1970_ = l_String_Slice_instInhabitedRevSplitIterator___redArg();
stack->m_obj
 = v_res_1970_;
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___redArg___boxed(lean_object* v___dummy_1971_){
_start:
{
lean_object* v_res_1972_; 
v_res_1972_ = l_String_Slice_instInhabitedRevSplitIterator___redArg();
return v_res_1972_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator(lean_object* v_a_1973_, lean_object* v_a_1974_, lean_object* v_a_1975_, lean_object* v_a_1976_, lean_object* v_a_1977_){
_start:
{
lean_object* v___x_1978_; 
v___x_1978_ = lean_box(1);
return v___x_1978_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instInhabitedRevSplitIterator___boxed(lean_object* v_a_1979_, lean_object* v_a_1980_, lean_object* v_a_1981_, lean_object* v_a_1982_, lean_object* v_a_1983_){
_start:
{
lean_object* v_res_1984_; 
v_res_1984_ = l_String_Slice_instInhabitedRevSplitIterator(v_a_1979_, v_a_1980_, v_a_1981_, v_a_1982_, v_a_1983_);
lean_dec(v_a_1983_);
lean_dec_ref(v_a_1982_);
lean_dec(v_a_1981_);
return v_res_1984_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0(lean_object* v_inst_1985_, lean_object* v_s_1986_, lean_object* v_inst_1987_, lean_object* v_x_1988_){
_start:
{
if (lean_obj_tag(v_x_1988_) == 0)
{
lean_object* v_currPos_1989_; lean_object* v_searcher_1990_; lean_object* v___x_1992_; uint8_t v_isShared_1993_; uint8_t v_isSharedCheck_2048_; 
v_currPos_1989_ = lean_ctor_get(v_x_1988_, 0);
v_searcher_1990_ = lean_ctor_get(v_x_1988_, 1);
v_isSharedCheck_2048_ = !lean_is_exclusive(v_x_1988_);
if (v_isSharedCheck_2048_ == 0)
{
v___x_1992_ = v_x_1988_;
v_isShared_1993_ = v_isSharedCheck_2048_;
goto v_resetjp_1991_;
}
else
{
lean_inc(v_searcher_1990_);
lean_inc(v_currPos_1989_);
lean_dec(v_x_1988_);
v___x_1992_ = lean_box(0);
v_isShared_1993_ = v_isSharedCheck_2048_;
goto v_resetjp_1991_;
}
v_resetjp_1991_:
{
lean_object* v___x_1994_; 
lean_inc_ref(v_s_1986_);
v___x_1994_ = lean_apply_2(v_inst_1985_, v_s_1986_, v_searcher_1990_);
switch(lean_obj_tag(v___x_1994_))
{
case 0:
{
lean_object* v_out_1995_; 
v_out_1995_ = lean_ctor_get(v___x_1994_, 1);
lean_inc(v_out_1995_);
if (lean_obj_tag(v_out_1995_) == 0)
{
lean_object* v_it_1996_; lean_object* v___x_1998_; 
lean_dec_ref_known(v_out_1995_, 2);
lean_dec_ref(v_s_1986_);
v_it_1996_ = lean_ctor_get(v___x_1994_, 0);
lean_inc(v_it_1996_);
lean_dec_ref_known(v___x_1994_, 2);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v_it_1996_);
v___x_1998_ = v___x_1992_;
goto v_reusejp_1997_;
}
else
{
lean_object* v_reuseFailAlloc_2001_; 
v_reuseFailAlloc_2001_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2001_, 0, v_currPos_1989_);
lean_ctor_set(v_reuseFailAlloc_2001_, 1, v_it_1996_);
v___x_1998_ = v_reuseFailAlloc_2001_;
goto v_reusejp_1997_;
}
v_reusejp_1997_:
{
lean_object* v___x_1999_; lean_object* v___x_2000_; 
v___x_1999_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_1999_, 0, v___x_1998_);
v___x_2000_ = lean_apply_2(v_inst_1987_, lean_box(0), v___x_1999_);
return v___x_2000_;
}
}
else
{
lean_object* v_it_2002_; lean_object* v___x_2004_; uint8_t v_isShared_2005_; uint8_t v_isSharedCheck_2016_; 
v_it_2002_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2016_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2016_ == 0)
{
lean_object* v_unused_2017_; 
v_unused_2017_ = lean_ctor_get(v___x_1994_, 1);
lean_dec(v_unused_2017_);
v___x_2004_ = v___x_1994_;
v_isShared_2005_ = v_isSharedCheck_2016_;
goto v_resetjp_2003_;
}
else
{
lean_inc(v_it_2002_);
lean_dec(v___x_1994_);
v___x_2004_ = lean_box(0);
v_isShared_2005_ = v_isSharedCheck_2016_;
goto v_resetjp_2003_;
}
v_resetjp_2003_:
{
lean_object* v_startPos_2006_; lean_object* v_endPos_2007_; lean_object* v_slice_2008_; lean_object* v_nextIt_2010_; 
v_startPos_2006_ = lean_ctor_get(v_out_1995_, 0);
lean_inc(v_startPos_2006_);
v_endPos_2007_ = lean_ctor_get(v_out_1995_, 1);
lean_inc(v_endPos_2007_);
lean_dec_ref_known(v_out_1995_, 2);
v_slice_2008_ = l_String_Slice_slice_x21(v_s_1986_, v_endPos_2007_, v_currPos_1989_);
lean_dec(v_currPos_1989_);
lean_dec(v_endPos_2007_);
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v_it_2002_);
lean_ctor_set(v___x_1992_, 0, v_startPos_2006_);
v_nextIt_2010_ = v___x_1992_;
goto v_reusejp_2009_;
}
else
{
lean_object* v_reuseFailAlloc_2015_; 
v_reuseFailAlloc_2015_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2015_, 0, v_startPos_2006_);
lean_ctor_set(v_reuseFailAlloc_2015_, 1, v_it_2002_);
v_nextIt_2010_ = v_reuseFailAlloc_2015_;
goto v_reusejp_2009_;
}
v_reusejp_2009_:
{
lean_object* v___x_2012_; 
if (v_isShared_2005_ == 0)
{
lean_ctor_set(v___x_2004_, 1, v_slice_2008_);
lean_ctor_set(v___x_2004_, 0, v_nextIt_2010_);
v___x_2012_ = v___x_2004_;
goto v_reusejp_2011_;
}
else
{
lean_object* v_reuseFailAlloc_2014_; 
v_reuseFailAlloc_2014_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2014_, 0, v_nextIt_2010_);
lean_ctor_set(v_reuseFailAlloc_2014_, 1, v_slice_2008_);
v___x_2012_ = v_reuseFailAlloc_2014_;
goto v_reusejp_2011_;
}
v_reusejp_2011_:
{
lean_object* v___x_2013_; 
v___x_2013_ = lean_apply_2(v_inst_1987_, lean_box(0), v___x_2012_);
return v___x_2013_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2018_; lean_object* v___x_2020_; uint8_t v_isShared_2021_; uint8_t v_isSharedCheck_2029_; 
lean_dec_ref(v_s_1986_);
v_it_2018_ = lean_ctor_get(v___x_1994_, 0);
v_isSharedCheck_2029_ = !lean_is_exclusive(v___x_1994_);
if (v_isSharedCheck_2029_ == 0)
{
v___x_2020_ = v___x_1994_;
v_isShared_2021_ = v_isSharedCheck_2029_;
goto v_resetjp_2019_;
}
else
{
lean_inc(v_it_2018_);
lean_dec(v___x_1994_);
v___x_2020_ = lean_box(0);
v_isShared_2021_ = v_isSharedCheck_2029_;
goto v_resetjp_2019_;
}
v_resetjp_2019_:
{
lean_object* v___x_2023_; 
if (v_isShared_1993_ == 0)
{
lean_ctor_set(v___x_1992_, 1, v_it_2018_);
v___x_2023_ = v___x_1992_;
goto v_reusejp_2022_;
}
else
{
lean_object* v_reuseFailAlloc_2028_; 
v_reuseFailAlloc_2028_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2028_, 0, v_currPos_1989_);
lean_ctor_set(v_reuseFailAlloc_2028_, 1, v_it_2018_);
v___x_2023_ = v_reuseFailAlloc_2028_;
goto v_reusejp_2022_;
}
v_reusejp_2022_:
{
lean_object* v___x_2025_; 
if (v_isShared_2021_ == 0)
{
lean_ctor_set(v___x_2020_, 0, v___x_2023_);
v___x_2025_ = v___x_2020_;
goto v_reusejp_2024_;
}
else
{
lean_object* v_reuseFailAlloc_2027_; 
v_reuseFailAlloc_2027_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2027_, 0, v___x_2023_);
v___x_2025_ = v_reuseFailAlloc_2027_;
goto v_reusejp_2024_;
}
v_reusejp_2024_:
{
lean_object* v___x_2026_; 
v___x_2026_ = lean_apply_2(v_inst_1987_, lean_box(0), v___x_2025_);
return v___x_2026_;
}
}
}
}
default: 
{
lean_object* v___x_2030_; uint8_t v_decide_2031_; 
lean_del_object(v___x_1992_);
v___x_2030_ = lean_unsigned_to_nat(0u);
v_decide_2031_ = lean_nat_dec_eq(v_currPos_1989_, v___x_2030_);
if (v_decide_2031_ == 0)
{
lean_object* v_str_2032_; lean_object* v_startInclusive_2033_; lean_object* v___x_2035_; uint8_t v_isShared_2036_; uint8_t v_isSharedCheck_2044_; 
v_str_2032_ = lean_ctor_get(v_s_1986_, 0);
v_startInclusive_2033_ = lean_ctor_get(v_s_1986_, 1);
v_isSharedCheck_2044_ = !lean_is_exclusive(v_s_1986_);
if (v_isSharedCheck_2044_ == 0)
{
lean_object* v_unused_2045_; 
v_unused_2045_ = lean_ctor_get(v_s_1986_, 2);
lean_dec(v_unused_2045_);
v___x_2035_ = v_s_1986_;
v_isShared_2036_ = v_isSharedCheck_2044_;
goto v_resetjp_2034_;
}
else
{
lean_inc(v_startInclusive_2033_);
lean_inc(v_str_2032_);
lean_dec(v_s_1986_);
v___x_2035_ = lean_box(0);
v_isShared_2036_ = v_isSharedCheck_2044_;
goto v_resetjp_2034_;
}
v_resetjp_2034_:
{
lean_object* v___x_2037_; lean_object* v_slice_2039_; 
v___x_2037_ = lean_nat_add(v_startInclusive_2033_, v_currPos_1989_);
lean_dec(v_currPos_1989_);
if (v_isShared_2036_ == 0)
{
lean_ctor_set(v___x_2035_, 2, v___x_2037_);
v_slice_2039_ = v___x_2035_;
goto v_reusejp_2038_;
}
else
{
lean_object* v_reuseFailAlloc_2043_; 
v_reuseFailAlloc_2043_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2043_, 0, v_str_2032_);
lean_ctor_set(v_reuseFailAlloc_2043_, 1, v_startInclusive_2033_);
lean_ctor_set(v_reuseFailAlloc_2043_, 2, v___x_2037_);
v_slice_2039_ = v_reuseFailAlloc_2043_;
goto v_reusejp_2038_;
}
v_reusejp_2038_:
{
lean_object* v___x_2040_; lean_object* v___x_2041_; lean_object* v___x_2042_; 
v___x_2040_ = lean_box(1);
v___x_2041_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2041_, 0, v___x_2040_);
lean_ctor_set(v___x_2041_, 1, v_slice_2039_);
v___x_2042_ = lean_apply_2(v_inst_1987_, lean_box(0), v___x_2041_);
return v___x_2042_;
}
}
}
else
{
lean_object* v___x_2046_; lean_object* v___x_2047_; 
lean_dec(v_currPos_1989_);
lean_dec_ref(v_s_1986_);
v___x_2046_ = lean_box(2);
v___x_2047_ = lean_apply_2(v_inst_1987_, lean_box(0), v___x_2046_);
return v___x_2047_;
}
}
}
}
}
else
{
lean_object* v___x_2049_; lean_object* v___x_2050_; 
lean_dec_ref(v_s_1986_);
lean_dec(v_inst_1985_);
v___x_2049_ = lean_box(2);
v___x_2050_ = lean_apply_2(v_inst_1987_, lean_box(0), v___x_2049_);
return v___x_2050_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg(lean_object* v_inst_2051_, lean_object* v_s_2052_, lean_object* v_inst_2053_){
_start:
{
lean_object* v___f_2054_; 
v___f_2054_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2054_, 0, v_inst_2051_);
lean_closure_set(v___f_2054_, 1, v_s_2052_);
lean_closure_set(v___f_2054_, 2, v_inst_2053_);
return v___f_2054_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure(lean_object* v_00_u03c1_2055_, lean_object* v_00_u03c1_2056_, lean_object* v_00_u03c3_2057_, lean_object* v_inst_2058_, lean_object* v_inst_2059_, lean_object* v_m_2060_, lean_object* v_s_2061_, lean_object* v_inst_2062_){
_start:
{
lean_object* v___f_2063_; 
v___f_2063_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorOfPure___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2063_, 0, v_inst_2058_);
lean_closure_set(v___f_2063_, 1, v_s_2061_);
lean_closure_set(v___f_2063_, 2, v_inst_2062_);
return v___f_2063_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorOfPure___boxed(lean_object* v_00_u03c1_2064_, lean_object* v_00_u03c1_2065_, lean_object* v_00_u03c3_2066_, lean_object* v_inst_2067_, lean_object* v_inst_2068_, lean_object* v_m_2069_, lean_object* v_s_2070_, lean_object* v_inst_2071_){
_start:
{
lean_object* v_res_2072_; 
v_res_2072_ = l_String_Slice_RevSplitIterator_instIteratorOfPure(v_00_u03c1_2064_, v_00_u03c1_2065_, v_00_u03c3_2066_, v_inst_2067_, v_inst_2068_, v_m_2069_, v_s_2070_, v_inst_2071_);
lean_dec(v_inst_2068_);
lean_dec(v_00_u03c1_2065_);
return v_res_2072_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(lean_object* v_x_2073_){
_start:
{
if (lean_obj_tag(v_x_2073_) == 0)
{
lean_object* v_searcher_2074_; lean_object* v___x_2075_; 
v_searcher_2074_ = lean_ctor_get(v_x_2073_, 1);
lean_inc(v_searcher_2074_);
v___x_2075_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2075_, 0, v_searcher_2074_);
return v___x_2075_;
}
else
{
lean_object* v___x_2076_; 
v___x_2076_ = lean_box(0);
return v___x_2076_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg___boxed(lean_object* v_x_2077_){
_start:
{
lean_object* v_res_2078_; 
v_res_2078_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2077_);
lean_dec(v_x_2077_);
return v_res_2078_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(lean_object* v_00_u03c1_2079_, lean_object* v_00_u03c1_2080_, lean_object* v_00_u03c3_2081_, lean_object* v_inst_2082_, lean_object* v_s_2083_, lean_object* v_x_2084_){
_start:
{
lean_object* v___x_2085_; 
v___x_2085_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___redArg(v_x_2084_);
return v___x_2085_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption___boxed(lean_object* v_00_u03c1_2086_, lean_object* v_00_u03c1_2087_, lean_object* v_00_u03c3_2088_, lean_object* v_inst_2089_, lean_object* v_s_2090_, lean_object* v_x_2091_){
_start:
{
lean_object* v_res_2092_; 
v_res_2092_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_toOption(v_00_u03c1_2086_, v_00_u03c1_2087_, v_00_u03c3_2088_, v_inst_2089_, v_s_2090_, v_x_2091_);
lean_dec(v_x_2091_);
lean_dec_ref(v_s_2090_);
lean_dec(v_inst_2089_);
lean_dec(v_00_u03c1_2087_);
return v_res_2092_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___redArg(lean_object* v_x_2093_, lean_object* v_h__1_2094_, lean_object* v_h__2_2095_){
_start:
{
if (lean_obj_tag(v_x_2093_) == 0)
{
lean_object* v_currPos_2096_; lean_object* v_searcher_2097_; lean_object* v___x_2098_; 
lean_dec(v_h__2_2095_);
v_currPos_2096_ = lean_ctor_get(v_x_2093_, 0);
lean_inc(v_currPos_2096_);
v_searcher_2097_ = lean_ctor_get(v_x_2093_, 1);
lean_inc(v_searcher_2097_);
lean_dec_ref_known(v_x_2093_, 2);
v___x_2098_ = lean_apply_2(v_h__1_2094_, v_currPos_2096_, v_searcher_2097_);
return v___x_2098_;
}
else
{
lean_object* v___x_2099_; lean_object* v___x_2100_; 
lean_dec(v_h__1_2094_);
v___x_2099_ = lean_box(0);
v___x_2100_ = lean_apply_1(v_h__2_2095_, v___x_2099_);
return v___x_2100_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(lean_object* v_00_u03c1_2101_, lean_object* v_00_u03c1_2102_, lean_object* v_00_u03c3_2103_, lean_object* v_inst_2104_, lean_object* v_m_2105_, lean_object* v_s_2106_, lean_object* v_motive_2107_, lean_object* v_x_2108_, lean_object* v_h__1_2109_, lean_object* v_h__2_2110_){
_start:
{
if (lean_obj_tag(v_x_2108_) == 0)
{
lean_object* v_currPos_2111_; lean_object* v_searcher_2112_; lean_object* v___x_2113_; 
lean_dec(v_h__2_2110_);
v_currPos_2111_ = lean_ctor_get(v_x_2108_, 0);
lean_inc(v_currPos_2111_);
v_searcher_2112_ = lean_ctor_get(v_x_2108_, 1);
lean_inc(v_searcher_2112_);
lean_dec_ref_known(v_x_2108_, 2);
v___x_2113_ = lean_apply_2(v_h__1_2109_, v_currPos_2111_, v_searcher_2112_);
return v___x_2113_;
}
else
{
lean_object* v___x_2114_; lean_object* v___x_2115_; 
lean_dec(v_h__1_2109_);
v___x_2114_ = lean_box(0);
v___x_2115_ = lean_apply_1(v_h__2_2110_, v___x_2114_);
return v___x_2115_;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter___boxed(lean_object* v_00_u03c1_2116_, lean_object* v_00_u03c1_2117_, lean_object* v_00_u03c3_2118_, lean_object* v_inst_2119_, lean_object* v_m_2120_, lean_object* v_s_2121_, lean_object* v_motive_2122_, lean_object* v_x_2123_, lean_object* v_h__1_2124_, lean_object* v_h__2_2125_){
_start:
{
lean_object* v_res_2126_; 
v_res_2126_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__3_splitter(v_00_u03c1_2116_, v_00_u03c1_2117_, v_00_u03c3_2118_, v_inst_2119_, v_m_2120_, v_s_2121_, v_motive_2122_, v_x_2123_, v_h__1_2124_, v_h__2_2125_);
lean_dec_ref(v_s_2121_);
lean_dec(v_inst_2119_);
lean_dec(v_00_u03c1_2117_);
return v_res_2126_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___redArg(lean_object* v_x_2127_, lean_object* v_x_2128_, lean_object* v_h__1_2129_, lean_object* v_h__2_2130_, lean_object* v_h__3_2131_, lean_object* v_h__4_2132_, lean_object* v_h__5_2133_, lean_object* v_h__6_2134_, lean_object* v_h__7_2135_, lean_object* v_h__8_2136_){
_start:
{
if (lean_obj_tag(v_x_2127_) == 0)
{
lean_dec(v_h__8_2136_);
lean_dec(v_h__7_2135_);
lean_dec(v_h__6_2134_);
switch(lean_obj_tag(v_x_2128_))
{
case 0:
{
lean_object* v_it_2137_; 
lean_dec(v_h__5_2133_);
lean_dec(v_h__4_2132_);
lean_dec(v_h__3_2131_);
v_it_2137_ = lean_ctor_get(v_x_2128_, 0);
if (lean_obj_tag(v_it_2137_) == 0)
{
lean_object* v_currPos_2138_; lean_object* v_searcher_2139_; lean_object* v_out_2140_; lean_object* v_currPos_2141_; lean_object* v_searcher_2142_; lean_object* v___x_2143_; 
lean_inc_ref(v_it_2137_);
lean_dec(v_h__2_2130_);
v_currPos_2138_ = lean_ctor_get(v_x_2127_, 0);
lean_inc(v_currPos_2138_);
v_searcher_2139_ = lean_ctor_get(v_x_2127_, 1);
lean_inc(v_searcher_2139_);
lean_dec_ref_known(v_x_2127_, 2);
v_out_2140_ = lean_ctor_get(v_x_2128_, 1);
lean_inc(v_out_2140_);
lean_dec_ref_known(v_x_2128_, 2);
v_currPos_2141_ = lean_ctor_get(v_it_2137_, 0);
lean_inc(v_currPos_2141_);
v_searcher_2142_ = lean_ctor_get(v_it_2137_, 1);
lean_inc(v_searcher_2142_);
lean_dec_ref_known(v_it_2137_, 2);
v___x_2143_ = lean_apply_5(v_h__1_2129_, v_currPos_2138_, v_searcher_2139_, v_currPos_2141_, v_searcher_2142_, v_out_2140_);
return v___x_2143_;
}
else
{
lean_object* v_currPos_2144_; lean_object* v_searcher_2145_; lean_object* v_out_2146_; lean_object* v___x_2147_; 
lean_dec(v_h__1_2129_);
v_currPos_2144_ = lean_ctor_get(v_x_2127_, 0);
lean_inc(v_currPos_2144_);
v_searcher_2145_ = lean_ctor_get(v_x_2127_, 1);
lean_inc(v_searcher_2145_);
lean_dec_ref_known(v_x_2127_, 2);
v_out_2146_ = lean_ctor_get(v_x_2128_, 1);
lean_inc(v_out_2146_);
lean_dec_ref_known(v_x_2128_, 2);
v___x_2147_ = lean_apply_3(v_h__2_2130_, v_currPos_2144_, v_searcher_2145_, v_out_2146_);
return v___x_2147_;
}
}
case 1:
{
lean_object* v_it_2148_; 
lean_dec(v_h__5_2133_);
lean_dec(v_h__2_2130_);
lean_dec(v_h__1_2129_);
v_it_2148_ = lean_ctor_get(v_x_2128_, 0);
lean_inc(v_it_2148_);
lean_dec_ref_known(v_x_2128_, 1);
if (lean_obj_tag(v_it_2148_) == 0)
{
lean_object* v_currPos_2149_; lean_object* v_searcher_2150_; lean_object* v_currPos_2151_; lean_object* v_searcher_2152_; lean_object* v___x_2153_; 
lean_dec(v_h__4_2132_);
v_currPos_2149_ = lean_ctor_get(v_x_2127_, 0);
lean_inc(v_currPos_2149_);
v_searcher_2150_ = lean_ctor_get(v_x_2127_, 1);
lean_inc(v_searcher_2150_);
lean_dec_ref_known(v_x_2127_, 2);
v_currPos_2151_ = lean_ctor_get(v_it_2148_, 0);
lean_inc(v_currPos_2151_);
v_searcher_2152_ = lean_ctor_get(v_it_2148_, 1);
lean_inc(v_searcher_2152_);
lean_dec_ref_known(v_it_2148_, 2);
v___x_2153_ = lean_apply_4(v_h__3_2131_, v_currPos_2149_, v_searcher_2150_, v_currPos_2151_, v_searcher_2152_);
return v___x_2153_;
}
else
{
lean_object* v_currPos_2154_; lean_object* v_searcher_2155_; lean_object* v___x_2156_; 
lean_dec(v_h__3_2131_);
v_currPos_2154_ = lean_ctor_get(v_x_2127_, 0);
lean_inc(v_currPos_2154_);
v_searcher_2155_ = lean_ctor_get(v_x_2127_, 1);
lean_inc(v_searcher_2155_);
lean_dec_ref_known(v_x_2127_, 2);
v___x_2156_ = lean_apply_2(v_h__4_2132_, v_currPos_2154_, v_searcher_2155_);
return v___x_2156_;
}
}
default: 
{
lean_object* v_currPos_2157_; lean_object* v_searcher_2158_; lean_object* v___x_2159_; 
lean_dec(v_h__4_2132_);
lean_dec(v_h__3_2131_);
lean_dec(v_h__2_2130_);
lean_dec(v_h__1_2129_);
v_currPos_2157_ = lean_ctor_get(v_x_2127_, 0);
lean_inc(v_currPos_2157_);
v_searcher_2158_ = lean_ctor_get(v_x_2127_, 1);
lean_inc(v_searcher_2158_);
lean_dec_ref_known(v_x_2127_, 2);
v___x_2159_ = lean_apply_2(v_h__5_2133_, v_currPos_2157_, v_searcher_2158_);
return v___x_2159_;
}
}
}
else
{
lean_dec(v_h__5_2133_);
lean_dec(v_h__4_2132_);
lean_dec(v_h__3_2131_);
lean_dec(v_h__2_2130_);
lean_dec(v_h__1_2129_);
switch(lean_obj_tag(v_x_2128_))
{
case 0:
{
lean_object* v_it_2160_; lean_object* v_out_2161_; lean_object* v___x_2162_; 
lean_dec(v_h__8_2136_);
lean_dec(v_h__7_2135_);
v_it_2160_ = lean_ctor_get(v_x_2128_, 0);
lean_inc(v_it_2160_);
v_out_2161_ = lean_ctor_get(v_x_2128_, 1);
lean_inc(v_out_2161_);
lean_dec_ref_known(v_x_2128_, 2);
v___x_2162_ = lean_apply_2(v_h__6_2134_, v_it_2160_, v_out_2161_);
return v___x_2162_;
}
case 1:
{
lean_object* v_it_2163_; lean_object* v___x_2164_; 
lean_dec(v_h__8_2136_);
lean_dec(v_h__6_2134_);
v_it_2163_ = lean_ctor_get(v_x_2128_, 0);
lean_inc(v_it_2163_);
lean_dec_ref_known(v_x_2128_, 1);
v___x_2164_ = lean_apply_1(v_h__7_2135_, v_it_2163_);
return v___x_2164_;
}
default: 
{
lean_object* v___x_2165_; lean_object* v___x_2166_; 
lean_dec(v_h__7_2135_);
lean_dec(v_h__6_2134_);
v___x_2165_ = lean_box(0);
v___x_2166_ = lean_apply_1(v_h__8_2136_, v___x_2165_);
return v___x_2166_;
}
}
}
}
}
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(lean_object* v_00_u03c1_2167_, lean_object* v_00_u03c1_2168_, lean_object* v_00_u03c3_2169_, lean_object* v_inst_2170_, lean_object* v_m_2171_, lean_object* v_s_2172_, lean_object* v_motive_2173_, lean_object* v_x_2174_, lean_object* v_x_2175_, lean_object* v_h__1_2176_, lean_object* v_h__2_2177_, lean_object* v_h__3_2178_, lean_object* v_h__4_2179_, lean_object* v_h__5_2180_, lean_object* v_h__6_2181_, lean_object* v_h__7_2182_, lean_object* v_h__8_2183_){
_start:
{
if (lean_obj_tag(v_x_2174_) == 0)
{
lean_dec(v_h__8_2183_);
lean_dec(v_h__7_2182_);
lean_dec(v_h__6_2181_);
switch(lean_obj_tag(v_x_2175_))
{
case 0:
{
lean_object* v_it_2184_; 
lean_dec(v_h__5_2180_);
lean_dec(v_h__4_2179_);
lean_dec(v_h__3_2178_);
v_it_2184_ = lean_ctor_get(v_x_2175_, 0);
if (lean_obj_tag(v_it_2184_) == 0)
{
lean_object* v_currPos_2185_; lean_object* v_searcher_2186_; lean_object* v_out_2187_; lean_object* v_currPos_2188_; lean_object* v_searcher_2189_; lean_object* v___x_2190_; 
lean_inc_ref(v_it_2184_);
lean_dec(v_h__2_2177_);
v_currPos_2185_ = lean_ctor_get(v_x_2174_, 0);
lean_inc(v_currPos_2185_);
v_searcher_2186_ = lean_ctor_get(v_x_2174_, 1);
lean_inc(v_searcher_2186_);
lean_dec_ref_known(v_x_2174_, 2);
v_out_2187_ = lean_ctor_get(v_x_2175_, 1);
lean_inc(v_out_2187_);
lean_dec_ref_known(v_x_2175_, 2);
v_currPos_2188_ = lean_ctor_get(v_it_2184_, 0);
lean_inc(v_currPos_2188_);
v_searcher_2189_ = lean_ctor_get(v_it_2184_, 1);
lean_inc(v_searcher_2189_);
lean_dec_ref_known(v_it_2184_, 2);
v___x_2190_ = lean_apply_5(v_h__1_2176_, v_currPos_2185_, v_searcher_2186_, v_currPos_2188_, v_searcher_2189_, v_out_2187_);
return v___x_2190_;
}
else
{
lean_object* v_currPos_2191_; lean_object* v_searcher_2192_; lean_object* v_out_2193_; lean_object* v___x_2194_; 
lean_dec(v_h__1_2176_);
v_currPos_2191_ = lean_ctor_get(v_x_2174_, 0);
lean_inc(v_currPos_2191_);
v_searcher_2192_ = lean_ctor_get(v_x_2174_, 1);
lean_inc(v_searcher_2192_);
lean_dec_ref_known(v_x_2174_, 2);
v_out_2193_ = lean_ctor_get(v_x_2175_, 1);
lean_inc(v_out_2193_);
lean_dec_ref_known(v_x_2175_, 2);
v___x_2194_ = lean_apply_3(v_h__2_2177_, v_currPos_2191_, v_searcher_2192_, v_out_2193_);
return v___x_2194_;
}
}
case 1:
{
lean_object* v_it_2195_; 
lean_dec(v_h__5_2180_);
lean_dec(v_h__2_2177_);
lean_dec(v_h__1_2176_);
v_it_2195_ = lean_ctor_get(v_x_2175_, 0);
lean_inc(v_it_2195_);
lean_dec_ref_known(v_x_2175_, 1);
if (lean_obj_tag(v_it_2195_) == 0)
{
lean_object* v_currPos_2196_; lean_object* v_searcher_2197_; lean_object* v_currPos_2198_; lean_object* v_searcher_2199_; lean_object* v___x_2200_; 
lean_dec(v_h__4_2179_);
v_currPos_2196_ = lean_ctor_get(v_x_2174_, 0);
lean_inc(v_currPos_2196_);
v_searcher_2197_ = lean_ctor_get(v_x_2174_, 1);
lean_inc(v_searcher_2197_);
lean_dec_ref_known(v_x_2174_, 2);
v_currPos_2198_ = lean_ctor_get(v_it_2195_, 0);
lean_inc(v_currPos_2198_);
v_searcher_2199_ = lean_ctor_get(v_it_2195_, 1);
lean_inc(v_searcher_2199_);
lean_dec_ref_known(v_it_2195_, 2);
v___x_2200_ = lean_apply_4(v_h__3_2178_, v_currPos_2196_, v_searcher_2197_, v_currPos_2198_, v_searcher_2199_);
return v___x_2200_;
}
else
{
lean_object* v_currPos_2201_; lean_object* v_searcher_2202_; lean_object* v___x_2203_; 
lean_dec(v_h__3_2178_);
v_currPos_2201_ = lean_ctor_get(v_x_2174_, 0);
lean_inc(v_currPos_2201_);
v_searcher_2202_ = lean_ctor_get(v_x_2174_, 1);
lean_inc(v_searcher_2202_);
lean_dec_ref_known(v_x_2174_, 2);
v___x_2203_ = lean_apply_2(v_h__4_2179_, v_currPos_2201_, v_searcher_2202_);
return v___x_2203_;
}
}
default: 
{
lean_object* v_currPos_2204_; lean_object* v_searcher_2205_; lean_object* v___x_2206_; 
lean_dec(v_h__4_2179_);
lean_dec(v_h__3_2178_);
lean_dec(v_h__2_2177_);
lean_dec(v_h__1_2176_);
v_currPos_2204_ = lean_ctor_get(v_x_2174_, 0);
lean_inc(v_currPos_2204_);
v_searcher_2205_ = lean_ctor_get(v_x_2174_, 1);
lean_inc(v_searcher_2205_);
lean_dec_ref_known(v_x_2174_, 2);
v___x_2206_ = lean_apply_2(v_h__5_2180_, v_currPos_2204_, v_searcher_2205_);
return v___x_2206_;
}
}
}
else
{
lean_dec(v_h__5_2180_);
lean_dec(v_h__4_2179_);
lean_dec(v_h__3_2178_);
lean_dec(v_h__2_2177_);
lean_dec(v_h__1_2176_);
switch(lean_obj_tag(v_x_2175_))
{
case 0:
{
lean_object* v_it_2207_; lean_object* v_out_2208_; lean_object* v___x_2209_; 
lean_dec(v_h__8_2183_);
lean_dec(v_h__7_2182_);
v_it_2207_ = lean_ctor_get(v_x_2175_, 0);
lean_inc(v_it_2207_);
v_out_2208_ = lean_ctor_get(v_x_2175_, 1);
lean_inc(v_out_2208_);
lean_dec_ref_known(v_x_2175_, 2);
v___x_2209_ = lean_apply_2(v_h__6_2181_, v_it_2207_, v_out_2208_);
return v___x_2209_;
}
case 1:
{
lean_object* v_it_2210_; lean_object* v___x_2211_; 
lean_dec(v_h__8_2183_);
lean_dec(v_h__6_2181_);
v_it_2210_ = lean_ctor_get(v_x_2175_, 0);
lean_inc(v_it_2210_);
lean_dec_ref_known(v_x_2175_, 1);
v___x_2211_ = lean_apply_1(v_h__7_2182_, v_it_2210_);
return v___x_2211_;
}
default: 
{
lean_object* v___x_2212_; lean_object* v___x_2213_; 
lean_dec(v_h__7_2182_);
lean_dec(v_h__6_2181_);
v___x_2212_ = lean_box(0);
v___x_2213_ = lean_apply_1(v_h__8_2183_, v___x_2212_);
return v___x_2213_;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter_0interp(lean_interpreter_value* stack)
{
lean_object* v_00_u03c1_2168_ = stack[1].m_obj;
lean_object* v_inst_2170_ = stack[3].m_obj;
lean_object* v_s_2172_ = stack[5].m_obj;
lean_object* v_x_2174_ = stack[7].m_obj;
lean_object* v_x_2175_ = stack[8].m_obj;
lean_object* v_h__1_2176_ = stack[9].m_obj;
lean_object* v_h__2_2177_ = stack[10].m_obj;
lean_object* v_h__3_2178_ = stack[11].m_obj;
lean_object* v_h__4_2179_ = stack[12].m_obj;
lean_object* v_h__5_2180_ = stack[13].m_obj;
lean_object* v_h__6_2181_ = stack[14].m_obj;
lean_object* v_h__7_2182_ = stack[15].m_obj;
lean_object* v_h__8_2183_ = stack[16].m_obj;
lean_object* v_res_2214_;
v_res_2214_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(lean_box(0), v_00_u03c1_2168_, lean_box(0), v_inst_2170_, lean_box(0), v_s_2172_, lean_box(0), v_x_2174_, v_x_2175_, v_h__1_2176_, v_h__2_2177_, v_h__3_2178_, v_h__4_2179_, v_h__5_2180_, v_h__6_2181_, v_h__7_2182_, v_h__8_2183_);
stack->m_obj
 = v_res_2214_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter___boxed(lean_object** _args){
lean_object* v_00_u03c1_2215_ = _args[0];
lean_object* v_00_u03c1_2216_ = _args[1];
lean_object* v_00_u03c3_2217_ = _args[2];
lean_object* v_inst_2218_ = _args[3];
lean_object* v_m_2219_ = _args[4];
lean_object* v_s_2220_ = _args[5];
lean_object* v_motive_2221_ = _args[6];
lean_object* v_x_2222_ = _args[7];
lean_object* v_x_2223_ = _args[8];
lean_object* v_h__1_2224_ = _args[9];
lean_object* v_h__2_2225_ = _args[10];
lean_object* v_h__3_2226_ = _args[11];
lean_object* v_h__4_2227_ = _args[12];
lean_object* v_h__5_2228_ = _args[13];
lean_object* v_h__6_2229_ = _args[14];
lean_object* v_h__7_2230_ = _args[15];
lean_object* v_h__8_2231_ = _args[16];
_start:
{
lean_object* v_res_2232_; 
v_res_2232_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_instIteratorOfPure_match__1_splitter(v_00_u03c1_2215_, v_00_u03c1_2216_, v_00_u03c3_2217_, v_inst_2218_, v_m_2219_, v_s_2220_, v_motive_2221_, v_x_2222_, v_x_2223_, v_h__1_2224_, v_h__2_2225_, v_h__3_2226_, v_h__4_2227_, v_h__5_2228_, v_h__6_2229_, v_h__7_2230_, v_h__8_2231_);
lean_dec_ref(v_s_2220_);
lean_dec(v_inst_2218_);
lean_dec(v_00_u03c1_2216_);
return v_res_2232_;
}
}
lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg(){
_start:
{
lean_object* v___x_2234_; 
v___x_2234_ = lean_box(0);
return v___x_2234_;
}
}
LEAN_EXPORT void l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_2235_;
v_res_2235_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg();
stack->m_obj
 = v_res_2235_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg___boxed(lean_object* v___dummy_2236_){
_start:
{
lean_object* v_res_2237_; 
v_res_2237_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___redArg();
return v_res_2237_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(lean_object* v_00_u03c1_2238_, lean_object* v_00_u03c1_2239_, lean_object* v_00_u03c3_2240_, lean_object* v_inst_2241_, lean_object* v_inst_2242_, lean_object* v_s_2243_, lean_object* v_inst_2244_){
_start:
{
lean_object* v___x_2245_; 
v___x_2245_ = lean_box(0);
return v___x_2245_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation___boxed(lean_object* v_00_u03c1_2246_, lean_object* v_00_u03c1_2247_, lean_object* v_00_u03c3_2248_, lean_object* v_inst_2249_, lean_object* v_inst_2250_, lean_object* v_s_2251_, lean_object* v_inst_2252_){
_start:
{
lean_object* v_res_2253_; 
v_res_2253_ = l___private_Init_Data_String_Slice_0__String_Slice_RevSplitIterator_finitenessRelation(v_00_u03c1_2246_, v_00_u03c1_2247_, v_00_u03c3_2248_, v_inst_2249_, v_inst_2250_, v_s_2251_, v_inst_2252_);
lean_dec_ref(v_s_2251_);
lean_dec(v_inst_2250_);
lean_dec(v_inst_2249_);
lean_dec(v_00_u03c1_2247_);
return v_res_2253_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0(lean_object* v_toPure_2254_, lean_object* v_recur_2255_, lean_object* v_it_2256_, lean_object* v_____do__lift_2257_){
_start:
{
if (lean_obj_tag(v_____do__lift_2257_) == 0)
{
lean_object* v_a_2258_; lean_object* v___x_2259_; 
lean_dec(v_it_2256_);
lean_dec(v_recur_2255_);
v_a_2258_ = lean_ctor_get(v_____do__lift_2257_, 0);
lean_inc(v_a_2258_);
lean_dec_ref_known(v_____do__lift_2257_, 1);
v___x_2259_ = lean_apply_2(v_toPure_2254_, lean_box(0), v_a_2258_);
return v___x_2259_;
}
else
{
lean_object* v_a_2260_; lean_object* v___x_2261_; 
lean_dec(v_toPure_2254_);
v_a_2260_ = lean_ctor_get(v_____do__lift_2257_, 0);
lean_inc(v_a_2260_);
lean_dec_ref_known(v_____do__lift_2257_, 1);
v___x_2261_ = lean_apply_4(v_recur_2255_, v_it_2256_, v_a_2260_, lean_box(0), lean_box(0));
return v___x_2261_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1(lean_object* v_toPure_2262_, lean_object* v_recur_2263_, lean_object* v___y_2264_, lean_object* v_acc_2265_, lean_object* v_toBind_2266_, lean_object* v_s_2267_){
_start:
{
switch(lean_obj_tag(v_s_2267_))
{
case 0:
{
lean_object* v_it_2268_; lean_object* v_out_2269_; lean_object* v___f_2270_; lean_object* v___x_2271_; lean_object* v___x_2272_; 
v_it_2268_ = lean_ctor_get(v_s_2267_, 0);
lean_inc(v_it_2268_);
v_out_2269_ = lean_ctor_get(v_s_2267_, 1);
lean_inc(v_out_2269_);
lean_dec_ref_known(v_s_2267_, 2);
v___f_2270_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__0), 4, 3);
lean_closure_set(v___f_2270_, 0, v_toPure_2262_);
lean_closure_set(v___f_2270_, 1, v_recur_2263_);
lean_closure_set(v___f_2270_, 2, v_it_2268_);
v___x_2271_ = lean_apply_3(v___y_2264_, v_out_2269_, lean_box(0), v_acc_2265_);
v___x_2272_ = lean_apply_4(v_toBind_2266_, lean_box(0), lean_box(0), v___x_2271_, v___f_2270_);
return v___x_2272_;
}
case 1:
{
lean_object* v_it_2273_; lean_object* v___x_2274_; 
lean_dec(v_toBind_2266_);
lean_dec(v___y_2264_);
lean_dec(v_toPure_2262_);
v_it_2273_ = lean_ctor_get(v_s_2267_, 0);
lean_inc(v_it_2273_);
lean_dec_ref_known(v_s_2267_, 1);
v___x_2274_ = lean_apply_4(v_recur_2263_, v_it_2273_, v_acc_2265_, lean_box(0), lean_box(0));
return v___x_2274_;
}
default: 
{
lean_object* v___x_2275_; 
lean_dec(v_toBind_2266_);
lean_dec(v___y_2264_);
lean_dec(v_recur_2263_);
v___x_2275_ = lean_apply_2(v_toPure_2262_, lean_box(0), v_acc_2265_);
return v___x_2275_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2(lean_object* v_toPure_2276_, lean_object* v___y_2277_, lean_object* v_toBind_2278_, lean_object* v_inst_2279_, lean_object* v_s_2280_, lean_object* v_toPure_2281_, lean_object* v_lift_2282_, lean_object* v_it_2283_, lean_object* v_acc_2284_, lean_object* v_hP_2285_, lean_object* v_recur_2286_){
_start:
{
lean_object* v___f_2287_; 
v___f_2287_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__1), 6, 5);
lean_closure_set(v___f_2287_, 0, v_toPure_2276_);
lean_closure_set(v___f_2287_, 1, v_recur_2286_);
lean_closure_set(v___f_2287_, 2, v___y_2277_);
lean_closure_set(v___f_2287_, 3, v_acc_2284_);
lean_closure_set(v___f_2287_, 4, v_toBind_2278_);
if (lean_obj_tag(v_it_2283_) == 0)
{
lean_object* v_currPos_2288_; lean_object* v_searcher_2289_; lean_object* v___x_2291_; uint8_t v_isShared_2292_; uint8_t v_isSharedCheck_2352_; 
v_currPos_2288_ = lean_ctor_get(v_it_2283_, 0);
v_searcher_2289_ = lean_ctor_get(v_it_2283_, 1);
v_isSharedCheck_2352_ = !lean_is_exclusive(v_it_2283_);
if (v_isSharedCheck_2352_ == 0)
{
v___x_2291_ = v_it_2283_;
v_isShared_2292_ = v_isSharedCheck_2352_;
goto v_resetjp_2290_;
}
else
{
lean_inc(v_searcher_2289_);
lean_inc(v_currPos_2288_);
lean_dec(v_it_2283_);
v___x_2291_ = lean_box(0);
v_isShared_2292_ = v_isSharedCheck_2352_;
goto v_resetjp_2290_;
}
v_resetjp_2290_:
{
lean_object* v___x_2293_; 
lean_inc_ref(v_s_2280_);
v___x_2293_ = lean_apply_2(v_inst_2279_, v_s_2280_, v_searcher_2289_);
switch(lean_obj_tag(v___x_2293_))
{
case 0:
{
lean_object* v_out_2294_; 
v_out_2294_ = lean_ctor_get(v___x_2293_, 1);
lean_inc(v_out_2294_);
if (lean_obj_tag(v_out_2294_) == 0)
{
lean_object* v_it_2295_; lean_object* v___x_2297_; 
lean_dec_ref_known(v_out_2294_, 2);
lean_dec_ref(v_s_2280_);
v_it_2295_ = lean_ctor_get(v___x_2293_, 0);
lean_inc(v_it_2295_);
lean_dec_ref_known(v___x_2293_, 2);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 1, v_it_2295_);
v___x_2297_ = v___x_2291_;
goto v_reusejp_2296_;
}
else
{
lean_object* v_reuseFailAlloc_2301_; 
v_reuseFailAlloc_2301_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2301_, 0, v_currPos_2288_);
lean_ctor_set(v_reuseFailAlloc_2301_, 1, v_it_2295_);
v___x_2297_ = v_reuseFailAlloc_2301_;
goto v_reusejp_2296_;
}
v_reusejp_2296_:
{
lean_object* v___x_2298_; lean_object* v___x_2299_; lean_object* v___x_2300_; 
v___x_2298_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_2298_, 0, v___x_2297_);
v___x_2299_ = lean_apply_2(v_toPure_2281_, lean_box(0), v___x_2298_);
v___x_2300_ = lean_apply_4(v_lift_2282_, lean_box(0), lean_box(0), v___f_2287_, v___x_2299_);
return v___x_2300_;
}
}
else
{
lean_object* v_it_2302_; lean_object* v___x_2304_; uint8_t v_isShared_2305_; uint8_t v_isSharedCheck_2317_; 
v_it_2302_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2317_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2317_ == 0)
{
lean_object* v_unused_2318_; 
v_unused_2318_ = lean_ctor_get(v___x_2293_, 1);
lean_dec(v_unused_2318_);
v___x_2304_ = v___x_2293_;
v_isShared_2305_ = v_isSharedCheck_2317_;
goto v_resetjp_2303_;
}
else
{
lean_inc(v_it_2302_);
lean_dec(v___x_2293_);
v___x_2304_ = lean_box(0);
v_isShared_2305_ = v_isSharedCheck_2317_;
goto v_resetjp_2303_;
}
v_resetjp_2303_:
{
lean_object* v_startPos_2306_; lean_object* v_endPos_2307_; lean_object* v_slice_2308_; lean_object* v_nextIt_2310_; 
v_startPos_2306_ = lean_ctor_get(v_out_2294_, 0);
lean_inc(v_startPos_2306_);
v_endPos_2307_ = lean_ctor_get(v_out_2294_, 1);
lean_inc(v_endPos_2307_);
lean_dec_ref_known(v_out_2294_, 2);
v_slice_2308_ = l_String_Slice_slice_x21(v_s_2280_, v_endPos_2307_, v_currPos_2288_);
lean_dec(v_currPos_2288_);
lean_dec(v_endPos_2307_);
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 1, v_it_2302_);
lean_ctor_set(v___x_2291_, 0, v_startPos_2306_);
v_nextIt_2310_ = v___x_2291_;
goto v_reusejp_2309_;
}
else
{
lean_object* v_reuseFailAlloc_2316_; 
v_reuseFailAlloc_2316_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2316_, 0, v_startPos_2306_);
lean_ctor_set(v_reuseFailAlloc_2316_, 1, v_it_2302_);
v_nextIt_2310_ = v_reuseFailAlloc_2316_;
goto v_reusejp_2309_;
}
v_reusejp_2309_:
{
lean_object* v___x_2312_; 
if (v_isShared_2305_ == 0)
{
lean_ctor_set(v___x_2304_, 1, v_slice_2308_);
lean_ctor_set(v___x_2304_, 0, v_nextIt_2310_);
v___x_2312_ = v___x_2304_;
goto v_reusejp_2311_;
}
else
{
lean_object* v_reuseFailAlloc_2315_; 
v_reuseFailAlloc_2315_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2315_, 0, v_nextIt_2310_);
lean_ctor_set(v_reuseFailAlloc_2315_, 1, v_slice_2308_);
v___x_2312_ = v_reuseFailAlloc_2315_;
goto v_reusejp_2311_;
}
v_reusejp_2311_:
{
lean_object* v___x_2313_; lean_object* v___x_2314_; 
v___x_2313_ = lean_apply_2(v_toPure_2281_, lean_box(0), v___x_2312_);
v___x_2314_ = lean_apply_4(v_lift_2282_, lean_box(0), lean_box(0), v___f_2287_, v___x_2313_);
return v___x_2314_;
}
}
}
}
}
case 1:
{
lean_object* v_it_2319_; lean_object* v___x_2321_; uint8_t v_isShared_2322_; uint8_t v_isSharedCheck_2331_; 
lean_dec_ref(v_s_2280_);
v_it_2319_ = lean_ctor_get(v___x_2293_, 0);
v_isSharedCheck_2331_ = !lean_is_exclusive(v___x_2293_);
if (v_isSharedCheck_2331_ == 0)
{
v___x_2321_ = v___x_2293_;
v_isShared_2322_ = v_isSharedCheck_2331_;
goto v_resetjp_2320_;
}
else
{
lean_inc(v_it_2319_);
lean_dec(v___x_2293_);
v___x_2321_ = lean_box(0);
v_isShared_2322_ = v_isSharedCheck_2331_;
goto v_resetjp_2320_;
}
v_resetjp_2320_:
{
lean_object* v___x_2324_; 
if (v_isShared_2292_ == 0)
{
lean_ctor_set(v___x_2291_, 1, v_it_2319_);
v___x_2324_ = v___x_2291_;
goto v_reusejp_2323_;
}
else
{
lean_object* v_reuseFailAlloc_2330_; 
v_reuseFailAlloc_2330_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_2330_, 0, v_currPos_2288_);
lean_ctor_set(v_reuseFailAlloc_2330_, 1, v_it_2319_);
v___x_2324_ = v_reuseFailAlloc_2330_;
goto v_reusejp_2323_;
}
v_reusejp_2323_:
{
lean_object* v___x_2326_; 
if (v_isShared_2322_ == 0)
{
lean_ctor_set(v___x_2321_, 0, v___x_2324_);
v___x_2326_ = v___x_2321_;
goto v_reusejp_2325_;
}
else
{
lean_object* v_reuseFailAlloc_2329_; 
v_reuseFailAlloc_2329_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2329_, 0, v___x_2324_);
v___x_2326_ = v_reuseFailAlloc_2329_;
goto v_reusejp_2325_;
}
v_reusejp_2325_:
{
lean_object* v___x_2327_; lean_object* v___x_2328_; 
v___x_2327_ = lean_apply_2(v_toPure_2281_, lean_box(0), v___x_2326_);
v___x_2328_ = lean_apply_4(v_lift_2282_, lean_box(0), lean_box(0), v___f_2287_, v___x_2327_);
return v___x_2328_;
}
}
}
}
default: 
{
lean_object* v___x_2332_; uint8_t v_decide_2333_; 
lean_del_object(v___x_2291_);
v___x_2332_ = lean_unsigned_to_nat(0u);
v_decide_2333_ = lean_nat_dec_eq(v_currPos_2288_, v___x_2332_);
if (v_decide_2333_ == 0)
{
lean_object* v_str_2334_; lean_object* v_startInclusive_2335_; lean_object* v___x_2337_; uint8_t v_isShared_2338_; uint8_t v_isSharedCheck_2347_; 
v_str_2334_ = lean_ctor_get(v_s_2280_, 0);
v_startInclusive_2335_ = lean_ctor_get(v_s_2280_, 1);
v_isSharedCheck_2347_ = !lean_is_exclusive(v_s_2280_);
if (v_isSharedCheck_2347_ == 0)
{
lean_object* v_unused_2348_; 
v_unused_2348_ = lean_ctor_get(v_s_2280_, 2);
lean_dec(v_unused_2348_);
v___x_2337_ = v_s_2280_;
v_isShared_2338_ = v_isSharedCheck_2347_;
goto v_resetjp_2336_;
}
else
{
lean_inc(v_startInclusive_2335_);
lean_inc(v_str_2334_);
lean_dec(v_s_2280_);
v___x_2337_ = lean_box(0);
v_isShared_2338_ = v_isSharedCheck_2347_;
goto v_resetjp_2336_;
}
v_resetjp_2336_:
{
lean_object* v___x_2339_; lean_object* v_slice_2341_; 
v___x_2339_ = lean_nat_add(v_startInclusive_2335_, v_currPos_2288_);
lean_dec(v_currPos_2288_);
if (v_isShared_2338_ == 0)
{
lean_ctor_set(v___x_2337_, 2, v___x_2339_);
v_slice_2341_ = v___x_2337_;
goto v_reusejp_2340_;
}
else
{
lean_object* v_reuseFailAlloc_2346_; 
v_reuseFailAlloc_2346_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2346_, 0, v_str_2334_);
lean_ctor_set(v_reuseFailAlloc_2346_, 1, v_startInclusive_2335_);
lean_ctor_set(v_reuseFailAlloc_2346_, 2, v___x_2339_);
v_slice_2341_ = v_reuseFailAlloc_2346_;
goto v_reusejp_2340_;
}
v_reusejp_2340_:
{
lean_object* v___x_2342_; lean_object* v___x_2343_; lean_object* v___x_2344_; lean_object* v___x_2345_; 
v___x_2342_ = lean_box(1);
v___x_2343_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2343_, 0, v___x_2342_);
lean_ctor_set(v___x_2343_, 1, v_slice_2341_);
v___x_2344_ = lean_apply_2(v_toPure_2281_, lean_box(0), v___x_2343_);
v___x_2345_ = lean_apply_4(v_lift_2282_, lean_box(0), lean_box(0), v___f_2287_, v___x_2344_);
return v___x_2345_;
}
}
}
else
{
lean_object* v___x_2349_; lean_object* v___x_2350_; lean_object* v___x_2351_; 
lean_dec(v_currPos_2288_);
lean_dec_ref(v_s_2280_);
v___x_2349_ = lean_box(2);
v___x_2350_ = lean_apply_2(v_toPure_2281_, lean_box(0), v___x_2349_);
v___x_2351_ = lean_apply_4(v_lift_2282_, lean_box(0), lean_box(0), v___f_2287_, v___x_2350_);
return v___x_2351_;
}
}
}
}
}
else
{
lean_object* v___x_2353_; lean_object* v___x_2354_; lean_object* v___x_2355_; 
lean_dec_ref(v_s_2280_);
lean_dec(v_inst_2279_);
v___x_2353_ = lean_box(2);
v___x_2354_ = lean_apply_2(v_toPure_2281_, lean_box(0), v___x_2353_);
v___x_2355_ = lean_apply_4(v_lift_2282_, lean_box(0), lean_box(0), v___f_2287_, v___x_2354_);
return v___x_2355_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3(lean_object* v_inst_2356_, lean_object* v_inst_2357_, lean_object* v_s_2358_, lean_object* v_toPure_2359_, lean_object* v_lift_2360_, lean_object* v_00_u03b3_2361_, lean_object* v_Pl_2362_, lean_object* v_it_2363_, lean_object* v_init_2364_, lean_object* v___y_2365_){
_start:
{
lean_object* v_toApplicative_2366_; lean_object* v_toBind_2367_; lean_object* v_toPure_2368_; lean_object* v___f_2369_; lean_object* v___x_2370_; 
v_toApplicative_2366_ = lean_ctor_get(v_inst_2356_, 0);
lean_inc_ref(v_toApplicative_2366_);
v_toBind_2367_ = lean_ctor_get(v_inst_2356_, 1);
lean_inc(v_toBind_2367_);
lean_dec_ref(v_inst_2356_);
v_toPure_2368_ = lean_ctor_get(v_toApplicative_2366_, 1);
lean_inc(v_toPure_2368_);
lean_dec_ref(v_toApplicative_2366_);
v___f_2369_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__2), 11, 7);
lean_closure_set(v___f_2369_, 0, v_toPure_2368_);
lean_closure_set(v___f_2369_, 1, v___y_2365_);
lean_closure_set(v___f_2369_, 2, v_toBind_2367_);
lean_closure_set(v___f_2369_, 3, v_inst_2357_);
lean_closure_set(v___f_2369_, 4, v_s_2358_);
lean_closure_set(v___f_2369_, 5, v_toPure_2359_);
lean_closure_set(v___f_2369_, 6, v_lift_2360_);
v___x_2370_ = l_WellFounded_opaqueFix_u2083___redArg(v___f_2369_, v_it_2363_, v_init_2364_, lean_box(0));
return v___x_2370_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(lean_object* v_inst_2371_, lean_object* v_s_2372_, lean_object* v_inst_2373_, lean_object* v_inst_2374_){
_start:
{
lean_object* v_toApplicative_2375_; lean_object* v_toPure_2376_; lean_object* v___f_2377_; 
v_toApplicative_2375_ = lean_ctor_get(v_inst_2373_, 0);
lean_inc_ref(v_toApplicative_2375_);
lean_dec_ref(v_inst_2373_);
v_toPure_2376_ = lean_ctor_get(v_toApplicative_2375_, 1);
lean_inc(v_toPure_2376_);
lean_dec_ref(v_toApplicative_2375_);
v___f_2377_ = lean_alloc_closure((void*)(l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg___lam__3), 10, 4);
lean_closure_set(v___f_2377_, 0, v_inst_2374_);
lean_closure_set(v___f_2377_, 1, v_inst_2371_);
lean_closure_set(v___f_2377_, 2, v_s_2372_);
lean_closure_set(v___f_2377_, 3, v_toPure_2376_);
return v___f_2377_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(lean_object* v_00_u03c1_2378_, lean_object* v_00_u03c1_2379_, lean_object* v_00_u03c3_2380_, lean_object* v_inst_2381_, lean_object* v_inst_2382_, lean_object* v_m_2383_, lean_object* v_n_2384_, lean_object* v_s_2385_, lean_object* v_inst_2386_, lean_object* v_inst_2387_){
_start:
{
lean_object* v___x_2388_; 
v___x_2388_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___redArg(v_inst_2381_, v_s_2385_, v_inst_2386_, v_inst_2387_);
return v___x_2388_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad___boxed(lean_object* v_00_u03c1_2389_, lean_object* v_00_u03c1_2390_, lean_object* v_00_u03c3_2391_, lean_object* v_inst_2392_, lean_object* v_inst_2393_, lean_object* v_m_2394_, lean_object* v_n_2395_, lean_object* v_s_2396_, lean_object* v_inst_2397_, lean_object* v_inst_2398_){
_start:
{
lean_object* v_res_2399_; 
v_res_2399_ = l_String_Slice_RevSplitIterator_instIteratorLoopOfMonad(v_00_u03c1_2389_, v_00_u03c1_2390_, v_00_u03c3_2391_, v_inst_2392_, v_inst_2393_, v_m_2394_, v_n_2395_, v_s_2396_, v_inst_2397_, v_inst_2398_);
lean_dec(v_inst_2393_);
lean_dec(v_00_u03c1_2390_);
return v_res_2399_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___redArg(lean_object* v_s_2400_, lean_object* v_inst_2401_){
_start:
{
lean_object* v_startInclusive_2402_; lean_object* v_endExclusive_2403_; lean_object* v___x_2404_; lean_object* v___x_2405_; lean_object* v___x_2406_; 
v_startInclusive_2402_ = lean_ctor_get(v_s_2400_, 1);
v_endExclusive_2403_ = lean_ctor_get(v_s_2400_, 2);
v___x_2404_ = lean_nat_sub(v_endExclusive_2403_, v_startInclusive_2402_);
v___x_2405_ = lean_apply_1(v_inst_2401_, v_s_2400_);
v___x_2406_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_2406_, 0, v___x_2404_);
lean_ctor_set(v___x_2406_, 1, v___x_2405_);
return v___x_2406_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit(lean_object* v_00_u03c3_2407_, lean_object* v_00_u03c1_2408_, lean_object* v_s_2409_, lean_object* v_pat_2410_, lean_object* v_inst_2411_){
_start:
{
lean_object* v___x_2412_; 
v___x_2412_ = l_String_Slice_revSplit___redArg(v_s_2409_, v_inst_2411_);
return v___x_2412_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revSplit___boxed(lean_object* v_00_u03c3_2413_, lean_object* v_00_u03c1_2414_, lean_object* v_s_2415_, lean_object* v_pat_2416_, lean_object* v_inst_2417_){
_start:
{
lean_object* v_res_2418_; 
v_res_2418_ = l_String_Slice_revSplit(v_00_u03c3_2413_, v_00_u03c1_2414_, v_s_2415_, v_pat_2416_, v_inst_2417_);
lean_dec(v_pat_2416_);
return v_res_2418_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___redArg(lean_object* v_s_2419_, lean_object* v_inst_2420_){
_start:
{
lean_object* v_skipSuffix_x3f_2421_; lean_object* v___x_2422_; 
v_skipSuffix_x3f_2421_ = lean_ctor_get(v_inst_2420_, 0);
lean_inc_ref(v_skipSuffix_x3f_2421_);
lean_dec_ref(v_inst_2420_);
v___x_2422_ = lean_apply_1(v_skipSuffix_x3f_2421_, v_s_2419_);
return v___x_2422_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f(lean_object* v_00_u03c1_2423_, lean_object* v_s_2424_, lean_object* v_pat_2425_, lean_object* v_inst_2426_){
_start:
{
lean_object* v_skipSuffix_x3f_2427_; lean_object* v___x_2428_; 
v_skipSuffix_x3f_2427_ = lean_ctor_get(v_inst_2426_, 0);
lean_inc_ref(v_skipSuffix_x3f_2427_);
lean_dec_ref(v_inst_2426_);
v___x_2428_ = lean_apply_1(v_skipSuffix_x3f_2427_, v_s_2424_);
return v___x_2428_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffix_x3f___boxed(lean_object* v_00_u03c1_2429_, lean_object* v_s_2430_, lean_object* v_pat_2431_, lean_object* v_inst_2432_){
_start:
{
lean_object* v_res_2433_; 
v_res_2433_ = l_String_Slice_skipSuffix_x3f(v_00_u03c1_2429_, v_s_2430_, v_pat_2431_, v_inst_2432_);
lean_dec(v_pat_2431_);
return v_res_2433_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg(lean_object* v_s_2434_, lean_object* v_pos_2435_, lean_object* v_inst_2436_){
_start:
{
lean_object* v_str_2437_; lean_object* v_startInclusive_2438_; lean_object* v___x_2440_; uint8_t v_isShared_2441_; uint8_t v_isSharedCheck_2456_; 
v_str_2437_ = lean_ctor_get(v_s_2434_, 0);
v_startInclusive_2438_ = lean_ctor_get(v_s_2434_, 1);
v_isSharedCheck_2456_ = !lean_is_exclusive(v_s_2434_);
if (v_isSharedCheck_2456_ == 0)
{
lean_object* v_unused_2457_; 
v_unused_2457_ = lean_ctor_get(v_s_2434_, 2);
lean_dec(v_unused_2457_);
v___x_2440_ = v_s_2434_;
v_isShared_2441_ = v_isSharedCheck_2456_;
goto v_resetjp_2439_;
}
else
{
lean_inc(v_startInclusive_2438_);
lean_inc(v_str_2437_);
lean_dec(v_s_2434_);
v___x_2440_ = lean_box(0);
v_isShared_2441_ = v_isSharedCheck_2456_;
goto v_resetjp_2439_;
}
v_resetjp_2439_:
{
lean_object* v_skipSuffix_x3f_2442_; lean_object* v___x_2443_; lean_object* v___x_2445_; 
v_skipSuffix_x3f_2442_ = lean_ctor_get(v_inst_2436_, 0);
lean_inc_ref(v_skipSuffix_x3f_2442_);
lean_dec_ref(v_inst_2436_);
v___x_2443_ = lean_nat_add(v_startInclusive_2438_, v_pos_2435_);
if (v_isShared_2441_ == 0)
{
lean_ctor_set(v___x_2440_, 2, v___x_2443_);
v___x_2445_ = v___x_2440_;
goto v_reusejp_2444_;
}
else
{
lean_object* v_reuseFailAlloc_2455_; 
v_reuseFailAlloc_2455_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2455_, 0, v_str_2437_);
lean_ctor_set(v_reuseFailAlloc_2455_, 1, v_startInclusive_2438_);
lean_ctor_set(v_reuseFailAlloc_2455_, 2, v___x_2443_);
v___x_2445_ = v_reuseFailAlloc_2455_;
goto v_reusejp_2444_;
}
v_reusejp_2444_:
{
lean_object* v___x_2446_; 
v___x_2446_ = lean_apply_1(v_skipSuffix_x3f_2442_, v___x_2445_);
if (lean_obj_tag(v___x_2446_) == 0)
{
return v___x_2446_;
}
else
{
lean_object* v_val_2447_; lean_object* v___x_2449_; uint8_t v_isShared_2450_; uint8_t v_isSharedCheck_2454_; 
v_val_2447_ = lean_ctor_get(v___x_2446_, 0);
v_isSharedCheck_2454_ = !lean_is_exclusive(v___x_2446_);
if (v_isSharedCheck_2454_ == 0)
{
v___x_2449_ = v___x_2446_;
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
else
{
lean_inc(v_val_2447_);
lean_dec(v___x_2446_);
v___x_2449_ = lean_box(0);
v_isShared_2450_ = v_isSharedCheck_2454_;
goto v_resetjp_2448_;
}
v_resetjp_2448_:
{
lean_object* v___x_2452_; 
if (v_isShared_2450_ == 0)
{
v___x_2452_ = v___x_2449_;
goto v_reusejp_2451_;
}
else
{
lean_object* v_reuseFailAlloc_2453_; 
v_reuseFailAlloc_2453_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2453_, 0, v_val_2447_);
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
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___redArg___boxed(lean_object* v_s_2458_, lean_object* v_pos_2459_, lean_object* v_inst_2460_){
_start:
{
lean_object* v_res_2461_; 
v_res_2461_ = l_String_Slice_Pos_revSkip_x3f___redArg(v_s_2458_, v_pos_2459_, v_inst_2460_);
lean_dec(v_pos_2459_);
return v_res_2461_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f(lean_object* v_00_u03c1_2462_, lean_object* v_s_2463_, lean_object* v_pos_2464_, lean_object* v_pat_2465_, lean_object* v_inst_2466_){
_start:
{
lean_object* v_str_2467_; lean_object* v_startInclusive_2468_; lean_object* v___x_2470_; uint8_t v_isShared_2471_; uint8_t v_isSharedCheck_2486_; 
v_str_2467_ = lean_ctor_get(v_s_2463_, 0);
v_startInclusive_2468_ = lean_ctor_get(v_s_2463_, 1);
v_isSharedCheck_2486_ = !lean_is_exclusive(v_s_2463_);
if (v_isSharedCheck_2486_ == 0)
{
lean_object* v_unused_2487_; 
v_unused_2487_ = lean_ctor_get(v_s_2463_, 2);
lean_dec(v_unused_2487_);
v___x_2470_ = v_s_2463_;
v_isShared_2471_ = v_isSharedCheck_2486_;
goto v_resetjp_2469_;
}
else
{
lean_inc(v_startInclusive_2468_);
lean_inc(v_str_2467_);
lean_dec(v_s_2463_);
v___x_2470_ = lean_box(0);
v_isShared_2471_ = v_isSharedCheck_2486_;
goto v_resetjp_2469_;
}
v_resetjp_2469_:
{
lean_object* v_skipSuffix_x3f_2472_; lean_object* v___x_2473_; lean_object* v___x_2475_; 
v_skipSuffix_x3f_2472_ = lean_ctor_get(v_inst_2466_, 0);
lean_inc_ref(v_skipSuffix_x3f_2472_);
lean_dec_ref(v_inst_2466_);
v___x_2473_ = lean_nat_add(v_startInclusive_2468_, v_pos_2464_);
if (v_isShared_2471_ == 0)
{
lean_ctor_set(v___x_2470_, 2, v___x_2473_);
v___x_2475_ = v___x_2470_;
goto v_reusejp_2474_;
}
else
{
lean_object* v_reuseFailAlloc_2485_; 
v_reuseFailAlloc_2485_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2485_, 0, v_str_2467_);
lean_ctor_set(v_reuseFailAlloc_2485_, 1, v_startInclusive_2468_);
lean_ctor_set(v_reuseFailAlloc_2485_, 2, v___x_2473_);
v___x_2475_ = v_reuseFailAlloc_2485_;
goto v_reusejp_2474_;
}
v_reusejp_2474_:
{
lean_object* v___x_2476_; 
v___x_2476_ = lean_apply_1(v_skipSuffix_x3f_2472_, v___x_2475_);
if (lean_obj_tag(v___x_2476_) == 0)
{
return v___x_2476_;
}
else
{
lean_object* v_val_2477_; lean_object* v___x_2479_; uint8_t v_isShared_2480_; uint8_t v_isSharedCheck_2484_; 
v_val_2477_ = lean_ctor_get(v___x_2476_, 0);
v_isSharedCheck_2484_ = !lean_is_exclusive(v___x_2476_);
if (v_isSharedCheck_2484_ == 0)
{
v___x_2479_ = v___x_2476_;
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
else
{
lean_inc(v_val_2477_);
lean_dec(v___x_2476_);
v___x_2479_ = lean_box(0);
v_isShared_2480_ = v_isSharedCheck_2484_;
goto v_resetjp_2478_;
}
v_resetjp_2478_:
{
lean_object* v___x_2482_; 
if (v_isShared_2480_ == 0)
{
v___x_2482_ = v___x_2479_;
goto v_reusejp_2481_;
}
else
{
lean_object* v_reuseFailAlloc_2483_; 
v_reuseFailAlloc_2483_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2483_, 0, v_val_2477_);
v___x_2482_ = v_reuseFailAlloc_2483_;
goto v_reusejp_2481_;
}
v_reusejp_2481_:
{
return v___x_2482_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkip_x3f___boxed(lean_object* v_00_u03c1_2488_, lean_object* v_s_2489_, lean_object* v_pos_2490_, lean_object* v_pat_2491_, lean_object* v_inst_2492_){
_start:
{
lean_object* v_res_2493_; 
v_res_2493_ = l_String_Slice_Pos_revSkip_x3f(v_00_u03c1_2488_, v_s_2489_, v_pos_2490_, v_pat_2491_, v_inst_2492_);
lean_dec(v_pat_2491_);
lean_dec(v_pos_2490_);
return v_res_2493_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___redArg(lean_object* v_s_2494_, lean_object* v_inst_2495_){
_start:
{
lean_object* v_skipSuffix_x3f_2496_; lean_object* v___x_2497_; 
v_skipSuffix_x3f_2496_ = lean_ctor_get(v_inst_2495_, 0);
lean_inc_ref(v_skipSuffix_x3f_2496_);
lean_dec_ref(v_inst_2495_);
lean_inc_ref(v_s_2494_);
v___x_2497_ = lean_apply_1(v_skipSuffix_x3f_2496_, v_s_2494_);
if (lean_obj_tag(v___x_2497_) == 0)
{
lean_object* v___x_2498_; 
lean_dec_ref(v_s_2494_);
v___x_2498_ = lean_box(0);
return v___x_2498_;
}
else
{
lean_object* v_val_2499_; lean_object* v___x_2501_; uint8_t v_isShared_2502_; uint8_t v_isSharedCheck_2517_; 
v_val_2499_ = lean_ctor_get(v___x_2497_, 0);
v_isSharedCheck_2517_ = !lean_is_exclusive(v___x_2497_);
if (v_isSharedCheck_2517_ == 0)
{
v___x_2501_ = v___x_2497_;
v_isShared_2502_ = v_isSharedCheck_2517_;
goto v_resetjp_2500_;
}
else
{
lean_inc(v_val_2499_);
lean_dec(v___x_2497_);
v___x_2501_ = lean_box(0);
v_isShared_2502_ = v_isSharedCheck_2517_;
goto v_resetjp_2500_;
}
v_resetjp_2500_:
{
lean_object* v_str_2503_; lean_object* v_startInclusive_2504_; lean_object* v___x_2506_; uint8_t v_isShared_2507_; uint8_t v_isSharedCheck_2515_; 
v_str_2503_ = lean_ctor_get(v_s_2494_, 0);
v_startInclusive_2504_ = lean_ctor_get(v_s_2494_, 1);
v_isSharedCheck_2515_ = !lean_is_exclusive(v_s_2494_);
if (v_isSharedCheck_2515_ == 0)
{
lean_object* v_unused_2516_; 
v_unused_2516_ = lean_ctor_get(v_s_2494_, 2);
lean_dec(v_unused_2516_);
v___x_2506_ = v_s_2494_;
v_isShared_2507_ = v_isSharedCheck_2515_;
goto v_resetjp_2505_;
}
else
{
lean_inc(v_startInclusive_2504_);
lean_inc(v_str_2503_);
lean_dec(v_s_2494_);
v___x_2506_ = lean_box(0);
v_isShared_2507_ = v_isSharedCheck_2515_;
goto v_resetjp_2505_;
}
v_resetjp_2505_:
{
lean_object* v___x_2508_; lean_object* v___x_2510_; 
v___x_2508_ = lean_nat_add(v_startInclusive_2504_, v_val_2499_);
lean_dec(v_val_2499_);
if (v_isShared_2507_ == 0)
{
lean_ctor_set(v___x_2506_, 2, v___x_2508_);
v___x_2510_ = v___x_2506_;
goto v_reusejp_2509_;
}
else
{
lean_object* v_reuseFailAlloc_2514_; 
v_reuseFailAlloc_2514_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2514_, 0, v_str_2503_);
lean_ctor_set(v_reuseFailAlloc_2514_, 1, v_startInclusive_2504_);
lean_ctor_set(v_reuseFailAlloc_2514_, 2, v___x_2508_);
v___x_2510_ = v_reuseFailAlloc_2514_;
goto v_reusejp_2509_;
}
v_reusejp_2509_:
{
lean_object* v___x_2512_; 
if (v_isShared_2502_ == 0)
{
lean_ctor_set(v___x_2501_, 0, v___x_2510_);
v___x_2512_ = v___x_2501_;
goto v_reusejp_2511_;
}
else
{
lean_object* v_reuseFailAlloc_2513_; 
v_reuseFailAlloc_2513_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2513_, 0, v___x_2510_);
v___x_2512_ = v_reuseFailAlloc_2513_;
goto v_reusejp_2511_;
}
v_reusejp_2511_:
{
return v___x_2512_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f(lean_object* v_00_u03c1_2518_, lean_object* v_s_2519_, lean_object* v_pat_2520_, lean_object* v_inst_2521_){
_start:
{
lean_object* v_skipSuffix_x3f_2522_; lean_object* v___x_2523_; 
v_skipSuffix_x3f_2522_ = lean_ctor_get(v_inst_2521_, 0);
lean_inc_ref(v_skipSuffix_x3f_2522_);
lean_dec_ref(v_inst_2521_);
lean_inc_ref(v_s_2519_);
v___x_2523_ = lean_apply_1(v_skipSuffix_x3f_2522_, v_s_2519_);
if (lean_obj_tag(v___x_2523_) == 0)
{
lean_object* v___x_2524_; 
lean_dec_ref(v_s_2519_);
v___x_2524_ = lean_box(0);
return v___x_2524_;
}
else
{
lean_object* v_val_2525_; lean_object* v___x_2527_; uint8_t v_isShared_2528_; uint8_t v_isSharedCheck_2543_; 
v_val_2525_ = lean_ctor_get(v___x_2523_, 0);
v_isSharedCheck_2543_ = !lean_is_exclusive(v___x_2523_);
if (v_isSharedCheck_2543_ == 0)
{
v___x_2527_ = v___x_2523_;
v_isShared_2528_ = v_isSharedCheck_2543_;
goto v_resetjp_2526_;
}
else
{
lean_inc(v_val_2525_);
lean_dec(v___x_2523_);
v___x_2527_ = lean_box(0);
v_isShared_2528_ = v_isSharedCheck_2543_;
goto v_resetjp_2526_;
}
v_resetjp_2526_:
{
lean_object* v_str_2529_; lean_object* v_startInclusive_2530_; lean_object* v___x_2532_; uint8_t v_isShared_2533_; uint8_t v_isSharedCheck_2541_; 
v_str_2529_ = lean_ctor_get(v_s_2519_, 0);
v_startInclusive_2530_ = lean_ctor_get(v_s_2519_, 1);
v_isSharedCheck_2541_ = !lean_is_exclusive(v_s_2519_);
if (v_isSharedCheck_2541_ == 0)
{
lean_object* v_unused_2542_; 
v_unused_2542_ = lean_ctor_get(v_s_2519_, 2);
lean_dec(v_unused_2542_);
v___x_2532_ = v_s_2519_;
v_isShared_2533_ = v_isSharedCheck_2541_;
goto v_resetjp_2531_;
}
else
{
lean_inc(v_startInclusive_2530_);
lean_inc(v_str_2529_);
lean_dec(v_s_2519_);
v___x_2532_ = lean_box(0);
v_isShared_2533_ = v_isSharedCheck_2541_;
goto v_resetjp_2531_;
}
v_resetjp_2531_:
{
lean_object* v___x_2534_; lean_object* v___x_2536_; 
v___x_2534_ = lean_nat_add(v_startInclusive_2530_, v_val_2525_);
lean_dec(v_val_2525_);
if (v_isShared_2533_ == 0)
{
lean_ctor_set(v___x_2532_, 2, v___x_2534_);
v___x_2536_ = v___x_2532_;
goto v_reusejp_2535_;
}
else
{
lean_object* v_reuseFailAlloc_2540_; 
v_reuseFailAlloc_2540_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2540_, 0, v_str_2529_);
lean_ctor_set(v_reuseFailAlloc_2540_, 1, v_startInclusive_2530_);
lean_ctor_set(v_reuseFailAlloc_2540_, 2, v___x_2534_);
v___x_2536_ = v_reuseFailAlloc_2540_;
goto v_reusejp_2535_;
}
v_reusejp_2535_:
{
lean_object* v___x_2538_; 
if (v_isShared_2528_ == 0)
{
lean_ctor_set(v___x_2527_, 0, v___x_2536_);
v___x_2538_ = v___x_2527_;
goto v_reusejp_2537_;
}
else
{
lean_object* v_reuseFailAlloc_2539_; 
v_reuseFailAlloc_2539_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_2539_, 0, v___x_2536_);
v___x_2538_ = v_reuseFailAlloc_2539_;
goto v_reusejp_2537_;
}
v_reusejp_2537_:
{
return v___x_2538_;
}
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix_x3f___boxed(lean_object* v_00_u03c1_2544_, lean_object* v_s_2545_, lean_object* v_pat_2546_, lean_object* v_inst_2547_){
_start:
{
lean_object* v_res_2548_; 
v_res_2548_ = l_String_Slice_dropSuffix_x3f(v_00_u03c1_2544_, v_s_2545_, v_pat_2546_, v_inst_2547_);
lean_dec(v_pat_2546_);
return v_res_2548_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___redArg(lean_object* v_s_2549_, lean_object* v_inst_2550_){
_start:
{
lean_object* v_skipSuffix_x3f_2551_; lean_object* v___x_2552_; 
v_skipSuffix_x3f_2551_ = lean_ctor_get(v_inst_2550_, 0);
lean_inc_ref(v_skipSuffix_x3f_2551_);
lean_dec_ref(v_inst_2550_);
lean_inc_ref(v_s_2549_);
v___x_2552_ = lean_apply_1(v_skipSuffix_x3f_2551_, v_s_2549_);
if (lean_obj_tag(v___x_2552_) == 0)
{
return v_s_2549_;
}
else
{
lean_object* v_val_2553_; lean_object* v_str_2554_; lean_object* v_startInclusive_2555_; lean_object* v___x_2557_; uint8_t v_isShared_2558_; uint8_t v_isSharedCheck_2563_; 
v_val_2553_ = lean_ctor_get(v___x_2552_, 0);
lean_inc(v_val_2553_);
lean_dec_ref_known(v___x_2552_, 1);
v_str_2554_ = lean_ctor_get(v_s_2549_, 0);
v_startInclusive_2555_ = lean_ctor_get(v_s_2549_, 1);
v_isSharedCheck_2563_ = !lean_is_exclusive(v_s_2549_);
if (v_isSharedCheck_2563_ == 0)
{
lean_object* v_unused_2564_; 
v_unused_2564_ = lean_ctor_get(v_s_2549_, 2);
lean_dec(v_unused_2564_);
v___x_2557_ = v_s_2549_;
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
else
{
lean_inc(v_startInclusive_2555_);
lean_inc(v_str_2554_);
lean_dec(v_s_2549_);
v___x_2557_ = lean_box(0);
v_isShared_2558_ = v_isSharedCheck_2563_;
goto v_resetjp_2556_;
}
v_resetjp_2556_:
{
lean_object* v___x_2559_; lean_object* v___x_2561_; 
v___x_2559_ = lean_nat_add(v_startInclusive_2555_, v_val_2553_);
lean_dec(v_val_2553_);
if (v_isShared_2558_ == 0)
{
lean_ctor_set(v___x_2557_, 2, v___x_2559_);
v___x_2561_ = v___x_2557_;
goto v_reusejp_2560_;
}
else
{
lean_object* v_reuseFailAlloc_2562_; 
v_reuseFailAlloc_2562_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2562_, 0, v_str_2554_);
lean_ctor_set(v_reuseFailAlloc_2562_, 1, v_startInclusive_2555_);
lean_ctor_set(v_reuseFailAlloc_2562_, 2, v___x_2559_);
v___x_2561_ = v_reuseFailAlloc_2562_;
goto v_reusejp_2560_;
}
v_reusejp_2560_:
{
return v___x_2561_;
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix(lean_object* v_00_u03c1_2565_, lean_object* v_s_2566_, lean_object* v_pat_2567_, lean_object* v_inst_2568_){
_start:
{
lean_object* v___x_2569_; 
v___x_2569_ = l_String_Slice_dropSuffix___redArg(v_s_2566_, v_inst_2568_);
return v___x_2569_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropSuffix___boxed(lean_object* v_00_u03c1_2570_, lean_object* v_s_2571_, lean_object* v_pat_2572_, lean_object* v_inst_2573_){
_start:
{
lean_object* v_res_2574_; 
v_res_2574_ = l_String_Slice_dropSuffix(v_00_u03c1_2570_, v_s_2571_, v_pat_2572_, v_inst_2573_);
lean_dec(v_pat_2572_);
return v_res_2574_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEnd(lean_object* v_s_2575_, lean_object* v_n_2576_){
_start:
{
lean_object* v_str_2577_; lean_object* v_startInclusive_2578_; lean_object* v_endExclusive_2579_; lean_object* v___x_2580_; lean_object* v___x_2581_; lean_object* v___x_2583_; uint8_t v_isShared_2584_; uint8_t v_isSharedCheck_2589_; 
v_str_2577_ = lean_ctor_get(v_s_2575_, 0);
lean_inc_ref(v_str_2577_);
v_startInclusive_2578_ = lean_ctor_get(v_s_2575_, 1);
lean_inc(v_startInclusive_2578_);
v_endExclusive_2579_ = lean_ctor_get(v_s_2575_, 2);
v___x_2580_ = lean_nat_sub(v_endExclusive_2579_, v_startInclusive_2578_);
v___x_2581_ = l_String_Slice_Pos_prevn(v_s_2575_, v___x_2580_, v_n_2576_);
v_isSharedCheck_2589_ = !lean_is_exclusive(v_s_2575_);
if (v_isSharedCheck_2589_ == 0)
{
lean_object* v_unused_2590_; lean_object* v_unused_2591_; lean_object* v_unused_2592_; 
v_unused_2590_ = lean_ctor_get(v_s_2575_, 2);
lean_dec(v_unused_2590_);
v_unused_2591_ = lean_ctor_get(v_s_2575_, 1);
lean_dec(v_unused_2591_);
v_unused_2592_ = lean_ctor_get(v_s_2575_, 0);
lean_dec(v_unused_2592_);
v___x_2583_ = v_s_2575_;
v_isShared_2584_ = v_isSharedCheck_2589_;
goto v_resetjp_2582_;
}
else
{
lean_dec(v_s_2575_);
v___x_2583_ = lean_box(0);
v_isShared_2584_ = v_isSharedCheck_2589_;
goto v_resetjp_2582_;
}
v_resetjp_2582_:
{
lean_object* v___x_2585_; lean_object* v___x_2587_; 
v___x_2585_ = lean_nat_add(v_startInclusive_2578_, v___x_2581_);
lean_dec(v___x_2581_);
if (v_isShared_2584_ == 0)
{
lean_ctor_set(v___x_2583_, 2, v___x_2585_);
v___x_2587_ = v___x_2583_;
goto v_reusejp_2586_;
}
else
{
lean_object* v_reuseFailAlloc_2588_; 
v_reuseFailAlloc_2588_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2588_, 0, v_str_2577_);
lean_ctor_set(v_reuseFailAlloc_2588_, 1, v_startInclusive_2578_);
lean_ctor_set(v_reuseFailAlloc_2588_, 2, v___x_2585_);
v___x_2587_ = v_reuseFailAlloc_2588_;
goto v_reusejp_2586_;
}
v_reusejp_2586_:
{
return v___x_2587_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg(lean_object* v_s_2593_, lean_object* v_pos_2594_, lean_object* v_inst_2595_){
_start:
{
lean_object* v_str_2596_; lean_object* v_startInclusive_2597_; lean_object* v_skipSuffix_x3f_2598_; lean_object* v___x_2599_; lean_object* v___x_2600_; lean_object* v___x_2601_; 
v_str_2596_ = lean_ctor_get(v_s_2593_, 0);
v_startInclusive_2597_ = lean_ctor_get(v_s_2593_, 1);
v_skipSuffix_x3f_2598_ = lean_ctor_get(v_inst_2595_, 0);
v___x_2599_ = lean_nat_add(v_startInclusive_2597_, v_pos_2594_);
lean_inc(v_startInclusive_2597_);
lean_inc_ref(v_str_2596_);
v___x_2600_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2600_, 0, v_str_2596_);
lean_ctor_set(v___x_2600_, 1, v_startInclusive_2597_);
lean_ctor_set(v___x_2600_, 2, v___x_2599_);
lean_inc_ref(v_skipSuffix_x3f_2598_);
v___x_2601_ = lean_apply_1(v_skipSuffix_x3f_2598_, v___x_2600_);
if (lean_obj_tag(v___x_2601_) == 0)
{
lean_dec_ref(v_inst_2595_);
return v_pos_2594_;
}
else
{
lean_object* v_val_2602_; lean_object* v___x_2603_; lean_object* v___x_2604_; uint8_t v___x_2605_; 
v_val_2602_ = lean_ctor_get(v___x_2601_, 0);
lean_inc(v_val_2602_);
lean_dec_ref_known(v___x_2601_, 1);
v___x_2603_ = lean_unsigned_to_nat(1u);
v___x_2604_ = lean_nat_add(v_val_2602_, v___x_2603_);
v___x_2605_ = lean_nat_dec_le(v___x_2604_, v_pos_2594_);
lean_dec(v___x_2604_);
if (v___x_2605_ == 0)
{
lean_dec(v_val_2602_);
lean_dec_ref(v_inst_2595_);
return v_pos_2594_;
}
else
{
lean_dec(v_pos_2594_);
v_pos_2594_ = v_val_2602_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___redArg___boxed(lean_object* v_s_2607_, lean_object* v_pos_2608_, lean_object* v_inst_2609_){
_start:
{
lean_object* v_res_2610_; 
v_res_2610_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2607_, v_pos_2608_, v_inst_2609_);
lean_dec_ref(v_s_2607_);
return v_res_2610_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile(lean_object* v_00_u03c1_2611_, lean_object* v_s_2612_, lean_object* v_pos_2613_, lean_object* v_pat_2614_, lean_object* v_inst_2615_){
_start:
{
lean_object* v___x_2616_; 
v___x_2616_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2612_, v_pos_2613_, v_inst_2615_);
return v___x_2616_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___boxed(lean_object* v_00_u03c1_2617_, lean_object* v_s_2618_, lean_object* v_pos_2619_, lean_object* v_pat_2620_, lean_object* v_inst_2621_){
_start:
{
lean_object* v_res_2622_; 
v_res_2622_ = l_String_Slice_Pos_revSkipWhile(v_00_u03c1_2617_, v_s_2618_, v_pos_2619_, v_pat_2620_, v_inst_2621_);
lean_dec(v_pat_2620_);
lean_dec_ref(v_s_2618_);
return v_res_2622_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg(lean_object* v_s_2623_, lean_object* v_inst_2624_){
_start:
{
lean_object* v_startInclusive_2625_; lean_object* v_endExclusive_2626_; lean_object* v___x_2627_; lean_object* v___x_2628_; 
v_startInclusive_2625_ = lean_ctor_get(v_s_2623_, 1);
v_endExclusive_2626_ = lean_ctor_get(v_s_2623_, 2);
v___x_2627_ = lean_nat_sub(v_endExclusive_2626_, v_startInclusive_2625_);
v___x_2628_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2623_, v___x_2627_, v_inst_2624_);
return v___x_2628_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___redArg___boxed(lean_object* v_s_2629_, lean_object* v_inst_2630_){
_start:
{
lean_object* v_res_2631_; 
v_res_2631_ = l_String_Slice_skipSuffixWhile___redArg(v_s_2629_, v_inst_2630_);
lean_dec_ref(v_s_2629_);
return v_res_2631_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile(lean_object* v_00_u03c1_2632_, lean_object* v_s_2633_, lean_object* v_pat_2634_, lean_object* v_inst_2635_){
_start:
{
lean_object* v_startInclusive_2636_; lean_object* v_endExclusive_2637_; lean_object* v___x_2638_; lean_object* v___x_2639_; 
v_startInclusive_2636_ = lean_ctor_get(v_s_2633_, 1);
v_endExclusive_2637_ = lean_ctor_get(v_s_2633_, 2);
v___x_2638_ = lean_nat_sub(v_endExclusive_2637_, v_startInclusive_2636_);
v___x_2639_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2633_, v___x_2638_, v_inst_2635_);
return v___x_2639_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_skipSuffixWhile___boxed(lean_object* v_00_u03c1_2640_, lean_object* v_s_2641_, lean_object* v_pat_2642_, lean_object* v_inst_2643_){
_start:
{
lean_object* v_res_2644_; 
v_res_2644_ = l_String_Slice_skipSuffixWhile(v_00_u03c1_2640_, v_s_2641_, v_pat_2642_, v_inst_2643_);
lean_dec(v_pat_2642_);
lean_dec_ref(v_s_2641_);
return v_res_2644_;
}
}
uint8_t l_String_Slice_revAll___redArg(lean_object* v_s_2645_, lean_object* v_inst_2646_){
_start:
{
lean_object* v_startInclusive_2647_; lean_object* v_endExclusive_2648_; lean_object* v___x_2649_; lean_object* v___x_2650_; lean_object* v___x_2651_; uint8_t v_decide_2652_; 
v_startInclusive_2647_ = lean_ctor_get(v_s_2645_, 1);
v_endExclusive_2648_ = lean_ctor_get(v_s_2645_, 2);
v___x_2649_ = lean_nat_sub(v_endExclusive_2648_, v_startInclusive_2647_);
v___x_2650_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2645_, v___x_2649_, v_inst_2646_);
v___x_2651_ = lean_unsigned_to_nat(0u);
v_decide_2652_ = lean_nat_dec_eq(v___x_2650_, v___x_2651_);
lean_dec(v___x_2650_);
return v_decide_2652_;
}
}
LEAN_EXPORT void l_String_Slice_revAll___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2645_ = stack[0].m_obj;
lean_object* v_inst_2646_ = stack[1].m_obj;
uint8_t v_res_2653_;
v_res_2653_ = l_String_Slice_revAll___redArg(v_s_2645_, v_inst_2646_);
stack->m_num = v_res_2653_;
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___redArg___boxed(lean_object* v_s_2654_, lean_object* v_inst_2655_){
_start:
{
uint8_t v_res_2656_; lean_object* v_r_2657_; 
v_res_2656_ = l_String_Slice_revAll___redArg(v_s_2654_, v_inst_2655_);
lean_dec_ref(v_s_2654_);
v_r_2657_ = lean_box(v_res_2656_);
return v_r_2657_;
}
}
uint8_t l_String_Slice_revAll(lean_object* v_00_u03c1_2658_, lean_object* v_s_2659_, lean_object* v_pat_2660_, lean_object* v_inst_2661_){
_start:
{
lean_object* v_startInclusive_2662_; lean_object* v_endExclusive_2663_; lean_object* v___x_2664_; lean_object* v___x_2665_; lean_object* v___x_2666_; uint8_t v_decide_2667_; 
v_startInclusive_2662_ = lean_ctor_get(v_s_2659_, 1);
v_endExclusive_2663_ = lean_ctor_get(v_s_2659_, 2);
v___x_2664_ = lean_nat_sub(v_endExclusive_2663_, v_startInclusive_2662_);
v___x_2665_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2659_, v___x_2664_, v_inst_2661_);
v___x_2666_ = lean_unsigned_to_nat(0u);
v_decide_2667_ = lean_nat_dec_eq(v___x_2665_, v___x_2666_);
lean_dec(v___x_2665_);
return v_decide_2667_;
}
}
LEAN_EXPORT void l_String_Slice_revAll_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_2659_ = stack[1].m_obj;
lean_object* v_pat_2660_ = stack[2].m_obj;
lean_object* v_inst_2661_ = stack[3].m_obj;
uint8_t v_res_2668_;
v_res_2668_ = l_String_Slice_revAll(lean_box(0), v_s_2659_, v_pat_2660_, v_inst_2661_);
stack->m_num = v_res_2668_;
}
LEAN_EXPORT lean_object* l_String_Slice_revAll___boxed(lean_object* v_00_u03c1_2669_, lean_object* v_s_2670_, lean_object* v_pat_2671_, lean_object* v_inst_2672_){
_start:
{
uint8_t v_res_2673_; lean_object* v_r_2674_; 
v_res_2673_ = l_String_Slice_revAll(v_00_u03c1_2669_, v_s_2670_, v_pat_2671_, v_inst_2672_);
lean_dec(v_pat_2671_);
lean_dec_ref(v_s_2670_);
v_r_2674_ = lean_box(v_res_2673_);
return v_r_2674_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___redArg(lean_object* v_s_2675_, lean_object* v_inst_2676_){
_start:
{
lean_object* v_str_2677_; lean_object* v_startInclusive_2678_; lean_object* v_endExclusive_2679_; lean_object* v___x_2680_; lean_object* v___x_2681_; lean_object* v___x_2683_; uint8_t v_isShared_2684_; uint8_t v_isSharedCheck_2689_; 
v_str_2677_ = lean_ctor_get(v_s_2675_, 0);
lean_inc_ref(v_str_2677_);
v_startInclusive_2678_ = lean_ctor_get(v_s_2675_, 1);
lean_inc(v_startInclusive_2678_);
v_endExclusive_2679_ = lean_ctor_get(v_s_2675_, 2);
v___x_2680_ = lean_nat_sub(v_endExclusive_2679_, v_startInclusive_2678_);
v___x_2681_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2675_, v___x_2680_, v_inst_2676_);
v_isSharedCheck_2689_ = !lean_is_exclusive(v_s_2675_);
if (v_isSharedCheck_2689_ == 0)
{
lean_object* v_unused_2690_; lean_object* v_unused_2691_; lean_object* v_unused_2692_; 
v_unused_2690_ = lean_ctor_get(v_s_2675_, 2);
lean_dec(v_unused_2690_);
v_unused_2691_ = lean_ctor_get(v_s_2675_, 1);
lean_dec(v_unused_2691_);
v_unused_2692_ = lean_ctor_get(v_s_2675_, 0);
lean_dec(v_unused_2692_);
v___x_2683_ = v_s_2675_;
v_isShared_2684_ = v_isSharedCheck_2689_;
goto v_resetjp_2682_;
}
else
{
lean_dec(v_s_2675_);
v___x_2683_ = lean_box(0);
v_isShared_2684_ = v_isSharedCheck_2689_;
goto v_resetjp_2682_;
}
v_resetjp_2682_:
{
lean_object* v___x_2685_; lean_object* v___x_2687_; 
v___x_2685_ = lean_nat_add(v_startInclusive_2678_, v___x_2681_);
lean_dec(v___x_2681_);
if (v_isShared_2684_ == 0)
{
lean_ctor_set(v___x_2683_, 2, v___x_2685_);
v___x_2687_ = v___x_2683_;
goto v_reusejp_2686_;
}
else
{
lean_object* v_reuseFailAlloc_2688_; 
v_reuseFailAlloc_2688_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2688_, 0, v_str_2677_);
lean_ctor_set(v_reuseFailAlloc_2688_, 1, v_startInclusive_2678_);
lean_ctor_set(v_reuseFailAlloc_2688_, 2, v___x_2685_);
v___x_2687_ = v_reuseFailAlloc_2688_;
goto v_reusejp_2686_;
}
v_reusejp_2686_:
{
return v___x_2687_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile(lean_object* v_00_u03c1_2693_, lean_object* v_s_2694_, lean_object* v_pat_2695_, lean_object* v_inst_2696_){
_start:
{
lean_object* v_str_2697_; lean_object* v_startInclusive_2698_; lean_object* v_endExclusive_2699_; lean_object* v___x_2700_; lean_object* v___x_2701_; lean_object* v___x_2703_; uint8_t v_isShared_2704_; uint8_t v_isSharedCheck_2709_; 
v_str_2697_ = lean_ctor_get(v_s_2694_, 0);
lean_inc_ref(v_str_2697_);
v_startInclusive_2698_ = lean_ctor_get(v_s_2694_, 1);
lean_inc(v_startInclusive_2698_);
v_endExclusive_2699_ = lean_ctor_get(v_s_2694_, 2);
v___x_2700_ = lean_nat_sub(v_endExclusive_2699_, v_startInclusive_2698_);
v___x_2701_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2694_, v___x_2700_, v_inst_2696_);
v_isSharedCheck_2709_ = !lean_is_exclusive(v_s_2694_);
if (v_isSharedCheck_2709_ == 0)
{
lean_object* v_unused_2710_; lean_object* v_unused_2711_; lean_object* v_unused_2712_; 
v_unused_2710_ = lean_ctor_get(v_s_2694_, 2);
lean_dec(v_unused_2710_);
v_unused_2711_ = lean_ctor_get(v_s_2694_, 1);
lean_dec(v_unused_2711_);
v_unused_2712_ = lean_ctor_get(v_s_2694_, 0);
lean_dec(v_unused_2712_);
v___x_2703_ = v_s_2694_;
v_isShared_2704_ = v_isSharedCheck_2709_;
goto v_resetjp_2702_;
}
else
{
lean_dec(v_s_2694_);
v___x_2703_ = lean_box(0);
v_isShared_2704_ = v_isSharedCheck_2709_;
goto v_resetjp_2702_;
}
v_resetjp_2702_:
{
lean_object* v___x_2705_; lean_object* v___x_2707_; 
v___x_2705_ = lean_nat_add(v_startInclusive_2698_, v___x_2701_);
lean_dec(v___x_2701_);
if (v_isShared_2704_ == 0)
{
lean_ctor_set(v___x_2703_, 2, v___x_2705_);
v___x_2707_ = v___x_2703_;
goto v_reusejp_2706_;
}
else
{
lean_object* v_reuseFailAlloc_2708_; 
v_reuseFailAlloc_2708_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2708_, 0, v_str_2697_);
lean_ctor_set(v_reuseFailAlloc_2708_, 1, v_startInclusive_2698_);
lean_ctor_set(v_reuseFailAlloc_2708_, 2, v___x_2705_);
v___x_2707_ = v_reuseFailAlloc_2708_;
goto v_reusejp_2706_;
}
v_reusejp_2706_:
{
return v___x_2707_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_dropEndWhile___boxed(lean_object* v_00_u03c1_2713_, lean_object* v_s_2714_, lean_object* v_pat_2715_, lean_object* v_inst_2716_){
_start:
{
lean_object* v_res_2717_; 
v_res_2717_ = l_String_Slice_dropEndWhile(v_00_u03c1_2713_, v_s_2714_, v_pat_2715_, v_inst_2716_);
lean_dec(v_pat_2715_);
return v_res_2717_;
}
}
static lean_object* _init_l_String_Slice_trimAsciiEnd___closed__0(void){
_start:
{
lean_object* v___x_2718_; lean_object* v___x_2719_; 
v___x_2718_ = ((lean_object*)(l_String_Slice_trimAsciiStart___closed__0));
v___x_2719_ = l_String_Slice_Pattern_CharPred_instBackwardPatternForallCharBool(v___x_2718_);
return v___x_2719_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAsciiEnd(lean_object* v_s_2720_){
_start:
{
lean_object* v___x_2721_; lean_object* v_str_2722_; lean_object* v_startInclusive_2723_; lean_object* v_endExclusive_2724_; lean_object* v___x_2725_; lean_object* v___x_2726_; lean_object* v___x_2728_; uint8_t v_isShared_2729_; uint8_t v_isSharedCheck_2734_; 
v___x_2721_ = lean_obj_once(&l_String_Slice_trimAsciiEnd___closed__0, &l_String_Slice_trimAsciiEnd___closed__0_once, _init_l_String_Slice_trimAsciiEnd___closed__0);
v_str_2722_ = lean_ctor_get(v_s_2720_, 0);
lean_inc_ref(v_str_2722_);
v_startInclusive_2723_ = lean_ctor_get(v_s_2720_, 1);
lean_inc(v_startInclusive_2723_);
v_endExclusive_2724_ = lean_ctor_get(v_s_2720_, 2);
v___x_2725_ = lean_nat_sub(v_endExclusive_2724_, v_startInclusive_2723_);
v___x_2726_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2720_, v___x_2725_, v___x_2721_);
v_isSharedCheck_2734_ = !lean_is_exclusive(v_s_2720_);
if (v_isSharedCheck_2734_ == 0)
{
lean_object* v_unused_2735_; lean_object* v_unused_2736_; lean_object* v_unused_2737_; 
v_unused_2735_ = lean_ctor_get(v_s_2720_, 2);
lean_dec(v_unused_2735_);
v_unused_2736_ = lean_ctor_get(v_s_2720_, 1);
lean_dec(v_unused_2736_);
v_unused_2737_ = lean_ctor_get(v_s_2720_, 0);
lean_dec(v_unused_2737_);
v___x_2728_ = v_s_2720_;
v_isShared_2729_ = v_isSharedCheck_2734_;
goto v_resetjp_2727_;
}
else
{
lean_dec(v_s_2720_);
v___x_2728_ = lean_box(0);
v_isShared_2729_ = v_isSharedCheck_2734_;
goto v_resetjp_2727_;
}
v_resetjp_2727_:
{
lean_object* v___x_2730_; lean_object* v___x_2732_; 
v___x_2730_ = lean_nat_add(v_startInclusive_2723_, v___x_2726_);
lean_dec(v___x_2726_);
if (v_isShared_2729_ == 0)
{
lean_ctor_set(v___x_2728_, 2, v___x_2730_);
v___x_2732_ = v___x_2728_;
goto v_reusejp_2731_;
}
else
{
lean_object* v_reuseFailAlloc_2733_; 
v_reuseFailAlloc_2733_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2733_, 0, v_str_2722_);
lean_ctor_set(v_reuseFailAlloc_2733_, 1, v_startInclusive_2723_);
lean_ctor_set(v_reuseFailAlloc_2733_, 2, v___x_2730_);
v___x_2732_ = v_reuseFailAlloc_2733_;
goto v_reusejp_2731_;
}
v_reusejp_2731_:
{
return v___x_2732_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEnd(lean_object* v_s_2738_, lean_object* v_n_2739_){
_start:
{
lean_object* v_str_2740_; lean_object* v_startInclusive_2741_; lean_object* v_endExclusive_2742_; lean_object* v___x_2743_; lean_object* v___x_2744_; lean_object* v___x_2746_; uint8_t v_isShared_2747_; uint8_t v_isSharedCheck_2752_; 
v_str_2740_ = lean_ctor_get(v_s_2738_, 0);
lean_inc_ref(v_str_2740_);
v_startInclusive_2741_ = lean_ctor_get(v_s_2738_, 1);
lean_inc(v_startInclusive_2741_);
v_endExclusive_2742_ = lean_ctor_get(v_s_2738_, 2);
lean_inc(v_endExclusive_2742_);
v___x_2743_ = lean_nat_sub(v_endExclusive_2742_, v_startInclusive_2741_);
v___x_2744_ = l_String_Slice_Pos_prevn(v_s_2738_, v___x_2743_, v_n_2739_);
v_isSharedCheck_2752_ = !lean_is_exclusive(v_s_2738_);
if (v_isSharedCheck_2752_ == 0)
{
lean_object* v_unused_2753_; lean_object* v_unused_2754_; lean_object* v_unused_2755_; 
v_unused_2753_ = lean_ctor_get(v_s_2738_, 2);
lean_dec(v_unused_2753_);
v_unused_2754_ = lean_ctor_get(v_s_2738_, 1);
lean_dec(v_unused_2754_);
v_unused_2755_ = lean_ctor_get(v_s_2738_, 0);
lean_dec(v_unused_2755_);
v___x_2746_ = v_s_2738_;
v_isShared_2747_ = v_isSharedCheck_2752_;
goto v_resetjp_2745_;
}
else
{
lean_dec(v_s_2738_);
v___x_2746_ = lean_box(0);
v_isShared_2747_ = v_isSharedCheck_2752_;
goto v_resetjp_2745_;
}
v_resetjp_2745_:
{
lean_object* v___x_2748_; lean_object* v___x_2750_; 
v___x_2748_ = lean_nat_add(v_startInclusive_2741_, v___x_2744_);
lean_dec(v___x_2744_);
lean_dec(v_startInclusive_2741_);
if (v_isShared_2747_ == 0)
{
lean_ctor_set(v___x_2746_, 1, v___x_2748_);
v___x_2750_ = v___x_2746_;
goto v_reusejp_2749_;
}
else
{
lean_object* v_reuseFailAlloc_2751_; 
v_reuseFailAlloc_2751_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2751_, 0, v_str_2740_);
lean_ctor_set(v_reuseFailAlloc_2751_, 1, v___x_2748_);
lean_ctor_set(v_reuseFailAlloc_2751_, 2, v_endExclusive_2742_);
v___x_2750_ = v_reuseFailAlloc_2751_;
goto v_reusejp_2749_;
}
v_reusejp_2749_:
{
return v___x_2750_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___redArg(lean_object* v_s_2756_, lean_object* v_inst_2757_){
_start:
{
lean_object* v_str_2758_; lean_object* v_startInclusive_2759_; lean_object* v_endExclusive_2760_; lean_object* v___x_2761_; lean_object* v___x_2762_; lean_object* v___x_2764_; uint8_t v_isShared_2765_; uint8_t v_isSharedCheck_2770_; 
v_str_2758_ = lean_ctor_get(v_s_2756_, 0);
lean_inc_ref(v_str_2758_);
v_startInclusive_2759_ = lean_ctor_get(v_s_2756_, 1);
lean_inc(v_startInclusive_2759_);
v_endExclusive_2760_ = lean_ctor_get(v_s_2756_, 2);
lean_inc(v_endExclusive_2760_);
v___x_2761_ = lean_nat_sub(v_endExclusive_2760_, v_startInclusive_2759_);
v___x_2762_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2756_, v___x_2761_, v_inst_2757_);
v_isSharedCheck_2770_ = !lean_is_exclusive(v_s_2756_);
if (v_isSharedCheck_2770_ == 0)
{
lean_object* v_unused_2771_; lean_object* v_unused_2772_; lean_object* v_unused_2773_; 
v_unused_2771_ = lean_ctor_get(v_s_2756_, 2);
lean_dec(v_unused_2771_);
v_unused_2772_ = lean_ctor_get(v_s_2756_, 1);
lean_dec(v_unused_2772_);
v_unused_2773_ = lean_ctor_get(v_s_2756_, 0);
lean_dec(v_unused_2773_);
v___x_2764_ = v_s_2756_;
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
else
{
lean_dec(v_s_2756_);
v___x_2764_ = lean_box(0);
v_isShared_2765_ = v_isSharedCheck_2770_;
goto v_resetjp_2763_;
}
v_resetjp_2763_:
{
lean_object* v___x_2766_; lean_object* v___x_2768_; 
v___x_2766_ = lean_nat_add(v_startInclusive_2759_, v___x_2762_);
lean_dec(v___x_2762_);
lean_dec(v_startInclusive_2759_);
if (v_isShared_2765_ == 0)
{
lean_ctor_set(v___x_2764_, 1, v___x_2766_);
v___x_2768_ = v___x_2764_;
goto v_reusejp_2767_;
}
else
{
lean_object* v_reuseFailAlloc_2769_; 
v_reuseFailAlloc_2769_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2769_, 0, v_str_2758_);
lean_ctor_set(v_reuseFailAlloc_2769_, 1, v___x_2766_);
lean_ctor_set(v_reuseFailAlloc_2769_, 2, v_endExclusive_2760_);
v___x_2768_ = v_reuseFailAlloc_2769_;
goto v_reusejp_2767_;
}
v_reusejp_2767_:
{
return v___x_2768_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile(lean_object* v_00_u03c1_2774_, lean_object* v_s_2775_, lean_object* v_pat_2776_, lean_object* v_inst_2777_){
_start:
{
lean_object* v_str_2778_; lean_object* v_startInclusive_2779_; lean_object* v_endExclusive_2780_; lean_object* v___x_2781_; lean_object* v___x_2782_; lean_object* v___x_2784_; uint8_t v_isShared_2785_; uint8_t v_isSharedCheck_2790_; 
v_str_2778_ = lean_ctor_get(v_s_2775_, 0);
lean_inc_ref(v_str_2778_);
v_startInclusive_2779_ = lean_ctor_get(v_s_2775_, 1);
lean_inc(v_startInclusive_2779_);
v_endExclusive_2780_ = lean_ctor_get(v_s_2775_, 2);
lean_inc(v_endExclusive_2780_);
v___x_2781_ = lean_nat_sub(v_endExclusive_2780_, v_startInclusive_2779_);
v___x_2782_ = l_String_Slice_Pos_revSkipWhile___redArg(v_s_2775_, v___x_2781_, v_inst_2777_);
v_isSharedCheck_2790_ = !lean_is_exclusive(v_s_2775_);
if (v_isSharedCheck_2790_ == 0)
{
lean_object* v_unused_2791_; lean_object* v_unused_2792_; lean_object* v_unused_2793_; 
v_unused_2791_ = lean_ctor_get(v_s_2775_, 2);
lean_dec(v_unused_2791_);
v_unused_2792_ = lean_ctor_get(v_s_2775_, 1);
lean_dec(v_unused_2792_);
v_unused_2793_ = lean_ctor_get(v_s_2775_, 0);
lean_dec(v_unused_2793_);
v___x_2784_ = v_s_2775_;
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
else
{
lean_dec(v_s_2775_);
v___x_2784_ = lean_box(0);
v_isShared_2785_ = v_isSharedCheck_2790_;
goto v_resetjp_2783_;
}
v_resetjp_2783_:
{
lean_object* v___x_2786_; lean_object* v___x_2788_; 
v___x_2786_ = lean_nat_add(v_startInclusive_2779_, v___x_2782_);
lean_dec(v___x_2782_);
lean_dec(v_startInclusive_2779_);
if (v_isShared_2785_ == 0)
{
lean_ctor_set(v___x_2784_, 1, v___x_2786_);
v___x_2788_ = v___x_2784_;
goto v_reusejp_2787_;
}
else
{
lean_object* v_reuseFailAlloc_2789_; 
v_reuseFailAlloc_2789_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2789_, 0, v_str_2778_);
lean_ctor_set(v_reuseFailAlloc_2789_, 1, v___x_2786_);
lean_ctor_set(v_reuseFailAlloc_2789_, 2, v_endExclusive_2780_);
v___x_2788_ = v_reuseFailAlloc_2789_;
goto v_reusejp_2787_;
}
v_reusejp_2787_:
{
return v___x_2788_;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_takeEndWhile___boxed(lean_object* v_00_u03c1_2794_, lean_object* v_s_2795_, lean_object* v_pat_2796_, lean_object* v_inst_2797_){
_start:
{
lean_object* v_res_2798_; 
v_res_2798_ = l_String_Slice_takeEndWhile(v_00_u03c1_2794_, v_s_2795_, v_pat_2796_, v_inst_2797_);
lean_dec(v_pat_2796_);
return v_res_2798_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___redArg(lean_object* v_inst_2799_, lean_object* v_s_2800_, lean_object* v_inst_2801_){
_start:
{
lean_object* v___f_2802_; lean_object* v_searcher_2803_; lean_object* v___x_2804_; lean_object* v___f_2805_; lean_object* v___x_2806_; 
v___f_2802_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__0));
lean_inc_ref(v_s_2800_);
v_searcher_2803_ = lean_apply_1(v_inst_2801_, v_s_2800_);
v___x_2804_ = lean_box(0);
v___f_2805_ = ((lean_object*)(l_String_Slice_find_x3f___redArg___closed__0));
v___x_2806_ = lean_apply_7(v_inst_2799_, v_s_2800_, v___f_2802_, lean_box(0), lean_box(0), v_searcher_2803_, v___x_2804_, v___f_2805_);
return v___x_2806_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f(lean_object* v_00_u03c3_2807_, lean_object* v_inst_2808_, lean_object* v_inst_2809_, lean_object* v_00_u03c1_2810_, lean_object* v_s_2811_, lean_object* v_pat_2812_, lean_object* v_inst_2813_){
_start:
{
lean_object* v___x_2814_; 
v___x_2814_ = l_String_Slice_revFind_x3f___redArg(v_inst_2809_, v_s_2811_, v_inst_2813_);
return v___x_2814_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_revFind_x3f___boxed(lean_object* v_00_u03c3_2815_, lean_object* v_inst_2816_, lean_object* v_inst_2817_, lean_object* v_00_u03c1_2818_, lean_object* v_s_2819_, lean_object* v_pat_2820_, lean_object* v_inst_2821_){
_start:
{
lean_object* v_res_2822_; 
v_res_2822_ = l_String_Slice_revFind_x3f(v_00_u03c3_2815_, v_inst_2816_, v_inst_2817_, v_00_u03c1_2818_, v_s_2819_, v_pat_2820_, v_inst_2821_);
lean_dec(v_pat_2820_);
lean_dec(v_inst_2816_);
return v_res_2822_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(lean_object* v_s_2823_, lean_object* v_pos_2824_){
_start:
{
lean_object* v_str_2825_; lean_object* v_startInclusive_2826_; lean_object* v_endExclusive_2827_; lean_object* v___x_2828_; lean_object* v___x_2837_; lean_object* v___x_2838_; uint8_t v_decide_2839_; 
v_str_2825_ = lean_ctor_get(v_s_2823_, 0);
v_startInclusive_2826_ = lean_ctor_get(v_s_2823_, 1);
v_endExclusive_2827_ = lean_ctor_get(v_s_2823_, 2);
v___x_2828_ = lean_nat_add(v_startInclusive_2826_, v_pos_2824_);
v___x_2837_ = lean_unsigned_to_nat(0u);
v___x_2838_ = lean_nat_sub(v_endExclusive_2827_, v___x_2828_);
v_decide_2839_ = lean_nat_dec_eq(v___x_2837_, v___x_2838_);
lean_dec(v___x_2838_);
if (v_decide_2839_ == 0)
{
uint32_t v___x_2840_; uint32_t v___x_2841_; uint8_t v___x_2842_; 
v___x_2840_ = lean_string_utf8_get_fast(v_str_2825_, v___x_2828_);
v___x_2841_ = 32;
v___x_2842_ = lean_uint32_dec_eq(v___x_2840_, v___x_2841_);
if (v___x_2842_ == 0)
{
uint32_t v___x_2843_; uint8_t v___x_2844_; 
v___x_2843_ = 9;
v___x_2844_ = lean_uint32_dec_eq(v___x_2840_, v___x_2843_);
if (v___x_2844_ == 0)
{
uint32_t v___x_2845_; uint8_t v___x_2846_; 
v___x_2845_ = 13;
v___x_2846_ = lean_uint32_dec_eq(v___x_2840_, v___x_2845_);
if (v___x_2846_ == 0)
{
uint32_t v___x_2847_; uint8_t v___x_2848_; 
v___x_2847_ = 10;
v___x_2848_ = lean_uint32_dec_eq(v___x_2840_, v___x_2847_);
if (v___x_2848_ == 0)
{
lean_dec(v___x_2828_);
return v_pos_2824_;
}
else
{
goto v___jp_2829_;
}
}
else
{
goto v___jp_2829_;
}
}
else
{
goto v___jp_2829_;
}
}
else
{
goto v___jp_2829_;
}
}
else
{
lean_dec(v___x_2828_);
return v_pos_2824_;
}
v___jp_2829_:
{
lean_object* v___x_2830_; lean_object* v___x_2831_; lean_object* v___x_2832_; lean_object* v___x_2833_; lean_object* v___x_2834_; uint8_t v___x_2835_; 
v___x_2830_ = lean_string_utf8_next_fast(v_str_2825_, v___x_2828_);
v___x_2831_ = lean_nat_sub(v___x_2830_, v___x_2828_);
lean_dec(v___x_2828_);
v___x_2832_ = lean_nat_add(v_pos_2824_, v___x_2831_);
lean_dec(v___x_2831_);
v___x_2833_ = lean_unsigned_to_nat(1u);
v___x_2834_ = lean_nat_add(v_pos_2824_, v___x_2833_);
v___x_2835_ = lean_nat_dec_le(v___x_2834_, v___x_2832_);
lean_dec(v___x_2834_);
if (v___x_2835_ == 0)
{
lean_dec(v___x_2832_);
return v_pos_2824_;
}
else
{
lean_dec(v_pos_2824_);
v_pos_2824_ = v___x_2832_;
goto _start;
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0___boxed(lean_object* v_s_2849_, lean_object* v_pos_2850_){
_start:
{
lean_object* v_res_2851_; 
v_res_2851_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2849_, v_pos_2850_);
lean_dec_ref(v_s_2849_);
return v_res_2851_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(lean_object* v_s_2852_, lean_object* v_pos_2853_){
_start:
{
lean_object* v_str_2854_; lean_object* v_startInclusive_2855_; lean_object* v___x_2856_; lean_object* v___x_2857_; lean_object* v___x_2858_; uint8_t v_decide_2859_; 
v_str_2854_ = lean_ctor_get(v_s_2852_, 0);
v_startInclusive_2855_ = lean_ctor_get(v_s_2852_, 1);
v___x_2856_ = lean_nat_add(v_startInclusive_2855_, v_pos_2853_);
v___x_2857_ = lean_nat_sub(v___x_2856_, v_startInclusive_2855_);
v___x_2858_ = lean_unsigned_to_nat(0u);
v_decide_2859_ = lean_nat_dec_eq(v___x_2857_, v___x_2858_);
if (v_decide_2859_ == 0)
{
lean_object* v___x_2860_; lean_object* v___x_2861_; lean_object* v___x_2862_; lean_object* v___x_2863_; lean_object* v___x_2868_; uint32_t v___x_2869_; uint32_t v___x_2870_; uint8_t v___x_2871_; 
lean_inc(v_startInclusive_2855_);
lean_inc_ref(v_str_2854_);
v___x_2860_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2860_, 0, v_str_2854_);
lean_ctor_set(v___x_2860_, 1, v_startInclusive_2855_);
lean_ctor_set(v___x_2860_, 2, v___x_2856_);
v___x_2861_ = lean_unsigned_to_nat(1u);
v___x_2862_ = lean_nat_sub(v___x_2857_, v___x_2861_);
lean_dec(v___x_2857_);
v___x_2863_ = l_String_Slice_posLE(v___x_2860_, v___x_2862_);
lean_dec_ref_known(v___x_2860_, 3);
v___x_2868_ = lean_nat_add(v_startInclusive_2855_, v___x_2863_);
v___x_2869_ = lean_string_utf8_get_fast(v_str_2854_, v___x_2868_);
lean_dec(v___x_2868_);
v___x_2870_ = 32;
v___x_2871_ = lean_uint32_dec_eq(v___x_2869_, v___x_2870_);
if (v___x_2871_ == 0)
{
uint32_t v___x_2872_; uint8_t v___x_2873_; 
v___x_2872_ = 9;
v___x_2873_ = lean_uint32_dec_eq(v___x_2869_, v___x_2872_);
if (v___x_2873_ == 0)
{
uint32_t v___x_2874_; uint8_t v___x_2875_; 
v___x_2874_ = 13;
v___x_2875_ = lean_uint32_dec_eq(v___x_2869_, v___x_2874_);
if (v___x_2875_ == 0)
{
uint32_t v___x_2876_; uint8_t v___x_2877_; 
v___x_2876_ = 10;
v___x_2877_ = lean_uint32_dec_eq(v___x_2869_, v___x_2876_);
if (v___x_2877_ == 0)
{
lean_dec(v___x_2863_);
return v_pos_2853_;
}
else
{
goto v___jp_2864_;
}
}
else
{
goto v___jp_2864_;
}
}
else
{
goto v___jp_2864_;
}
}
else
{
goto v___jp_2864_;
}
v___jp_2864_:
{
lean_object* v___x_2865_; uint8_t v___x_2866_; 
v___x_2865_ = lean_nat_add(v___x_2863_, v___x_2861_);
v___x_2866_ = lean_nat_dec_le(v___x_2865_, v_pos_2853_);
lean_dec(v___x_2865_);
if (v___x_2866_ == 0)
{
lean_dec(v___x_2863_);
return v_pos_2853_;
}
else
{
lean_dec(v_pos_2853_);
v_pos_2853_ = v___x_2863_;
goto _start;
}
}
}
else
{
lean_dec(v___x_2857_);
lean_dec(v___x_2856_);
return v_pos_2853_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1___boxed(lean_object* v_s_2878_, lean_object* v_pos_2879_){
_start:
{
lean_object* v_res_2880_; 
v_res_2880_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v_s_2878_, v_pos_2879_);
lean_dec_ref(v_s_2878_);
return v_res_2880_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_trimAscii(lean_object* v_s_2881_){
_start:
{
lean_object* v_str_2882_; lean_object* v_startInclusive_2883_; lean_object* v_endExclusive_2884_; lean_object* v___x_2885_; lean_object* v___x_2886_; lean_object* v___x_2888_; uint8_t v_isShared_2889_; uint8_t v_isSharedCheck_2898_; 
v_str_2882_ = lean_ctor_get(v_s_2881_, 0);
lean_inc_ref(v_str_2882_);
v_startInclusive_2883_ = lean_ctor_get(v_s_2881_, 1);
lean_inc(v_startInclusive_2883_);
v_endExclusive_2884_ = lean_ctor_get(v_s_2881_, 2);
lean_inc(v_endExclusive_2884_);
v___x_2885_ = lean_unsigned_to_nat(0u);
v___x_2886_ = l_String_Slice_Pos_skipWhile___at___00String_Slice_trimAscii_spec__0(v_s_2881_, v___x_2885_);
v_isSharedCheck_2898_ = !lean_is_exclusive(v_s_2881_);
if (v_isSharedCheck_2898_ == 0)
{
lean_object* v_unused_2899_; lean_object* v_unused_2900_; lean_object* v_unused_2901_; 
v_unused_2899_ = lean_ctor_get(v_s_2881_, 2);
lean_dec(v_unused_2899_);
v_unused_2900_ = lean_ctor_get(v_s_2881_, 1);
lean_dec(v_unused_2900_);
v_unused_2901_ = lean_ctor_get(v_s_2881_, 0);
lean_dec(v_unused_2901_);
v___x_2888_ = v_s_2881_;
v_isShared_2889_ = v_isSharedCheck_2898_;
goto v_resetjp_2887_;
}
else
{
lean_dec(v_s_2881_);
v___x_2888_ = lean_box(0);
v_isShared_2889_ = v_isSharedCheck_2898_;
goto v_resetjp_2887_;
}
v_resetjp_2887_:
{
lean_object* v___x_2890_; lean_object* v___x_2892_; 
v___x_2890_ = lean_nat_add(v_startInclusive_2883_, v___x_2886_);
lean_dec(v___x_2886_);
lean_dec(v_startInclusive_2883_);
lean_inc(v_endExclusive_2884_);
lean_inc(v___x_2890_);
lean_inc_ref(v_str_2882_);
if (v_isShared_2889_ == 0)
{
lean_ctor_set(v___x_2888_, 1, v___x_2890_);
v___x_2892_ = v___x_2888_;
goto v_reusejp_2891_;
}
else
{
lean_object* v_reuseFailAlloc_2897_; 
v_reuseFailAlloc_2897_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_2897_, 0, v_str_2882_);
lean_ctor_set(v_reuseFailAlloc_2897_, 1, v___x_2890_);
lean_ctor_set(v_reuseFailAlloc_2897_, 2, v_endExclusive_2884_);
v___x_2892_ = v_reuseFailAlloc_2897_;
goto v_reusejp_2891_;
}
v_reusejp_2891_:
{
lean_object* v___x_2893_; lean_object* v___x_2894_; lean_object* v___x_2895_; lean_object* v___x_2896_; 
v___x_2893_ = lean_nat_sub(v_endExclusive_2884_, v___x_2890_);
lean_dec(v_endExclusive_2884_);
v___x_2894_ = l_String_Slice_Pos_revSkipWhile___at___00String_Slice_trimAscii_spec__1(v___x_2892_, v___x_2893_);
lean_dec_ref(v___x_2892_);
v___x_2895_ = lean_nat_add(v___x_2890_, v___x_2894_);
lean_dec(v___x_2894_);
v___x_2896_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2896_, 0, v_str_2882_);
lean_ctor_set(v___x_2896_, 1, v___x_2890_);
lean_ctor_set(v___x_2896_, 2, v___x_2895_);
return v___x_2896_;
}
}
}
}
uint8_t l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(lean_object* v_s1_2902_, lean_object* v_s1Curr_2903_, lean_object* v_s2_2904_, lean_object* v_s2Curr_2905_){
_start:
{
lean_object* v_str_2906_; lean_object* v_startInclusive_2907_; lean_object* v_endExclusive_2908_; lean_object* v___x_2909_; uint8_t v___y_2911_; lean_object* v___x_2941_; lean_object* v___x_2942_; uint8_t v___x_2943_; 
v_str_2906_ = lean_ctor_get(v_s1_2902_, 0);
v_startInclusive_2907_ = lean_ctor_get(v_s1_2902_, 1);
v_endExclusive_2908_ = lean_ctor_get(v_s1_2902_, 2);
v___x_2909_ = lean_nat_sub(v_endExclusive_2908_, v_startInclusive_2907_);
v___x_2941_ = lean_unsigned_to_nat(1u);
v___x_2942_ = lean_nat_add(v_s1Curr_2903_, v___x_2941_);
v___x_2943_ = lean_nat_dec_le(v___x_2942_, v___x_2909_);
lean_dec(v___x_2942_);
if (v___x_2943_ == 0)
{
v___y_2911_ = v___x_2943_;
goto v___jp_2910_;
}
else
{
lean_object* v_startInclusive_2944_; lean_object* v_endExclusive_2945_; lean_object* v___x_2946_; lean_object* v___x_2947_; uint8_t v___x_2948_; 
v_startInclusive_2944_ = lean_ctor_get(v_s2_2904_, 1);
v_endExclusive_2945_ = lean_ctor_get(v_s2_2904_, 2);
v___x_2946_ = lean_nat_sub(v_endExclusive_2945_, v_startInclusive_2944_);
v___x_2947_ = lean_nat_add(v_s2Curr_2905_, v___x_2941_);
v___x_2948_ = lean_nat_dec_le(v___x_2947_, v___x_2946_);
lean_dec(v___x_2946_);
lean_dec(v___x_2947_);
v___y_2911_ = v___x_2948_;
goto v___jp_2910_;
}
v___jp_2910_:
{
if (v___y_2911_ == 0)
{
uint8_t v_decide_2912_; 
v_decide_2912_ = lean_nat_dec_eq(v_s1Curr_2903_, v___x_2909_);
lean_dec(v___x_2909_);
lean_dec(v_s1Curr_2903_);
if (v_decide_2912_ == 0)
{
lean_dec(v_s2Curr_2905_);
return v_decide_2912_;
}
else
{
lean_object* v_startInclusive_2913_; lean_object* v_endExclusive_2914_; lean_object* v___x_2915_; uint8_t v_decide_2916_; 
v_startInclusive_2913_ = lean_ctor_get(v_s2_2904_, 1);
v_endExclusive_2914_ = lean_ctor_get(v_s2_2904_, 2);
v___x_2915_ = lean_nat_sub(v_endExclusive_2914_, v_startInclusive_2913_);
v_decide_2916_ = lean_nat_dec_eq(v_s2Curr_2905_, v___x_2915_);
lean_dec(v___x_2915_);
lean_dec(v_s2Curr_2905_);
return v_decide_2916_;
}
}
else
{
lean_object* v_str_2917_; lean_object* v_startInclusive_2918_; lean_object* v___x_2919_; uint8_t v___x_2920_; uint8_t v___x_2921_; uint8_t v___x_2922_; uint8_t v___x_2923_; uint8_t v___x_2924_; uint8_t v___x_2925_; uint8_t v___x_2926_; uint8_t v___x_2927_; uint8_t v_c1_2928_; lean_object* v___x_2929_; uint8_t v___x_2930_; uint8_t v___x_2931_; uint8_t v___x_2932_; uint8_t v___x_2933_; uint8_t v___x_2934_; uint8_t v_c2_2935_; uint8_t v___x_2936_; 
lean_dec(v___x_2909_);
v_str_2917_ = lean_ctor_get(v_s2_2904_, 0);
v_startInclusive_2918_ = lean_ctor_get(v_s2_2904_, 1);
v___x_2919_ = lean_nat_add(v_startInclusive_2907_, v_s1Curr_2903_);
v___x_2920_ = lean_string_get_byte_fast(v_str_2906_, v___x_2919_);
v___x_2921_ = 65;
v___x_2922_ = lean_uint8_sub(v___x_2920_, v___x_2921_);
v___x_2923_ = 26;
v___x_2924_ = lean_uint8_dec_lt(v___x_2922_, v___x_2923_);
v___x_2925_ = lean_bool_to_uint8(v___x_2924_);
v___x_2926_ = 5;
v___x_2927_ = lean_uint8_shift_left(v___x_2925_, v___x_2926_);
v_c1_2928_ = lean_uint8_add(v___x_2920_, v___x_2927_);
v___x_2929_ = lean_nat_add(v_startInclusive_2918_, v_s2Curr_2905_);
v___x_2930_ = lean_string_get_byte_fast(v_str_2917_, v___x_2929_);
v___x_2931_ = lean_uint8_sub(v___x_2930_, v___x_2921_);
v___x_2932_ = lean_uint8_dec_lt(v___x_2931_, v___x_2923_);
v___x_2933_ = lean_bool_to_uint8(v___x_2932_);
v___x_2934_ = lean_uint8_shift_left(v___x_2933_, v___x_2926_);
v_c2_2935_ = lean_uint8_add(v___x_2930_, v___x_2934_);
v___x_2936_ = lean_uint8_dec_eq(v_c1_2928_, v_c2_2935_);
if (v___x_2936_ == 0)
{
lean_dec(v_s2Curr_2905_);
lean_dec(v_s1Curr_2903_);
return v___x_2936_;
}
else
{
lean_object* v___x_2937_; lean_object* v___x_2938_; lean_object* v___x_2939_; 
v___x_2937_ = lean_unsigned_to_nat(1u);
v___x_2938_ = lean_nat_add(v_s1Curr_2903_, v___x_2937_);
lean_dec(v_s1Curr_2903_);
v___x_2939_ = lean_nat_add(v_s2Curr_2905_, v___x_2937_);
lean_dec(v_s2Curr_2905_);
v_s1Curr_2903_ = v___x_2938_;
v_s2Curr_2905_ = v___x_2939_;
goto _start;
}
}
}
}
}
LEAN_EXPORT void l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go_0interp(lean_interpreter_value* stack)
{
lean_object* v_s1_2902_ = stack[0].m_obj;
lean_object* v_s1Curr_2903_ = stack[1].m_obj;
lean_object* v_s2_2904_ = stack[2].m_obj;
lean_object* v_s2Curr_2905_ = stack[3].m_obj;
uint8_t v_res_2949_;
v_res_2949_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_2902_, v_s1Curr_2903_, v_s2_2904_, v_s2Curr_2905_);
stack->m_num = v_res_2949_;
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go___boxed(lean_object* v_s1_2950_, lean_object* v_s1Curr_2951_, lean_object* v_s2_2952_, lean_object* v_s2Curr_2953_){
_start:
{
uint8_t v_res_2954_; lean_object* v_r_2955_; 
v_res_2954_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_2950_, v_s1Curr_2951_, v_s2_2952_, v_s2Curr_2953_);
lean_dec_ref(v_s2_2952_);
lean_dec_ref(v_s1_2950_);
v_r_2955_ = lean_box(v_res_2954_);
return v_r_2955_;
}
}
uint8_t l_String_Slice_eqIgnoreAsciiCase(lean_object* v_s1_2956_, lean_object* v_s2_2957_){
_start:
{
lean_object* v_startInclusive_2958_; lean_object* v_endExclusive_2959_; lean_object* v_startInclusive_2960_; lean_object* v_endExclusive_2961_; lean_object* v___x_2962_; lean_object* v___x_2963_; uint8_t v___x_2964_; 
v_startInclusive_2958_ = lean_ctor_get(v_s1_2956_, 1);
v_endExclusive_2959_ = lean_ctor_get(v_s1_2956_, 2);
v_startInclusive_2960_ = lean_ctor_get(v_s2_2957_, 1);
v_endExclusive_2961_ = lean_ctor_get(v_s2_2957_, 2);
v___x_2962_ = lean_nat_sub(v_endExclusive_2959_, v_startInclusive_2958_);
v___x_2963_ = lean_nat_sub(v_endExclusive_2961_, v_startInclusive_2960_);
v___x_2964_ = lean_nat_dec_eq(v___x_2962_, v___x_2963_);
lean_dec(v___x_2963_);
lean_dec(v___x_2962_);
if (v___x_2964_ == 0)
{
return v___x_2964_;
}
else
{
lean_object* v___x_2965_; uint8_t v___x_2966_; 
v___x_2965_ = lean_unsigned_to_nat(0u);
v___x_2966_ = l___private_Init_Data_String_Slice_0__String_Slice_eqIgnoreAsciiCase_go(v_s1_2956_, v___x_2965_, v_s2_2957_, v___x_2965_);
return v___x_2966_;
}
}
}
LEAN_EXPORT void l_String_Slice_eqIgnoreAsciiCase_0interp(lean_interpreter_value* stack)
{
lean_object* v_s1_2956_ = stack[0].m_obj;
lean_object* v_s2_2957_ = stack[1].m_obj;
uint8_t v_res_2967_;
v_res_2967_ = l_String_Slice_eqIgnoreAsciiCase(v_s1_2956_, v_s2_2957_);
stack->m_num = v_res_2967_;
}
LEAN_EXPORT lean_object* l_String_Slice_eqIgnoreAsciiCase___boxed(lean_object* v_s1_2968_, lean_object* v_s2_2969_){
_start:
{
uint8_t v_res_2970_; lean_object* v_r_2971_; 
v_res_2970_ = l_String_Slice_eqIgnoreAsciiCase(v_s1_2968_, v_s2_2969_);
lean_dec_ref(v_s2_2969_);
lean_dec_ref(v_s1_2968_);
v_r_2971_ = lean_box(v_res_2970_);
return v_r_2971_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines_lineMap(lean_object* v_s_2972_){
_start:
{
lean_object* v_str_2973_; lean_object* v_startInclusive_2974_; lean_object* v_endExclusive_2975_; lean_object* v___x_2976_; lean_object* v___x_2977_; uint8_t v_decide_2978_; 
v_str_2973_ = lean_ctor_get(v_s_2972_, 0);
v_startInclusive_2974_ = lean_ctor_get(v_s_2972_, 1);
v_endExclusive_2975_ = lean_ctor_get(v_s_2972_, 2);
v___x_2976_ = lean_nat_sub(v_endExclusive_2975_, v_startInclusive_2974_);
v___x_2977_ = lean_unsigned_to_nat(0u);
v_decide_2978_ = lean_nat_dec_eq(v___x_2976_, v___x_2977_);
if (v_decide_2978_ == 0)
{
uint32_t v___x_2979_; lean_object* v___x_2980_; lean_object* v___x_2981_; lean_object* v___x_2982_; lean_object* v___x_2983_; uint32_t v___x_2984_; uint8_t v___x_2985_; 
v___x_2979_ = 10;
v___x_2980_ = lean_unsigned_to_nat(1u);
v___x_2981_ = lean_nat_sub(v___x_2976_, v___x_2980_);
lean_dec(v___x_2976_);
v___x_2982_ = l_String_Slice_posLE(v_s_2972_, v___x_2981_);
v___x_2983_ = lean_nat_add(v_startInclusive_2974_, v___x_2982_);
lean_dec(v___x_2982_);
v___x_2984_ = lean_string_utf8_get_fast(v_str_2973_, v___x_2983_);
v___x_2985_ = lean_uint32_dec_eq(v___x_2984_, v___x_2979_);
if (v___x_2985_ == 0)
{
lean_dec(v___x_2983_);
return v_s_2972_;
}
else
{
lean_object* v___x_2987_; uint8_t v_isShared_2988_; uint8_t v_isSharedCheck_3001_; 
lean_inc(v_startInclusive_2974_);
lean_inc_ref(v_str_2973_);
v_isSharedCheck_3001_ = !lean_is_exclusive(v_s_2972_);
if (v_isSharedCheck_3001_ == 0)
{
lean_object* v_unused_3002_; lean_object* v_unused_3003_; lean_object* v_unused_3004_; 
v_unused_3002_ = lean_ctor_get(v_s_2972_, 2);
lean_dec(v_unused_3002_);
v_unused_3003_ = lean_ctor_get(v_s_2972_, 1);
lean_dec(v_unused_3003_);
v_unused_3004_ = lean_ctor_get(v_s_2972_, 0);
lean_dec(v_unused_3004_);
v___x_2987_ = v_s_2972_;
v_isShared_2988_ = v_isSharedCheck_3001_;
goto v_resetjp_2986_;
}
else
{
lean_dec(v_s_2972_);
v___x_2987_ = lean_box(0);
v_isShared_2988_ = v_isSharedCheck_3001_;
goto v_resetjp_2986_;
}
v_resetjp_2986_:
{
lean_object* v___x_2990_; 
lean_inc(v___x_2983_);
lean_inc(v_startInclusive_2974_);
lean_inc_ref(v_str_2973_);
if (v_isShared_2988_ == 0)
{
lean_ctor_set(v___x_2987_, 2, v___x_2983_);
v___x_2990_ = v___x_2987_;
goto v_reusejp_2989_;
}
else
{
lean_object* v_reuseFailAlloc_3000_; 
v_reuseFailAlloc_3000_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3000_, 0, v_str_2973_);
lean_ctor_set(v_reuseFailAlloc_3000_, 1, v_startInclusive_2974_);
lean_ctor_set(v_reuseFailAlloc_3000_, 2, v___x_2983_);
v___x_2990_ = v_reuseFailAlloc_3000_;
goto v_reusejp_2989_;
}
v_reusejp_2989_:
{
lean_object* v___x_2991_; uint8_t v_decide_2992_; 
v___x_2991_ = lean_nat_sub(v___x_2983_, v_startInclusive_2974_);
lean_dec(v___x_2983_);
v_decide_2992_ = lean_nat_dec_eq(v___x_2991_, v___x_2977_);
if (v_decide_2992_ == 0)
{
uint32_t v___x_2993_; lean_object* v___x_2994_; lean_object* v___x_2995_; lean_object* v___x_2996_; uint32_t v___x_2997_; uint8_t v___x_2998_; 
v___x_2993_ = 13;
v___x_2994_ = lean_nat_sub(v___x_2991_, v___x_2980_);
lean_dec(v___x_2991_);
v___x_2995_ = l_String_Slice_posLE(v___x_2990_, v___x_2994_);
v___x_2996_ = lean_nat_add(v_startInclusive_2974_, v___x_2995_);
lean_dec(v___x_2995_);
v___x_2997_ = lean_string_utf8_get_fast(v_str_2973_, v___x_2996_);
v___x_2998_ = lean_uint32_dec_eq(v___x_2997_, v___x_2993_);
if (v___x_2998_ == 0)
{
lean_dec(v___x_2996_);
lean_dec(v_startInclusive_2974_);
lean_dec_ref(v_str_2973_);
return v___x_2990_;
}
else
{
lean_object* v___x_2999_; 
lean_dec_ref(v___x_2990_);
v___x_2999_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v___x_2999_, 0, v_str_2973_);
lean_ctor_set(v___x_2999_, 1, v_startInclusive_2974_);
lean_ctor_set(v___x_2999_, 2, v___x_2996_);
return v___x_2999_;
}
}
else
{
lean_dec(v___x_2991_);
lean_dec(v_startInclusive_2974_);
lean_dec_ref(v_str_2973_);
return v___x_2990_;
}
}
}
}
}
else
{
lean_dec(v___x_2976_);
return v_s_2972_;
}
}
}
lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg(){
_start:
{
lean_object* v___x_3008_; 
v___x_3008_ = ((lean_object*)(l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___closed__0));
return v___x_3008_;
}
}
LEAN_EXPORT void l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg_0interp(lean_interpreter_value* stack)
{
lean_object* v_res_3009_;
v_res_3009_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
stack->m_obj
 = v_res_3009_;
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg___boxed(lean_object* v___dummy_3010_){
_start:
{
lean_object* v_res_3011_; 
v_res_3011_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
return v_res_3011_;
}
}
static lean_object* _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0(void){
_start:
{
lean_object* v___x_3012_; 
v___x_3012_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___redArg();
return v___x_3012_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(lean_object* v_s_3013_){
_start:
{
lean_object* v___x_3014_; 
v___x_3014_ = lean_obj_once(&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0, &l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_once, _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0);
return v___x_3014_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___boxed(lean_object* v_s_3015_){
_start:
{
lean_object* v_res_3016_; 
v_res_3016_ = l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0(v_s_3015_);
lean_dec_ref(v_s_3015_);
return v_res_3016_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines(lean_object* v_s_3017_){
_start:
{
lean_object* v___x_3018_; 
v___x_3018_ = lean_obj_once(&l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0, &l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0_once, _init_l_String_Slice_splitInclusive___at___00String_Slice_lines_spec__0___closed__0);
return v___x_3018_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_lines___boxed(lean_object* v_s_3019_){
_start:
{
lean_object* v_res_3020_; 
v_res_3020_ = l_String_Slice_lines(v_s_3019_);
lean_dec_ref(v_s_3019_);
return v_res_3020_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(lean_object* v_s_3021_, lean_object* v_a_3022_, lean_object* v_b_3023_){
_start:
{
lean_object* v_str_3024_; lean_object* v_startInclusive_3025_; lean_object* v_endExclusive_3026_; lean_object* v___x_3027_; uint8_t v_decide_3028_; 
v_str_3024_ = lean_ctor_get(v_s_3021_, 0);
v_startInclusive_3025_ = lean_ctor_get(v_s_3021_, 1);
v_endExclusive_3026_ = lean_ctor_get(v_s_3021_, 2);
v___x_3027_ = lean_nat_sub(v_endExclusive_3026_, v_startInclusive_3025_);
v_decide_3028_ = lean_nat_dec_eq(v_a_3022_, v___x_3027_);
lean_dec(v___x_3027_);
if (v_decide_3028_ == 0)
{
lean_object* v_snd_3029_; lean_object* v___x_3031_; uint8_t v_isShared_3032_; uint8_t v_isSharedCheck_3060_; 
v_snd_3029_ = lean_ctor_get(v_b_3023_, 1);
v_isSharedCheck_3060_ = !lean_is_exclusive(v_b_3023_);
if (v_isSharedCheck_3060_ == 0)
{
lean_object* v_unused_3061_; 
v_unused_3061_ = lean_ctor_get(v_b_3023_, 0);
lean_dec(v_unused_3061_);
v___x_3031_ = v_b_3023_;
v_isShared_3032_ = v_isSharedCheck_3060_;
goto v_resetjp_3030_;
}
else
{
lean_inc(v_snd_3029_);
lean_dec(v_b_3023_);
v___x_3031_ = lean_box(0);
v_isShared_3032_ = v_isSharedCheck_3060_;
goto v_resetjp_3030_;
}
v_resetjp_3030_:
{
lean_object* v___x_3039_; lean_object* v___x_3040_; lean_object* v___x_3041_; lean_object* v___x_3042_; uint32_t v___x_3043_; uint32_t v___x_3044_; uint8_t v___x_3045_; 
v___x_3039_ = lean_box(0);
v___x_3040_ = lean_nat_add(v_startInclusive_3025_, v_a_3022_);
lean_dec(v_a_3022_);
v___x_3041_ = lean_string_utf8_next_fast(v_str_3024_, v___x_3040_);
v___x_3042_ = lean_nat_sub(v___x_3041_, v_startInclusive_3025_);
v___x_3043_ = lean_string_utf8_get_fast(v_str_3024_, v___x_3040_);
lean_dec(v___x_3040_);
v___x_3044_ = 95;
v___x_3045_ = lean_uint32_dec_eq(v___x_3043_, v___x_3044_);
if (v___x_3045_ == 0)
{
uint32_t v___x_3046_; uint8_t v___x_3047_; 
v___x_3046_ = 48;
v___x_3047_ = lean_uint32_dec_le(v___x_3046_, v___x_3043_);
if (v___x_3047_ == 0)
{
lean_dec(v___x_3042_);
goto v___jp_3033_;
}
else
{
uint32_t v___x_3048_; uint8_t v___x_3049_; 
v___x_3048_ = 57;
v___x_3049_ = lean_uint32_dec_le(v___x_3043_, v___x_3048_);
if (v___x_3049_ == 0)
{
lean_dec(v___x_3042_);
goto v___jp_3033_;
}
else
{
lean_object* v___x_3050_; lean_object* v___x_3051_; 
lean_del_object(v___x_3031_);
lean_dec(v_snd_3029_);
v___x_3050_ = lean_box(v___x_3047_);
v___x_3051_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3051_, 0, v___x_3039_);
lean_ctor_set(v___x_3051_, 1, v___x_3050_);
v_a_3022_ = v___x_3042_;
v_b_3023_ = v___x_3051_;
goto _start;
}
}
}
else
{
uint8_t v___x_3053_; 
lean_del_object(v___x_3031_);
v___x_3053_ = lean_unbox(v_snd_3029_);
if (v___x_3053_ == 0)
{
lean_object* v___x_3054_; lean_object* v___x_3055_; lean_object* v___x_3056_; 
lean_dec(v___x_3042_);
v___x_3054_ = lean_box(v_decide_3028_);
v___x_3055_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3055_, 0, v___x_3054_);
v___x_3056_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3056_, 0, v___x_3055_);
lean_ctor_set(v___x_3056_, 1, v_snd_3029_);
return v___x_3056_;
}
else
{
lean_object* v___x_3057_; lean_object* v___x_3058_; 
lean_dec(v_snd_3029_);
v___x_3057_ = lean_box(v_decide_3028_);
v___x_3058_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v___x_3058_, 0, v___x_3039_);
lean_ctor_set(v___x_3058_, 1, v___x_3057_);
v_a_3022_ = v___x_3042_;
v_b_3023_ = v___x_3058_;
goto _start;
}
}
v___jp_3033_:
{
lean_object* v___x_3034_; lean_object* v___x_3035_; lean_object* v___x_3037_; 
v___x_3034_ = lean_box(v_decide_3028_);
v___x_3035_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3035_, 0, v___x_3034_);
if (v_isShared_3032_ == 0)
{
lean_ctor_set(v___x_3031_, 0, v___x_3035_);
v___x_3037_ = v___x_3031_;
goto v_reusejp_3036_;
}
else
{
lean_object* v_reuseFailAlloc_3038_; 
v_reuseFailAlloc_3038_ = lean_alloc_ctor(0, 2, 0);
lean_ctor_set(v_reuseFailAlloc_3038_, 0, v___x_3035_);
lean_ctor_set(v_reuseFailAlloc_3038_, 1, v_snd_3029_);
v___x_3037_ = v_reuseFailAlloc_3038_;
goto v_reusejp_3036_;
}
v_reusejp_3036_:
{
return v___x_3037_;
}
}
}
}
else
{
lean_dec(v_a_3022_);
return v_b_3023_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg___boxed(lean_object* v_s_3062_, lean_object* v_a_3063_, lean_object* v_b_3064_){
_start:
{
lean_object* v_res_3065_; 
v_res_3065_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3062_, v_a_3063_, v_b_3064_);
lean_dec_ref(v_s_3062_);
return v_res_3065_;
}
}
uint8_t l_String_Slice_isNat(lean_object* v_s_3070_){
_start:
{
lean_object* v___x_3071_; lean_object* v___x_3072_; lean_object* v___x_3073_; lean_object* v_fst_3074_; 
v___x_3071_ = ((lean_object*)(l_String_Slice_isNat___closed__0));
v___x_3072_ = lean_unsigned_to_nat(0u);
v___x_3073_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3070_, v___x_3072_, v___x_3071_);
v_fst_3074_ = lean_ctor_get(v___x_3073_, 0);
if (lean_obj_tag(v_fst_3074_) == 0)
{
lean_object* v_snd_3075_; uint8_t v___x_3076_; 
v_snd_3075_ = lean_ctor_get(v___x_3073_, 1);
lean_inc(v_snd_3075_);
lean_dec_ref(v___x_3073_);
v___x_3076_ = lean_unbox(v_snd_3075_);
lean_dec(v_snd_3075_);
return v___x_3076_;
}
else
{
lean_object* v_val_3077_; uint8_t v___x_3078_; 
lean_inc_ref(v_fst_3074_);
lean_dec_ref(v___x_3073_);
v_val_3077_ = lean_ctor_get(v_fst_3074_, 0);
lean_inc(v_val_3077_);
lean_dec_ref_known(v_fst_3074_, 1);
v___x_3078_ = lean_unbox(v_val_3077_);
lean_dec(v_val_3077_);
return v___x_3078_;
}
}
}
LEAN_EXPORT void l_String_Slice_isNat_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3070_ = stack[0].m_obj;
uint8_t v_res_3079_;
v_res_3079_ = l_String_Slice_isNat(v_s_3070_);
stack->m_num = v_res_3079_;
}
LEAN_EXPORT lean_object* l_String_Slice_isNat___boxed(lean_object* v_s_3080_){
_start:
{
uint8_t v_res_3081_; lean_object* v_r_3082_; 
v_res_3081_ = l_String_Slice_isNat(v_s_3080_);
lean_dec_ref(v_s_3080_);
v_r_3082_ = lean_box(v_res_3081_);
return v_r_3082_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(lean_object* v_s_3083_, lean_object* v_inst_3084_, lean_object* v_R_3085_, lean_object* v_a_3086_, lean_object* v_b_3087_, lean_object* v_c_3088_){
_start:
{
lean_object* v___x_3089_; 
v___x_3089_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___redArg(v_s_3083_, v_a_3086_, v_b_3087_);
return v___x_3089_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0___boxed(lean_object* v_s_3090_, lean_object* v_inst_3091_, lean_object* v_R_3092_, lean_object* v_a_3093_, lean_object* v_b_3094_, lean_object* v_c_3095_){
_start:
{
lean_object* v_res_3096_; 
v_res_3096_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_isNat_spec__0(v_s_3090_, v_inst_3091_, v_R_3092_, v_a_3093_, v_b_3094_, v_c_3095_);
lean_dec_ref(v_s_3090_);
return v_res_3096_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(lean_object* v_s_3097_, lean_object* v_a_3098_, lean_object* v_b_3099_){
_start:
{
lean_object* v_str_3100_; lean_object* v_startInclusive_3101_; lean_object* v_endExclusive_3102_; lean_object* v___x_3103_; uint8_t v_decide_3104_; 
v_str_3100_ = lean_ctor_get(v_s_3097_, 0);
v_startInclusive_3101_ = lean_ctor_get(v_s_3097_, 1);
v_endExclusive_3102_ = lean_ctor_get(v_s_3097_, 2);
v___x_3103_ = lean_nat_sub(v_endExclusive_3102_, v_startInclusive_3101_);
v_decide_3104_ = lean_nat_dec_eq(v_a_3098_, v___x_3103_);
lean_dec(v___x_3103_);
if (v_decide_3104_ == 0)
{
lean_object* v___x_3105_; lean_object* v___x_3106_; lean_object* v___x_3107_; uint32_t v___x_3108_; uint32_t v___x_3109_; uint8_t v___x_3110_; 
v___x_3105_ = lean_nat_add(v_startInclusive_3101_, v_a_3098_);
lean_dec(v_a_3098_);
v___x_3106_ = lean_string_utf8_next_fast(v_str_3100_, v___x_3105_);
v___x_3107_ = lean_nat_sub(v___x_3106_, v_startInclusive_3101_);
v___x_3108_ = lean_string_utf8_get_fast(v_str_3100_, v___x_3105_);
lean_dec(v___x_3105_);
v___x_3109_ = 95;
v___x_3110_ = lean_uint32_dec_eq(v___x_3108_, v___x_3109_);
if (v___x_3110_ == 0)
{
lean_object* v___x_3111_; lean_object* v___x_3112_; lean_object* v___x_3113_; lean_object* v___x_3114_; lean_object* v___x_3115_; lean_object* v___x_3116_; 
v___x_3111_ = lean_unsigned_to_nat(10u);
v___x_3112_ = lean_nat_mul(v_b_3099_, v___x_3111_);
lean_dec(v_b_3099_);
v___x_3113_ = lean_uint32_to_nat(v___x_3108_);
v___x_3114_ = lean_unsigned_to_nat(48u);
v___x_3115_ = lean_nat_sub(v___x_3113_, v___x_3114_);
lean_dec(v___x_3113_);
v___x_3116_ = lean_nat_add(v___x_3112_, v___x_3115_);
lean_dec(v___x_3115_);
lean_dec(v___x_3112_);
v_a_3098_ = v___x_3107_;
v_b_3099_ = v___x_3116_;
goto _start;
}
else
{
v_a_3098_ = v___x_3107_;
goto _start;
}
}
else
{
lean_dec(v_a_3098_);
return v_b_3099_;
}
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg___boxed(lean_object* v_s_3119_, lean_object* v_a_3120_, lean_object* v_b_3121_){
_start:
{
lean_object* v_res_3122_; 
v_res_3122_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3119_, v_a_3120_, v_b_3121_);
lean_dec_ref(v_s_3119_);
return v_res_3122_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f(lean_object* v_s_3123_){
_start:
{
uint8_t v___x_3124_; 
v___x_3124_ = l_String_Slice_isNat(v_s_3123_);
if (v___x_3124_ == 0)
{
lean_object* v___x_3125_; 
v___x_3125_ = lean_box(0);
return v___x_3125_;
}
else
{
lean_object* v___x_3126_; lean_object* v___x_3127_; lean_object* v___x_3128_; 
v___x_3126_ = lean_unsigned_to_nat(0u);
v___x_3127_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3123_, v___x_3126_, v___x_3126_);
v___x_3128_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v___x_3128_, 0, v___x_3127_);
return v___x_3128_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x3f___boxed(lean_object* v_s_3129_){
_start:
{
lean_object* v_res_3130_; 
v_res_3130_ = l_String_Slice_toNat_x3f(v_s_3129_);
lean_dec_ref(v_s_3129_);
return v_res_3130_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(lean_object* v_s_3131_, lean_object* v_inst_3132_, lean_object* v_R_3133_, lean_object* v_a_3134_, lean_object* v_b_3135_, lean_object* v_c_3136_){
_start:
{
lean_object* v___x_3137_; 
v___x_3137_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3131_, v_a_3134_, v_b_3135_);
return v___x_3137_;
}
}
LEAN_EXPORT lean_object* l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___boxed(lean_object* v_s_3138_, lean_object* v_inst_3139_, lean_object* v_R_3140_, lean_object* v_a_3141_, lean_object* v_b_3142_, lean_object* v_c_3143_){
_start:
{
lean_object* v_res_3144_; 
v_res_3144_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0(v_s_3138_, v_inst_3139_, v_R_3140_, v_a_3141_, v_b_3142_, v_c_3143_);
lean_dec_ref(v_s_3138_);
return v_res_3144_;
}
}
LEAN_EXPORT lean_object* l_panic___at___00String_Slice_toNat_x21_spec__0(lean_object* v_msg_3145_){
_start:
{
lean_object* v___x_3146_; lean_object* v___x_3147_; 
v___x_3146_ = lean_unsigned_to_nat(0u);
v___x_3147_ = lean_panic_fn_borrowed(v___x_3146_, v_msg_3145_);
return v___x_3147_;
}
}
static lean_object* _init_l_String_Slice_toNat_x21___closed__3(void){
_start:
{
lean_object* v___x_3151_; lean_object* v___x_3152_; lean_object* v___x_3153_; lean_object* v___x_3154_; lean_object* v___x_3155_; lean_object* v___x_3156_; 
v___x_3151_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__2));
v___x_3152_ = lean_unsigned_to_nat(4u);
v___x_3153_ = lean_unsigned_to_nat(1040u);
v___x_3154_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__1));
v___x_3155_ = ((lean_object*)(l_String_Slice_toNat_x21___closed__0));
v___x_3156_ = l_mkPanicMessageWithDecl(v___x_3155_, v___x_3154_, v___x_3153_, v___x_3152_, v___x_3151_);
return v___x_3156_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21(lean_object* v_s_3157_){
_start:
{
uint8_t v___x_3158_; 
v___x_3158_ = l_String_Slice_isNat(v_s_3157_);
if (v___x_3158_ == 0)
{
lean_object* v___x_3159_; lean_object* v___x_3160_; 
v___x_3159_ = lean_obj_once(&l_String_Slice_toNat_x21___closed__3, &l_String_Slice_toNat_x21___closed__3_once, _init_l_String_Slice_toNat_x21___closed__3);
v___x_3160_ = l_panic___at___00String_Slice_toNat_x21_spec__0(v___x_3159_);
return v___x_3160_;
}
else
{
lean_object* v___x_3161_; lean_object* v___x_3162_; 
v___x_3161_ = lean_unsigned_to_nat(0u);
v___x_3162_ = l_WellFounded_opaqueFix_u2083___at___00String_Slice_toNat_x3f_spec__0___redArg(v_s_3157_, v___x_3161_, v___x_3161_);
return v___x_3162_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toNat_x21___boxed(lean_object* v_s_3163_){
_start:
{
lean_object* v_res_3164_; 
v_res_3164_ = l_String_Slice_toNat_x21(v_s_3163_);
lean_dec_ref(v_s_3163_);
return v_res_3164_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f(lean_object* v_s_3165_){
_start:
{
lean_object* v___x_3166_; lean_object* v___x_3167_; 
v___x_3166_ = lean_unsigned_to_nat(0u);
v___x_3167_ = l_String_Slice_Pos_get_x3f(v_s_3165_, v___x_3166_);
return v___x_3167_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_front_x3f___boxed(lean_object* v_s_3168_){
_start:
{
lean_object* v_res_3169_; 
v_res_3169_ = l_String_Slice_front_x3f(v_s_3168_);
lean_dec_ref(v_s_3168_);
return v_res_3169_;
}
}
uint32_t l_String_Slice_front(lean_object* v_s_3170_){
_start:
{
lean_object* v___x_3171_; lean_object* v___x_3172_; 
v___x_3171_ = lean_unsigned_to_nat(0u);
v___x_3172_ = l_String_Slice_Pos_get_x3f(v_s_3170_, v___x_3171_);
if (lean_obj_tag(v___x_3172_) == 0)
{
uint32_t v___x_3173_; 
v___x_3173_ = 65;
return v___x_3173_;
}
else
{
lean_object* v_val_3174_; uint32_t v___x_3175_; 
v_val_3174_ = lean_ctor_get(v___x_3172_, 0);
lean_inc(v_val_3174_);
lean_dec_ref_known(v___x_3172_, 1);
v___x_3175_ = lean_unbox_uint32(v_val_3174_);
lean_dec(v_val_3174_);
return v___x_3175_;
}
}
}
LEAN_EXPORT void l_String_Slice_front_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3170_ = stack[0].m_obj;
uint32_t v_res_3176_;
v_res_3176_ = l_String_Slice_front(v_s_3170_);
stack->m_num = v_res_3176_;
}
LEAN_EXPORT lean_object* l_String_Slice_front___boxed(lean_object* v_s_3177_){
_start:
{
uint32_t v_res_3178_; lean_object* v_r_3179_; 
v_res_3178_ = l_String_Slice_front(v_s_3177_);
lean_dec_ref(v_s_3177_);
v_r_3179_ = lean_box_uint32(v_res_3178_);
return v_r_3179_;
}
}
uint8_t l_String_Slice_isInt(lean_object* v_s_3180_){
_start:
{
lean_object* v_str_3181_; lean_object* v_startInclusive_3182_; lean_object* v_endExclusive_3183_; lean_object* v___x_3184_; lean_object* v___x_3185_; uint8_t v_decide_3186_; 
v_str_3181_ = lean_ctor_get(v_s_3180_, 0);
v_startInclusive_3182_ = lean_ctor_get(v_s_3180_, 1);
v_endExclusive_3183_ = lean_ctor_get(v_s_3180_, 2);
v___x_3184_ = lean_unsigned_to_nat(0u);
v___x_3185_ = lean_nat_sub(v_endExclusive_3183_, v_startInclusive_3182_);
v_decide_3186_ = lean_nat_dec_eq(v___x_3184_, v___x_3185_);
lean_dec(v___x_3185_);
if (v_decide_3186_ == 0)
{
uint32_t v___x_3187_; uint32_t v___x_3188_; uint8_t v___x_3189_; 
v___x_3187_ = 45;
v___x_3188_ = lean_string_utf8_get_fast(v_str_3181_, v_startInclusive_3182_);
v___x_3189_ = lean_uint32_dec_eq(v___x_3188_, v___x_3187_);
if (v___x_3189_ == 0)
{
uint8_t v___x_3190_; 
v___x_3190_ = l_String_Slice_isNat(v_s_3180_);
lean_dec_ref(v_s_3180_);
return v___x_3190_;
}
else
{
lean_object* v___x_3192_; uint8_t v_isShared_3193_; uint8_t v_isSharedCheck_3201_; 
lean_inc(v_endExclusive_3183_);
lean_inc(v_startInclusive_3182_);
lean_inc_ref(v_str_3181_);
v_isSharedCheck_3201_ = !lean_is_exclusive(v_s_3180_);
if (v_isSharedCheck_3201_ == 0)
{
lean_object* v_unused_3202_; lean_object* v_unused_3203_; lean_object* v_unused_3204_; 
v_unused_3202_ = lean_ctor_get(v_s_3180_, 2);
lean_dec(v_unused_3202_);
v_unused_3203_ = lean_ctor_get(v_s_3180_, 1);
lean_dec(v_unused_3203_);
v_unused_3204_ = lean_ctor_get(v_s_3180_, 0);
lean_dec(v_unused_3204_);
v___x_3192_ = v_s_3180_;
v_isShared_3193_ = v_isSharedCheck_3201_;
goto v_resetjp_3191_;
}
else
{
lean_dec(v_s_3180_);
v___x_3192_ = lean_box(0);
v_isShared_3193_ = v_isSharedCheck_3201_;
goto v_resetjp_3191_;
}
v_resetjp_3191_:
{
lean_object* v___x_3194_; lean_object* v___x_3195_; lean_object* v___x_3196_; lean_object* v___x_3198_; 
v___x_3194_ = lean_string_utf8_next_fast(v_str_3181_, v_startInclusive_3182_);
v___x_3195_ = lean_nat_sub(v___x_3194_, v_startInclusive_3182_);
v___x_3196_ = lean_nat_add(v_startInclusive_3182_, v___x_3195_);
lean_dec(v___x_3195_);
lean_dec(v_startInclusive_3182_);
if (v_isShared_3193_ == 0)
{
lean_ctor_set(v___x_3192_, 1, v___x_3196_);
v___x_3198_ = v___x_3192_;
goto v_reusejp_3197_;
}
else
{
lean_object* v_reuseFailAlloc_3200_; 
v_reuseFailAlloc_3200_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3200_, 0, v_str_3181_);
lean_ctor_set(v_reuseFailAlloc_3200_, 1, v___x_3196_);
lean_ctor_set(v_reuseFailAlloc_3200_, 2, v_endExclusive_3183_);
v___x_3198_ = v_reuseFailAlloc_3200_;
goto v_reusejp_3197_;
}
v_reusejp_3197_:
{
uint8_t v___x_3199_; 
v___x_3199_ = l_String_Slice_isNat(v___x_3198_);
lean_dec_ref(v___x_3198_);
return v___x_3199_;
}
}
}
}
else
{
uint8_t v___x_3205_; 
v___x_3205_ = l_String_Slice_isNat(v_s_3180_);
lean_dec_ref(v_s_3180_);
return v___x_3205_;
}
}
}
LEAN_EXPORT void l_String_Slice_isInt_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3180_ = stack[0].m_obj;
uint8_t v_res_3206_;
v_res_3206_ = l_String_Slice_isInt(v_s_3180_);
stack->m_num = v_res_3206_;
}
LEAN_EXPORT lean_object* l_String_Slice_isInt___boxed(lean_object* v_s_3207_){
_start:
{
uint8_t v_res_3208_; lean_object* v_r_3209_; 
v_res_3208_ = l_String_Slice_isInt(v_s_3207_);
v_r_3209_ = lean_box(v_res_3208_);
return v_r_3209_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x3f(lean_object* v_s_3210_){
_start:
{
lean_object* v_str_3223_; lean_object* v_startInclusive_3224_; lean_object* v_endExclusive_3225_; lean_object* v___x_3226_; lean_object* v___x_3227_; uint8_t v_decide_3228_; 
v_str_3223_ = lean_ctor_get(v_s_3210_, 0);
v_startInclusive_3224_ = lean_ctor_get(v_s_3210_, 1);
v_endExclusive_3225_ = lean_ctor_get(v_s_3210_, 2);
v___x_3226_ = lean_unsigned_to_nat(0u);
v___x_3227_ = lean_nat_sub(v_endExclusive_3225_, v_startInclusive_3224_);
v_decide_3228_ = lean_nat_dec_eq(v___x_3226_, v___x_3227_);
lean_dec(v___x_3227_);
if (v_decide_3228_ == 0)
{
uint32_t v___x_3229_; uint32_t v___x_3230_; uint8_t v___x_3231_; 
v___x_3229_ = 45;
v___x_3230_ = lean_string_utf8_get_fast(v_str_3223_, v_startInclusive_3224_);
v___x_3231_ = lean_uint32_dec_eq(v___x_3230_, v___x_3229_);
if (v___x_3231_ == 0)
{
goto v___jp_3211_;
}
else
{
lean_object* v___x_3233_; uint8_t v_isShared_3234_; uint8_t v_isSharedCheck_3252_; 
lean_inc(v_endExclusive_3225_);
lean_inc(v_startInclusive_3224_);
lean_inc_ref(v_str_3223_);
v_isSharedCheck_3252_ = !lean_is_exclusive(v_s_3210_);
if (v_isSharedCheck_3252_ == 0)
{
lean_object* v_unused_3253_; lean_object* v_unused_3254_; lean_object* v_unused_3255_; 
v_unused_3253_ = lean_ctor_get(v_s_3210_, 2);
lean_dec(v_unused_3253_);
v_unused_3254_ = lean_ctor_get(v_s_3210_, 1);
lean_dec(v_unused_3254_);
v_unused_3255_ = lean_ctor_get(v_s_3210_, 0);
lean_dec(v_unused_3255_);
v___x_3233_ = v_s_3210_;
v_isShared_3234_ = v_isSharedCheck_3252_;
goto v_resetjp_3232_;
}
else
{
lean_dec(v_s_3210_);
v___x_3233_ = lean_box(0);
v_isShared_3234_ = v_isSharedCheck_3252_;
goto v_resetjp_3232_;
}
v_resetjp_3232_:
{
lean_object* v___x_3235_; lean_object* v___x_3236_; lean_object* v___x_3237_; lean_object* v___x_3239_; 
v___x_3235_ = lean_string_utf8_next_fast(v_str_3223_, v_startInclusive_3224_);
v___x_3236_ = lean_nat_sub(v___x_3235_, v_startInclusive_3224_);
v___x_3237_ = lean_nat_add(v_startInclusive_3224_, v___x_3236_);
lean_dec(v___x_3236_);
lean_dec(v_startInclusive_3224_);
if (v_isShared_3234_ == 0)
{
lean_ctor_set(v___x_3233_, 1, v___x_3237_);
v___x_3239_ = v___x_3233_;
goto v_reusejp_3238_;
}
else
{
lean_object* v_reuseFailAlloc_3251_; 
v_reuseFailAlloc_3251_ = lean_alloc_ctor(0, 3, 0);
lean_ctor_set(v_reuseFailAlloc_3251_, 0, v_str_3223_);
lean_ctor_set(v_reuseFailAlloc_3251_, 1, v___x_3237_);
lean_ctor_set(v_reuseFailAlloc_3251_, 2, v_endExclusive_3225_);
v___x_3239_ = v_reuseFailAlloc_3251_;
goto v_reusejp_3238_;
}
v_reusejp_3238_:
{
lean_object* v___x_3240_; 
v___x_3240_ = l_String_Slice_toNat_x3f(v___x_3239_);
lean_dec_ref(v___x_3239_);
if (lean_obj_tag(v___x_3240_) == 0)
{
lean_object* v___x_3241_; 
v___x_3241_ = lean_box(0);
return v___x_3241_;
}
else
{
lean_object* v_val_3242_; lean_object* v___x_3244_; uint8_t v_isShared_3245_; uint8_t v_isSharedCheck_3250_; 
v_val_3242_ = lean_ctor_get(v___x_3240_, 0);
v_isSharedCheck_3250_ = !lean_is_exclusive(v___x_3240_);
if (v_isSharedCheck_3250_ == 0)
{
v___x_3244_ = v___x_3240_;
v_isShared_3245_ = v_isSharedCheck_3250_;
goto v_resetjp_3243_;
}
else
{
lean_inc(v_val_3242_);
lean_dec(v___x_3240_);
v___x_3244_ = lean_box(0);
v_isShared_3245_ = v_isSharedCheck_3250_;
goto v_resetjp_3243_;
}
v_resetjp_3243_:
{
lean_object* v___x_3246_; lean_object* v___x_3248_; 
v___x_3246_ = l_Int_negOfNat(v_val_3242_);
lean_dec(v_val_3242_);
if (v_isShared_3245_ == 0)
{
lean_ctor_set(v___x_3244_, 0, v___x_3246_);
v___x_3248_ = v___x_3244_;
goto v_reusejp_3247_;
}
else
{
lean_object* v_reuseFailAlloc_3249_; 
v_reuseFailAlloc_3249_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3249_, 0, v___x_3246_);
v___x_3248_ = v_reuseFailAlloc_3249_;
goto v_reusejp_3247_;
}
v_reusejp_3247_:
{
return v___x_3248_;
}
}
}
}
}
}
}
else
{
goto v___jp_3211_;
}
v___jp_3211_:
{
lean_object* v___x_3212_; 
v___x_3212_ = l_String_Slice_toNat_x3f(v_s_3210_);
lean_dec_ref(v_s_3210_);
if (lean_obj_tag(v___x_3212_) == 0)
{
lean_object* v___x_3213_; 
v___x_3213_ = lean_box(0);
return v___x_3213_;
}
else
{
lean_object* v_val_3214_; lean_object* v___x_3216_; uint8_t v_isShared_3217_; uint8_t v_isSharedCheck_3222_; 
v_val_3214_ = lean_ctor_get(v___x_3212_, 0);
v_isSharedCheck_3222_ = !lean_is_exclusive(v___x_3212_);
if (v_isSharedCheck_3222_ == 0)
{
v___x_3216_ = v___x_3212_;
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
else
{
lean_inc(v_val_3214_);
lean_dec(v___x_3212_);
v___x_3216_ = lean_box(0);
v_isShared_3217_ = v_isSharedCheck_3222_;
goto v_resetjp_3215_;
}
v_resetjp_3215_:
{
lean_object* v___x_3218_; lean_object* v___x_3220_; 
v___x_3218_ = lean_nat_to_int(v_val_3214_);
if (v_isShared_3217_ == 0)
{
lean_ctor_set(v___x_3216_, 0, v___x_3218_);
v___x_3220_ = v___x_3216_;
goto v_reusejp_3219_;
}
else
{
lean_object* v_reuseFailAlloc_3221_; 
v_reuseFailAlloc_3221_ = lean_alloc_ctor(1, 1, 0);
lean_ctor_set(v_reuseFailAlloc_3221_, 0, v___x_3218_);
v___x_3220_ = v_reuseFailAlloc_3221_;
goto v_reusejp_3219_;
}
v_reusejp_3219_:
{
return v___x_3220_;
}
}
}
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_toInt_x21(lean_object* v_s_3257_){
_start:
{
lean_object* v___x_3258_; 
v___x_3258_ = l_String_Slice_toInt_x3f(v_s_3257_);
if (lean_obj_tag(v___x_3258_) == 0)
{
lean_object* v___x_3259_; lean_object* v___x_3260_; lean_object* v___x_3261_; 
v___x_3259_ = l_Int_instInhabited;
v___x_3260_ = ((lean_object*)(l_String_Slice_toInt_x21___closed__0));
v___x_3261_ = l_panic___redArg(v___x_3259_, v___x_3260_);
return v___x_3261_;
}
else
{
lean_object* v_val_3262_; 
v_val_3262_ = lean_ctor_get(v___x_3258_, 0);
lean_inc(v_val_3262_);
lean_dec_ref_known(v___x_3258_, 1);
return v_val_3262_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f(lean_object* v_s_3263_){
_start:
{
lean_object* v_startInclusive_3264_; lean_object* v_endExclusive_3265_; lean_object* v___x_3266_; lean_object* v___x_3267_; 
v_startInclusive_3264_ = lean_ctor_get(v_s_3263_, 1);
v_endExclusive_3265_ = lean_ctor_get(v_s_3263_, 2);
v___x_3266_ = lean_nat_sub(v_endExclusive_3265_, v_startInclusive_3264_);
v___x_3267_ = l_String_Slice_Pos_prev_x3f(v_s_3263_, v___x_3266_);
lean_dec(v___x_3266_);
if (lean_obj_tag(v___x_3267_) == 0)
{
lean_object* v___x_3268_; 
v___x_3268_ = lean_box(0);
return v___x_3268_;
}
else
{
lean_object* v_val_3269_; lean_object* v___x_3270_; 
v_val_3269_ = lean_ctor_get(v___x_3267_, 0);
lean_inc(v_val_3269_);
lean_dec_ref_known(v___x_3267_, 1);
v___x_3270_ = l_String_Slice_Pos_get_x3f(v_s_3263_, v_val_3269_);
lean_dec(v_val_3269_);
return v___x_3270_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_back_x3f___boxed(lean_object* v_s_3271_){
_start:
{
lean_object* v_res_3272_; 
v_res_3272_ = l_String_Slice_back_x3f(v_s_3271_);
lean_dec_ref(v_s_3271_);
return v_res_3272_;
}
}
uint32_t l_String_Slice_back(lean_object* v_s_3273_){
_start:
{
lean_object* v_startInclusive_3274_; lean_object* v_endExclusive_3275_; lean_object* v___x_3276_; lean_object* v___x_3277_; 
v_startInclusive_3274_ = lean_ctor_get(v_s_3273_, 1);
v_endExclusive_3275_ = lean_ctor_get(v_s_3273_, 2);
v___x_3276_ = lean_nat_sub(v_endExclusive_3275_, v_startInclusive_3274_);
v___x_3277_ = l_String_Slice_Pos_prev_x3f(v_s_3273_, v___x_3276_);
lean_dec(v___x_3276_);
if (lean_obj_tag(v___x_3277_) == 0)
{
uint32_t v___x_3278_; 
v___x_3278_ = 65;
return v___x_3278_;
}
else
{
lean_object* v_val_3279_; lean_object* v___x_3280_; 
v_val_3279_ = lean_ctor_get(v___x_3277_, 0);
lean_inc(v_val_3279_);
lean_dec_ref_known(v___x_3277_, 1);
v___x_3280_ = l_String_Slice_Pos_get_x3f(v_s_3273_, v_val_3279_);
lean_dec(v_val_3279_);
if (lean_obj_tag(v___x_3280_) == 0)
{
uint32_t v___x_3281_; 
v___x_3281_ = 65;
return v___x_3281_;
}
else
{
lean_object* v_val_3282_; uint32_t v___x_3283_; 
v_val_3282_ = lean_ctor_get(v___x_3280_, 0);
lean_inc(v_val_3282_);
lean_dec_ref_known(v___x_3280_, 1);
v___x_3283_ = lean_unbox_uint32(v_val_3282_);
lean_dec(v_val_3282_);
return v___x_3283_;
}
}
}
}
LEAN_EXPORT void l_String_Slice_back_0interp(lean_interpreter_value* stack)
{
lean_object* v_s_3273_ = stack[0].m_obj;
uint32_t v_res_3284_;
v_res_3284_ = l_String_Slice_back(v_s_3273_);
stack->m_num = v_res_3284_;
}
LEAN_EXPORT lean_object* l_String_Slice_back___boxed(lean_object* v_s_3285_){
_start:
{
uint32_t v_res_3286_; lean_object* v_r_3287_; 
v_res_3286_ = l_String_Slice_back(v_s_3285_);
lean_dec_ref(v_s_3285_);
v_r_3287_ = lean_box_uint32(v_res_3286_);
return v_r_3287_;
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(lean_object* v_acc_3288_, lean_object* v_s_3289_, lean_object* v_a_3290_){
_start:
{
if (lean_obj_tag(v_a_3290_) == 0)
{
return v_acc_3288_;
}
else
{
lean_object* v_head_3291_; lean_object* v_tail_3292_; lean_object* v_str_3293_; lean_object* v_startInclusive_3294_; lean_object* v_endExclusive_3295_; lean_object* v_str_3296_; lean_object* v_startInclusive_3297_; lean_object* v_endExclusive_3298_; lean_object* v___x_3299_; lean_object* v___x_3300_; lean_object* v___x_3301_; lean_object* v___x_3302_; 
v_head_3291_ = lean_ctor_get(v_a_3290_, 0);
v_tail_3292_ = lean_ctor_get(v_a_3290_, 1);
v_str_3293_ = lean_ctor_get(v_s_3289_, 0);
v_startInclusive_3294_ = lean_ctor_get(v_s_3289_, 1);
v_endExclusive_3295_ = lean_ctor_get(v_s_3289_, 2);
v_str_3296_ = lean_ctor_get(v_head_3291_, 0);
v_startInclusive_3297_ = lean_ctor_get(v_head_3291_, 1);
v_endExclusive_3298_ = lean_ctor_get(v_head_3291_, 2);
v___x_3299_ = lean_string_utf8_extract_fast(v_str_3293_, v_startInclusive_3294_, v_endExclusive_3295_);
v___x_3300_ = lean_string_append(v_acc_3288_, v___x_3299_);
lean_dec_ref(v___x_3299_);
v___x_3301_ = lean_string_utf8_extract_fast(v_str_3296_, v_startInclusive_3297_, v_endExclusive_3298_);
v___x_3302_ = lean_string_append(v___x_3300_, v___x_3301_);
lean_dec_ref(v___x_3301_);
v_acc_3288_ = v___x_3302_;
v_a_3290_ = v_tail_3292_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go___boxed(lean_object* v_acc_3304_, lean_object* v_s_3305_, lean_object* v_a_3306_){
_start:
{
lean_object* v_res_3307_; 
v_res_3307_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v_acc_3304_, v_s_3305_, v_a_3306_);
lean_dec(v_a_3306_);
lean_dec_ref(v_s_3305_);
return v_res_3307_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate(lean_object* v_s_3308_, lean_object* v_x_3309_){
_start:
{
if (lean_obj_tag(v_x_3309_) == 0)
{
lean_object* v___x_3310_; 
v___x_3310_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
return v___x_3310_;
}
else
{
lean_object* v_head_3311_; lean_object* v_tail_3312_; lean_object* v_str_3313_; lean_object* v_startInclusive_3314_; lean_object* v_endExclusive_3315_; lean_object* v___x_3316_; lean_object* v___x_3317_; 
v_head_3311_ = lean_ctor_get(v_x_3309_, 0);
v_tail_3312_ = lean_ctor_get(v_x_3309_, 1);
v_str_3313_ = lean_ctor_get(v_head_3311_, 0);
v_startInclusive_3314_ = lean_ctor_get(v_head_3311_, 1);
v_endExclusive_3315_ = lean_ctor_get(v_head_3311_, 2);
v___x_3316_ = lean_string_utf8_extract_fast(v_str_3313_, v_startInclusive_3314_, v_endExclusive_3315_);
v___x_3317_ = l___private_Init_Data_String_Slice_0__String_Slice_intercalate_go(v___x_3316_, v_s_3308_, v_tail_3312_);
return v___x_3317_;
}
}
}
LEAN_EXPORT lean_object* l_String_Slice_intercalate___boxed(lean_object* v_s_3318_, lean_object* v_x_3319_){
_start:
{
lean_object* v_res_3320_; 
v_res_3320_ = l_String_Slice_intercalate(v_s_3318_, v_x_3319_);
lean_dec(v_x_3319_);
lean_dec_ref(v_s_3318_);
return v_res_3320_;
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0(lean_object* v_x_3321_, lean_object* v_x_3322_){
_start:
{
if (lean_obj_tag(v_x_3322_) == 0)
{
return v_x_3321_;
}
else
{
lean_object* v_head_3323_; lean_object* v_tail_3324_; lean_object* v_str_3325_; lean_object* v_startInclusive_3326_; lean_object* v_endExclusive_3327_; lean_object* v___x_3328_; lean_object* v___x_3329_; 
v_head_3323_ = lean_ctor_get(v_x_3322_, 0);
v_tail_3324_ = lean_ctor_get(v_x_3322_, 1);
v_str_3325_ = lean_ctor_get(v_head_3323_, 0);
v_startInclusive_3326_ = lean_ctor_get(v_head_3323_, 1);
v_endExclusive_3327_ = lean_ctor_get(v_head_3323_, 2);
v___x_3328_ = lean_string_utf8_extract_fast(v_str_3325_, v_startInclusive_3326_, v_endExclusive_3327_);
v___x_3329_ = lean_string_append(v_x_3321_, v___x_3328_);
lean_dec_ref(v___x_3328_);
v_x_3321_ = v___x_3329_;
v_x_3322_ = v_tail_3324_;
goto _start;
}
}
}
LEAN_EXPORT lean_object* l_List_foldl___at___00String_Slice_join_spec__0___boxed(lean_object* v_x_3331_, lean_object* v_x_3332_){
_start:
{
lean_object* v_res_3333_; 
v_res_3333_ = l_List_foldl___at___00String_Slice_join_spec__0(v_x_3331_, v_x_3332_);
lean_dec(v_x_3332_);
return v_res_3333_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join(lean_object* v_l_3334_){
_start:
{
lean_object* v___x_3335_; lean_object* v___x_3336_; 
v___x_3335_ = ((lean_object*)(l_String_Slice_replace___redArg___closed__1));
v___x_3336_ = l_List_foldl___at___00String_Slice_join_spec__0(v___x_3335_, v_l_3334_);
return v___x_3336_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_join___boxed(lean_object* v_l_3337_){
_start:
{
lean_object* v_res_3338_; 
v_res_3338_ = l_String_Slice_join(v_l_3337_);
lean_dec(v_l_3337_);
return v_res_3338_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName(lean_object* v_s_3339_){
_start:
{
lean_object* v___x_3340_; lean_object* v___x_3341_; 
v___x_3340_ = l_String_Slice_toString(v_s_3339_);
v___x_3341_ = l_String_toName(v___x_3340_);
return v___x_3341_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_toName___boxed(lean_object* v_s_3342_){
_start:
{
lean_object* v_res_3343_; 
v_res_3343_ = l_String_Slice_toName(v_s_3342_);
lean_dec_ref(v_s_3342_);
return v_res_3343_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0(lean_object* v_s_3344_){
_start:
{
lean_object* v_str_3345_; lean_object* v_startInclusive_3346_; lean_object* v_endExclusive_3347_; lean_object* v___x_3348_; lean_object* v___x_3349_; 
v_str_3345_ = lean_ctor_get(v_s_3344_, 0);
v_startInclusive_3346_ = lean_ctor_get(v_s_3344_, 1);
v_endExclusive_3347_ = lean_ctor_get(v_s_3344_, 2);
v___x_3348_ = lean_string_utf8_extract_fast(v_str_3345_, v_startInclusive_3346_, v_endExclusive_3347_);
v___x_3349_ = lean_alloc_ctor(3, 1, 0);
lean_ctor_set(v___x_3349_, 0, v___x_3348_);
return v___x_3349_;
}
}
LEAN_EXPORT lean_object* l_String_Slice_instToFormat___lam__0___boxed(lean_object* v_s_3350_){
_start:
{
lean_object* v_res_3351_; 
v_res_3351_ = l_String_Slice_instToFormat___lam__0(v_s_3350_);
lean_dec_ref(v_s_3350_);
return v_res_3351_;
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
